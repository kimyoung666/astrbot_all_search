"""AstrBot 多引擎网页与图片搜索插件（必应 / 百度 / 哔哩哔哩）。

- 网页搜索：在必应（cn.bing.com）、百度（www.baidu.com）、哔哩哔哩（api.bilibili.com）
  上搜索公开内容。不指定引擎时并发搜索全部已启用引擎并合并结果。
- 图片搜索：支持必应与百度；哔哩哔哩不提供图片搜索，会明确提示不支持。
- 哔哩哔哩返回视频直链与视频简介（含 UP 主、播放量、时长等辅助信息）。

设计要点：
- 网页搜索与图片转发是**两项完全独立**的能力，网页搜索不会暗中附带图片。
- 图片仅在**工具调用期间**由插件直接发送到当前会话，AI 只收到不含图片直链的
  文字回执；命令路径通过 yield 返回图片链。
- 失败不泄密：日志与回执只记录稳定错误码，绝不回显 Cookie、API Key 或远端错误正文。
- 百度可用性受出口 IP 影响，被拦截时引导用户配置百度 Cookies。
"""

import asyncio
import html as _html
import json
import re
import urllib.parse
from dataclasses import dataclass, field

import aiohttp

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.message_components import Image, Plain
from astrbot.api.star import Context, Star

# ---------------------------------------------------------------------------
# 常量
# ---------------------------------------------------------------------------

# 稳定错误码：仅用于日志与回执，不暴露远端细节
E_DISABLED = "E_DISABLED"                  # 插件总开关关闭
E_WEB_DISABLED = "E_WEB_DISABLED"          # 网页搜索关闭
E_IMG_DISABLED = "E_IMG_DISABLED"          # 图片搜索关闭
E_EMPTY_QUERY = "E_EMPTY_QUERY"            # 关键词为空
E_TIMEOUT = "E_TIMEOUT"                    # 请求超时
E_NETWORK = "E_NETWORK"                    # 网络异常
E_HTTP = "E_HTTP"                          # 非 200 响应
E_PARSE = "E_PARSE"                        # 解析异常
E_NO_RESULT = "E_NO_RESULT"                # 无结果
E_SEND_FAIL = "E_SEND_FAIL"                # 图片发送失败
E_UNKNOWN_ENGINE = "E_UNKNOWN_ENGINE"      # 无法识别的引擎名
E_ENGINE_DISABLED = "E_ENGINE_DISABLED"    # 目标引擎被关闭
E_BAIDU_BLOCKED = "E_BAIDU_BLOCKED"        # 百度命中安全验证
E_BILI_RISK = "E_BILI_RISK"                # 哔哩哔哩风控（412）
E_IMG_UNSUPPORTED = "E_IMG_UNSUPPORTED"    # 该引擎不支持图片搜索
E_ALL_FAILED = "E_ALL_FAILED"              # 多引擎全部失败

# 引擎固定顺序，保证多引擎合并输出稳定
_ENGINE_ORDER = ("bing", "baidu", "bilibili")

# 引擎显示名
_ENGINE_LABELS = {
    "bing": "必应",
    "baidu": "百度",
    "bilibili": "哔哩哔哩",
}

# 引擎别名表：别名（小写）-> 引擎标识
_ENGINE_ALIASES = {
    "bing": {"bing", "必应"},
    "baidu": {"baidu", "bd", "百度"},
    "bilibili": {"bilibili", "bili", "b站", "哔哩哔哩", "哔哩", "哔站"},
}
_ALIAS_TO_ENGINE = {
    alias.lower(): engine
    for engine, aliases in _ENGINE_ALIASES.items()
    for alias in aliases
}

# 时效筛选：Bing 的 filters=ex1:"ezX" 语法
_FRESHNESS_MAP = {
    "day": "ez1",
    "week": "ez2",
    "month": "ez3",
    "year": "ez4",
}

_DEFAULT_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)

# 百度对请求头校验严格，使用完整的浏览器指纹头
_BAIDU_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

_TAG_RE = re.compile(r"<[^>]+>")
_WS_RE = re.compile(r"\s+")
# 百度结果块：只以带 mu="..."（真实结果地址）的容器为锚点切分，
# 避免把广告位 / 无结果容器误当作结果边界。
_BAIDU_BLOCK_RE = re.compile(
    r'<div[^>]*class="result c-container[^"]*"(?=[^>]*\bmu=")'
    r'(.*?)'
    r'(?=<div[^>]*class="result c-container[^"]*"[^>]*\bmu="|</body>|$)',
    re.S,
)
_BAIDU_MU_RE = re.compile(r'\bmu="([^"]+)"')
_BAIDU_H3_RE = re.compile(r"<h3[^>]*>(.*?)</h3>", re.S)
_BAIDU_SNIPPET_RE = re.compile(
    r'class="[^"]*(?:content-right|c-abstract|content-abstract)[^"]*"[^>]*>(.*?)</div>',
    re.S,
)


def _strip_tags(raw: str) -> str:
    """去掉 HTML 标签并还原实体，压缩空白。"""
    if not raw:
        return ""
    text = _TAG_RE.sub("", raw)
    text = _html.unescape(text)
    return _WS_RE.sub(" ", text).strip()


def _clamp(value, low, high, fallback):
    """安全地把配置/参数限定到 [low, high] 区间。"""
    try:
        v = int(value)
    except (TypeError, ValueError):
        return fallback
    return max(low, min(high, v))


def _normalize_url_for_dedupe(url: str) -> str:
    """URL 归一化：仅用于多引擎合并去重。"""
    if not url:
        return ""
    u = url.strip().split("#", 1)[0]
    return u.rstrip("/").lower()


# ---------------------------------------------------------------------------
# 统一数据结构与异常
# ---------------------------------------------------------------------------


@dataclass
class SearchResult:
    """统一的单条搜索结果，所有引擎归一化到该结构。"""

    title: str = ""
    url: str = ""            # 网页/视频直链；图片搜索时为原图直链
    snippet: str = ""        # 摘要 / 视频简介
    source: str = ""         # "bing" / "baidu" / "bilibili"
    extra: dict = field(default_factory=dict)


class EngineHttpError(Exception):
    """HTTP 状态异常，携带状态码，便于日志分类。"""

    def __init__(self, status: int):
        self.status = status
        super().__init__(f"http {status}")


class BaiduBlockedError(Exception):
    """百度命中安全验证（反爬拦截）。"""


class ImageUnsupportedError(Exception):
    """该引擎不支持图片搜索。"""


# ---------------------------------------------------------------------------
# 引擎基类
# ---------------------------------------------------------------------------


class BaseEngine:
    """搜索引擎基类：负责会话管理与统一请求封装。

    每个引擎自持 aiohttp 会话，避免不同站点的 Cookie 互相污染。
    """

    name: str = ""
    label: str = ""
    supports_image: bool = False

    def __init__(self, host: str, timeout: int):
        self.host = (host or "").strip().strip("/")
        if self.host.startswith(("http://", "https://")):
            self.base = self.host.rstrip("/")
        else:
            self.base = f"https://{self.host}"
        self.timeout = timeout
        self._session: aiohttp.ClientSession | None = None

    async def _new_session(self) -> aiohttp.ClientSession:
        return aiohttp.ClientSession(
            headers={"User-Agent": _DEFAULT_UA, "Accept-Language": "zh-CN,zh;q=0.9"},
        )

    async def _get_session(self) -> aiohttp.ClientSession:
        if self._session is None or self._session.closed:
            self._session = await self._new_session()
        return self._session

    async def close(self) -> None:
        if self._session and not self._session.closed:
            await self._session.close()
        self._session = None

    async def _fetch(
        self,
        url: str,
        headers: dict | None = None,
        params: dict | None = None,
        allow_redirects: bool = True,
    ) -> str:
        """发起 GET 请求，返回网页文本。异常统一抛给上层映射为错误码。"""
        session = await self._get_session()
        timeout = aiohttp.ClientTimeout(total=self.timeout)
        async with session.get(
            url,
            headers=headers,
            params=params,
            timeout=timeout,
            allow_redirects=allow_redirects,
        ) as resp:
            if resp.status != 200:
                raise EngineHttpError(resp.status)
            return await resp.text(errors="ignore")

    async def search_web(self, query: str, count: int, freshness: str = "") -> list[SearchResult]:
        raise NotImplementedError

    async def search_images(self, query: str, count: int) -> list[SearchResult]:
        raise ImageUnsupportedError


# ---------------------------------------------------------------------------
# 必应引擎
# ---------------------------------------------------------------------------


class BingEngine(BaseEngine):
    """必应搜索：网页 + 图片。"""

    name = "bing"
    label = "必应"
    supports_image = True

    async def search_web(self, query: str, count: int, freshness: str = "") -> list[SearchResult]:
        params = {
            "q": query,
            "count": str(count),
            "setlang": "zh-CN",
            "ensearch": "0",
        }
        if freshness in _FRESHNESS_MAP:
            params["filters"] = f'ex1:"{_FRESHNESS_MAP[freshness]}"'
        url = f"{self.base}/search?" + urllib.parse.urlencode(params)
        body = await self._fetch(url)
        return self._parse_web(body, count)

    def _parse_web(self, body: str, count: int) -> list[SearchResult]:
        results: list[SearchResult] = []
        blocks = re.findall(r'<li class="b_algo".*?</li>', body, re.S)
        for block in blocks:
            link = re.search(
                r'<h2[^>]*>\s*<a[^>]*href="([^"]+)"[^>]*>(.*?)</a>', block, re.S
            )
            if not link:
                continue
            url = _html.unescape(link.group(1))
            title = _strip_tags(link.group(2))
            snippet_m = re.search(r'<p[^>]*>(.*?)</p>', block, re.S)
            snippet = _strip_tags(snippet_m.group(1)) if snippet_m else ""
            if not title and not url:
                continue
            results.append(
                SearchResult(title=title, url=url, snippet=snippet, source=self.name)
            )
            if len(results) >= count:
                break
        return results

    async def search_images(self, query: str, count: int) -> list[SearchResult]:
        params = {"q": query, "first": "1", "count": str(count)}
        url = f"{self.base}/images/search?" + urllib.parse.urlencode(params)
        body = await self._fetch(url)
        return self._parse_images(body, count)

    def _parse_images(self, body: str, count: int) -> list[SearchResult]:
        results: list[SearchResult] = []
        metas = re.findall(r'class="iusc"[^>]*m="([^"]+)"', body)
        for raw in metas:
            try:
                meta = json.loads(_html.unescape(raw))
            except (ValueError, TypeError):
                continue
            murl = meta.get("murl") or meta.get("turl")
            if not murl:
                continue
            results.append(
                SearchResult(
                    title=meta.get("t", ""),
                    url=murl,
                    source=self.name,
                    extra={"thumb": meta.get("turl", ""), "purl": meta.get("purl", "")},
                )
            )
            if len(results) >= count:
                break
        return results


# ---------------------------------------------------------------------------
# 百度引擎
# ---------------------------------------------------------------------------


class BaiduEngine(BaseEngine):
    """百度搜索：网页 + 图片。

    百度反爬较强，能否成功主要取决于服务器出口 IP。
    - 用户配置了 Cookies 时，走显式 Cookie 请求头（不写入 jar，避免污染）。
    - 未配置时先请求首页预热 Cookie（BAIDUID 等）再搜索，提高成功率。
    - 命中安全验证页或解析出 0 条结果时，统一抛 BaiduBlockedError，
      以便上层引导用户配置 baidu_cookies。
    """

    name = "baidu"
    label = "百度"
    supports_image = True

    _IMAGE_HOST = "image.baidu.com"

    def __init__(self, host: str, timeout: int, cookies: str = ""):
        super().__init__(host, timeout)
        self.cookies = (cookies or "").strip()
        self._warmed = False

    async def _new_session(self) -> aiohttp.ClientSession:
        # 百度首页会写无域名 Cookie，需要 unsafe=True 才能落进 jar
        jar = aiohttp.CookieJar(unsafe=True)
        return aiohttp.ClientSession(
            headers={"User-Agent": _BAIDU_UA, "Accept-Language": "zh-CN,zh;q=0.9"},
            cookie_jar=jar,
        )

    def _headers(self, referer: str = "") -> dict:
        headers = {
            "User-Agent": _BAIDU_UA,
            "Accept": (
                "text/html,application/xhtml+xml,application/xml;q=0.9,"
                "image/avif,image/webp,*/*;q=0.8"
            ),
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "same-origin",
            "Upgrade-Insecure-Requests": "1",
        }
        if referer:
            headers["Referer"] = referer
        if self.cookies:
            headers["Cookie"] = self.cookies
        return headers

    async def _warmup(self) -> None:
        """请求首页让 CookieJar 落 BAIDUID 等基础 Cookie（仅一次）。"""
        if self._warmed:
            return
        self._warmed = True
        try:
            session = await self._get_session()
            timeout = aiohttp.ClientTimeout(total=self.timeout)
            async with session.get(
                f"{self.base}/",
                headers=self._headers(),
                timeout=timeout,
                allow_redirects=True,
            ) as resp:
                await resp.read()
        except Exception:  # noqa: BLE001 —— 预热失败不阻断后续搜索
            logger.debug("[baidu] warmup skipped")

    @staticmethod
    def _is_blocked(body: str) -> bool:
        return len(body) < 5000 and (
            "安全验证" in body or "timeout-title" in body or "wappass" in body
        )

    async def search_web(self, query: str, count: int, freshness: str = "") -> list[SearchResult]:
        await self._warmup()
        params = {
            "ie": "utf-8",
            "f": "8",
            "rsv_bp": "1",
            "tn": "baidu",
            "wd": query,
            "rn": str(count),
        }
        body = await self._fetch(
            f"{self.base}/s",
            headers=self._headers(referer=f"{self.base}/"),
            params=params,
        )
        return self._parse_web(body, count)

    def _parse_web(self, body: str, count: int) -> list[SearchResult]:
        if self._is_blocked(body):
            raise BaiduBlockedError()
        results: list[SearchResult] = []
        for block in _BAIDU_BLOCK_RE.findall(body):
            mu = _BAIDU_MU_RE.search(block)
            h3 = _BAIDU_H3_RE.search(block)
            title = _strip_tags(h3.group(1)) if h3 else ""
            url = _html.unescape(mu.group(1)) if mu else ""
            if not url and not title:
                continue
            # 百度自家跳转锚点（如 mc.baidu.com 移动版入口）不是有效结果
            if url and "mc.baidu.com" in url and not title:
                continue
            snip = _BAIDU_SNIPPET_RE.search(block)
            snippet = _strip_tags(snip.group(1)) if snip else ""
            results.append(
                SearchResult(title=title, url=url, snippet=snippet, source=self.name)
            )
            if len(results) >= count:
                break
        if not results:
            # 成功页却解析不到结果，通常仍是被风控降级，按拦截处理以给出 Cookie 引导
            raise BaiduBlockedError()
        return results

    async def search_images(self, query: str, count: int) -> list[SearchResult]:
        await self._warmup()
        params = {
            "tn": "resultjson_com",
            "ipn": "rj",
            "word": query,
            "pn": "0",
            "rn": str(count),
        }
        body = await self._fetch(
            f"https://{self._IMAGE_HOST}/search/acjson",
            headers=self._headers(referer=f"https://{self._IMAGE_HOST}/"),
            params=params,
        )
        return self._parse_images(body, count)

    def _parse_images(self, body: str, count: int) -> list[SearchResult]:
        try:
            data = json.loads(body)
        except (ValueError, TypeError) as exc:
            raise BaiduBlockedError() from exc
        if not isinstance(data, dict):
            raise BaiduBlockedError()
        items = data.get("data") or []
        results: list[SearchResult] = []
        for item in items:
            if not isinstance(item, dict):
                continue
            murl = item.get("middleURL") or item.get("hoverURL") or item.get("thumbURL")
            if not murl:
                continue
            results.append(
                SearchResult(
                    title=_strip_tags(item.get("fromPageTitleEnc", "")),
                    url=murl,
                    source=self.name,
                    extra={
                        "thumb": item.get("thumbURL", ""),
                        "from": item.get("fromURLHost", ""),
                    },
                )
            )
            if len(results) >= count:
                break
        if not results:
            raise BaiduBlockedError()
        return results


# ---------------------------------------------------------------------------
# 哔哩哔哩引擎
# ---------------------------------------------------------------------------


class BilibiliEngine(BaseEngine):
    """哔哩哔哩视频搜索：返回视频直链与视频简介。

    使用公开搜索接口，无需登录即可使用；配置 Cookies 可提升稳定性。
    未配置 Cookies 时会先访问一次主站以获取 buvid3 等设备指纹 Cookie，
    否则接口容易返回 412（风控）。
    """

    name = "bilibili"
    label = "哔哩哔哩"
    supports_image = False

    def __init__(self, host: str, timeout: int, cookies: str = ""):
        super().__init__(host, timeout)
        self.cookies = (cookies or "").strip()
        self._warmed = False

    async def _new_session(self) -> aiohttp.ClientSession:
        jar = aiohttp.CookieJar(unsafe=True)
        return aiohttp.ClientSession(
            headers={"User-Agent": _DEFAULT_UA, "Accept-Language": "zh-CN,zh;q=0.9"},
            cookie_jar=jar,
        )

    def _headers(self) -> dict:
        headers = {
            "User-Agent": _DEFAULT_UA,
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Referer": "https://search.bilibili.com/",
            "Origin": "https://search.bilibili.com",
        }
        if self.cookies:
            headers["Cookie"] = self.cookies
        return headers

    async def _warmup(self) -> None:
        """访问主站获取 buvid3 等设备指纹 Cookie（仅一次），降低 412 风控概率。"""
        if self._warmed or self.cookies:
            # 已自带 Cookies 时无需预热
            self._warmed = True
            return
        self._warmed = True
        try:
            session = await self._get_session()
            timeout = aiohttp.ClientTimeout(total=self.timeout)
            async with session.get(
                "https://www.bilibili.com/",
                headers={"User-Agent": _DEFAULT_UA, "Accept-Language": "zh-CN,zh;q=0.9"},
                timeout=timeout,
                allow_redirects=True,
            ) as resp:
                await resp.read()
        except Exception:  # noqa: BLE001 —— 预热失败不阻断后续搜索
            logger.debug("[bilibili] warmup skipped")

    async def search_web(self, query: str, count: int, freshness: str = "") -> list[SearchResult]:
        await self._warmup()
        params = {
            "search_type": "video",
            "keyword": query,
            "page": "1",
        }
        body = await self._fetch(
            f"{self.base}/x/web-interface/search/type",
            headers=self._headers(),
            params=params,
        )
        return self._parse_web(body, count)

    def _parse_web(self, body: str, count: int) -> list[SearchResult]:
        try:
            data = json.loads(body)
        except (ValueError, TypeError):
            return []
        if not isinstance(data, dict) or data.get("code") != 0:
            return []
        payload = data.get("data") or {}
        groups = payload.get("result") or []
        items = self._extract_video_items(groups)

        results: list[SearchResult] = []
        for item in items:
            if not isinstance(item, dict):
                continue
            bvid = (item.get("bvid") or "").strip()
            url = f"https://www.bilibili.com/video/{bvid}" if bvid else (item.get("arcurl") or "")
            if not url:
                continue
            snippet = (item.get("description") or "").replace("\r", "").replace("\n", " ")
            results.append(
                SearchResult(
                    title=_strip_tags(str(item.get("title", ""))),
                    url=url,
                    snippet=_WS_RE.sub(" ", snippet).strip(),
                    source=self.name,
                    extra={
                        "author": item.get("author") or item.get("uname", ""),
                        "play": item.get("play", ""),
                        "danmaku": item.get("danmaku", ""),
                        "duration": item.get("duration", ""),
                        "typename": item.get("typename", ""),
                    },
                )
            )
            if len(results) >= count:
                break
        return results

    @staticmethod
    def _extract_video_items(groups) -> list:
        """从搜索响应中取出视频列表，兼容多种返回形态。

        - `search/type`（已按 search_type=video 过滤）：`result` 直接就是视频列表。
        - `search/all/v2`：`result` 是分组列表，video 组用 `result_type`/`type`
          标记，视频在其 `data` 字段中。
        """
        if isinstance(groups, dict):
            # {"video": [...], "media_bangumi": [...]}
            return groups.get("video") or []
        if not isinstance(groups, list) or not groups:
            return []
        if not all(isinstance(g, dict) for g in groups):
            return []

        # 形态一：列表本身就是视频条目（每项直接带 bvid / arcurl）
        if any(g.get("bvid") or g.get("arcurl") for g in groups):
            return groups

        # 形态二：分组列表，找到 video 组并取其 data
        for group in groups:
            gtype = group.get("result_type") or group.get("type")
            if gtype != "video":
                continue
            inner = group.get("data")
            if isinstance(inner, list):
                return inner
            return [group]
        return []


_ENGINE_CLASSES = {
    "bing": BingEngine,
    "baidu": BaiduEngine,
    "bilibili": BilibiliEngine,
}


# ---------------------------------------------------------------------------
# 插件主体
# ---------------------------------------------------------------------------


class BingSearchPlugin(Star):
    def __init__(self, context: Context, config: dict | None = None):
        super().__init__(context)
        self.config = config or {}
        self._engines: dict[str, BaseEngine] = {}

    # -- 配置读取（每次实时读取，支持 WebUI 热更新） -------------------------

    def _cfg(self, key: str, default):
        val = self.config.get(key, default)
        return default if val is None else val

    def _want_url(self) -> bool:
        return bool(self._cfg("need_url", True))

    def _max_snippet(self) -> int:
        return _clamp(self._cfg("max_snippet_chars", 1200), 200, 8000, 1200)

    def _timeout(self) -> int:
        return _clamp(self._cfg("timeout_seconds", 30), 5, 120, 30)

    def _default_count(self) -> int:
        return _clamp(self._cfg("default_count", 5), 1, 50, 5)

    def _merge_total_count(self) -> int:
        return _clamp(self._cfg("merge_total_count", 5), 1, 50, 5)

    def _default_image_count(self) -> int:
        return _clamp(self._cfg("default_image_count", 3), 1, 5, 3)

    def _default_bilibili_count(self) -> int:
        return _clamp(self._cfg("default_bilibili_count", 5), 1, 20, 5)

    def _need_summary(self) -> bool:
        return bool(self._cfg("need_summary", True))

    def _enabled(self) -> bool:
        return bool(self._cfg("enabled", True))

    def _web_enabled(self) -> bool:
        return bool(self._cfg("enable_web_search", True))

    def _img_enabled(self) -> bool:
        return bool(self._cfg("enable_image_search", True))

    def _merge_all(self) -> bool:
        return bool(self._cfg("merge_all_engines", True))

    def _engine_enabled(self, name: str) -> bool:
        return bool(self._cfg(f"enable_{name}", True))

    def _default_engine(self) -> str:
        val = str(self._cfg("default_engine", "bing")).strip().lower()
        return val if val in _ENGINE_CLASSES else "bing"

    def _count_for(self, engine: str) -> int:
        """单引擎条数：B 站有自己的默认条数配置。"""
        if engine == "bilibili":
            return self._default_bilibili_count()
        return self._default_count()

    # -- 引擎实例管理 -------------------------------------------------------

    def _engine_for(self, name: str) -> BaseEngine:
        host_key = f"{name}_host"
        default_host = {
            "bing": "cn.bing.com",
            "baidu": "www.baidu.com",
            "bilibili": "api.bilibili.com",
        }[name]
        host = str(self._cfg(host_key, default_host))
        timeout = self._timeout()
        cookies = str(self._cfg(f"{name}_cookies", "")) if name != "bing" else ""

        engine = self._engines.get(name)
        # host / 超时 / Cookies 变化时重建，保证配置热更新生效
        if (
            engine is None
            or engine.host != host.strip().strip("/")
            or engine.timeout != timeout
            or getattr(engine, "cookies", "") != cookies.strip()
        ):
            if engine is not None:
                # 旧会话交由事件循环回收，避免阻塞当前调用
                asyncio.ensure_future(engine.close())
            cls = _ENGINE_CLASSES[name]
            if name == "bing":
                engine = cls(host, timeout)
            else:
                engine = cls(host, timeout, cookies)
            self._engines[name] = engine
        return engine

    # -- 统一抓取封装（错误码 + 日志脱敏） ----------------------------------

    @staticmethod
    def _map_exception(name: str, exc: BaseException) -> str:
        """把引擎异常映射为稳定错误码。"""
        if isinstance(exc, asyncio.TimeoutError):
            logger.warning("[%s] %s", name, E_TIMEOUT)
            return E_TIMEOUT
        if isinstance(exc, BaiduBlockedError):
            logger.warning("[%s] %s", name, E_BAIDU_BLOCKED)
            return E_BAIDU_BLOCKED
        if isinstance(exc, ImageUnsupportedError):
            return E_IMG_UNSUPPORTED
        if isinstance(exc, EngineHttpError):
            logger.warning("[%s] %s status=%s", name, E_HTTP, exc.status)
            # 哔哩哔哩的 412 是风控限流，单独给出可操作提示
            if name == "bilibili" and exc.status == 412:
                return E_BILI_RISK
            return E_HTTP
        if isinstance(exc, aiohttp.ClientError):
            logger.warning("[%s] %s", name, E_NETWORK)
            return E_NETWORK
        logger.warning("[%s] %s", name, E_PARSE, exc_info=True)
        return E_PARSE

    async def _fetch_web(self, name: str, query: str, count: int, freshness: str = "") -> tuple[str, list]:
        """单引擎网页搜索，返回 (错误码或空串, 结果列表)。"""
        engine = self._engine_for(name)
        try:
            results = await engine.search_web(query, count, freshness)
        except Exception as exc:  # noqa: BLE001 —— 兜底，绝不外泄异常正文
            return self._map_exception(name, exc), []
        if not results:
            return E_NO_RESULT, []
        return "", results

    async def _fetch_images(self, name: str, query: str, count: int) -> tuple[str, list]:
        engine = self._engine_for(name)
        try:
            results = await engine.search_images(query, count)
        except Exception as exc:  # noqa: BLE001
            return self._map_exception(name, exc), []
        if not results:
            return E_NO_RESULT, []
        return "", results

    async def _run_web(self, engines: list[str], query: str, freshness: str = "") -> tuple[dict, list]:
        """并发执行多引擎网页搜索。

        返回 (每引擎明细 {engine: (code, results)}, 合并去重并截断后的结果列表)。

        多引擎合并时采用**轮转（round-robin）**取样：先各引擎取第 1 条，
        再各取第 2 条……这样各引擎结果都能出现在有限的总条数里，
        不会因为第一个引擎条数多就把其他引擎挤掉。
        """
        tasks = [self._fetch_web(e, query, self._count_for(e), freshness) for e in engines]
        raw = await asyncio.gather(*tasks, return_exceptions=True)

        details: dict[str, tuple[str, list]] = {}
        ordered = [e for e in _ENGINE_ORDER if e in engines]
        for name in ordered:
            item = raw[engines.index(name)]
            if isinstance(item, BaseException):
                details[name] = (self._map_exception(name, item), [])
                continue
            code, results = item
            details[name] = (code, results)

        # 轮转合并 + 按 URL 去重
        merged: list[SearchResult] = []
        seen: set[str] = set()
        limit = self._merge_total_count()
        buckets = [list(details.get(n, ("", []))[1]) for n in ordered]
        idx = 0
        while len(merged) < limit and any(buckets):
            progressed = False
            for bucket in buckets:
                if idx < len(bucket):
                    progressed = True
                    r = bucket[idx]
                    key = _normalize_url_for_dedupe(r.url)
                    if key and key in seen:
                        continue
                    if key:
                        seen.add(key)
                    merged.append(r)
                    if len(merged) >= limit:
                        break
            if not progressed:
                break
            idx += 1
        return details, merged

    async def _run_images(self, engines: list[str], query: str) -> tuple[dict, list]:
        tasks = [self._fetch_images(e, query, self._default_image_count()) for e in engines]
        raw = await asyncio.gather(*tasks, return_exceptions=True)

        details: dict[str, tuple[str, list]] = {}
        merged: list[SearchResult] = []
        seen: set[str] = set()
        ordered = [e for e in _ENGINE_ORDER if e in engines]
        for name in ordered:
            item = raw[engines.index(name)]
            if isinstance(item, BaseException):
                details[name] = (self._map_exception(name, item), [])
                continue
            code, results = item
            details[name] = (code, results)
            for r in results:
                key = _normalize_url_for_dedupe(r.url)
                if key and key in seen:
                    continue
                if key:
                    seen.add(key)
                merged.append(r)
        return details, merged[: self._default_image_count()]

    # -- 结果格式化 ---------------------------------------------------------

    def _clip(self, text: str, limit: int) -> str:
        return text[:limit] + "…" if len(text) > limit else text

    def _result_lines(self, idx: int, item: SearchResult, show_tag: bool) -> list[str]:
        """单条结果的格式化行。哔哩哔哩按需求展示「视频直链 + 视频简介」。"""
        want_url = self._want_url()
        want_summary = self._need_summary()
        limit = self._max_snippet()
        tag = f"[{item.source}] " if show_tag else ""
        lines = [f"{idx}. {tag}标题：{item.title or '（无标题）'}"]

        if item.source == "bilibili":
            if want_url and item.url:
                lines.append(f"   链接：{item.url}")
            if want_summary and item.snippet:
                lines.append(f"   简介：{self._clip(item.snippet, limit)}")
            extra = item.extra or {}
            meta = []
            if extra.get("author"):
                meta.append(f"UP主：{extra['author']}")
            if extra.get("play") not in ("", None):
                meta.append(f"播放：{extra['play']}")
            if extra.get("duration"):
                meta.append(f"时长：{extra['duration']}")
            if extra.get("typename"):
                meta.append(f"分区：{extra['typename']}")
            if meta:
                lines.append("   " + "｜".join(meta))
            return lines

        if want_summary and item.snippet:
            lines.append(f"   摘要：{self._clip(item.snippet, limit)}")
        if want_url and item.url:
            lines.append(f"   来源：{item.url}")
        return lines

    def _web_text(self, query: str, merged: list, details: dict) -> str:
        """把多引擎网页结果格式化为给 AI 的纯文本（不含任何图片）。"""
        show_tag = len(details) > 1
        multi = len(merged) > 1 or show_tag
        head = (
            f"搜索结果（关键词：{query}，合并 {len(merged)} 条）："
            if multi
            else f"搜索结果（关键词：{query}，共 {len(merged)} 条）："
        )
        lines = [head]
        for idx, item in enumerate(merged, 1):
            lines.extend(self._result_lines(idx, item, show_tag))

        failures = [(n, c) for n, (c, _r) in details.items() if c]
        if failures:
            lines.append("——")
            for name, code in failures:
                lines.append(f"{_ENGINE_LABELS.get(name, name)}：{self._error_text(code, name)}")
        return "\n".join(lines)

    def _error_text(self, code: str, engine: str = "") -> str:
        mapping = {
            E_TIMEOUT: "搜索请求超时，请稍后再试。",
            E_NETWORK: "网络异常，搜索请求失败。",
            E_HTTP: "搜索服务返回异常响应。",
            E_PARSE: "搜索结果解析失败。",
            E_NO_RESULT: "未找到相关结果。",
            E_BAIDU_BLOCKED: (
                "触发安全验证（百度成功率取决于服务器出口 IP），"
                "请在 WebUI 填写「百度 Cookies」后重试。"
            ),
            E_BILI_RISK: (
                "触发风控限流，请稍后重试；或在 WebUI 填写「哔哩哔哩 Cookies」"
                "（建议包含 buvid3）以提升稳定性。"
            ),
            E_IMG_UNSUPPORTED: "该引擎不支持图片搜索，请改用 bing 或 baidu。",
            E_ENGINE_DISABLED: "该引擎已在插件配置中关闭。",
            E_UNKNOWN_ENGINE: "无法识别的搜索引擎。",
            E_ALL_FAILED: "所有搜索引擎均未返回结果。",
        }
        text = mapping.get(code, "搜索失败，请稍后再试。")
        if engine and code == E_ENGINE_DISABLED:
            text = f"{_ENGINE_LABELS.get(engine, engine)}：{text}"
        return text

    # -- 命令解析 -----------------------------------------------------------

    @staticmethod
    def _parse_engine_and_query(msg: str) -> tuple[list[str], str]:
        """从消息中解析「引擎 + 关键词」。

        规则：
        - 从消息开头连续剥离命中的引擎名（如 bing / 百度 / b站），其余为关键词。
        - 单个 token 内可用英文逗号列举多个引擎，如 `bing,baidu 关键词`。
        - 未命中任何引擎则整个消息都是关键词，引擎列表为空（表示使用默认策略）。
        """
        msg = (msg or "").strip()
        if not msg:
            return [], ""
        tokens = msg.split()
        engines: list[str] = []
        while tokens:
            # 首个 token 支持逗号列举：bing,baidu
            parts = [p.strip().lower() for p in tokens[0].split(",")]
            if parts and all(p and p in _ALIAS_TO_ENGINE for p in parts):
                for p in parts:
                    eng = _ALIAS_TO_ENGINE[p]
                    if eng not in engines:
                        engines.append(eng)
                tokens.pop(0)
                continue
            if tokens[0].lower() in _ALIAS_TO_ENGINE:
                eng = _ALIAS_TO_ENGINE[tokens[0].lower()]
                if eng not in engines:
                    engines.append(eng)
                tokens.pop(0)
                continue
            break
        query = " ".join(tokens).strip()
        return engines, query

    def _extract_query(self, event: AstrMessageEvent) -> str:
        """从消息中去掉命令前缀，取剩余关键词（不含引擎解析）。"""
        msg = (event.message_str or "").strip()
        if not msg:
            return ""
        parts = msg.split(maxsplit=1)
        return parts[1].strip() if len(parts) > 1 else ""

    def _want_engines_web(self, requested: list[str]) -> tuple[list[str], str]:
        """解析网页搜索要用的引擎列表，返回 (引擎列表, 错误码或空串)。"""
        if requested:
            for name in requested:
                if not self._engine_enabled(name):
                    return [], E_ENGINE_DISABLED
            return requested, ""
        if self._merge_all():
            engines = [e for e in _ENGINE_ORDER if self._engine_enabled(e)]
            return engines, ""
        return [self._default_engine()], ""

    def _want_engines_image(self, requested: list[str]) -> tuple[list[str], str]:
        """图片搜索：哔哩哔哩不支持；默认只用支持图片的引擎。"""
        if requested:
            for name in requested:
                if not _ENGINE_CLASSES[name].supports_image:
                    return [], E_IMG_UNSUPPORTED
                if not self._engine_enabled(name):
                    return [], E_ENGINE_DISABLED
            return requested, ""
        engines = [
            e for e in _ENGINE_ORDER
            if _ENGINE_CLASSES[e].supports_image and self._engine_enabled(e)
        ]
        if not engines:
            return [], E_IMG_DISABLED
        return engines, ""

    # -- 命令：中文主命令 + 英文兼容 ----------------------------------------

    @filter.command("搜索")
    async def cmd_web_zh(self, event: AstrMessageEvent):
        """多引擎网页搜索"""
        async for r in self._cmd_web(event):
            yield r

    @filter.command("search")
    async def cmd_web_en(self, event: AstrMessageEvent):
        """多引擎网页搜索（英文兼容命令）"""
        async for r in self._cmd_web(event):
            yield r

    @filter.command("搜图")
    async def cmd_image_zh(self, event: AstrMessageEvent):
        """多引擎图片搜索"""
        async for r in self._cmd_image(event):
            yield r

    @filter.command("image")
    async def cmd_image_en(self, event: AstrMessageEvent):
        """多引擎图片搜索（英文兼容命令）"""
        async for r in self._cmd_image(event):
            yield r

    async def _cmd_web(self, event: AstrMessageEvent):
        if not self._enabled():
            yield event.plain_result("搜索插件当前已关闭。")
            return
        if not self._web_enabled():
            yield event.plain_result("网页搜索功能当前已关闭。")
            return
        requested, query = self._parse_engine_and_query(self._extract_query(event))
        if not query:
            yield event.plain_result(
                "用法：/搜索 [搜索引擎] <关键词>\n"
                "搜索引擎可选：bing/必应、百度/bd、bilibili/b站；留空则搜索全部引擎。"
            )
            return
        engines, code = self._want_engines_web(requested)
        if not engines:
            yield event.plain_result(self._error_text(code, requested[0] if requested else ""))
            return
        details, merged = await self._run_web(engines, query)
        if not merged:
            # 全部失败：优先给出百度 Cookie 引导
            codes = [c for c, _r in details.values() if c]
            pick = E_BAIDU_BLOCKED if E_BAIDU_BLOCKED in codes else (codes[0] if codes else E_ALL_FAILED)
            yield event.plain_result(self._error_text(pick, engines[0]))
            return
        yield event.plain_result(self._web_text(query, merged, details))

    async def _cmd_image(self, event: AstrMessageEvent):
        if not self._enabled():
            yield event.plain_result("搜索插件当前已关闭。")
            return
        if not self._img_enabled():
            yield event.plain_result("图片搜索功能当前已关闭。")
            return
        requested, query = self._parse_engine_and_query(self._extract_query(event))
        if not query:
            yield event.plain_result(
                "用法：/搜图 [搜索引擎] <关键词>\n"
                "搜索引擎可选：bing/必应、百度/bd；哔哩哔哩不支持图片搜索。"
            )
            return
        engines, code = self._want_engines_image(requested)
        if not engines:
            yield event.plain_result(self._error_text(code, requested[0] if requested else ""))
            return
        details, merged = await self._run_images(engines, query)
        if not merged:
            codes = [c for c, _r in details.values() if c]
            pick = E_BAIDU_BLOCKED if E_BAIDU_BLOCKED in codes else (codes[0] if codes else E_ALL_FAILED)
            yield event.plain_result(self._error_text(pick, engines[0]))
            return
        chain = [Plain(f"图片搜索（关键词：{query}），共 {len(merged)} 张：")]
        for item in merged:
            chain.append(Image(item.url))
        yield event.chain_result(chain)

    # -- LLM 工具 1：网页搜索（绝不附图） -----------------------------------

    async def _tool_web(self, event: AstrMessageEvent, query: str, count: int = 0,
                        freshness: str = "", engine: str = ""):
        """网页搜索工具的内部实现。"""
        if not self._enabled():
            yield event.plain_result(f"搜索失败（{E_DISABLED}）：插件已关闭。")
            return
        if not self._web_enabled():
            yield event.plain_result(f"搜索失败（{E_WEB_DISABLED}）：网页搜索已关闭。")
            return
        q = (query or "").strip()
        if not q:
            yield event.plain_result(f"搜索失败（{E_EMPTY_QUERY}）：关键词为空。")
            return

        requested: list[str] = []
        raw_engine = (engine or "").strip()
        if raw_engine:
            key = raw_engine.lower()
            if key in _ALIAS_TO_ENGINE:
                requested = [_ALIAS_TO_ENGINE[key]]
            else:
                yield event.plain_result(f"搜索失败（{E_UNKNOWN_ENGINE}）：{raw_engine}")
                return

        engines, code = self._want_engines_web(requested)
        if not engines:
            yield event.plain_result(f"搜索失败（{code}）。")
            return

        merged: list = []
        details: dict = {}
        if len(engines) == 1 and count:
            # 显式指定条数且单引擎时，尊重调用方要求
            n = _clamp(count, 1, 50, self._count_for(engines[0]))
            name = engines[0]
            c, results = await self._fetch_web(name, q, n, (freshness or "").strip().lower())
            details[name] = (c, results)
            merged = results
        else:
            details, merged = await self._run_web(engines, q, (freshness or "").strip().lower())

        if not merged:
            codes = [c for c, _r in details.values() if c]
            pick = E_BAIDU_BLOCKED if E_BAIDU_BLOCKED in codes else (codes[0] if codes else E_ALL_FAILED)
            yield event.plain_result(f"搜索失败（{pick}）。")
            return
        yield event.plain_result(self._web_text(q, merged, details))

    @filter.llm_tool(name="web_search_bing")
    async def web_search_bing(self, event: AstrMessageEvent, query: str, count: int = 0,
                              freshness: str = "", engine: str = ""):
        """在搜索引擎（必应/百度/哔哩哔哩）搜索公开网页与视频，返回带标题、摘要与来源的结果列表。

        仅返回文本结果，不会附带或转发任何图片。
        哔哩哔哩返回视频直链与视频简介。

        Args:
            query(string): 搜索关键词，必填。
            count(number): 需要的结果条数，可选，1-50，默认使用插件配置值。
            freshness(string): 时效筛选，可选，取值 day/week/month/year 之一，留空表示不限（仅必应生效）。
            engine(string): 指定搜索引擎，可选，取值 bing / baidu / bilibili 或其别名
                （必应、百度、bd、b站、bili、哔哩哔哩）；留空表示搜索全部已启用引擎并合并结果。
        """
        async for r in self._tool_web(event, query, count, freshness, engine):
            yield r

    @filter.llm_tool(name="web_search")
    async def web_search(self, event: AstrMessageEvent, query: str, count: int = 0,
                         freshness: str = "", engine: str = ""):
        """在搜索引擎（必应/百度/哔哩哔哩）搜索公开网页与视频，返回带标题、摘要与来源的结果列表。

        Args:
            query(string): 搜索关键词，必填。
            count(number): 需要的结果条数，可选，1-50，默认使用插件配置值。
            freshness(string): 时效筛选，可选，取值 day/week/month/year 之一，留空表示不限（仅必应生效）。
            engine(string): 指定搜索引擎，可选，取值 bing / baidu / bilibili 或其别名；留空表示全部引擎。
        """
        async for r in self._tool_web(event, query, count, freshness, engine):
            yield r

    # -- LLM 工具 2：图片搜索（工具调用期间直接发图，回执不含直链） ---------

    async def _tool_image(self, event: AstrMessageEvent, query: str, count: int = 0,
                          engine: str = ""):
        """图片搜索工具的内部实现。"""
        if not self._enabled():
            yield event.plain_result(f"搜图失败（{E_DISABLED}）：插件已关闭。")
            return
        if not self._img_enabled():
            yield event.plain_result(f"搜图失败（{E_IMG_DISABLED}）：图片搜索已关闭。")
            return
        q = (query or "").strip()
        if not q:
            yield event.plain_result(f"搜图失败（{E_EMPTY_QUERY}）：关键词为空。")
            return

        requested: list[str] = []
        raw_engine = (engine or "").strip()
        if raw_engine:
            key = raw_engine.lower()
            if key in _ALIAS_TO_ENGINE:
                requested = [_ALIAS_TO_ENGINE[key]]
            else:
                yield event.plain_result(f"搜图失败（{E_UNKNOWN_ENGINE}）：{raw_engine}")
                return

        engines, code = self._want_engines_image(requested)
        if not engines:
            yield event.plain_result(f"搜图失败（{code}）：{self._error_text(code)}")
            return

        details, merged = await self._run_images(engines, q)
        if not merged:
            codes = [c for c, _r in details.values() if c]
            pick = E_BAIDU_BLOCKED if E_BAIDU_BLOCKED in codes else (codes[0] if codes else E_ALL_FAILED)
            yield event.plain_result(f"搜图失败（{pick}）。")
            return

        if count:
            merged = merged[: _clamp(count, 1, 5, self._default_image_count())]

        sent = 0
        failed = 0
        for item in merged:
            try:
                await event.send(event.make_result().url_image(item.url))
                sent += 1
            except Exception:  # noqa: BLE001 —— 单张失败继续尝试剩余图片
                failed += 1
                logger.warning("[search] %s", E_SEND_FAIL)
            await asyncio.sleep(0.3)  # 轻微节流，避免刷屏触发平台风控

        if sent == 0:
            yield event.plain_result(f"搜图失败（{E_SEND_FAIL}）：{failed} 张图片均发送失败。")
            return
        yield event.plain_result(f"图搜完成：已发送 {sent} 张，失败 {failed} 张（来源已随图片保留）。")

    @filter.llm_tool(name="image_search_bing")
    async def image_search_bing(self, event: AstrMessageEvent, query: str, count: int = 0,
                                engine: str = ""):
        """在搜索引擎（必应/百度）搜索图片，并在本次工具调用期间直接把 1-5 张图片发送到当前对话。

        图片由插件直接发送给用户，调用方只会收到不含图片直链的文字回执
        （包含成功与失败的数量），无需也不能再次转发图片。
        哔哩哔哩不支持图片搜索。

        Args:
            query(string): 搜索关键词，必填。
            count(number): 需要发送的图片数量，可选，1-5，默认使用插件配置值。
            engine(string): 指定搜索引擎，可选，取值 bing / baidu 或其别名（必应、百度、bd）；
                留空表示使用全部支持图片搜索的已启用引擎。哔哩哔哩不支持图片搜索。
        """
        async for r in self._tool_image(event, query, count, engine):
            yield r

    @filter.llm_tool(name="image_search")
    async def image_search(self, event: AstrMessageEvent, query: str, count: int = 0,
                           engine: str = ""):
        """在搜索引擎（必应/百度）搜索图片，并在本次工具调用期间直接把 1-5 张图片发送到当前对话。

        Args:
            query(string): 搜索关键词，必填。
            count(number): 需要发送的图片数量，可选，1-5，默认使用插件配置值。
            engine(string): 指定搜索引擎，可选，取值 bing / baidu 或其别名；留空表示全部支持图片的引擎。
        """
        async for r in self._tool_image(event, query, count, engine):
            yield r

    # -- 生命周期 -----------------------------------------------------------

    async def terminate(self):
        """插件卸载/停用时释放所有网络会话。"""
        for engine in list(self._engines.values()):
            try:
                await engine.close()
            except Exception:  # noqa: BLE001
                logger.debug("[search] close engine failed")
        self._engines.clear()
