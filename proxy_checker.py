#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Verificador / gerador de listas de proxies para o MegaBasterd.

Baixa as fontes publicas, testa cada proxy (HTTP, HTTPS CONNECT e SOCKS5),
mede latencia e (opcionalmente) velocidade de download, e grava listas
ordenadas do mais rapido para o mais lento em:

    http.txt    -> proxies HTTP validos em requisicao HTTP pura
    https.txt   -> proxies HTTP validos no tunel HTTPS (CONNECT) - ideais p/ MegaBasterd
    socks5.txt  -> proxies SOCKS5 validos no tunel HTTPS

Formato de saida compativel com o MegaBasterd: IP:PORT ou
IP:PORT@base64(usuario):base64(senha). Arquivos .txt antigos sao copiados
para uma subpasta backup_<data> antes de serem substituidos.

Exemplos:
    python proxy_checker.py
    python proxy_checker.py --threads 300 --limit 500
    python proxy_checker.py --from-file proxy/http.txt
    python proxy_checker.py --out "E:\\caminho\\proxy" --speed-test 120
"""

from __future__ import annotations

import argparse
import base64
import contextlib
import csv
import http.client
import os
import re
import shutil
import socket
import ssl
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from urllib.parse import urlsplit
from urllib.request import Request, build_opener, ProxyHandler

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# (familia, url) -- familia "http" cobre proxies que falam HTTP/HTTPS CONNECT.
SOURCES: list[tuple[str, str]] = [
    ("http", "https://raw.githubusercontent.com/mmpx12/proxy-list/master/http.txt"),
    ("http", "https://raw.githubusercontent.com/mmpx12/proxy-list/master/https.txt"),
    ("http", "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt"),
    ("http", "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt"),
    ("http", "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/protocols/http/data.txt"),
    ("http", "https://raw.githubusercontent.com/roosterkid/openproxylist/main/HTTPS_RAW.txt"),
    ("http", "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/https.txt"),
    ("socks5", "https://raw.githubusercontent.com/mmpx12/proxy-list/master/socks5.txt"),
    ("socks5", "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/protocols/socks5/data.txt"),
]

DEFAULT_HTTPS_URL = "https://mega.nz/"
DEFAULT_HTTPS_FALLBACKS = ["https://g.api.mega.co.nz/cs"]
DEFAULT_HTTP_URL = "http://checkip.amazonaws.com/"
DEFAULT_HTTP_FALLBACKS = [
    "http://icanhazip.com/",
    "http://ifconfig.me/ip",
    "http://api.ipify.org/?format=json",
]
DEFAULT_SPEED_URL = "https://cachefly.cachefly.net/1mb.test"
DEFAULT_HTTP_SPEED_URL = "http://cachefly.cachefly.net/1mb.test"

HOST_RE = re.compile(r"^(?:\d{1,3}(?:\.\d{1,3}){3}|[A-Za-z0-9](?:[A-Za-z0-9.-]*[A-Za-z0-9])?)$")
IP_TEXT_RE = re.compile(r"^(?:\d{1,3}(?:\.\d{1,3}){3}|[0-9A-Fa-f:]{2,45})$")
SCHEME_RE = re.compile(r"^(?P<scheme>[A-Za-z][A-Za-z0-9+.-]*)://")

_SSL_CTX: ssl.SSLContext | None = None
_SSL_LOCK = threading.Lock()
_LOCAL_IP: str | None = None


class ProxyFailure(Exception):
    pass


class TcpUnreachable(ProxyFailure):
    pass


class TargetRejected(ProxyFailure):
    pass


# --------------------------------------------------------------------------
# Modelos
# --------------------------------------------------------------------------


@dataclass
class Proxy:
    proto: str  # "http" | "socks5"
    host: str
    port: int
    user: str | None = None
    password: str | None = None

    @property
    def addr(self) -> str:
        return f"{self.host}:{self.port}"

    def key(self) -> tuple:
        return (self.proto, self.host.lower(), self.port, self.user, self.password)

    def mega_line(self) -> str:
        if self.user is None:
            return self.addr
        u = base64.b64encode((self.user or "").encode("utf-8")).decode("ascii")
        p = base64.b64encode((self.password or "").encode("utf-8")).decode("ascii")
        return f"{self.addr}@{u}:{p}"


@dataclass
class Result:
    proxy: Proxy
    http_ok: bool = False
    https_ok: bool = False
    http_ms: float | None = None
    https_ms: float | None = None
    speed_kbps: float | None = None
    speed_via: str = ""
    http_err: str = ""
    https_err: str = ""
    sources: set[str] = field(default_factory=set)

    @property
    def latency(self) -> float:
        vals = [v for v in (self.https_ms, self.http_ms) if v is not None]
        return min(vals) if vals else float("inf")


# --------------------------------------------------------------------------
# Parsing de entradas
# --------------------------------------------------------------------------


def _valid_host(host: str) -> bool:
    if not host or not HOST_RE.match(host):
        return False
    if re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", host):
        return all(0 <= int(part) <= 255 for part in host.split("."))
    return True


def _split_hostport(text: str) -> tuple[str, int] | None:
    text = text.strip()
    if text.count(":") != 1:
        return None
    host, port_s = text.rsplit(":", 1)
    host = host.strip()
    if not _valid_host(host) or not port_s.isdigit():
        return None
    port = int(port_s)
    if not 1 <= port <= 65535:
        return None
    return host, port


def _decode_auth(text: str) -> tuple[str, str]:
    if ":" not in text:
        return text, ""
    u, p = text.split(":", 1)
    try:
        du = base64.b64decode(u, validate=True).decode("utf-8")
        dp = base64.b64decode(p, validate=True).decode("utf-8")
        return du, dp
    except Exception:
        return u, p


def parse_line(line: str, default_proto: str, source: str) -> Proxy | None:
    line = line.strip().lstrip("\ufeff").strip()
    if not line or line.startswith("#"):
        return None
    low = line.lower()
    if low.startswith("error code") or low.startswith("<") or low.startswith("{"):
        return None

    proto = default_proto
    if line.startswith("*"):
        proto = "socks5"
        line = line[1:].strip()

    had_scheme = False
    m = SCHEME_RE.match(line)
    if m:
        scheme = m.group("scheme").lower()
        line = line[m.end():].strip()
        had_scheme = True
        if scheme in ("http", "https"):
            proto = "http"
        elif scheme in ("socks5", "socks", "socks5h"):
            proto = "socks5"
        elif scheme in ("socks4", "socks4a"):
            return None
        else:
            return None

    auth: tuple[str, str] | None = None
    if "@" in line:
        left, right = line.split("@", 1)
        left_hp = _split_hostport(left)
        right_hp = _split_hostport(right)
        if had_scheme and right_hp is not None:
            # http://usuario:senha@ip:porta
            auth = _decode_auth(left)
            hostport = right_hp
        elif left_hp is not None:
            # ip:porta@b64usuario:b64senha (formato do MegaBasterd)
            auth = _decode_auth(right)
            hostport = left_hp
        elif right_hp is not None:
            auth = _decode_auth(left)
            hostport = right_hp
        else:
            return None
    else:
        hostport = _split_hostport(line)
        if hostport is None:
            return None

    host, port = hostport
    if auth is None:
        return Proxy(proto, host, port)
    return Proxy(proto, host, port, auth[0], auth[1])


# --------------------------------------------------------------------------
# Rede
# --------------------------------------------------------------------------


def _ssl_context() -> ssl.SSLContext:
    global _SSL_CTX
    with _SSL_LOCK:
        if _SSL_CTX is None:
            _SSL_CTX = ssl.create_default_context()
        return _SSL_CTX


def _connect(host: str, port: int, timeout: float) -> socket.socket:
    try:
        return socket.create_connection((host, port), timeout=min(timeout, 5.0))
    except OSError as exc:
        raise TcpUnreachable(str(exc) or type(exc).__name__) from exc


def _recv_exact(sock: socket.socket, n: int, deadline: float | None = None) -> bytes:
    buf = bytearray()
    while len(buf) < n:
        if deadline is not None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise socket.timeout("tempo esgotado")
            sock.settimeout(remaining)
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise ProxyFailure("conexao encerrada")
        buf.extend(chunk)
    return bytes(buf)


def _read_until(sock: socket.socket, delim: bytes, deadline: float, limit: int = 65536) -> bytes:
    buf = bytearray()
    while delim not in buf:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise socket.timeout("tempo esgotado")
        sock.settimeout(remaining)
        chunk = sock.recv(4096)
        if not chunk:
            break
        buf.extend(chunk)
        if len(buf) > limit:
            break
    return bytes(buf)


def _basic_token(p: Proxy) -> str:
    raw = f"{p.user}:{p.password or ''}".encode("utf-8")
    return base64.b64encode(raw).decode("ascii")


def _http_tunnel(p: Proxy, host: str, port: int, timeout: float) -> socket.socket:
    sock = _connect(p.host, p.port, timeout)
    deadline = time.monotonic() + timeout
    try:
        req = (
            f"CONNECT {host}:{port} HTTP/1.1\r\n"
            f"Host: {host}:{port}\r\n"
            f"User-Agent: {UA}\r\n"
            "Proxy-Connection: keep-alive\r\n"
        )
        if p.user is not None:
            req += f"Proxy-Authorization: Basic {_basic_token(p)}\r\n"
        req += "\r\n"
        sock.sendall(req.encode("latin-1"))
        data = _read_until(sock, b"\r\n\r\n", deadline)
        if not data:
            raise ProxyFailure("CONNECT sem resposta")
        status = data.split(b"\r\n", 1)[0].decode("latin-1", "replace")
        if not re.match(r"HTTP/\d(?:\.\d)?\s+2\d\d", status):
            raise ProxyFailure(status[:90])
        return sock
    except Exception:
        with contextlib.suppress(Exception):
            sock.close()
        raise


def _socks5_tunnel(p: Proxy, host: str, port: int, timeout: float) -> socket.socket:
    sock = _connect(p.host, p.port, timeout)
    deadline = time.monotonic() + timeout
    try:
        if p.user is not None:
            sock.sendall(b"\x05\x02\x00\x02")
        else:
            sock.sendall(b"\x05\x01\x00")
        ver, method = _recv_exact(sock, 2, deadline)
        if ver != 0x05:
            raise ProxyFailure("SOCKS5 versao invalida")
        if method == 0x02:
            u = (p.user or "").encode("utf-8")[:255]
            pw = (p.password or "").encode("utf-8")[:255]
            sock.sendall(bytes([0x01, len(u)]) + u + bytes([len(pw)]) + pw)
            _, status = _recv_exact(sock, 2, deadline)
            if status != 0x00:
                raise ProxyFailure("SOCKS5 auth recusada")
        elif method != 0x00:
            raise ProxyFailure(f"SOCKS5 metodo {method} recusado")

        hostb = host.encode("idna")
        if len(hostb) > 255:
            raise ProxyFailure("host SOCKS5 longo demais")
        sock.sendall(
            b"\x05\x01\x00\x03"
            + bytes([len(hostb)])
            + hostb
            + port.to_bytes(2, "big")
        )
        ver, rep, _, atyp = _recv_exact(sock, 4, deadline)
        if ver != 0x05 or rep != 0x00:
            raise ProxyFailure(f"SOCKS5 CONNECT recusado (codigo {rep})")
        if atyp == 0x01:
            _recv_exact(sock, 4, deadline)
        elif atyp == 0x03:
            size = _recv_exact(sock, 1, deadline)[0]
            _recv_exact(sock, size, deadline)
        elif atyp == 0x04:
            _recv_exact(sock, 16, deadline)
        else:
            raise ProxyFailure("SOCKS5 resposta invalida")
        _recv_exact(sock, 2, deadline)
        return sock
    except Exception:
        with contextlib.suppress(Exception):
            sock.close()
        raise


def _tunnel(p: Proxy, host: str, port: int, timeout: float) -> socket.socket:
    if p.proto == "socks5":
        return _socks5_tunnel(p, host, port, timeout)
    return _http_tunnel(p, host, port, timeout)


def _wrap_tls(sock: socket.socket, host: str, timeout: float) -> ssl.SSLSocket:
    sock.settimeout(timeout)
    return _ssl_context().wrap_socket(sock, server_hostname=host)


def split_url(url: str) -> tuple[str, str, int, str]:
    if "://" not in url:
        url = "http://" + url
    u = urlsplit(url)
    if not u.hostname:
        raise ValueError(f"URL invalida: {url}")
    scheme = u.scheme.lower()
    port = u.port or (443 if scheme == "https" else 80)
    path = u.path or "/"
    if u.query:
        path += "?" + u.query
    return scheme, u.hostname, port, path


def _read_response(sock: socket.socket, max_read: int) -> tuple[int, bytes]:
    resp = http.client.HTTPResponse(sock, method="GET")
    status = 0
    body = b""
    try:
        resp.begin()
        status = resp.status
        try:
            body = resp.read(max_read)
        except http.client.IncompleteRead as exc:
            body = exc.partial
    finally:
        with contextlib.suppress(Exception):
            resp.close()
    return status, body


def _get_via_tunnel(
    sock: socket.socket, host: str, port: int, path: str, timeout: float, max_read: int
) -> tuple[int, bytes]:
    sock.settimeout(timeout)
    host_hdr = host if port == 443 else f"{host}:{port}"
    req = (
        f"GET {path} HTTP/1.1\r\n"
        f"Host: {host_hdr}\r\n"
        f"User-Agent: {UA}\r\n"
        "Accept: */*\r\n"
        "Accept-Encoding: identity\r\n"
        "Connection: close\r\n\r\n"
    )
    sock.sendall(req.encode("latin-1"))
    return _read_response(sock, max_read)


def _get_absolute(
    p: Proxy, url: str, host: str, port: int, timeout: float, max_read: int
) -> tuple[int, bytes]:
    sock = _connect(p.host, p.port, timeout)
    try:
        sock.settimeout(timeout)
        host_hdr = host if port == 80 else f"{host}:{port}"
        req = (
            f"GET {url} HTTP/1.1\r\n"
            f"Host: {host_hdr}\r\n"
            f"User-Agent: {UA}\r\n"
            "Accept: */*\r\n"
            "Accept-Encoding: identity\r\n"
            "Proxy-Connection: close\r\n"
            "Connection: close\r\n"
        )
        if p.user is not None:
            req += f"Proxy-Authorization: Basic {_basic_token(p)}\r\n"
        req += "\r\n"
        sock.sendall(req.encode("latin-1"))
        return _read_response(sock, max_read)
    finally:
        with contextlib.suppress(Exception):
            sock.close()


def _body_ok(host: str, body: bytes) -> bool:
    if not body:
        return False
    h = host.lower()
    head = body[:8192]
    if "mega.nz" in h:
        if h.startswith("g.api"):
            return head.lstrip().startswith((b"[", b"-"))
        return b"MEGA" in head
    if "ipify" in h:
        m = re.search(rb'"ip"\s*:\s*"([^"]+)"', head)
        if not m:
            return False
        return _egress_ok(m.group(1).decode("ascii", "ignore"))
    if "ip-api" in h:
        return b'"status"' in head
    if "checkip" in h or "icanhazip" in h or "ifconfig" in h:
        text = head.decode("ascii", "ignore").strip()
        return bool(IP_TEXT_RE.match(text)) and _egress_ok(text)
    return True


def _egress_ok(ip: str) -> bool:
    # Uma borda de CDN responde em nome da propria CDN e devolve o IP do
    # cliente; um proxy real entrega o IP dele. Rejeita o falso positivo.
    return _LOCAL_IP is None or ip.strip() != _LOCAL_IP


def _short_err(exc: BaseException) -> str:
    text = f"{type(exc).__name__}: {exc}" if str(exc) else type(exc).__name__
    return text.replace("\r", " ").replace("\n", " ")[:120]


def measure_https(p: Proxy, url: str, timeout: float) -> float:
    scheme, host, port, path = split_url(url)
    if scheme != "https":
        raise ValueError("a URL de teste HTTPS precisa usar https://")
    t0 = time.monotonic()
    raw = _tunnel(p, host, port, timeout)
    tls: socket.socket | None = None
    try:
        tls = _wrap_tls(raw, host, timeout)
        status, body = _get_via_tunnel(tls, host, port, path, timeout, 16384)
        elapsed = (time.monotonic() - t0) * 1000.0
        if not 200 <= status < 300:
            raise TargetRejected(f"HTTP {status}")
        if not _body_ok(host, body):
            raise TargetRejected("resposta invalida")
        return elapsed
    finally:
        with contextlib.suppress(Exception):
            if tls is not None:
                tls.close()
        with contextlib.suppress(Exception):
            raw.close()


def measure_http(p: Proxy, url: str, timeout: float) -> float:
    scheme, host, port, _ = split_url(url)
    if scheme != "http":
        raise ValueError("a URL de teste HTTP precisa usar http://")
    t0 = time.monotonic()
    status, body = _get_absolute(p, url, host, port, timeout, 16384)
    elapsed = (time.monotonic() - t0) * 1000.0
    if not 200 <= status < 300:
        raise TargetRejected(f"HTTP {status}")
    if not _body_ok(host, body):
        raise TargetRejected("resposta invalida")
    return elapsed


def measure_https_any(p: Proxy, urls: list[str], timeout: float) -> float:
    last: TargetRejected | None = None
    for url in urls:
        try:
            return measure_https(p, url, timeout)
        except TargetRejected as exc:
            last = exc
    raise last or TargetRejected("nenhum alvo HTTPS respondeu")


def measure_http_any(p: Proxy, urls: list[str], timeout: float, min_ok: int = 2) -> float:
    required = max(1, min(min_ok, len(urls)))
    successes: list[float] = []
    last: TargetRejected | None = None
    for url in urls:
        try:
            successes.append(measure_http(p, url, timeout))
            if len(successes) >= required:
                return min(successes)
        except TargetRejected as exc:
            last = exc
    if len(successes) >= required:
        return min(successes)
    if successes:
        raise TargetRejected(f"apenas {len(successes)}/{len(urls)} alvos confirmaram")
    raise last or TargetRejected("nenhum alvo HTTP respondeu")


def measure_speed(p: Proxy, use_https: bool, args: argparse.Namespace) -> float:
    url = args.speed_url if use_https else args.http_speed_url
    url = url.replace("{bytes}", str(args.speed_bytes))
    scheme, host, port, path = split_url(url)

    t0 = time.monotonic()
    if use_https:
        raw = _tunnel(p, host, port, args.speed_timeout)
        tls: socket.socket | None = None
        try:
            tls = _wrap_tls(raw, host, args.speed_timeout)
            status, body = _get_via_tunnel(
                tls, host, port, path, args.speed_timeout, args.speed_bytes
            )
        finally:
            with contextlib.suppress(Exception):
                if tls is not None:
                    tls.close()
            with contextlib.suppress(Exception):
                raw.close()
    else:
        status, body = _get_absolute(
            p, url, host, port, args.speed_timeout, args.speed_bytes
        )

    elapsed = time.monotonic() - t0
    if not 200 <= status < 300:
        raise ProxyFailure(f"HTTP {status}")
    minimum = min(args.speed_bytes // 4, 30000)
    if len(body) < minimum:
        raise ProxyFailure(f"download curto ({len(body)} bytes)")
    return (len(body) / 1024.0) / max(elapsed, 0.001)


# --------------------------------------------------------------------------
# Download e parsing das fontes
# --------------------------------------------------------------------------


def fetch_source(url: str, timeout: float = 30.0, tries: int = 2) -> str:
    opener = build_opener(ProxyHandler({}))
    req = Request(url, headers={"User-Agent": UA, "Cache-Control": "no-cache"})
    last: BaseException | None = None
    for attempt in range(tries):
        try:
            with opener.open(req, timeout=timeout) as resp:
                if getattr(resp, "status", 200) != 200:
                    raise ProxyFailure(f"HTTP {resp.status}")
                return resp.read().decode("utf-8", "replace")
        except Exception as exc:
            last = exc
            if attempt + 1 < tries:
                time.sleep(0.5 + attempt)
    assert last is not None
    raise last


def discover_local_ip(timeout: float = 8.0) -> str | None:
    opener = build_opener(ProxyHandler({}))
    for url in ("http://checkip.amazonaws.com/", "http://icanhazip.com/"):
        try:
            req = Request(url, headers={"User-Agent": UA, "Cache-Control": "no-cache"})
            with opener.open(req, timeout=timeout) as resp:
                text = resp.read(128).decode("ascii", "ignore").strip()
            if IP_TEXT_RE.match(text):
                return text
        except Exception:
            continue
    return None


def read_source_specs(path: str) -> list[tuple[str, str]]:
    specs: list[tuple[str, str]] = []
    for raw in Path(path).read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line or (line.startswith("#") and not line.lower().startswith("#socks5 ")):
            continue
        family = "http"
        if line.lower().startswith("#socks5 "):
            family = "socks5"
            line = line[8:].strip()
        else:
            m = re.match(r"^(http|socks5|socks)\s+(\S+)$", line, re.I)
            if m:
                family = "socks5" if m.group(1).lower().startswith("socks") else "http"
                line = m.group(2)
        if line.startswith(("http://", "https://")):
            specs.append((family, line))
    return specs


def load_candidates(
    specs: list[tuple[str, str]], max_per_source: int
) -> tuple[dict[tuple, Proxy], dict[tuple, set[str]], list[dict]]:
    results: list[tuple[str, str, str | None]] = []

    def job(spec: tuple[str, str]) -> tuple[str, str, str | None, str | None]:
        family, url = spec
        try:
            return family, url, fetch_source(url), None
        except Exception as exc:
            return family, url, None, _short_err(exc)

    with ThreadPoolExecutor(max_workers=min(8, max(1, len(specs)))) as pool:
        for future in as_completed([pool.submit(job, s) for s in specs]):
            results.append(future.result())

    proxies: dict[tuple, Proxy] = {}
    proxy_sources: dict[tuple, set[str]] = {}
    stats: list[dict] = []
    for family, url, text, error in results:
        name = url.rsplit("/", 1)[-1] or url
        if error is not None:
            stats.append({"url": url, "ok": False, "entries": 0, "error": error})
            print(f"  [x] {name}: {error}")
            continue
        count = 0
        parsed_any = 0
        lines = (text or "").splitlines()
        if max_per_source > 0:
            lines = lines[:max_per_source]
        for line in lines:
            parsed_any += 1
            proxy = parse_line(line, family, name)
            if proxy is None:
                continue
            key = proxy.key()
            if key not in proxies:
                proxies[key] = proxy
                proxy_sources[key] = set()
            proxy_sources[key].add(name)
            count += 1
        stats.append({"url": url, "ok": True, "entries": count, "error": ""})
        print(f"  [ok] {name}: {count} entradas")

    return proxies, proxy_sources, stats


def load_from_file(path: str, max_per_source: int) -> tuple[dict[tuple, Proxy], dict[tuple, set[str]], list[dict]]:
    p = Path(path)
    text = p.read_text(encoding="utf-8", errors="replace")
    default_family = "socks5" if "socks" in p.name.lower() else "http"
    proxies: dict[tuple, Proxy] = {}
    proxy_sources: dict[tuple, set[str]] = {}
    lines = text.splitlines()
    if max_per_source > 0:
        lines = lines[:max_per_source]
    for line in lines:
        proxy = parse_line(line, default_family, p.name)
        if proxy is None:
            continue
        key = proxy.key()
        if key not in proxies:
            proxies[key] = proxy
            proxy_sources[key] = set()
        proxy_sources[key].add(p.name)
    stats = [{"url": str(p), "ok": True, "entries": len(proxies), "error": ""}]
    print(f"  [ok] {p.name}: {len(proxies)} entradas locais")
    return proxies, proxy_sources, stats


# --------------------------------------------------------------------------
# Verificacao
# --------------------------------------------------------------------------


def check_proxy(proxy: Proxy, args: argparse.Namespace) -> Result:
    result = Result(proxy=proxy)

    if proxy.proto == "socks5":
        try:
            result.https_ms = measure_https_any(proxy, args.https_targets, args.timeout)
            result.https_ok = True
        except Exception as exc:
            result.https_err = _short_err(exc)
        return result

    try:
        result.https_ms = measure_https_any(proxy, args.https_targets, args.timeout)
        result.https_ok = True
    except TcpUnreachable as exc:
        result.https_err = _short_err(exc)
        result.http_err = "TCP inacessivel"
        return result
    except Exception as exc:
        result.https_err = _short_err(exc)

    try:
        result.http_ms = measure_http_any(
            proxy, args.http_targets, args.timeout, args.min_http_targets
        )
        result.http_ok = True
    except Exception as exc:
        result.http_err = _short_err(exc)
    return result


def run_checks(
    proxies: list[Proxy], args: argparse.Namespace, label: str = "Testando"
) -> list[Result]:
    total = len(proxies)
    results: list[Result] = []
    done = 0
    alive = 0
    lock = threading.Lock()
    stop = threading.Event()
    started = time.monotonic()

    def report_progress() -> None:
        nonlocal done, alive
        last_line = 0.0
        while not stop.wait(0.5):
            now = time.monotonic()
            with lock:
                d, a = done, alive
            if d == total:
                continue
            elapsed = now - started
            rate = d / elapsed if elapsed > 0 else 0.0
            eta = (total - d) / rate if rate > 0 else 0.0
            line = (
                f"{label} {d}/{total} ({d * 100.0 / max(total, 1):.1f}%) "
                f"| vivos: {a} | {_fmt_secs(elapsed)} | ETA {_fmt_secs(eta)}"
            )
            if sys.stderr.isatty():
                sys.stderr.write("\r\033[2K" + line)
                sys.stderr.flush()
            elif now - last_line >= 10:
                sys.stderr.write(line + "\n")
                sys.stderr.flush()
                last_line = now

    progress = threading.Thread(target=report_progress, daemon=True)
    progress.start()
    try:
        with ThreadPoolExecutor(max_workers=max(1, args.threads)) as pool:
            futures = {pool.submit(check_proxy, p, args): p for p in proxies}
            for future in as_completed(futures):
                try:
                    result = future.result()
                except Exception as exc:
                    result = Result(proxy=futures[future], https_err=_short_err(exc))
                with lock:
                    results.append(result)
                    done += 1
                    if result.http_ok or result.https_ok:
                        alive += 1
    finally:
        stop.set()
        progress.join(timeout=2)
        if sys.stderr.isatty():
            sys.stderr.write("\r\033[2K")
            sys.stderr.flush()

    return results


def run_speed_tests(finalists: dict[tuple, Result], args: argparse.Namespace) -> None:
    if not finalists:
        return
    total = len(finalists)
    done = 0
    lock = threading.Lock()
    item_list = list(finalists.values())

    def job(result: Result) -> None:
        use_https = result.https_ok
        try:
            result.speed_kbps = measure_speed(result.proxy, use_https, args)
            result.speed_via = "https" if use_https else "http"
        except Exception as exc:
            result.speed_via = f"falhou: {_short_err(exc)}"[:80]

    print(f"Medindo velocidade de {total} finalistas ({args.speed_workers} simultaneos)...")
    with ThreadPoolExecutor(max_workers=max(1, args.speed_workers)) as pool:
        futures = [pool.submit(job, r) for r in item_list]
        for _ in as_completed(futures):
            with lock:
                done += 1
            if sys.stderr.isatty() and done % max(1, total // 40) == 0:
                sys.stderr.write(f"\r\033[2KVelocidade {done}/{total}")
                sys.stderr.flush()
    if sys.stderr.isatty():
        sys.stderr.write("\r\033[2K")
        sys.stderr.flush()


def confirm_results(results: list[Result], args: argparse.Namespace) -> None:
    if not results:
        return
    print(f"Confirmando {len(results)} finalistas (2a verificacao)...")
    fresh = {
        r.proxy.key(): r
        for r in run_checks([r.proxy for r in results], args, label="Confirmando")
    }
    for old in results:
        new = fresh.get(old.proxy.key())
        if new is None:
            continue
        if old.http_ok:
            if new.http_ok:
                old.http_ms = _best_latency(old.http_ms, new.http_ms)
            else:
                old.http_ok = False
                old.http_err = "falhou na confirmacao: " + new.http_err
        if old.https_ok:
            if new.https_ok:
                old.https_ms = _best_latency(old.https_ms, new.https_ms)
            else:
                old.https_ok = False
                old.https_err = "falhou na confirmacao: " + new.https_err


def _best_latency(a: float | None, b: float | None) -> float | None:
    vals = [v for v in (a, b) if v is not None]
    return min(vals) if vals else None



def _fmt_secs(value: float) -> str:
    if value <= 0 or value == float("inf"):
        return "--:--"
    value = int(value)
    return f"{value // 60:02d}:{value % 60:02d}"


def _fmt_ms(value: float | None) -> str:
    return f"{value:5.0f}ms" if value is not None else "   --  "


def _latency_for(result: Result, attr: str) -> float:
    value = getattr(result, attr)
    return value if value is not None else float("inf")


def order_group(group: list[Result], latency_attr: str) -> list[Result]:
    tested = sorted(
        (r for r in group if r.speed_kbps is not None),
        key=lambda r: (-(r.speed_kbps or 0.0), _latency_for(r, latency_attr)),
    )
    untested = sorted(
        (r for r in group if r.speed_kbps is None),
        key=lambda r: _latency_for(r, latency_attr),
    )
    return tested + untested


def atomic_write(path: Path, text: str) -> None:
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8", newline="\n")
    os.replace(tmp, path)


def write_proxy_list(path: Path, results: list[Result]) -> None:
    atomic_write(path, "".join(r.proxy.mega_line() + "\n" for r in results))


def backup_existing(out_dir: Path) -> Path | None:
    names = ("http.txt", "https.txt", "socks5.txt")
    existing = [out_dir / n for n in names if (out_dir / n).exists() and (out_dir / n).stat().st_size > 0]
    if not existing:
        return None
    backup_dir = out_dir / f"backup_{datetime.now():%Y%m%d_%H%M%S}"
    backup_dir.mkdir(parents=True, exist_ok=True)
    for src in existing:
        shutil.copy2(src, backup_dir / src.name)
    return backup_dir


def write_csv(path: Path, results: list[Result]) -> None:
    with path.open("w", encoding="utf-8-sig", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(
            [
                "protocolo",
                "proxy",
                "http_ok",
                "https_ok",
                "latencia_http_ms",
                "latencia_https_ms",
                "velocidade_kbs",
                "medido_via",
                "erro_http",
                "erro_https",
                "fontes",
            ]
        )
        for r in sorted(results, key=lambda r: (r.proxy.proto, r.latency)):
            writer.writerow(
                [
                    r.proxy.proto,
                    r.proxy.addr,
                    "sim" if r.http_ok else "nao",
                    "sim" if r.https_ok else "nao",
                    f"{r.http_ms:.0f}" if r.http_ms is not None else "",
                    f"{r.https_ms:.0f}" if r.https_ms is not None else "",
                    f"{r.speed_kbps:.1f}" if r.speed_kbps is not None else "",
                    r.speed_via,
                    r.http_err,
                    r.https_err,
                    ", ".join(sorted(r.sources)),
                ]
            )


def write_report(
    path: Path,
    args: argparse.Namespace,
    source_stats: list[dict],
    total_candidates: int,
    results: list[Result],
    groups: dict[str, list[Result]],
    outputs: dict[str, list[Result]],
    backup_dir: Path | None,
    elapsed: float,
) -> None:
    lines: list[str] = []
    lines.append("RELATORIO DE VERIFICACAO DE PROXIES")
    lines.append(f"Gerado em: {datetime.now():%Y-%m-%d %H:%M:%S}")
    lines.append(f"Duracao: {_fmt_secs(elapsed)}")
    lines.append(f"Timeout: {args.timeout:g}s | Threads: {args.threads} | Limite por lista: {args.limit or 'sem limite'}")
    lines.append(f"Alvos HTTPS: {', '.join(args.https_targets)}")
    lines.append(f"Alvos HTTP: {', '.join(args.http_targets)}")
    lines.append(
        f"Confirmacao HTTP: >= {args.min_http_targets} alvos | IP local: {_LOCAL_IP or 'nao detectado'}"
    )
    lines.append("")
    lines.append("FONTES")
    ok_sources = 0
    for st in source_stats:
        if st["ok"]:
            ok_sources += 1
            lines.append(f"  [ok] {st['url']} -> {st['entries']} entradas")
        else:
            lines.append(f"  [x]  {st['url']} -> {st['error']}")
    lines.append(f"  Fontes ok: {ok_sources}/{len(source_stats)}")
    lines.append("")
    lines.append(f"Candidatos unicos: {total_candidates}")
    valid_http = sum(1 for r in results if r.proxy.proto == "http" and r.http_ok)
    valid_https = sum(1 for r in results if r.proxy.proto == "http" and r.https_ok)
    valid_socks = sum(1 for r in results if r.proxy.proto == "socks5" and r.https_ok)
    lines.append(f"Validos: HTTP={valid_http} | HTTPS(CONNECT)={valid_https} | SOCKS5={valid_socks}")
    lines.append("")
    lines.append("ARQUIVOS GERADOS")
    for name, items in outputs.items():
        lines.append(f"  {name}: {len(items)} proxies")
    if backup_dir is not None:
        lines.append(f"  Backup dos arquivos antigos: {backup_dir}")
    lines.append("")

    for name, items in outputs.items():
        lines.append(f"TOP 20 - {name} (mais rapido primeiro)")
        if not items:
            lines.append("  (nenhum proxy valido)")
        for r in items[:20]:
            speed = f"{r.speed_kbps:7.1f} KB/s" if r.speed_kbps is not None else "   --      "
            lines.append(
                f"  {r.proxy.addr:<22} {speed}  https={_fmt_ms(r.https_ms)}  http={_fmt_ms(r.http_ms)}"
            )
        lines.append("")

    lines.append("OBSERVACOES")
    lines.append("  - https.txt e a lista recomendada para o MegaBasterd (suporta CONNECT/HTTPS).")
    lines.append("  - http.txt contem proxies validos em HTTP puro; alguns podem nao suportar CONNECT.")
    lines.append("  - Cada proxy e validado em varios alvos para reduzir falsos negativos (429/bloqueios).")
    lines.append("  - Bordas de CDN que devolvem o IP do proprio cliente sao rejeitadas.")
    lines.append("  - socks5.txt contem apenas SOCKS5 validados no tunel HTTPS.")
    lines.append("  - A ordem prioriza velocidade medida (KB/s) e, em seguida, menor latencia.")
    lines.append("  - Execute novamente periodicamente; proxies gratuitos expiram rapido.")

    atomic_write(path, "\n".join(lines) + "\n")


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    default_out = Path(__file__).resolve().parent / "proxy"
    parser = argparse.ArgumentParser(
        description="Verifica e reconstroi listas de proxies (HTTP/HTTPS/SOCKS5) para o MegaBasterd.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Exemplos:\n"
            "  python proxy_checker.py\n"
            "  python proxy_checker.py --threads 300 --timeout 5 --limit 500\n"
            "  python proxy_checker.py --from-file proxy/http.txt --limit 50\n"
            "  python proxy_checker.py --out \"E:\\\\proxy\" --speed-test 150 --speed-workers 30\n"
        ),
    )
    parser.add_argument("--out", default=str(default_out), help=f"pasta de saida (padrao: {default_out})")
    parser.add_argument("--threads", type=int, default=200, help="verificacoes simultaneas (padrao: 200)")
    parser.add_argument("--timeout", type=float, default=5.0, help="timeout por teste em segundos (padrao: 5)")
    parser.add_argument("--limit", type=int, default=300, help="maximo de proxies por lista; 0 = sem limite (padrao: 300)")
    parser.add_argument("--speed-test", type=int, default=80, help="finalistas por lista no teste de velocidade; 0 = desliga (padrao: 80)")
    parser.add_argument("--speed-workers", type=int, default=25, help="testes de velocidade simultaneos (padrao: 25)")
    parser.add_argument("--speed-bytes", type=int, default=262144, help="bytes baixados no teste de velocidade (padrao: 262144)")
    parser.add_argument("--speed-timeout", type=float, default=15.0, help="timeout do teste de velocidade (padrao: 15)")
    parser.add_argument("--min-speed", type=float, default=0.0, help="descarta finalistas abaixo desta velocidade em KB/s (padrao: 0)")
    parser.add_argument(
        "--min-http-targets",
        type=int,
        default=2,
        help="alvos HTTP que precisam confirmar o proxy (padrao: 2)",
    )
    parser.add_argument("--url", default=DEFAULT_HTTPS_URL, help=f"alvo HTTPS principal (padrao: {DEFAULT_HTTPS_URL})")
    parser.add_argument(
        "--url-fallbacks",
        default=",".join(DEFAULT_HTTPS_FALLBACKS),
        help="alvos HTTPS alternativos, separados por virgula",
    )
    parser.add_argument("--http-url", default=DEFAULT_HTTP_URL, help=f"alvo HTTP principal (padrao: {DEFAULT_HTTP_URL})")
    parser.add_argument(
        "--http-url-fallbacks",
        default=",".join(DEFAULT_HTTP_FALLBACKS),
        help="alvos HTTP alternativos, separados por virgula",
    )
    parser.add_argument("--speed-url", default=DEFAULT_SPEED_URL, help="URL HTTPS do teste de velocidade; {bytes} e substituido")
    parser.add_argument("--http-speed-url", default=DEFAULT_HTTP_SPEED_URL, help="URL HTTP do teste de velocidade")
    parser.add_argument("--sources", help="arquivo com fontes extras (linhas 'http URL' ou 'socks5 URL')")
    parser.add_argument("--from-file", help="usa um arquivo local em vez de baixar as fontes")
    parser.add_argument("--max-per-source", type=int, default=0, help="limita linhas lidas por fonte; 0 = tudo")
    return parser


def _split_csv(value: str) -> list[str]:
    return [part.strip() for part in (value or "").split(",") if part.strip()]


def main(argv: list[str] | None = None) -> int:
    global _LOCAL_IP
    args = build_parser().parse_args(argv)
    with contextlib.suppress(Exception):
        sys.stdout.reconfigure(line_buffering=True)
    args.https_targets = list(dict.fromkeys([args.url] + _split_csv(args.url_fallbacks)))
    args.http_targets = list(dict.fromkeys([args.http_url] + _split_csv(args.http_url_fallbacks)))
    out_dir = Path(args.out).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    _LOCAL_IP = discover_local_ip()
    print(f"IP publico local: {_LOCAL_IP or 'nao detectado'}")

    started = time.monotonic()

    if args.from_file:
        print(f"Lendo proxies de {args.from_file} ...")
        proxies, proxy_sources, source_stats = load_from_file(args.from_file, args.max_per_source)
    else:
        print("Baixando fontes de proxies ...")
        specs = read_source_specs(args.sources) if args.sources else list(SOURCES)
        if not specs:
            print("Nenhuma fonte valida encontrada.", file=sys.stderr)
            return 2
        proxies, proxy_sources, source_stats = load_candidates(specs, args.max_per_source)

    if not proxies:
        print(
            "Nenhum proxy foi obtido das fontes (rede bloqueada ou listas vazias). "
            "Os arquivos existentes foram preservados.",
            file=sys.stderr,
        )
        return 2

    print(
        f"{len(proxies)} candidatos unicos "
        f"(HTTP={sum(1 for p in proxies.values() if p.proto == 'http')}, "
        f"SOCKS5={sum(1 for p in proxies.values() if p.proto == 'socks5')})"
    )

    results = run_checks(list(proxies.values()), args)
    for result in results:
        result.sources = proxy_sources.get(result.proxy.key(), set())

    http_valid = [r for r in results if r.proxy.proto == "http" and r.http_ok]
    https_valid = [r for r in results if r.proxy.proto == "http" and r.https_ok]
    socks_valid = [r for r in results if r.proxy.proto == "socks5" and r.https_ok]

    print("")
    print(f"Validos: HTTP={len(http_valid)} | HTTPS(CONNECT)={len(https_valid)} | SOCKS5={len(socks_valid)}")

    if not (http_valid or https_valid or socks_valid):
        empty_outputs = {"http.txt": [], "https.txt": [], "socks5.txt": []}
        write_csv(out_dir / "report.csv", results)
        write_report(
            out_dir / "report.log",
            args,
            source_stats,
            len(proxies),
            results,
            {"http": [], "https": [], "socks5": []},
            empty_outputs,
            None,
            time.monotonic() - started,
        )
        print(
            "Nenhum proxy passou na verificacao; as listas existentes foram preservadas. "
            f"Detalhes em {out_dir / 'report.log'}",
            file=sys.stderr,
        )
        return 3

    if args.speed_test > 0:
        finalists: dict[tuple, Result] = {}
        by_latency = lambda r: r.latency  # noqa: E731
        for group in (http_valid, https_valid, socks_valid):
            for r in sorted(group, key=by_latency)[: args.speed_test]:
                if r.speed_kbps is None:
                    finalists[r.proxy.key()] = r
        run_speed_tests(finalists, args)

    ordered_http = order_group(http_valid, "http_ms")
    ordered_https = order_group(https_valid, "https_ms")
    ordered_socks = order_group(socks_valid, "https_ms")

    margin = 50

    def preselect(items: list[Result]) -> list[Result]:
        return items if args.limit <= 0 else items[: args.limit + margin]

    sel_http = preselect(ordered_http)
    sel_https = preselect(ordered_https)
    sel_socks = preselect(ordered_socks)

    to_confirm: dict[tuple, Result] = {}
    for group in (sel_http, sel_https, sel_socks):
        for r in group:
            if r.speed_kbps is None:
                to_confirm[r.proxy.key()] = r
    confirm_results(list(to_confirm.values()), args)

    ordered_http = order_group([r for r in sel_http if r.http_ok], "http_ms")
    ordered_https = order_group([r for r in sel_https if r.https_ok], "https_ms")
    ordered_socks = order_group([r for r in sel_socks if r.https_ok], "https_ms")

    http_valid = [r for r in results if r.proxy.proto == "http" and r.http_ok]
    https_valid = [r for r in results if r.proxy.proto == "http" and r.https_ok]
    socks_valid = [r for r in results if r.proxy.proto == "socks5" and r.https_ok]
    print(
        f"Apos confirmacao: HTTP={len(http_valid)} | "
        f"HTTPS(CONNECT)={len(https_valid)} | SOCKS5={len(socks_valid)}"
    )

    if args.min_speed > 0:
        keep = lambda r: r.speed_kbps is not None and r.speed_kbps >= args.min_speed  # noqa: E731
        ordered_http = [r for r in ordered_http if keep(r)]
        ordered_https = [r for r in ordered_https if keep(r)]
        ordered_socks = [r for r in ordered_socks if keep(r)]

    if args.limit > 0:
        ordered_http = ordered_http[: args.limit]
        ordered_https = ordered_https[: args.limit]
        ordered_socks = ordered_socks[: args.limit]

    backup_dir = backup_existing(out_dir)
    outputs = {
        "http.txt": ordered_http,
        "https.txt": ordered_https,
        "socks5.txt": ordered_socks,
    }
    write_proxy_list(out_dir / "http.txt", ordered_http)
    write_proxy_list(out_dir / "https.txt", ordered_https)
    write_proxy_list(out_dir / "socks5.txt", ordered_socks)
    write_csv(out_dir / "report.csv", results)
    write_report(
        out_dir / "report.log",
        args,
        source_stats,
        len(proxies),
        results,
        {"http": http_valid, "https": https_valid, "socks5": socks_valid},
        outputs,
        backup_dir,
        time.monotonic() - started,
    )

    print("")
    for name, items in outputs.items():
        print(f"{name}: {len(items)} proxies gravados")
        for r in items[:5]:
            speed = f"{r.speed_kbps:8.1f} KB/s" if r.speed_kbps is not None else "     --   "
            print(
                f"   {r.proxy.addr:<22} {speed}  https={_fmt_ms(r.https_ms)}  http={_fmt_ms(r.http_ms)}"
            )
    if backup_dir is not None:
        print(f"Backup dos arquivos anteriores: {backup_dir}")
    print(f"Relatorios: {out_dir / 'report.log'} | {out_dir / 'report.csv'}")
    print(f"Tempo total: {_fmt_secs(time.monotonic() - started)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("\nInterrompido pelo usuario.", file=sys.stderr)
        raise SystemExit(130)
