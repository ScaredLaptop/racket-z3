#!/usr/bin/env python3
"""
Generate Racket FFI bindings (functions.rkt, enums.rkt, types.rkt)
from z3_api.h and z3_optimization.h.
"""
from __future__ import annotations
import re, sys
from pathlib import Path
import requests

HEADER_URLS = [
    "https://raw.githubusercontent.com/Z3Prover/z3/master/src/api/z3_api.h",
    "https://raw.githubusercontent.com/Z3Prover/z3/"
    "f63c9e366fad52638dc5c413fa6262c238468d26/src/api/z3_optimization.h",
]


C_TO_RKT = {
    "void": "_void", "bool": "_bool", "Z3_bool": "_bool",
    "int": "_int", "unsigned": "_uint", "unsigned int": "_uint",
    "unsigned long": "_ulong", "unsigned long long": "_ulong_long",
    "long": "_long", "long long": "_long_long",
    "float": "_float", "double": "_double",
    "size_t": "_size_t", "uint64_t": "_uint64", "int64_t": "_int64",
    "char *": "_string/utf-8", "const char *": "_string/utf-8",
    "Z3_string": "_string/utf-8", "Z3_char_ptr": "_string/utf-8",
    "Z3_string_ptr": "_pointer",
}

FUNC_PATTERNS = [
    re.compile(r"Z3_API\s+([A-Za-z0-9_ *]+?)\s+(Z3_[A-Za-z0-9_]+)\s*\(([^)]*)\)\s*;"),
    re.compile(r"([A-Za-z0-9_ *]+?)\s+Z3_API\s+(Z3_[A-Za-z0-9_]+)\s*\(([^)]*)\)\s*;"),
]
DEFINE_TYPE_RE  = re.compile(r"DEFINE_TYPE\(\s*(Z3_[A-Za-z0-9_]+)\s*\)")
TYPEDEF_PTR_RE  = re.compile(r"typedef\s+struct\s+_[A-Za-z0-9_]+\s*\*\s*(Z3_[A-Za-z0-9_]+)\s*;")
ENUM_RE         = re.compile(r"typedef\s+enum\s*\{([^}]+?)\}\s*(Z3_[A-Za-z0-9_]+)\s*;", re.S)

SKIP_FUNCS = {
    "Z3_is_recursive_datatype_sort",
    "Z3_get_array_arity",
}

def download(url):                    
    resp = requests.get(url, timeout=30)
    resp.raise_for_status()
    return resp.text

def get_full_header():
    return "\n\n".join(download(u) for u in HEADER_URLS)

def split_params(blob: str):
    blob = blob.strip()
    if not blob or blob == "void":
        return []
    out = []
    for p in blob.split(","):
        *type_tokens, name = p.replace("[]", " *").split()
        ctype = " ".join(type_tokens).replace("const ", "")
        if name.startswith("*"):
            ctype += " *"
            name = name.lstrip("*")
        out.append((ctype.strip(), name.strip()))
    return out

def split_enum_items(body: str):
    body = re.sub(r"/\*.*?\*/", "", body, flags=re.S)
    body = re.sub(r"//.*?$", "", body, flags=re.M)
    toks, neg = [], False
    for raw in filter(None, map(str.strip, body.split(","))):
        if "=" in raw:
            name, val = map(str.strip, raw.split("=", 1))
            toks.extend([name, "=", str(int(val, 0))])
            neg |= int(val, 0) < 0
        else:
            toks.append(raw)
    return toks, neg

opaque_aliases: set[str] = set()
enum_tags: set[str] = set()

def rkt_type(c_type: str) -> str:
    c_type = c_type.strip()
    if c_type in C_TO_RKT:
        return C_TO_RKT[c_type]
    if c_type.startswith("const "):
        return rkt_type(c_type[6:])
    if c_type.endswith("*"):
        return "_pointer"
    if c_type in enum_tags:
        return f"_{c_type}"
    if c_type.startswith("Z3_"):
        return f"_{c_type}" if c_type in opaque_aliases else "_pointer"
    return f"_{c_type}"

def emit_types(aliases, path: Path):
    with path.open("w", encoding="utf-8") as fp:
        fp.write("#lang racket/base\n(require ffi/unsafe)\n\n")
        for a in sorted(aliases):
            fp.write(f"(define-cpointer-type _{a} #:tag '{a})\n")
        fp.write("\n(provide (all-defined-out))\n")

def emit_enums(enum_infos, path: Path):
    with path.open("w", encoding="utf-8") as fp:
        fp.write("#lang racket/base\n(require ffi/unsafe)\n\n")
        for tag, toks, neg in enum_infos:
            base = " _fixint" if neg else ""
            fp.write(f"(define _{tag} (_enum '({' '.join(toks)}){base}))\n")
        fp.write("\n(provide (all-defined-out))\n")

def emit_functions(funcs, path: Path):
    with path.open("w", encoding="utf-8") as fp:
        fp.write("#lang racket/base\n"
                 "(require ffi/unsafe ffi/unsafe/define \"../path.rkt\" \"types.rkt\" \"enums.rkt\")\n\n")
        for name, ret, params in funcs:
            if name in SKIP_FUNCS: 
                continue
            args = " ".join(rkt_type(t) for t, _ in params)
            rng  = rkt_type(ret)
            sig  = f"(_fun {args} -> {rng})" if args else f"(_fun -> {rng})"
            fp.write(f"(define-z3 {name} {sig})\n")
        fp.write("\n(provide (all-defined-out))\n")

def generate(out_dir: Path):
    global opaque_aliases, enum_tags

    code  = get_full_header()
    opaque_aliases = set(DEFINE_TYPE_RE.findall(code) +
                         TYPEDEF_PTR_RE.findall(code))

    enum_infos = []
    for body, tag in ENUM_RE.findall(code):
        toks, neg = split_enum_items(body)
        enum_infos.append((tag, toks, neg))
        enum_tags.add(tag)

    funcs = []
    for pat in FUNC_PATTERNS:
        funcs += [(n, r.strip(), split_params(p))
                  for r, n, p in pat.findall(code)]

    out_dir.mkdir(parents=True, exist_ok=True)
    emit_types(opaque_aliases, out_dir / "types.rkt")
    emit_enums(enum_infos,        out_dir / "enums.rkt")
    emit_functions(funcs,         out_dir / "functions.rkt")

    print(f"Generated {len(opaque_aliases)} types, {len(enum_infos)} enums, "
          f"{len(funcs) - len(SKIP_FUNCS)} functions → {out_dir}/")

if __name__ == "__main__":
    generate(Path(sys.argv[1]) if len(sys.argv) > 1 else Path("."))
