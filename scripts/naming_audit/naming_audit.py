#!/usr/bin/env python3
"""
Naming-consistency audit for Mathlib.

Scans every `.lean` file under `Mathlib/`, `Archive/` and `Counterexamples/` (no Lean toolchain
needed: the scan is a heuristic, regex-based parse), runs a collection of naming checks, and
(re)writes `docs/naming_audit.md`.

The markdown file is a *living* document: every finding has a stable key and a `Status` column.
When the script is re-run, the `Status` and `Note` columns of rows that are still present are
preserved, new findings are added with status `open`, and findings whose declaration disappeared
are dropped (their count is reported in the summary). Triage therefore happens by editing the
markdown file directly.

Usage:
    python3 scripts/naming_audit/naming_audit.py [--root .] [--deps DIR ...] [--out docs/naming_audit.md]

Category F1 additionally spell-checks comments and docstrings; see `prose_typos.py`.

`--deps` may point at checkouts of Lean core (`src/Init`, `src/Std`, `src/Lean`) and Batteries so that
names declared upstream are recognised when checking for unknown / misspelled tokens.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prose_typos  # noqa: E402  (same directory)

# --------------------------------------------------------------------------------------------
# Part 1: extraction
# --------------------------------------------------------------------------------------------

DECL_KEYWORDS = [
    "class inductive", "class abbrev", "structure", "class", "inductive", "theorem", "lemma",
    "irreducible_def", "def", "abbrev", "instance", "axiom", "opaque", "alias",
]
MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "unsafe", "partial", "scoped",
             "local", "public", "meta"}
OPEN = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩", "⟦": "⟧"}
CLOSE = {v: k for k, v in OPEN.items()}
IDENT_RE = re.compile(r'(?:«[^»]*»|[^\s():{}\[\]⦃⦄⟨⟩«»,;"⟦⟧]+)+')
ATTR_TO_ADDITIVE_RE = re.compile(
    r"to_additive\??\s*((?:\((?:[^()]|\([^()]*\))*\)\s*|existing\s+|self\s+)*)([^\s\"()\[\],]+)?")


def strip_comments(src: str) -> str:
    """Replace comments with spaces, keeping newlines and string literals intact."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth == 0:
            if c == '"':
                j = i + 1
                while j < n and src[j] != '"':
                    if src[j] == "\\":
                        j += 1
                    j += 1
                out.append(src[i:j + 1])
                i = j + 1
                continue
            if src.startswith("--", i):
                j = src.find("\n", i)
                if j == -1:
                    j = n
                out.append(" " * (j - i))
                i = j
                continue
            if src.startswith("/-", i):
                depth = 1
                out.append("  ")
                i += 2
                continue
            out.append(c)
            i += 1
        else:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
    return "".join(out)


def find_matching_bracket(text: str, i: int) -> int:
    """`text[i]` is an opening bracket; return the index just past its matching close."""
    stack = [OPEN[text[i]]]
    j = i + 1
    n = len(text)
    while j < n and stack:
        c = text[j]
        if c == '"':
            k = j + 1
            while k < n and text[k] != '"':
                if text[k] == "\\":
                    k += 1
                k += 1
            j = k + 1
            continue
        if c in OPEN:
            stack.append(OPEN[c])
        elif c in CLOSE and stack and stack[-1] == c:
            stack.pop()
        j += 1
    return j


def parse_header(text: str, start: int, hard_end: int, inductive: bool = False):
    """Header of a declaration: from `start` until `:=` / `where` / a match arm / `extends` /
    `deriving` at bracket depth 0 (or `hard_end`)."""
    i = start
    depth = 0
    n = min(len(text), hard_end)
    while i < n:
        c = text[i]
        if c == '"':
            k = i + 1
            while k < n and text[k] != '"':
                if text[k] == "\\":
                    k += 1
                k += 1
            i = k + 1
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            if text.startswith(":=", i):
                return text[start:i], i
            if c == "|":
                ls = text.rfind("\n", 0, i) + 1
                if text[ls:i].strip() == "":
                    le = text.find("\n", i)
                    if le == -1:
                        le = n
                    if inductive or "=>" in text[i:le]:
                        return text[start:i], i
                elif inductive:
                    return text[start:i], i
            for kw in ("where", "deriving", "extends"):
                if text.startswith(kw, i) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.")) \
                        and (i + len(kw) >= n or not (text[i + len(kw)].isalnum() or text[i + len(kw)] in "_'.")):
                    return text[start:i], i
        i += 1
    return text[start:n], n


def split_binders_type(header: str):
    """Split a header into (binders, type) at the first depth-0 `:` (not `::`, not `:=`)."""
    depth = 0
    i = 0
    n = len(header)
    while i < n:
        c = header[i]
        if c == '"':
            k = i + 1
            while k < n and header[k] != '"':
                if header[k] == "\\":
                    k += 1
                k += 1
            i = k + 1
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif c == ":" and depth == 0:
            if header.startswith("::", i) or header.startswith(":=", i):
                i += 2
                continue
            if i > 0 and header[i - 1] == ":":
                i += 1
                continue
            return header[:i], header[i + 1:]
        i += 1
    return header, None


def parse_attrs(attr_text: str) -> dict:
    info = {"deprecated": "deprecated" in attr_text, "to_additive": None,
            "has_to_additive": "to_additive" in attr_text}
    m = ATTR_TO_ADDITIVE_RE.search(attr_text)
    if m and m.group(2):
        name = m.group(2)
        if name not in ("existing", "self") and not name.startswith("/"):
            info["to_additive"] = name
    return info


def parse_body_fields(text: str, body_start: int, body_end: int, kind: str):
    """Structure fields / inductive constructors from the indented body."""
    body = text[body_start:body_end]
    fields, ctors = [], []
    is_structure = kind in ("structure", "class")
    for line in body.split("\n"):
        stripped = line.lstrip()
        if not stripped:
            continue
        indent = len(line) - len(stripped)
        if stripped.startswith("|"):
            m = re.match(r"\|\s*((?:«[^»]*»|[^\s():{}\[\]⦃⦄⟨⟩«»,;\"⟦⟧|])+)", stripped)
            if m:
                ctors.append(m.group(1))
            continue
        if is_structure and indent == 2:
            s = re.sub(r"^(protected|private)\s+", "", stripped)
            if re.match(r"^\S+\s*::", s):  # custom constructor `mk ::`
                continue
            m = re.match(r"((?:«[^»]*»|[^\s():{}\[\]⦃⦄⟨⟩«»,;\"⟦⟧])+)\s*(:=|:|$)", s)
            if m:
                fname = m.group(1)
                if fname in ("where", "extends", "deriving"):
                    continue
                ftype = s[m.end():].strip() if m.group(2) == ":" else ""
                fields.append((fname, ftype))
            elif s.startswith("("):
                for bm in re.finditer(r"\(([^:()]+):([^()]*)\)", s):
                    for nm in bm.group(1).split():
                        fields.append((nm, bm.group(2).strip()))
    return fields, ctors


def extract_file(path: str, root: str) -> list:
    with open(path, encoding="utf-8") as f:
        src = f.read()
    text = strip_comments(src)
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    n = len(text)
    rel = os.path.relpath(path, root)

    def line_of(pos: int) -> int:
        lo, hi = 0, len(starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if starts[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    ns_stack: list = []       # (kind, name)
    var_stack: list = [{}]    # variable binders per scope
    decls: list = []

    def lookup_vars(t: str) -> dict:
        found = {}
        for tok in re.findall(r"[^\s()\[\]{}⦃⦄⟨⟩,;:]+", t):
            tok = tok.strip("'.¬-↑⇑⟪⟫")
            if tok and tok not in found:
                for frame in reversed(var_stack):
                    if tok in frame:
                        found[tok] = frame[tok]
                        break
        return found

    positions = [ls for ls in starts if ls < n and text[ls] != "\n" and not text[ls].isspace()]
    pi = 0
    consumed_until = -1
    while pi < len(positions):
        pos = positions[pi]
        pi += 1
        if pos < consumed_until:
            continue
        nxt = positions[pi] if pi < len(positions) else n
        line_end = text.find("\n", pos)
        if line_end == -1:
            line_end = n
        line = text[pos:line_end]
        m = re.match(r"(namespace|section|noncomputable section|end)\b\s*([^\s]*)", line)
        if m:
            kw, name = m.group(1), m.group(2)
            if kw == "namespace":
                ns_stack.append(("ns", name))
                var_stack.append({})
            elif kw.endswith("section"):
                ns_stack.append(("sec", name))
                var_stack.append({})
            elif ns_stack:
                if name:
                    for k in range(len(ns_stack) - 1, -1, -1):
                        if ns_stack[k][1] == name or ns_stack[k][1].endswith("." + name):
                            del ns_stack[k:]
                            del var_stack[k + 1:]
                            break
                    else:
                        ns_stack.pop()
                        var_stack.pop()
                else:
                    ns_stack.pop()
                    var_stack.pop()
                if not var_stack:
                    var_stack.append({})
            continue
        if line.startswith("variable"):
            vtext = text[pos + len("variable"):nxt]
            i = 0
            while i < len(vtext):
                c = vtext[i]
                if c in OPEN and c != "⟨":
                    j = find_matching_bracket(vtext, i)
                    grp = vtext[i + 1:j - 1]
                    if ":" in grp and c != "[":
                        names_part, _, type_part = grp.partition(":")
                        for nm in names_part.split():
                            var_stack[-1][nm] = " ".join(type_part.split())
                    i = j
                else:
                    i += 1
            continue
        if line.startswith("mutual"):
            end_pos = n
            for p in positions[pi:]:
                if text.startswith("end", p):
                    end_pos = p
                    break
            extra = [ls for ls in starts if pos < ls < end_pos and text.startswith("  ", ls)
                     and ls + 2 < n and not text[ls + 2].isspace()]
            positions = positions[:pi] + sorted(set(extra + positions[pi:]))
            continue
        # attributes and modifiers
        i = pos
        attr_text = ""
        mods = []
        while True:
            while i < nxt and text[i].isspace():
                i += 1
            if text.startswith("@[", i):
                j = find_matching_bracket(text, i + 1)
                attr_text += text[i:j] + " "
                i = j
                continue
            m = re.match(r"([A-Za-z_]+)\s", text[i:i + 30])
            if m and m.group(1) in MODIFIERS:
                mods.append(m.group(1))
                i += len(m.group(1))
                continue
            break
        kw = None
        for k in DECL_KEYWORDS:
            if text.startswith(k, i) and i + len(k) < n and text[i + len(k)].isspace():
                kw = k
                break
        if kw is None:
            continue
        j = i + len(kw)
        while j < nxt and text[j].isspace():
            j += 1
        ns_full = ".".join(x[1] for x in ns_stack if x[0] == "ns" and x[1])

        def full_of(nm: str):
            nm = nm.rstrip(".")
            return nm[len("_root_."):] if nm.startswith("_root_.") else (ns_full + "." if ns_full else "") + nm

        if kw == "alias":
            names = []
            if text.startswith("⟨", j):
                k = text.find("⟩", j)
                names = [x.strip() for x in text[j + 1:k].split(",") if x.strip() and x.strip() != "_"]
                j = k + 1
            else:
                m = IDENT_RE.match(text, j)
                if m:
                    names = [m.group(0)]
                    j = m.end()
            le = text.find("\n", j)
            rest = text[j:min(nxt, le if le != -1 else nxt)]
            mm = re.search(r":=\s*(\S+)", rest)
            for nm in names:
                decls.append({"file": rel, "line": line_of(pos), "kind": "alias", "name": nm.rstrip("."),
                              "full": full_of(nm), "mods": mods, "attrs": parse_attrs(attr_text),
                              "header": "", "binders": "", "type": None, "alias_of": mm.group(1) if mm else None,
                              "ns": ns_full, "vars": {}, "body_head": None})
            consumed_until = j
            continue
        anon = False
        prio = None
        if kw == "instance":
            while text.startswith("(", j):
                k = find_matching_bracket(text, j)
                if "priority" in text[j:k]:
                    prio = text[j:k]
                    j = k
                    while j < nxt and text[j].isspace():
                        j += 1
                else:
                    break
        m = IDENT_RE.match(text, j)
        name = None
        if m and not text.startswith(":", j) and text[j] not in "([{⦃":
            name = m.group(0)
            j = m.end()
        if kw == "instance" and name is None:
            anon = True
        if name is None and not anon:
            continue
        if name is not None:
            name = name.rstrip(".")
        header, hend = parse_header(text, j, nxt, inductive=kw in ("inductive", "class inductive"))
        binders, rtype = split_binders_type(header)
        binders = re.sub(r"^\{[^}:]*\}", "", binders.strip())  # universe parameters `.{u v}`
        body_head = None
        if hend < nxt and text.startswith(":=", hend):
            bm = re.match(r"\s*([^\s()\[\]{}⦃⦄⟨⟩,;:]+)", text[hend + 2:min(nxt, hend + 200)])
            if bm:
                body_head = bm.group(1)
        rec = {"file": rel, "line": line_of(pos), "kind": kw, "name": name,
               "full": full_of(name) if name is not None else None, "mods": mods,
               "attrs": parse_attrs(attr_text), "header": " ".join(header.split()),
               "binders": " ".join(binders.split()),
               "type": " ".join(rtype.split()) if rtype is not None else None, "ns": ns_full,
               "prio": prio, "vars": lookup_vars(binders + " " + (rtype or "")), "body_head": body_head}
        if kw in ("structure", "class", "inductive", "class inductive"):
            body_start = hend
            if kw in ("structure", "class"):
                wpos = text.find("where", hend, nxt)
                if wpos != -1:
                    body_start = wpos + 5
                else:
                    cpos = text.find(":=", hend, nxt)
                    if cpos != -1:
                        body_start = cpos + 2
            elif text.startswith("where", hend):
                body_start = hend + 5
            fields, ctors = parse_body_fields(text, body_start, nxt, kw if kw != "class inductive" else "inductive")
            rec["fields"] = fields
            rec["ctors"] = ctors
        decls.append(rec)
        consumed_until = max(j, hend)
    return decls


def extract_tree(root: str, dirs: list) -> list:
    out = []
    for d in dirs:
        base = os.path.join(root, d)
        for dp, _dn, fn in os.walk(base):
            for f in sorted(fn):
                if f.endswith(".lean"):
                    try:
                        out.extend(extract_file(os.path.join(dp, f), root))
                    except Exception as e:  # pragma: no cover - keep going on parse failures
                        print(f"warning: failed to parse {dp}/{f}: {e}", file=sys.stderr)
    return out


# --------------------------------------------------------------------------------------------
# Part 2: analysis
# --------------------------------------------------------------------------------------------

THM_KINDS = {"theorem", "lemma"}
DEF_KINDS = {"def", "abbrev", "irreducible_def", "opaque"}
TYPE_KINDS = {"structure", "class", "inductive", "class inductive", "class abbrev"}
CAMEL_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")
UPPER_TOKEN_OK = re.compile(r"^[A-Z](?:[0-9']|$)")  # single-letter names such as C, X, T'
META_PREFIXES = ("Mathlib/Tactic/", "Mathlib/Lean/", "Mathlib/Util/", "Mathlib/Testing/", "Mathlib/Mathport/")

# Tokens from the naming-convention dictionary that do not correspond to declarations.
DICT_TOKENS = {"natCast", "intCast", "ratCast", "nnratCast", "ofNat", "ofScientific", "biSup", "biInf",
               "biUnion", "biInter", "iUnion", "iInter", "sUnion", "sInter", "iSup", "iInf", "sSup", "sInf",
               "setOf", "toNat", "toFun", "invFun", "toReal", "toNNReal", "toENNReal", "eNorm", "enorm", "natAbs",
               "natDegree", "leadingCoeff", "nhdsWithin", "atTop", "atBot", "ofReal", "zpow", "zsmul", "nsmul",
               "npow", "fderiv", "iteratedFDeriv", "eLpNorm", "memLp"}

# Known outdated name components (Lean 3 era or superseded conventions), with the current spelling.
OUTDATED_TOKENS = {
    "bUnion": "biUnion", "bInter": "biInter", "supr": "iSup", "infi": "iInf", "bsupr": "biSup",
    "binfi": "biInf", "Union": "iUnion", "Inter": "iInter", "Sup": "sSup", "Inf": "sInf",
    "coe_nat": "natCast", "coe_int": "intCast", "nat_coe": "natCast", "int_coe": "intCast",
    "coe_rat": "ratCast", "nonzero": "ne_zero", "bit0": "(removed)", "bit1": "(removed)",
    "nat_abs": "natAbs", "emptyc": "emptyCollection", "nat_cast": "natCast", "int_cast": "intCast",
    "rat_cast": "ratCast", "finset_sum": "sum", "finset_prod": "prod", "is_o": "isLittleO",
    "is_O": "isBigO", "finsupp_sum": "sum", "finsupp_prod": "prod",
}

D_RULES = {
    "iff": (["↔", "Iff", "⇔"], "medium"),
    "ne": (["≠", "Ne", "¬", "NeZero"], "medium"),
    "eq": (["=", "Eq", "≍", "HEq", "≡"], "medium"),
    "not": (["¬", "≠", "Not", "∉", "False", "⊄", "∌", ".not", "!", "not "], "medium"),
    "mem": (["∈", "∉", "Mem", "mem"], "low"),
    "subset": (["⊆", "⊂", "Subset", "subset", "≤"], "medium"),
    "ssubset": (["⊂", "SSubset", "ssubset", "<"], "medium"),
    "dvd": (["∣", "Dvd", "dvd"], "medium"),
    "lt": (["<", ">", "Lt", "lt", "⊂"], "low"),
    "le": (["≤", "≥", "Le", "le", "⊆", "⊑"], "low"),
    "union": (["∪", "⋃", "Union", "union"], "medium"),
    "inter": (["∩", "⋂", "Inter", "inter"], "medium"),
}

CATEGORY_INFO = collections.OrderedDict([
    ("A1", ("Uppercase tokens in theorem names",
            "Theorem/lemma names are `snake_case`; an `UpperCamelCase` declaration referenced inside one must "
            "be written in `lowerCamelCase` (e.g. `isCompact_iff`, not `IsCompact_iff`). Accepted exceptions: "
            "single capital letters (`C`, `X`), Greek letters, interval names (`Icc`), and data-valued "
            "definitions whose own name is (by exception) `UpperCamelCase` (`Gamma`, `Lp`, `LSeries`). "
            "Confidence `high` = the token names an existing `UpperCamelCase` declaration; `low` = short acronym.")),
    ("A2", ("Prop-valued definitions not in UpperCamelCase",
            "A `def`/`abbrev` whose result type is `Prop` (or `… → Prop`) is a predicate and should be "
            "`UpperCamelCase` (`IsCompact`), not `lowerCamelCase`/`snake_case`.")),
    ("A3", ("Type-valued definitions not in UpperCamelCase",
            "A `def`/`abbrev` whose result type is `Type*`/`Sort*` should be `UpperCamelCase`. Functors into "
            "`Type` (`C ⥤ Type w`) are data and are not flagged.")),
    ("A4", ("Data definitions in snake_case",
            "Definitions producing data should be `lowerCamelCase`; underscores usually indicate a Lean 3 misport "
            "(`foo_bar` instead of `fooBar`). `Simps` projection names are exempt (their names are prescribed).")),
    ("A5", ("Structures / classes / inductives not in UpperCamelCase",
            "Types and type classes must be `UpperCamelCase`.")),
    ("A6", ("Instances of data-valued classes named in snake_case",
            "Instances of data-carrying classes (`Algebra`, `Module`, `Unique`, …) are data and should be "
            "`lowerCamelCase`; snake_case instance names are conventional only for `Prop`-valued classes.")),
    ("A7", ("Instances named in UpperCamelCase",
            "Explicit instance names are `lowerCamelCase` (or auto-generated `instFoo`), never `UpperCamelCase`.")),
    ("A8", ("Structure fields with unexpected casing",
            "Prop fields are `snake_case` (a single predicate is `lowerCamelCase`, e.g. `isOpen'`), data fields are "
            "`lowerCamelCase`, predicate-valued fields (`… → Prop`) are `UpperCamelCase` (`IsOpen`). Rows marked "
            "`mixed convention` are class-valued fields (`hasLimit : HasLimit F`) where both spellings coexist in "
            "Mathlib; `carrier : Type u` in bundled categories is an established exception.")),
    ("A9", ("Inductive constructors with unexpected casing",
            "Constructors of `Type`-valued inductives are `lowerCamelCase`; constructors of `Prop`-valued "
            "inductives are `snake_case` (they are proofs).")),
    ("A10", ("Namespaces containing underscores",
             "Namespaces are `UpperCamelCase` (or match the `lowerCamelCase` definition they scope).")),
    ("A11", ("Stray underscores in names",
             "Names with trailing `_` (often a workaround for keywords: `end_`, `from_`, `section_`) or `__`.")),
    ("B1", ("Probable spelling errors in name components",
            "Rare words (≤ 3 uses) within edit distance 1 (or 2 for long words) of a frequent word. Many rows are "
            "legitimate abbreviations or prefixes (`gsmul`, `hcongr`); rows I verified are marked `confirmed`.")),
    ("B2", ("camelCase tokens that do not correspond to any declaration",
            "A `lowerCamelCase`/`UpperCamelCase` token in a theorem name should name an existing declaration (or a "
            "dictionary word like `natCast`). `unknown` rows are typo/outdated candidates; `abbrev of X` rows are "
            "shortened references (`hasDeriv` for `HasDerivAt`) which are a milder inconsistency.")),
    ("B3", ("Flattened camelCase (`relindex` for `relIndex`)",
            "A lowercase token that is exactly the lowercased form of a multi-word camelCase declaration name.")),
    ("C1", ("Lean 3 style snake_case spellings of camelCase names",
            "Token sequences such as `set_of`, `nat_cast`, `strict_mono`, `not_mem` where Mathlib now uses "
            "`setOf`, `natCast`, `strictMono`, `notMem`. Only patterns whose camelCase spelling dominates are "
            "listed (counts are declarations using each spelling). Some rows are legitimate phrases.")),
    ("C2", ("Known outdated name components",
            "Components that were renamed library-wide (`supr`→`iSup`, `bUnion`→`biUnion`, `coe_nat`→`natCast`, "
            "`nonzero`→`ne_zero`, …) but survive in non-deprecated declarations.")),
    ("D1", ("Name/statement mismatches",
            "The conclusion part of the name (before the first `_of_`) mentions a relation (`iff`, `ne`, `eq`, "
            "`lt`, `le`, `subset`, `inter`, `union`, `dvd`, `not`, `mem`) that does not occur in the statement, "
            "e.g. `foo_ne_top : x < ∞`, `foo_inter : a ⊓ b`, `foo_le_bar : a < b`.")),
    ("D2", ("`succ`/`pred` names for `+ 1`/`- 1` statements",
            "Mathlib now states results with `n + 1` rather than `n.succ`; names still saying `succ` (or `pred` "
            "for `- 1`) are outdated, and vice versa.")),
    ("E1", ("Textually identical statements under different names",
            "Two non-deprecated theorems in the same namespace (or one at root) whose binders, statement and "
            "the types of the section variables they use are textually identical. Candidates for `alias`/removal.")),
    ("F1", ("Probable spelling errors in comments and docstrings",
            "Prose, not names: a word used at most twice in Mathlib's comments, unknown to `aspell`, and within "
            "edit distance 1 (or 2, for long words) of a word the comments use often. Identifiers that escape a "
            "code span, productive prefixes (`bi`, `co`, `semi`, …), inflections, proper nouns, license headers "
            "and bibliography entries are filtered out, but real English and mathematical words that `aspell` "
            "simply does not know (`imprimitive`, `probabilist`, `disequalities`) still come through, as do "
            "British spellings (`localisations`, `parametrised`); those are `fp`. Only the first site is listed "
            "when a word is misspelled more than once.")),
])


class Audit:
    def __init__(self, decls: list, dep_decls: list, root: str):
        self.decls = decls
        self.root = root
        self.findings: list = []
        self.live = [x for x in decls if not self.is_deprecated(x)]
        self.thms = [x for x in self.live if x["kind"] in THM_KINDS]
        self.defs = [x for x in self.live if x["kind"] in DEF_KINDS]
        self.known_last: set = set()
        self.known_lcfirst: set = set()
        for x in decls + dep_decls:
            self._learn(x)
        self.namespaces = self._collect_namespaces()
        self.known_stripped = {self.strip_decor(k) for k in self.known_last | self.known_lcfirst}
        self.prop_classes = self._prop_classes()
        self.upper_data_defs = self._upper_data_defs()
        self.class_decls = [x for x in decls if x["kind"] in ("class", "class inductive")]

    # ---- helpers
    @staticmethod
    def last(name: str) -> str:
        if name.endswith("»"):
            return name[name.rfind("«"):]
        return name.split(".")[-1]

    @staticmethod
    def strip_decor(tok: str) -> str:
        return re.sub(r"['!?₀-₉]+$", "", tok)

    @staticmethod
    def tokens(comp: str) -> list:
        return [t for t in comp.strip("«»").split("_") if t]

    def words(self, comp: str) -> list:
        out = []
        for t in self.tokens(comp):
            out.extend(w.lower() for w in CAMEL_RE.findall(self.strip_decor(t)))
        return out

    @staticmethod
    def is_deprecated(x: dict) -> bool:
        return x["attrs"]["deprecated"] or x["file"].startswith("Mathlib/Deprecated/")

    @staticmethod
    def loc(x: dict) -> str:
        return f"{x['file']}:{x['line']}"

    @staticmethod
    def prop_typed(t) -> bool:
        return t is not None and re.search(r"(^|\s|→|,)Prop\s*$", t) is not None

    @staticmethod
    def type_typed(t) -> bool:
        if t is None:
            return False
        seg = re.split(r"→|,", t)[-1].strip()
        return re.match(r"^(Type|Sort)(\s*\*|\s+[^\s]+|\s*\([^()]*\))?$", seg) is not None

    @staticmethod
    def conclusion_head(t):
        """Head symbol of the conclusion of a (possibly `∀`/`→`-prefixed) type."""
        if not t:
            return None
        s = t.strip()
        depth = 0
        last_cut = 0
        i = 0
        while i < len(s):
            c = s[i]
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0:
                if c == "→":
                    last_cut = i + 1
                elif c == "," and s[:i].lstrip().startswith("∀"):
                    last_cut = i + 1
            i += 1
        body = s[last_cut:].strip()
        m = re.match(r"([A-Za-z_][\w.']*)", body)
        return m.group(1).rstrip(".") if m else None

    def _learn(self, x: dict):
        if x["full"]:
            lc = self.last(x["full"])
            self.known_last.add(lc)
            self.known_lcfirst.add(lc[:1].lower() + lc[1:])
        for f, _ in x.get("fields", []):
            self.known_last.add(f)
            self.known_lcfirst.add(f[:1].lower() + f[1:])
        for c in x.get("ctors", []):
            self.known_last.add(c)
            self.known_lcfirst.add(c[:1].lower() + c[1:])

    def _collect_namespaces(self) -> collections.Counter:
        namespaces: collections.Counter = collections.Counter()
        for d in ("Mathlib", "Archive", "Counterexamples"):
            for dp, _dn, fn in os.walk(os.path.join(self.root, d)):
                for f in fn:
                    if f.endswith(".lean"):
                        with open(os.path.join(dp, f), encoding="utf-8") as fh:
                            for line in fh:
                                m = re.match(r"namespace\s+(\S+)", line)
                                if m:
                                    namespaces[m.group(1)] += 1
                                    for comp in m.group(1).split("."):
                                        self.known_last.add(comp)
                                        self.known_lcfirst.add(comp[:1].lower() + comp[1:])
        return namespaces

    def _prop_classes(self) -> set:
        props = set()
        for x in self.decls:
            if x["full"] and x["kind"] in TYPE_KINDS | DEF_KINDS and self.prop_typed(x["type"]):
                props.add(self.last(x["full"]))
                props.add(x["full"])
        props |= {"Fact", "Nonempty", "Subsingleton", "IsEmpty", "Finite", "Countable", "Infinite", "Nontrivial",
                  "Small", "NeZero", "Mono", "Epi", "IsIso", "Faithful", "Full", "Additive", "IsFiltered",
                  "IsCofiltered", "Balanced", "IsConnected", "IsPreconnected", "Final", "Initial", "IsDiscrete",
                  "Std.Commutative", "Std.Associative", "Std.IdempotentOp", "Std.Total", "Std.Refl", "Std.Symm",
                  "Std.Irrefl", "Std.Antisymm", "Std.Asymm", "Std.Trans", "Std.LawfulEqCmp", "Std.LawfulCmp",
                  "LawfulBEq", "ReflBEq", "DecidableRel", "DecidablePred", "LocallySmall", "EssentiallySmall",
                  "WellPowered", "IsWellOrder", "IsTrichotomous", "IsTrans", "IsRefl", "IsSymm", "IsAsymm",
                  "IsAntisymm", "IsIrrefl", "IsStrictOrder", "IsPartialOrder", "IsPreorder", "IsTotal",
                  "IsLinearOrder", "IsStrictTotalOrder", "IsEquiv", "WellFoundedLT", "WellFoundedGT",
                  "IsWellFounded", "UnivLE", "HasPullback", "HasPushout", "HasEqualizer", "HasCoequalizer",
                  "HasProduct", "HasCoproduct", "HasBinaryProduct", "HasBinaryCoproduct", "HasLimit", "HasColimit",
                  "HasLimitsOfShape", "HasColimitsOfShape", "PreservesLimit", "PreservesColimit", "ReflectsLimit",
                  "ReflectsColimit", "PreservesLimitsOfShape", "PreservesColimitsOfShape", "PreservesLimitsOfSize",
                  "PreservesColimitsOfSize", "PreservesFilteredColimits", "IsCorepresentable", "IsRepresentable",
                  "CreatesLimit", "CreatesColimit", "CreatesLimitsOfShape", "CreatesColimitsOfShape",
                  "CreatesLimitsOfSize", "CreatesColimitsOfSize", "ReflectsIsomorphisms", "PreservesLimits",
                  "PreservesColimits", "ReflectsLimits", "ReflectsColimits", "CreatesLimits", "CreatesColimits"}
        # untyped abbreviations whose body is a Prop class (`abbrev IsArtinianRing R := IsArtinian R R`)
        for _ in range(3):
            for x in self.decls:
                if x["full"] and x["kind"] in DEF_KINDS and x["type"] is None and x.get("body_head"):
                    bh = x["body_head"]
                    if bh in props or bh.split(".")[-1] in props:
                        props.add(self.last(x["full"]))
                        props.add(x["full"])
        props -= {"Decidable", "DecidableEq", "Inhabited", "Unique", "Fintype", "Encodable", "Denumerable"}
        return props

    def _upper_data_defs(self) -> set:
        out = set()
        for x in self.decls:
            if x["full"] and x["kind"] in DEF_KINDS | {"instance"} and not self.prop_typed(x["type"]):
                lc = self.last(x["full"])
                if lc[:1].isupper() and not self.type_typed(x["type"]):
                    out.add(lc)
        out |= {"Icc", "Ico", "Ioc", "Ioo", "Iic", "Ioi", "Ici", "Iio", "TFAE", "Prop", "Type", "Sort"}
        return out

    def upper_token_ok(self, t: str) -> bool:
        if UPPER_TOKEN_OK.match(t) or not t[:1].isascii():
            return True
        return self.strip_decor(t) in self.upper_data_defs

    def add(self, cat: str, x: dict, detail: str, conf: str, name=None, key=None):
        nm = name if name is not None else (x["full"] or f"(anonymous {x['kind']})")
        self.findings.append({"cat": cat, "key": key or f"{cat}|{nm}|{x['file']}", "name": nm, "kind": x["kind"],
                              "file": x["file"], "line": x["line"], "detail": detail, "conf": conf})

    def add_raw(self, cat: str, key: str, name: str, kind: str, file: str, line: int, detail: str, conf: str):
        self.findings.append({"cat": cat, "key": key, "name": name, "kind": kind, "file": file, "line": line,
                              "detail": detail, "conf": conf})

    # ---- A: casing
    def check_casing(self):
        for x in self.thms:
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            toks = self.tokens(comp)
            bad = [t for t in toks if t[:1].isupper() and not self.upper_token_ok(t)]
            if bad:
                if all(re.match(r"^[A-Z0-9₀-₉']+$", t) and len(self.strip_decor(t)) <= 5 for t in bad):
                    conf = "low"
                elif any(self.strip_decor(t) in self.known_last for t in bad):
                    conf = "high"
                else:
                    conf = "medium"
                self.add("A1", x, f"uppercase token(s) `{'`, `'.join(bad)}`", conf)
            if "__" in comp or comp.endswith("_"):
                self.add("A11", x, "stray underscore", "high")
        for x in self.defs:
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            t = x["type"]
            meta = " (meta code)" if x["file"].startswith(META_PREFIXES) else ""
            if "__" in comp or comp.endswith("_"):
                self.add("A11", x, "stray underscore", "high")
            if self.prop_typed(t):
                if not comp[:1].isupper():
                    self.add("A2", x, f"Prop-valued `{x['kind']}` (type `{t}`) should be UpperCamelCase{meta}",
                             "high" if not meta else "medium")
                elif "_" in comp.rstrip("'"):
                    self.add("A2", x, f"Prop-valued `{x['kind']}` (type `{t}`) contains an underscore{meta}", "high")
            elif self.type_typed(t):
                if not comp[:1].isupper():
                    self.add("A3", x, f"Type-valued `{x['kind']}` (type `{t}`) should be UpperCamelCase{meta}",
                             "medium")
                elif "_" in comp.rstrip("'"):
                    self.add("A3", x, f"Type-valued `{x['kind']}` (type `{t}`) contains an underscore{meta}", "high")
            elif "_" in comp.rstrip("'") and ".Simps." not in x["full"] and not x["full"].startswith("Simps."):
                self.add("A4", x, f"`{x['kind']}` in snake_case (type `{(t or '?')[:60]}`){meta}",
                         "low" if meta else "medium")
        for x in self.live:
            if x["kind"] in TYPE_KINDS:
                comp = self.last(x["full"])
                if comp.startswith("«"):
                    continue
                if not comp[:1].isupper():
                    self.add("A5", x, f"`{x['kind']}` should be UpperCamelCase", "high")
                elif "_" in comp.rstrip("'"):
                    self.add("A5", x, f"`{x['kind']}` contains an underscore", "high")
            if x["kind"] == "instance" and x["full"]:
                comp = self.last(x["full"])
                if comp.startswith("«"):
                    continue
                if "_" in comp.rstrip("'"):
                    head = self.conclusion_head(x["type"])
                    if head and len(head) > 1 and head not in ("letI", "haveI", "let", "have") \
                            and head not in self.prop_classes and head.split(".")[-1] not in self.prop_classes:
                        self.add("A6", x, f"snake_case instance of data-valued class `{head}`", "medium")
                elif comp[:1].isupper():
                    self.add("A7", x, "UpperCamelCase instance name", "low")
        for ns, cnt in self.namespaces.items():
            for comp in ns.split("."):
                if comp != "_root_" and not comp.startswith("«") and "_" in comp:
                    self.add_raw("A10", f"A10|{ns}", ns, "namespace", "", 0,
                                 f"namespace component `{comp}` contains an underscore ({cnt} occurrence(s))",
                                 "medium")
                    break

    # ---- A8/A9: fields and constructors
    def classify_field_type(self, ft: str) -> str:
        if not ft:
            return "unknown"
        ft = ft.split(" := ")[0].strip()
        if re.search(r"(^|\s|→|,)Prop\s*$", ft):
            return "pred"
        if self.type_typed(ft):
            return "type"
        head = self.conclusion_head(ft) or ""
        if len(head) >= 3 and head[:1].isupper():
            base = head.split(".")[-1]
            is_class = any(self.last(y["full"]) == base for y in self.class_decls) or head in self.prop_classes
            if head in self.prop_classes or base in self.prop_classes:
                return "propclass" if is_class and base not in {"True", "False"} else "prop"
        if any(c in ft for c in "=≠≤<↔∃¬∈∉⊆⊂∧∨∣≡"):
            return "prop"
        if "∀" in ft:
            return "prop"
        return "data"

    def check_fields(self):
        for x in self.live:
            if x["kind"] in ("structure", "class"):
                for fname, ftype in x.get("fields", []):
                    if fname.startswith("«") or fname in ("_", "mk"):
                        continue
                    cls = self.classify_field_type(ftype)
                    key = f"A8|{x['full']}.{fname}"
                    nm = f"{x['full']}.{fname}"
                    base = fname.rstrip("'")
                    short = ftype.split(" := ")[0][:60]
                    if cls == "pred" and not fname[:1].isupper():
                        self.add("A8", x, f"predicate-valued field `{fname} : {short}` should be UpperCamelCase",
                                 "medium", name=nm, key=key)
                    elif cls == "prop" and "_" not in base and re.search(r"[a-z][A-Z]", base) \
                            and base not in self.known_lcfirst:
                        self.add("A8", x, f"Prop field `{fname} : {short}` is camelCase (expected snake_case)",
                                 "medium", name=nm, key=key)
                    elif cls == "prop" and fname[:1].isupper():
                        self.add("A8", x, f"Prop field `{fname} : {short}` is UpperCamelCase (expected snake_case)",
                                 "medium", name=nm, key=key)
                    elif cls == "propclass" and "_" not in base and re.search(r"[a-z][A-Z]", base):
                        self.add("A8", x, f"class-valued field `{fname} : {short}` is camelCase (mixed convention)",
                                 "low", name=nm, key=key)
                    elif cls in ("data", "type") and "_" in base:
                        hd = (self.conclusion_head(ftype.split(" := ")[0]) or "")
                        conf = "medium" if (hd[:1].isupper() or any(c in ftype for c in "→×ℕℤℚℝℂ")) else "low"
                        self.add("A8", x, f"data field `{fname} : {short}` uses snake_case", conf, name=nm, key=key)
                    elif cls == "type" and not fname[:1].isupper():
                        self.add("A8", x, f"Type-valued field `{fname} : {short}` is lowercase (`carrier` is an "
                                          "established exception)", "low", name=nm, key=key)
            elif x["kind"] in ("inductive", "class inductive"):
                isprop = self.prop_typed(x["type"])
                for c in x.get("ctors", []):
                    base = c.rstrip("'")
                    key = f"A9|{x['full']}.{c}"
                    nm = f"{x['full']}.{c}"
                    if isprop:
                        if "_" not in base and re.search(r"[a-z][A-Z]", base):
                            self.add("A9", x, f"constructor `{c}` of a Prop-valued inductive is camelCase "
                                              "(expected snake_case)", "medium", name=nm, key=key)
                        elif c[:1].isupper():
                            self.add("A9", x, f"constructor `{c}` of a Prop-valued inductive is UpperCamelCase",
                                     "medium", name=nm, key=key)
                    elif "_" in base:
                        self.add("A9", x, f"constructor `{c}` of a Type-valued inductive uses snake_case",
                                 "medium", name=nm, key=key)
                    elif c[:1].isupper():
                        self.add("A9", x, f"constructor `{c}` of a Type-valued inductive is UpperCamelCase",
                                 "low", name=nm, key=key)

    # ---- B1: spelling
    def check_spelling(self):
        wc: collections.Counter = collections.Counter()
        where: dict = collections.defaultdict(list)
        for x in self.live:
            names = []
            if x["full"]:
                names.append(self.last(x["full"]))
            names += [f for f, _ in x.get("fields", [])] + list(x.get("ctors", []))
            if x["attrs"]["to_additive"]:
                names.append(self.last(x["attrs"]["to_additive"]))
            seen = set()
            for nm in names:
                if nm.startswith("«"):
                    continue
                for w in self.words(nm):
                    if w.isdigit() or len(w) < 4 or w in seen:
                        continue
                    seen.add(w)
                    wc[w] += 1
                    if len(where[w]) < 6:
                        where[w].append(x)
        freq = {w for w, c in wc.items() if c >= 30}
        rare = [w for w, c in wc.items() if c <= 3]

        def deletes(w: str, k: int) -> set:
            res = {w}
            frontier = {w}
            for _ in range(k):
                nxt = set()
                for s in frontier:
                    for i in range(len(s)):
                        nxt.add(s[:i] + s[i + 1:])
                res |= nxt
                frontier = nxt
            return res

        index: dict = collections.defaultdict(set)
        for w in freq:
            for d in deletes(w, 2):
                index[d].add(w)

        def dl(a: str, b: str) -> int:
            la, lb = len(a), len(b)
            dist = [[0] * (lb + 1) for _ in range(la + 1)]
            for i in range(la + 1):
                dist[i][0] = i
            for j in range(lb + 1):
                dist[0][j] = j
            for i in range(1, la + 1):
                for j in range(1, lb + 1):
                    cost = 0 if a[i - 1] == b[j - 1] else 1
                    dist[i][j] = min(dist[i - 1][j] + 1, dist[i][j - 1] + 1, dist[i - 1][j - 1] + cost)
                    if i > 1 and j > 1 and a[i - 1] == b[j - 2] and a[i - 2] == b[j - 1]:
                        dist[i][j] = min(dist[i][j], dist[i - 2][j - 2] + 1)
            return dist[la][lb]

        for w in rare:
            cands: set = set()
            for d in deletes(w, 2):
                cands |= index.get(d, set())
            best = None
            for c in cands:
                dist = dl(w, c)
                if (dist == 1 and len(w) >= 5) or (dist == 2 and len(w) >= 9 and wc[c] >= 100):
                    if best is None or dist < best[0] or (dist == best[0] and wc[c] > wc[best[1]]):
                        best = (dist, c)
            if best:
                ex = ", ".join(f"`{y['full'] or y['kind']}` ({self.loc(y)})" for y in where[w][:3])
                x0 = where[w][0]
                self.add_raw("B1", f"B1|{w}", w, "word", x0["file"], x0["line"],
                             f"`{w}` ({wc[w]}×) vs `{best[1]}` ({wc[best[1]]}×): {ex}", "low")

    # ---- B2: unknown camel tokens, B3: flattened camel tokens
    def check_camel_tokens(self):
        tc: collections.Counter = collections.Counter()
        where: dict = collections.defaultdict(list)
        for x in self.live:
            if not x["full"] or x["kind"] not in THM_KINDS:
                continue
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            seen = set()
            for t in self.tokens(comp):
                t = self.strip_decor(t)
                if not t or t in seen:
                    continue
                if re.search(r"[a-z][A-Z]", t) or (t[:1].isupper() and not UPPER_TOKEN_OK.match(t)):
                    seen.add(t)
                    tc[t] += 1
                    if len(where[t]) < 6:
                        where[t].append(x)
        superstrings = sorted(k for k in self.known_last | self.known_lcfirst if len(k) >= 6)
        for t, c in tc.items():
            if c > 12 or t in self.known_last or t in self.known_lcfirst or t in DICT_TOKENS \
                    or t in self.known_stripped or not t[:1].isascii():
                continue
            ex = ", ".join(f"`{y['full']}` ({self.loc(y)})" for y in where[t][:3])
            x0 = where[t][0]
            is_form = "is" + t[:1].upper() + t[1:]
            if t[:1].islower() and (is_form in self.known_lcfirst or is_form in self.known_last):
                self.add_raw("B2", f"B2|{t}", t, "token", x0["file"], x0["line"],
                             f"`{t}` ({c}×): outdated predicate spelling, now `{is_form}`: {ex}", "high")
                continue
            sup = [k for k in superstrings if t in k] if len(t) >= 5 else []
            if sup:
                self.add_raw("B2", f"B2|{t}", t, "token", x0["file"], x0["line"],
                             f"`{t}` ({c}×): abbrev of `{sup[0]}`: {ex}", "low")
            else:
                self.add_raw("B2", f"B2|{t}", t, "token", x0["file"], x0["line"],
                             f"`{t}` ({c}×): unknown: {ex}", "medium")
        # B3
        flat: dict = {}
        for k in self.known_last | self.known_lcfirst:
            if re.search(r"[a-z][A-Z]", k) and "_" not in k and len(CAMEL_RE.findall(k)) >= 2:
                flat.setdefault(self.strip_decor(k).lower(), set()).add(k)
        tc2: collections.Counter = collections.Counter()
        where2: dict = collections.defaultdict(list)
        for x in self.live:
            if not x["full"] or x["kind"] not in THM_KINDS | DEF_KINDS | {"instance"}:
                continue
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            for t in self.tokens(comp):
                t = self.strip_decor(t)
                if len(t) >= 6 and t.islower() and t in flat:
                    tc2[t] += 1
                    if len(where2[t]) < 6:
                        where2[t].append(x)
        for t, c in tc2.items():
            if c > 6:
                continue
            ex = ", ".join(f"`{y['full']}` ({self.loc(y)})" for y in where2[t][:3])
            x0 = where2[t][0]
            self.add_raw("B3", f"B3|{t}", t, "token", x0["file"], x0["line"],
                         f"`{t}` ({c}×) vs `{'`/`'.join(sorted(flat[t]))}`: {ex}", "medium")

    # ---- C1: snake_case forms of camelCase names, C2: outdated tokens
    def check_snake_of_camel(self):
        camel_names: dict = {}

        def snake(camel: str) -> str:
            return "_".join(w.lower() for w in CAMEL_RE.findall(camel))

        for x in self.decls:
            if x["full"] and x["kind"] in DEF_KINDS | TYPE_KINDS | {"instance"}:
                lc = self.last(x["full"])
                if re.search(r"[a-z][A-Z]", lc) and "_" not in lc:
                    camel_names.setdefault(snake(lc), set()).add(lc)
            for f, _ in x.get("fields", []):
                if re.search(r"[a-z][A-Z]", f) and "_" not in f:
                    camel_names.setdefault(snake(f), set()).add(f)
        hits: dict = collections.defaultdict(list)
        camel_tok: collections.Counter = collections.Counter()
        for x in self.live:
            if not x["full"] or x["kind"] not in THM_KINDS | DEF_KINDS:
                continue
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            toks = [self.strip_decor(t) for t in self.tokens(comp)]
            for t in set(toks):
                camel_tok[t] += 1
            n = len(toks)
            for i in range(n):
                for j in range(i + 2, min(n, i + 4) + 1):
                    s = "_".join(toks[i:j])
                    if s in camel_names:
                        hits[s].append(x)
        for s, xs in hits.items():
            cu = max(camel_tok[c] for c in camel_names[s])
            if cu < 5 or not (len(xs) <= 3 or 2 * len(xs) <= cu):
                continue
            conf = "high" if s.split("_")[0] in ("is", "has", "to", "of", "nat", "int", "rat", "set", "coe") \
                and 4 * len(xs) <= cu else "medium"
            ex = ", ".join(f"`{y['full']}` ({self.loc(y)})" for y in xs[:3])
            x0 = xs[0]
            self.add_raw("C1", f"C1|{s}", s, "pattern", x0["file"], x0["line"],
                         f"`{s}` ({len(xs)}×) vs `{'`/`'.join(sorted(camel_names[s]))}` ({cu}×): {ex}", conf)

    def check_outdated_tokens(self):
        for x in self.live:
            if not x["full"] or x["kind"] not in THM_KINDS | DEF_KINDS | {"instance"}:
                continue
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            toks = [self.strip_decor(t) for t in self.tokens(comp)]
            joined = "_".join(toks)
            for old, new in OUTDATED_TOKENS.items():
                if "_" in old:
                    if re.search(rf"(^|_){re.escape(old)}(_|$)", joined):
                        self.add("C2", x, f"`{old}` → `{new}`", "high" if old not in ("finset_sum", "finset_prod",
                                                                                     "finsupp_sum", "finsupp_prod")
                                 else "low", key=f"C2|{old}|{x['full']}|{x['file']}")
                elif old in toks:
                    self.add("C2", x, f"`{old}` → `{new}`", "high", key=f"C2|{old}|{x['full']}|{x['file']}")

    # ---- D: name vs statement
    def check_semantics(self):
        for x in self.thms:
            comp = self.last(x["full"])
            if comp.startswith("«"):
                continue
            toks = [self.strip_decor(t) for t in self.tokens(comp)]
            text = (x["binders"] or "") + " " + (x["type"] or "")
            ty = (x["type"] or "").strip()
            if not ty or re.match(r"^(have|let|haveI|letI|by|TFAE|obtain|suffices)\b", ty):
                continue
            concl = toks[:toks.index("of")] if "of" in toks else toks
            for tok, (needles, conf) in D_RULES.items():
                if tok in concl and not any(nd in text for nd in needles):
                    self.add("D1", x, f"`{tok}` in name, but statement is `{ty[:80]}`", conf,
                             key=f"D1|{tok}|{x['full']}|{x['file']}")
            if "succ" in toks and "succ" not in text and "Succ" not in text and "+ 1" in text:
                self.add("D2", x, f"`succ` in name, `+ 1` in statement: `{ty[:100]}`", "medium")
            if "pred" in toks and "pred" not in text and "Pred" not in text and "- 1" in text:
                self.add("D2", x, f"`pred` in name, `- 1` in statement: `{ty[:100]}`", "medium")
            if "add_one" in comp and "succ" in text and "+ 1" not in text:
                self.add("D2", x, f"`add_one` in name, `succ` in statement: `{ty[:100]}`", "medium")
            if "sub_one" in comp and "pred" in text and "- 1" not in text:
                self.add("D2", x, f"`sub_one` in name, `pred` in statement: `{ty[:100]}`", "medium")

    # ---- E1: duplicates
    def check_duplicates(self):
        groups: dict = collections.defaultdict(list)
        for x in self.thms:
            if x["type"] is None or len(x["type"]) < 12:
                continue
            b = re.sub(r"\[\s*\w+\s*:\s*", "[", x["binders"] or "")
            v = " ".join(f"{k}:{val}" for k, val in sorted(x.get("vars", {}).items()))
            groups[" ".join((v + " ; " + b + " ⊢ " + x["type"]).split())].append(x)
        for xs in groups.values():
            if len(xs) < 2 or all("private" in x["mods"] for x in xs) or len({x["full"] for x in xs}) < 2:
                continue
            nss = {x["full"].rsplit(".", 1)[0] if "." in x["full"] else "" for x in xs}
            if len(nss) > 1 and "" not in nss:
                continue
            x0 = xs[0]
            others = ", ".join(f"`{x['full']}` ({self.loc(x)})" for x in xs[1:])
            self.add_raw("E1", "E1|" + "|".join(sorted(x["full"] for x in xs)), x0["full"], "theorem", x0["file"],
                         x0["line"], f"`{x0['type'][:80]}` — also stated by {others}", "medium")

    # ---- F1: prose
    def check_prose(self, dirs):
        for w, corr, dist, fw, fc, sites in prose_typos.scan(self.root, dirs):
            file, line, kind = sites[0]
            more = f"; also at {len(sites) - 1} other site(s)" if len(sites) > 1 else ""
            conf = "high" if dist == 1 and fc >= 500 else "medium" if fc >= 100 else "low"
            self.add_raw("F1", f"F1|{w}", w, kind, file, line,
                         f"`{w}` → `{corr}` (distance {dist}; {fw} vs {fc} uses in comments{more})", conf)

    def run(self, prose_dirs=("Mathlib", "Archive", "Counterexamples")) -> list:
        self.check_casing()
        self.check_fields()
        self.check_spelling()
        self.check_camel_tokens()
        self.check_snake_of_camel()
        self.check_outdated_tokens()
        self.check_semantics()
        self.check_duplicates()
        self.check_prose(prose_dirs)
        return self.findings


# --------------------------------------------------------------------------------------------
# Part 3: markdown rendering with triage preservation
# --------------------------------------------------------------------------------------------

STATUSES = ("open", "confirmed", "fp", "fixed", "wontfix")
TOKEN_KEYED = {"C2", "D1"}       # key also contains the first `token` of the detail cell
NAME_KEYED = {"A8", "A9", "A10", "B1", "B2", "B3", "C1", "F1"}   # key is category + name only


def row_key(cat: str, name: str, file: str, detail: str) -> str:
    """Stable identity of a row, computed from its visible cells (so that line numbers may change)."""
    if cat in NAME_KEYED:
        return f"{cat}|{name}"
    if cat in TOKEN_KEYED:
        m = re.search(r"`([^`]*)`", detail)
        return f"{cat}|{m.group(1) if m else ''}|{name}|{file}"
    return f"{cat}|{name}|{file}"


def split_row(line: str):
    """Split a markdown table row into cells, honouring escaped pipes."""
    cells = re.split(r"(?<!\\)\|", line.strip())
    return [c.strip().replace("\\|", "|") for c in cells[1:-1]]


def read_existing(path: str) -> dict:
    """Return {key: (status, note)} from an existing audit file."""
    out = {}
    if not os.path.exists(path):
        return out
    cat = None
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"### ([A-Z]\d+):", line)
            if m:
                cat = m.group(1)
                continue
            if cat is None or not line.startswith("| "):
                continue
            cells = split_row(line)
            if len(cells) >= 5 and cells[0] in STATUSES:
                name = cells[1].strip("`")
                file = cells[2].strip("`").rsplit(":", 1)[0]
                out[row_key(cat, name, file, cells[3])] = (cells[0], cells[4])
    return out


def md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def render(findings: list, existing: dict, out_path: str, decl_count: int, file_count: int):
    by_cat: dict = collections.defaultdict(list)
    for f in findings:
        by_cat[f["cat"]].append(f)
    conf_rank = {"high": 0, "medium": 1, "low": 2}
    for f in findings:
        f["key"] = row_key(f["cat"], f["name"], f["file"], f["detail"])
    seen_keys = {f["key"] for f in findings}
    dropped = sum(1 for k in existing if k not in seen_keys)
    today = datetime.date.today().isoformat()
    lines = []
    lines.append("# Mathlib naming-consistency audit")
    lines.append("")
    lines.append(f"_Generated by `scripts/naming_audit/naming_audit.py` on {today}; "
                 f"{decl_count} declarations in {file_count} files scanned._")
    lines.append("")
    lines.append("This is a living document. Every row is identified by its category, declaration/token and file")
    lines.append("(not the line number). Re-running the script keeps the `Status` and `Note` cells of rows that are still present,")
    lines.append("adds new rows as `open`, and drops rows whose declaration no longer exists. Triage by editing")
    lines.append("the `Status`/`Note` cells in place.")
    lines.append("")
    lines.append("Statuses: `open` (not yet looked at), `confirmed` (checked by hand, should be fixed), `fp`")
    lines.append("(false positive or accepted exception), `fixed` (renamed; the row disappears on the next run),")
    lines.append("`wontfix` (real but deliberately left alone).")
    lines.append("")
    lines.append("Confidence (`conf`) is the scanner's own estimate of how likely a row is a genuine problem; it is")
    lines.append("not a triage verdict. Deprecated declarations and `Mathlib/Deprecated/` are excluded everywhere.")
    lines.append("")
    lines.append("## Conventions applied")
    lines.append("")
    lines.append("- Theorems and lemmas: `snake_case`; an `UpperCamelCase` name used inside one becomes")
    lines.append("  `lowerCamelCase` (`isCompact_iff_isClosed`), acronyms are lowercased as a block (`ennreal`).")
    lines.append("- `Prop`s and `Type`s (structures, classes, inductives, `Prop`/`Type`-valued definitions):")
    lines.append("  `UpperCamelCase`. Other definitions (functions, data): `lowerCamelCase`.")
    lines.append("- Structure fields follow the same rule as top-level declarations of the same kind.")
    lines.append("- Dictionary spellings: `natCast`, `intCast`, `ofNat`, `iSup`/`iInf`, `sSup`/`sInf`,")
    lines.append("  `biUnion`, `setOf`, `notMem`, `n + 1` (not `succ`), `ne_zero` (not `nonzero`), …")
    lines.append("- A name should describe the statement: `_iff` ↔ `↔`, `_ne_` ↔ `≠`, `_lt_` ↔ `<`, `_inter_` ↔ `∩`.")
    lines.append("- The same statement should not exist under two names unless one is an `alias`.")
    lines.append("- Comments and docstrings are English prose: category F1 checks their spelling against the")
    lines.append("  vocabulary Mathlib's own comments use, so that technical terms are not flagged.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append("| Category | Description | Rows | open | confirmed | fp | wontfix |")
    lines.append("|---|---|---:|---:|---:|---:|---:|")
    status_of = {}
    for f in findings:
        st, note = existing.get(f["key"], ("open", ""))
        status_of[f["key"]] = (st, note)
    for cat, (title, _desc) in CATEGORY_INFO.items():
        rows = by_cat.get(cat, [])
        cnt = collections.Counter(status_of[r["key"]][0] for r in rows)
        lines.append(f"| [{cat}](#{cat.lower()}-{re.sub(r'[^a-z0-9]+', '-', title.lower()).strip('-')}) | {title} | "
                     f"{len(rows)} | {cnt['open']} | {cnt['confirmed']} | {cnt['fp']} | {cnt['wontfix']} |")
    lines.append("")
    if dropped:
        lines.append(f"_{dropped} row(s) from the previous version of this file no longer apply and were dropped._")
        lines.append("")
    lines.append("## Findings")
    lines.append("")
    for cat, (title, desc) in CATEGORY_INFO.items():
        rows = by_cat.get(cat, [])
        lines.append(f"### {cat}: {title}")
        lines.append("")
        lines.append(desc)
        lines.append("")
        lines.append(f"{len(rows)} row(s).")
        lines.append("")
        if not rows:
            continue
        status_rank = {"confirmed": 0, "open": 1, "wontfix": 2, "fixed": 3, "fp": 4}
        rows.sort(key=lambda r: (status_rank[status_of[r["key"]][0]], conf_rank[r["conf"]], r["file"], r["line"],
                                 r["name"]))
        lines.append(f"| Status | {'Word' if cat == 'F1' else 'Declaration'} | Location | Detail | Note |")
        lines.append("|---|---|---|---|---|")
        for r in rows:
            st, note = status_of[r["key"]]
            loc = f"`{r['file']}:{r['line']}`" if r["file"] else ""
            lines.append(f"| {st} | `{md_escape(r['name'])}` | {loc} | ({r['conf']}) {md_escape(r['detail'])} | "
                         f"{md_escape(note)} |")
        lines.append("")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    return status_of


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".", help="Mathlib checkout")
    ap.add_argument("--deps", nargs="*", default=[], help="directories with upstream Lean sources")
    ap.add_argument("--out", default=None, help="output markdown (default docs/naming_audit.md)")
    ap.add_argument("--dump", default=None, help="also dump the raw declaration records to this JSON file")
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    out = args.out or os.path.join(root, "docs", "naming_audit.md")
    decls = extract_tree(root, ["Mathlib", "Archive", "Counterexamples"])
    if args.dump:
        with open(args.dump, "w") as f:
            json.dump(decls, f)
    dep_decls = []
    for d in args.deps:
        d = os.path.abspath(d)
        dep_decls.extend(extract_tree(os.path.dirname(d), [os.path.basename(d)]))
    audit = Audit(decls, dep_decls, root)
    findings = audit.run()
    existing = read_existing(out)
    files = len({x["file"] for x in decls})
    status_of = render(findings, existing, out, len(decls), files)
    counts = collections.Counter(f["cat"] for f in findings)
    print(f"{len(decls)} declarations, {len(findings)} findings -> {out}")
    for cat in CATEGORY_INFO:
        rows = [f for f in findings if f["cat"] == cat]
        c = collections.Counter(status_of[f["key"]][0] for f in rows)
        print(f"  {cat:4} {counts[cat]:5}  open={c['open']} confirmed={c['confirmed']} fp={c['fp']}")


if __name__ == "__main__":
    main()
