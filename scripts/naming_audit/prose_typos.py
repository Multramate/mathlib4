#!/usr/bin/env python3
"""
Find probable spelling mistakes in Lean comments and docstrings.

Mathlib's prose is full of technical vocabulary that no general dictionary knows
(`cocompact`, `semiring`, `biproduct`, ...), so a plain spell checker is useless on its own.
This scanner instead uses Mathlib's own comment corpus as the domain dictionary:

  a word is reported only when it is rare in the corpus, unknown to `aspell`, and within a
  small edit distance of a word that is common in the corpus.

That combination keeps genuine technical terms (common in the corpus) and proper nouns (known
to aspell, or common) out of the report, while single-occurrence slips like `commatative` next
to 2786 occurrences of `commutative` stand out.

Several further filters remove the systematic false positives that remain:

* identifiers that leak out of code spans are dropped by checking the word against the set of
  identifier fragments used in the *code* of the same files (`lintegral`, `aemeasurable`, ...);
* a word built from a common word and a productive mathematical prefix is a real term, not a
  typo (`bicomposition`, `coindependent`, `semisimple`);
* inflections of a common word are not typos (`monoidals`, `groupoids`);
* words that the corpus only ever writes capitalised are proper nouns (`Manin`, `Welzl`);
* license headers and bibliography entries are skipped, so author names and foreign-language
  titles never enter the corpus at all;
* words that occur inside a hyphenated compound are skipped (`algebro-geometric`).

Usage:
    python3 scripts/naming_audit/prose_typos.py [--root .] [--out report.tsv]

Requires `aspell` with an English dictionary; without it the aspell filter is skipped and the
report is much noisier.
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import subprocess
import sys

# ------------------------------------------------------------------ comment extraction

def extract_comments(src: str):
    """Yield (line_number, kind, text) for every comment in a Lean source file.

    kind is one of 'line' (`--`), 'doc' (`/-- -/`), 'mod' (`/-! -/`) or 'block' (`/- -/`).
    Nested block comments are handled, and string literals are skipped so that `"--"` inside a
    string is not mistaken for a comment.  The remaining, non-comment text is returned too, so
    that callers can tell prose apart from code.
    """
    out = []
    code = []
    i, n = 0, len(src)
    line = 1
    plain = i
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == "\\":
                    j += 1
                elif src[j] == "\n":
                    line += 1
                j += 1
            # A string literal's body is not code.  Leaving it in `code` registered every English
            # word inside a string as an identifier, and `scan`'s `keep()` then dropped that word
            # wherever it also occurred in real prose: `auxilliary` and `superceded` each sit in a
            # genuine docstring and in a deprecation message, and neither was ever reported.
            code.append(src[plain:i])
            i = j + 1
            plain = i
            continue
        if src.startswith("--", i):
            code.append(src[plain:i])
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append((line, "line", src[i + 2:j]))
            i = j
            plain = i
            continue
        if src.startswith("/-", i):
            code.append(src[plain:i])
            kind = ("doc" if src.startswith("/--", i)
                    else "mod" if src.startswith("/-!", i) else "block")
            start_line = line
            depth = 1
            j = i + 2
            body_start = j
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                    continue
                if src.startswith("-/", j):
                    depth -= 1
                    j += 2
                    continue
                if src[j] == "\n":
                    line += 1
                j += 1
            out.append((start_line, kind, src[body_start:max(body_start, j - 2)]))
            i = j
            plain = i
            continue
        i += 1
    code.append(src[plain:n])
    return out, "".join(code)


def extract_strings(src: str):
    """Yield (line_number, text) for every string literal body in a Lean source file.

    Comments are skipped, so a `"` inside one is not mistaken for a literal.  The body is returned
    raw: escapes, `{…}` antiquotations and Lean's `\\<newline>` string gaps are the caller's to
    strip, because what counts as prose differs by surface.
    """
    out = []
    i, n = 0, len(src)
    line = 1
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j == -1 else j
            continue
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                    continue
                if src.startswith("-/", j):
                    depth -= 1
                    j += 2
                    continue
                if src[j] == "\n":
                    line += 1
                j += 1
            i = j
            continue
        if c == '"':
            start_line = line
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == "\\":
                    j += 1
                    if j < n and src[j] == "\n":
                        line += 1
                elif src[j] == "\n":
                    line += 1
                j += 1
            out.append((start_line, src[i + 1:j]))
            i = j + 1
            continue
        i += 1
    return out


# A string literal is prose only if it reads like a sentence: interpolation holes, escapes and
# Lean's line continuations come out first, and what is left must be several lowercase words.
ANTIQUOT = re.compile(r"\{[^{}]*\}")
STRING_GAP = re.compile(r"\\\s*\n\s*")
ESCAPE = re.compile(r"\\[nrt\"\\']")


def string_prose(text: str) -> str:
    """The prose of a string literal body, or '' if it does not read like prose."""
    t = STRING_GAP.sub(" ", text)
    t = ANTIQUOT.sub(" ", t)
    t = ESCAPE.sub(" ", t)
    if len(re.findall(r"\b[a-z]{2,}\b", t)) < 5:
        return ""
    return t


# ------------------------------------------------------------------ prose cleaning

INLINE_CODE = re.compile(r"`[^`]*`")
FENCED = re.compile(r"```.*?```", re.S)
LATEX = re.compile(r"\$\$.*?\$\$|\$[^$\n]*\$|\\\(.*?\\\)|\\\[.*?\\\]", re.S)
URL = re.compile(r"https?://\S+|www\.\S+")
# `"D"ependent` and friends: a quoted letter spliced into a word, used for emphasis.
SPLICE = re.compile(r'"[A-Za-z]"(?=[A-Za-z])|(?<=[A-Za-z])"[A-Za-z]"')
# A bibliography entry, `[F. Trèves, *Topological vector spaces*][treves1967]`: titles and author
# names there are not English prose and are often not even English.
# Three forms, all of which wrap onto a second line in practice:
#   `[F. Trèves, *Topological vector spaces*][treves1967]`, `[crans2017]`, and «libre».
CITATION = re.compile(r"\[[^\[\]]*\]\[[^\]]*\]"
                      r"|\[[A-Za-z][A-Za-z0-9_.'-]*\]"
                      r"|«[^»]*»", re.S)
TEXCMD = re.compile(r"\\[A-Za-z]+")
# A "word" is a run of ASCII letters, optionally with internal apostrophes.
WORD = re.compile(r"[A-Za-z]+(?:'[A-Za-z]+)*")
IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")
# The license header at the top of every file: its `Authors:` list is not prose.
LICENSE = re.compile(r"^\s*Copyright", re.M)


# Marks where non-prose was cut out.  A word touching one of these is a fragment of something
# that was half code and half prose, such as the `ependent` left behind by ``a `d`ependent sum``.
CUT = "\x00"


def clean(text: str) -> str:
    """Strip everything that is not English prose: code spans, LaTeX, URLs, TeX commands.

    Each removed span leaves a `CUT` marker, so that a word abutting it can be recognised as a
    fragment rather than read as a misspelling.
    """
    for rx in (FENCED, INLINE_CODE, LATEX, URL, TEXCMD, SPLICE):
        text = rx.sub(CUT, text)
    return text


def prose_words(text: str):
    """Yield (word, hyphenated) for each prose word, skipping obvious identifier leakage."""
    cleaned = clean(CITATION.sub(CUT, text))
    for m in WORD.finditer(cleaned):
        w = m.group(0)
        # identifiers that leaked through: internal capitals, or all caps
        if w.isupper() and len(w) > 1:
            continue
        if re.search(r"[a-z][A-Z]", w):
            continue
        a, b = m.start(), m.end()
        # a word glued to a removed span is a fragment of it, not a word of the prose
        if (a > 0 and cleaned[a - 1] == CUT) or (b < len(cleaned) and cleaned[b] == CUT):
            continue
        hyphen = (a > 0 and cleaned[a - 1] == "-") or (b < len(cleaned) and cleaned[b] == "-")
        yield w, hyphen


def code_fragments(code: str, out: set) -> None:
    """Collect lowercased identifiers and their `_`-separated parts from Lean code."""
    for m in IDENT.finditer(code):
        ident = m.group(0)
        out.add(ident.lower())
        for part in ident.split("_"):
            if len(part) >= 3:
                out.add(part.lower())
        # split camelCase too: `lintegral_add` and `AEMeasurable` alike
        for part in re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])", ident):
            if len(part) >= 3:
                out.add(part.lower())


# ------------------------------------------------------------------ morphology

# Productive prefixes in mathematical English: `prefix + term` is a term, not a misspelling.
PREFIXES = (
    "anti", "auto", "bi", "co", "contra", "counter", "cross", "di", "endo", "epi", "equi",
    "hetero", "homo", "hyper", "infra", "inter", "intra", "iso", "meta", "mono", "multi",
    "non", "over", "para", "poly", "post", "pre", "pro", "proto", "pseudo", "quasi", "re",
    "semi", "sub", "super", "sur", "trans", "tri", "ultra", "un", "under", "uni",
)
SUFFIXES = ("s", "es", "ed", "d", "ing", "ly", "al", "ic", "ity", "ise", "ised", "ises",
            "isation", "ising", "ness", "er", "ers", "est", "able", "ion", "ions")


def morphological(w: str, common: set) -> bool:
    """True if `w` is a regular derivative of a word the corpus already uses often."""
    # A lone letter in front of a common word is an identifier, not a typo: `efloor`, `cgraph`.
    if len(w) > 4 and w[1:] in common:
        return True
    for p in PREFIXES:
        if w.startswith(p) and len(w) > len(p) + 2:
            stem = w[len(p):]
            if stem in common or any(stem + s in common for s in ("e", "s")):
                return True
    for s in SUFFIXES:
        if w.endswith(s) and len(w) > len(s) + 2:
            stem = w[: len(w) - len(s)]
            if stem in common or stem + "e" in common or stem + "y" in common:
                return True
            if len(stem) > 2 and stem[-1] == stem[-2] and stem[:-1] in common:
                return True
    return False


# ------------------------------------------------------------------ distance

def damerau(a: str, b: str, cap: int = 3) -> int:
    la, lb = len(a), len(b)
    if abs(la - lb) > cap:
        return cap + 1
    prev2 = None
    prev = list(range(lb + 1))
    for i in range(1, la + 1):
        cur = [i] + [0] * lb
        for j in range(1, lb + 1):
            cost = 0 if a[i - 1] == b[j - 1] else 1
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost)
            if prev2 is not None and i > 1 and j > 1 and a[i - 1] == b[j - 2] and a[i - 2] == b[j - 1]:
                cur[j] = min(cur[j], prev2[j - 2] + 1)
        if min(cur) > cap:
            return cap + 1
        prev2, prev = prev, cur
    return prev[lb]


def deletions(w: str, k: int) -> set:
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


# ------------------------------------------------------------------ the dictionary

# Without a dictionary the report roughly triples in size, and which words survive depends on which
# machine ran the script — so fall back to a hunspell word list before giving up. Set
# MATHLIB_TYPO_DICT to a .dic file to point the fallback somewhere specific.
DICT_ENV = "MATHLIB_TYPO_DICT"
DICT_GUESSES = (
    "/usr/share/hunspell/en_US.dic",
    "/usr/share/myspell/en_US.dic",
    "/usr/share/dict/words",
    os.path.expanduser("~/AppData/Local/Programs/MiKTeX/hunspell/dicts/en_US.dic"),
    os.path.expanduser("~/AppData/Local/Programs/MiKTeX/hunspell/dicts/en-GB.dic"),
)

_dictionary_cache = None


def load_dictionary() -> set:
    """An English word list, or the empty set if none is installed.

    A hunspell `.dic` lists stems with affix flags; rather than interpret the `.aff` rules, the
    regular inflections are added by hand, which is enough for the one question asked of it — is
    this word ordinary English?"""
    global _dictionary_cache
    if _dictionary_cache is not None:
        return _dictionary_cache
    words = set()
    for path in ([os.environ[DICT_ENV]] if os.environ.get(DICT_ENV) else []) + list(DICT_GUESSES):
        if not path or not os.path.exists(path):
            continue
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                w = line.split("/")[0].strip().lower()
                if w and w.isalpha():
                    words.add(w)
    if words:
        extra = set()
        for w in words:
            extra.update((w + "s", w + "es", w + "ed", w + "d", w + "ing", w + "ly"))
            if w.endswith("e"):
                extra.update((w[:-1] + "ing", w[:-1] + "ed"))
            if w.endswith("y"):
                extra.update((w[:-1] + "ies", w[:-1] + "ied"))
        words |= extra
    _dictionary_cache = words
    return words


def aspell_unknown(words) -> set:
    """Return the subset of `words` no dictionary recognises.

    `aspell` is asked first, because it knows about morphology; a hunspell word list is the
    fallback. With neither, every word is 'unknown' and the caller's report is much noisier — the
    warning says so."""
    try:
        p = subprocess.run(["aspell", "--lang=en", "--encoding=utf-8", "list"],
                           input="\n".join(sorted(words)), capture_output=True, text=True,
                           timeout=600)
        return set(p.stdout.split())
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        pass
    known = load_dictionary()
    if known:
        print(f"warning: aspell unavailable, using a hunspell word list ({len(known)} words)",
              file=sys.stderr)
        return {w for w in words if w.lower() not in known}
    print("warning: no dictionary available, skipping the dictionary filter", file=sys.stderr)
    return set(words)


# ------------------------------------------------------------------ main

def scan(root: str, dirs=("Mathlib", "Archive", "Counterexamples"), min_freq: int = 20,
         max_rare: int = 2, verbose: bool = False):
    """Scan the comments of a Mathlib checkout.

    Returns `(word, correction, distance, uses_of_word, uses_of_correction, sites)` for each
    probable misspelling, most-confident first; `sites` is a list of `(file, line, kind)`.
    """
    root = os.path.abspath(root)
    freq: collections.Counter = collections.Counter()
    lower: collections.Counter = collections.Counter()
    hyphenated: set = set()
    idents: set = set()
    sites: dict = collections.defaultdict(list)
    files = 0
    for d in dirs:
        for dp, _dn, fn in os.walk(os.path.join(root, d)):
            for f in sorted(fn):
                if not f.endswith(".lean"):
                    continue
                files += 1
                path = os.path.join(dp, f)
                rel = os.path.relpath(path, root).replace(os.sep, "/")
                with open(path, encoding="utf-8") as fh:
                    src = fh.read()
                comments, code = extract_comments(src)
                code_fragments(code, idents)
                for lineno, kind, text in comments:
                    if kind == "block" and LICENSE.search(text):
                        continue  # license header: `Authors:` is a name list, not prose
                    for w, hyph in prose_words(text):
                        lw = w.lower()
                        freq[lw] += 1
                        if not w[0].isupper():
                            lower[lw] += 1
                        if hyph:
                            hyphenated.add(lw)
                        if len(sites[lw]) < 4:
                            sites[lw].append((rel, lineno, kind))

    common = {w for w, c in freq.items() if c >= min_freq}
    rare = [w for w, c in freq.items() if c <= max_rare and len(w) >= 5 and w.isalpha()]
    say = (lambda m: print(m, file=sys.stderr)) if verbose else (lambda m: None)
    say(f"{files} files, {len(freq)} distinct prose words, {len(common)} common, "
        f"{len(rare)} rare candidates")

    def keep(w: str) -> bool:
        if w in idents:
            return False           # an identifier that escaped a code span
        if w in hyphenated:
            return False           # part of a compound, e.g. `algebro-geometric`
        if lower[w] == 0:
            return False           # only ever capitalised: a proper noun
        return not morphological(w, common)

    rare = [w for w in rare if keep(w)]
    say(f"{len(rare)} after identifier/morphology/proper-noun filters")
    rare = [w for w in rare if w in aspell_unknown(rare)]
    say(f"{len(rare)} rare words unknown to aspell")

    index: dict = collections.defaultdict(set)
    for w in common:
        for d in deletions(w, 2):
            index[d].add(w)

    rows = []
    for w in rare:
        cands: set = set()
        for d in deletions(w, 2):
            cands |= index.get(d, set())
        best = None
        for c in cands:
            if c == w:
                continue
            dist = damerau(w, c)
            ok = (dist == 1 and len(w) >= 5) or (dist == 2 and len(w) >= 9 and freq[c] >= 200)
            if ok and (best is None or dist < best[0]
                       or (dist == best[0] and freq[c] > freq[best[1]])):
                best = (dist, c)
        if best:
            rows.append((w, best[1], best[0], freq[w], freq[best[1]], sites[w]))
    rows.sort(key=lambda r: (-r[4], r[0]))
    say(f"{len(rows)} probable prose typos")
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--dirs", nargs="*", default=["Mathlib", "Archive", "Counterexamples"])
    ap.add_argument("--out", default=None, help="write a TSV report here")
    ap.add_argument("--min-freq", type=int, default=20,
                    help="a correction candidate must occur at least this often in the corpus")
    ap.add_argument("--max-rare", type=int, default=2,
                    help="only words occurring at most this often are considered typos")
    args = ap.parse_args()
    rows = scan(args.root, args.dirs, args.min_freq, args.max_rare, verbose=True)
    out = open(args.out, "w", encoding="utf-8") if args.out else sys.stdout
    for w, c, dist, fw, fc, ss in rows:
        loc = "; ".join(f"{a}:{b} ({k})" for a, b, k in ss)
        out.write(f"{w}\t{c}\t{dist}\t{fw}\t{fc}\t{loc}\n")
    if args.out:
        out.close()


if __name__ == "__main__":
    main()
