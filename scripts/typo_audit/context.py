#!/usr/bin/env python3
"""
Shared machinery for the typo audit's source modules.

A *source module* knows how to find English prose on one surface of the repository — Lean string
literals, repository markdown, the YAML data files, path components, and so on — and turns what it
finds into `Finding` records.  Every source module exposes one function::

    def collect(ctx: Context) -> list[Finding]

and nothing else.  All the shared judgement lives here, so that every surface is spell-checked
against the same yardstick: Mathlib's own comment corpus, the way `scripts/naming_audit/
prose_typos.py` does it.  A word is only ever reported when the corpus does not use it, a
dictionary does not know it, it is not an identifier, it is not a regular derivative of a common
word, and it is within one edit (two, if it is long) of a word the corpus uses often.

The corpus is built from comments under `Mathlib/`, `Archive/` and `Counterexamples/` only, never
from the surface being audited: a typo must not be able to vote itself into the dictionary.
"""
from __future__ import annotations

import collections
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "naming_audit"))
import prose_typos as pt  # noqa: E402

CORPUS_DIRS = ("Mathlib", "Archive", "Counterexamples")

WORD = re.compile(r"[A-Za-z]+(?:'[A-Za-z]+)*")


class Finding(dict):
    """One reported problem. `cat` is the category id the driver groups by."""

    def __init__(self, surface, cat, name, file, line, detail, conf="medium"):
        super().__init__(surface=surface, cat=cat, name=name, file=file, line=int(line),
                         detail=detail, conf=conf)


class Context:
    """The corpus, the dictionary and the suggestion engine, built once and shared."""

    def __init__(self, root: str, verbose: bool = False):
        self.root = os.path.abspath(root)
        self.verbose = verbose
        self.freq: collections.Counter = collections.Counter()
        self.hyphenated: set = set()
        self.idents: set = set()
        self._build_corpus()
        self.common = {w for w, c in self.freq.items() if c >= 20}
        self.dictionary = pt.load_dictionary()
        self._index = collections.defaultdict(set)
        for w in self.common:
            for d in pt.deletions(w, 2):
                self._index[d].add(w)
        self.say(f"corpus: {len(self.freq)} words ({len(self.common)} common), "
                 f"{len(self.idents)} code fragments, {len(self.dictionary)} dictionary words")

    def say(self, msg: str) -> None:
        if self.verbose:
            print(f"  {msg}", file=sys.stderr, flush=True)

    # ---- corpus ----------------------------------------------------------------------
    def _build_corpus(self):
        for d in CORPUS_DIRS:
            for dp, _dn, fn in os.walk(os.path.join(self.root, d)):
                for f in sorted(fn):
                    if not f.endswith(".lean"):
                        continue
                    with open(os.path.join(dp, f), encoding="utf-8") as fh:
                        src = fh.read()
                    comments, code = pt.extract_comments(src)
                    pt.code_fragments(code, self.idents)
                    for _line, kind, text in comments:
                        if kind == "block" and pt.LICENSE.search(text):
                            continue
                        # identifiers inside code spans are code, not prose
                        pt.code_fragments(
                            " ".join(s.strip("`") for s in pt.INLINE_CODE.findall(text)),
                            self.idents)
                        for w, hyph in pt.prose_words(text):
                            self.freq[w.lower()] += 1
                            if hyph:
                                self.hyphenated.add(w.lower())

    # ---- the judgement ---------------------------------------------------------------
    def suggest(self, word: str, local_idents: set = ()):
        """(correction, distance, uses) if `word` looks like a misspelling, else None.

        A word survives to become a suggestion only when Mathlib's comments never use it, no
        dictionary knows it, it is not an identifier, and it is not a regular derivative of a
        common word — and then only if some frequent corpus word is one edit away (two, for a
        long word with a very common correction)."""
        lw = word.lower()
        if len(lw) < 5 or not lw.isalpha():
            return None
        if self.freq.get(lw, 0):
            return None
        if lw in self.idents or lw in local_idents or lw in self.hyphenated:
            return None
        if lw in self.dictionary:
            return None
        if pt.morphological(lw, self.common):
            return None
        cands = set()
        for d in pt.deletions(lw, 2):
            cands |= self._index.get(d, set())
        best = None
        for cand in cands:
            if cand == lw:
                continue
            dist = pt.damerau(lw, cand)
            ok = (dist == 1 and len(lw) >= 5) or (dist == 2 and len(lw) >= 9
                                                  and self.freq[cand] >= 200)
            if ok and (best is None or dist < best[1]
                       or (dist == best[1] and self.freq[cand] > self.freq[best[0]])):
                best = (cand, dist)
        if best is None:
            return None
        return (best[0], best[1], self.freq[best[0]])

    def confidence(self, dist: int, uses: int) -> str:
        if dist == 1 and uses >= 500:
            return "high"
        if dist == 1 or uses >= 500:
            return "medium"
        return "low"

    def words(self, text: str):
        """(word, start offset) for each prose word of `text`."""
        for m in WORD.finditer(text):
            yield m.group(0), m.start()

    def rel(self, path: str) -> str:
        return os.path.relpath(path, self.root).replace(os.sep, "/")

    def walk(self, *dirs, ext=None):
        """Every file under `dirs` (relative to the root), optionally filtered by extension."""
        for d in dirs:
            base = os.path.join(self.root, d)
            if os.path.isfile(base):
                if ext is None or base.endswith(ext):
                    yield base
                continue
            for dp, dn, fn in os.walk(base):
                dn[:] = [x for x in dn if x not in (".git", ".lake", "build", "node_modules")]
                for f in sorted(fn):
                    if ext is None or f.endswith(ext):
                        yield os.path.join(dp, f)

    def read(self, path: str) -> str:
        try:
            with open(path, encoding="utf-8") as f:
                return f.read()
        except (UnicodeDecodeError, OSError):
            return ""


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def excerpt(text: str, at: int, width: int = 60) -> str:
    start = text.rfind("\n", 0, at) + 1
    end = text.find("\n", at)
    if end == -1:
        end = len(text)
    s = text[start:end].strip()
    return s[:width].rstrip() + "…" if len(s) > width else s
