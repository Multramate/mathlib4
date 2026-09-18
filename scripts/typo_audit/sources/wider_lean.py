#!/usr/bin/env python3
"""
Spell-check the Lean prose that lives *outside* the three audited libraries.

`scripts/naming_audit/prose_typos.py` only ever walks `Mathlib/`, `Archive/` and
`Counterexamples/`, and so does the corpus builder in `context.py`.  Everything else written in
Lean in this repository has therefore never been spell-checked once: `MathlibTest/` (412 files),
the `Cache/` (19) and `Wanted/` (18) libraries, `DownstreamTest/` (1), the Lean scripts under
`scripts/` (11), the `docs/Conv/` tutorial (2) and the root import files (6).  That is 469 files,
and once the compiler output below is taken out, 48,945 words of comments and docstrings — the
user-facing tutorial prose of `docs/Conv/`, the 14,180 words of commentary in `Cache/`, and the
explanations that tell the next maintainer what each regression test is guarding.

The surface needs its own extractor for one reason: `MathlibTest/` is not mostly prose.  It is
mostly *recorded compiler output*.

    /--
    info: Try this: simp only [foo]
    error: unknown identifier 'bar'
    -/
    #guard_msgs in
    example : True := by trivial

Those `#guard_msgs` expectation blocks are written as ordinary Lean docstrings, so a naive
extractor reads them as prose: they hold 33,728 of the 82,673 prose words on this surface — goal
states, metavariable names, pretty-printer output and deliberately misspelled test fixtures.  Left
in, they would drown the category.

Two signals identify an expectation block, and its lines are skipped if *either* holds:

* a `/-- … -/` whose closing delimiter is followed only by whitespace and then `#guard_msgs`.
  That is how the command is always written, with the docstring immediately above the
  `#guard_msgs … in` it belongs to.
* a `/-- … -/` whose body opens with `info:`, `error:`, `warning:` or `trace:`, the message
  severity the elaborator emits.  This catches the blocks where an attribute, a `set_option … in`
  or a second stacked expectation sits between the docstring and its `#guard_msgs` line.

Together they match 2,169 blocks.  Each signal alone finds around 2,150 of them, and the 33 blocks
that only one of the two catches were all read by hand: every one is genuine compiler output, so
neither signal is carrying the other.  In `MathlibTest/` the blocks cover 2,113 of the 2,374
docstrings `extract_comments` sees, and the 261 hand-written docstrings survive.

The match is recorded as a *line range* over the raw source rather than as a comment, because
`MathlibTest/` also contains commented-out test sections: `MathlibTest/Tactic/Check.lean:110-169`
is a `/- … -/` block with five whole expectation blocks nested inside it, which no per-comment
filter would ever see.  Working on raw text has one cost — in
`MathlibTest/DifferentialGeometry/Notation/Basic.lean` a `/--` quoted inside a recorded parse
error extends a block over two neighbouring `--` comments — but over-skipping costs recall, never
precision.

Apart from that the module is `prose_typos.scan` pointed at different directories:
`pt.extract_comments` for the comments, `pt.prose_words` to strip code spans, LaTeX and citations,
and `ctx.suggest` for the judgement, so this surface is held to the same standard as the rest of
the audit.  Identifiers harvested from the *code* of these same files are passed to `ctx.suggest`
as `local_idents`, because the test suite invents vocabulary the corpus has never seen (`fooz`,
`Bazzz`, `myUnexpander`) and those names leak into the surrounding comments.

Two morphology filters are added on top of `ctx.suggest`, because this surface talks about
*software* where Mathlib's comments talk about mathematics, and `pt.morphological` has a rule for
neither pattern:

* `_plural_of_identifier`: a regular plural whose singular is a name used in the code.  Comments
  here discuss code constantly, and `parens`, `mvars`, `fvars` are plurals of identifiers rather
  than English words.  Without it, `parens` in `MathlibTest/Algebra/Polynomial.lean:38` is
  reported as a misspelling of `parent`.
* `_verbal_derivation`: `X`+`-ize`/`-ise` and their inflections, a productive English suffix that
  `pt.morphological`'s SUFFIXES list omits.  Without it, `canonicalizes` in `Cache/Test.lean:143`
  is reported as a misspelling of `canonicalizer`.

Both were scored against an independent population before being adopted.  Re-running the shared
judgement over the 91 rare words it reports in Mathlib's *own* comments, the first filter removes
one row (`sumsets`) and the second removes nine (`coequalize`, `equaliser`, `localisations`,
`normaliser`, `parameterize`, `vectorization`, …).  All ten are legitimate words, so on that
population the pair costs no recall at all while removing ten false positives.

Deliberately left out:

* doubled words (`the the`).  It is the obvious structural check to add here, and it does not
  survive its own test: across the 48,945 words of this surface the only adjacent repetition
  outside the expectation blocks is `h h` in `MathlibTest/Tactic/Monotonicity.lean:140`, two Lean
  hypothesis names in an unbackticked tactic sketch.  One hit, and it is a false positive, so the
  category would be 100% noise.
* words shorter than five letters, which `ctx.suggest` will not judge.  This costs `at fist
  elaborated` in `MathlibTest/SetNotationForOrder.lean:101`, but `fist` is an ordinary English
  word that only context reveals as wrong, and no threshold that catches it stays precise.
* string literals in these trees.  They are `#guard` fixtures, tactic names and error text under
  test, not prose, and `lean_strings.py` is the surface for literals that are.
"""
from __future__ import annotations

import os
import re

import prose_typos as pt

from context import Finding, excerpt, line_of

SURFACE = "Lean prose outside Mathlib/Archive/Counterexamples"

CATEGORIES = {
    "W1": "Misspelling in a docstring or module docstring",
    "W2": "Misspelling in a line or block comment",
}

# The Lean trees the naming audit and the corpus builder never walk.  `scripts/` is walked
# recursively so that `scripts/SideSkimmer/lakefile.lean` is covered too.
DIRS = ("MathlibTest", "Cache", "Wanted", "DownstreamTest", "docs", "scripts")

# A `#guard_msgs` expected-output block, in the two shapes described above.  `(?:(?!-/).)*?` keeps
# each match inside one docstring, since expectation blocks never nest.
EXPECTATION = re.compile(
    r"/--(?:(?!-/).)*?-/\s*#guard_msgs"
    r"|/--\s*(?:info|error|warning|trace)\s*:(?:(?!-/).)*?-/",
    re.S | re.I)

# `-ize`/`-ise` and their inflections: English's productive verb-forming suffix, which
# `pt.morphological`'s SUFFIXES list does not have.
VERBAL = ("ize", "izes", "izing", "ized", "izer", "izers", "ization", "izations",
          "ise", "ises", "ising", "ised", "iser", "isers", "isation", "isations")


def _expectation_lines(src: str) -> set:
    """Line numbers covered by a `#guard_msgs` expected-output block."""
    lines = set()
    for m in EXPECTATION.finditer(src):
        lines.update(range(line_of(src, m.start()), line_of(src, m.end()) + 1))
    return lines


def _plural_of_identifier(word: str, idents: set) -> bool:
    """`parens`, `mvars`: a regular plural of a name used in the code is code, not a misspelling."""
    for suffix in ("s", "es"):
        stem = word[: len(word) - len(suffix)]
        if word.endswith(suffix) and len(stem) > 3 and stem in idents:
            return True
    return False


def _verbal_derivation(word: str, known: set) -> bool:
    """`canonicalizes`, `vectorization`: `-ize`/`-ise` built on a word that is already known."""
    for suffix in VERBAL:
        stem = word[: len(word) - len(suffix)]
        if word.endswith(suffix) and len(stem) > 2:
            if stem in known or stem + "e" in known or stem + "y" in known:
                return True
    return False


def _lean_files(ctx):
    """Every Lean file of the surface: the unaudited trees, then the root import files."""
    yield from ctx.walk(*DIRS, ext=".lean")
    for name in sorted(os.listdir(ctx.root)):
        if name.endswith(".lean") and os.path.isfile(os.path.join(ctx.root, name)):
            yield os.path.join(ctx.root, name)


def _offset(text: str, word: str) -> int:
    """Where `word` first stands in `text`, as a whole word; 0 if it cannot be located.

    Each word is reported once per comment, so the first occurrence is the one being located; the
    search is over the raw comment because `pt.prose_words` reads a cleaned copy whose offsets no
    longer line up with it.
    """
    m = re.search(rf"\b{re.escape(word)}\b", text)
    return m.start() if m else 0


def collect(ctx):
    # Two passes.  The test suite's invented identifiers have to be known before any comment in
    # any file is judged, because a name defined in one test file is discussed in another's prose.
    parsed = []
    idents: set = set()
    for path in _lean_files(ctx):
        src = ctx.read(path)
        if not src:
            continue
        comments, code = pt.extract_comments(src)
        pt.code_fragments(code, idents)
        parsed.append((path, src, comments))
    for _path, _src, comments in parsed:
        for _start, _kind, text in comments:
            # a name inside a code span is code, and must not be read as misspelled prose
            pt.code_fragments(
                " ".join(s.strip("`") for s in pt.INLINE_CODE.findall(text)), idents)
    idents |= ctx.idents
    known = ctx.common | ctx.dictionary
    ctx.say(f"{len(parsed)} Lean files outside the audited trees, {len(idents)} known names")

    findings = []
    for path, src, comments in parsed:
        rel = ctx.rel(path)
        expected = _expectation_lines(src)
        for start, kind, text in comments:
            if kind == "block" and pt.LICENSE.search(text):
                continue  # the copyright header: `Authors:` is a name list, not prose
            cat = "W1" if kind in ("doc", "mod") else "W2"
            seen = set()
            for word, hyphenated in pt.prose_words(text):
                if hyphenated or word.lower() in seen:
                    continue  # a compound member, or a repeat already reported for this comment
                seen.add(word.lower())
                at = _offset(text, word)
                line = start + line_of(text, at) - 1
                if line in expected:
                    continue  # recorded compiler output, not prose
                if _plural_of_identifier(word.lower(), idents):
                    continue
                if _verbal_derivation(word.lower(), known):
                    continue
                hit = ctx.suggest(word, idents)
                if not hit:
                    continue
                correction, dist, uses = hit
                findings.append(Finding(
                    SURFACE, cat, word.lower(), rel, line,
                    f"{word!r} -> {correction!r} (distance {dist}; Mathlib's comments use "
                    f"{correction!r} {uses} times and {word!r} never)  in: {excerpt(text, at)}",
                    ctx.confidence(dist, uses)))

    findings.sort(key=lambda f: (f["cat"], f["file"], f["line"]))
    return findings
