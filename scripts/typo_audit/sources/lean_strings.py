#!/usr/bin/env python3
"""
The English inside Lean *string literals*: the text a user of Mathlib actually reads.

Every other spell-checker in this repository reads comments.  `prose_typos.extract_comments`
deliberately throws string bodies away — it treats them as neither prose nor code — so the
messages Lean prints have never been checked by anything:

  * `throwError` / `logInfo` / `logWarning` text, and the `m!"…"` and `s!"…"` interpolations
    that build it;
  * the explanation in `@[deprecated "…"]`, which is the one sentence a downstream user sees
    when their proof breaks;
  * `register_option … descr` and the linter descriptions printed by `#help option`;
  * `lake exe cache` help text and its security notices, under `Cache/`.

This surface needs its own extractor because a string literal is not a comment: its body is full
of `{…}` antiquotations, `\\n` escapes and `\\`-newline gaps, all of which have to come out before
the remaining words are English, and because it lives everywhere — not just under `Mathlib/`, but
in `Cache/`, `MathlibTest/`, `Wanted/`, `DownstreamTest/`, `scripts/`, `docs/` and the root
`.lean` files.

The judgement is `ctx.suggest`, unchanged, so a word here is held to exactly the same standard as
a word in a comment.  Three things are layered on top of it, none of which it covers:

  * **Prose detection at a message site.**  `pt.string_prose` asks for five lowercase words before
    it calls a literal prose, which is right for a literal in general — most of Mathlib's 16k
    literals are syntax node kinds, option names and test fixtures.  But a literal that is the
    argument of `throwError` or the `descr` of a `register_option` is a human-readable message by
    construction, and a four-word one such as `throwError "not subtration on ordinals"` is plainly
    English.  For those positions only, three words are enough.
  * **A word the comments get wrong too.**  `ctx.suggest` refuses any word the corpus uses at all,
    because the corpus is the dictionary.  That is the right rule when a typo can only occur on
    the surface being audited, but `auxilliary` and `superceded` each appear once in a genuine
    Mathlib comment *and* once in the deprecation message at
    `Mathlib/GroupTheory/SpecificGroups/Alternating.lean:323`, and the comment occurrence hides the
    string one.  A word the corpus uses at most `CORPUS_RARE` times is not evidence of English —
    that is exactly the `--max-rare` threshold with which `prose_typos.scan` *nominates* typos —
    so such a word is put back through `ctx.suggest` with its own corpus count hidden, and
    reported separately as S2 so a reviewer can weigh it on its own.
  * **Doubled words**, which are invisible to any per-word check.  Kept precise by requiring the
    repetition to be exact including case, at least three letters, and a word the corpus or the
    dictionary knows — so `"subset notation notation"` is caught while `"h h"` and a repeated
    identifier in a test fixture are not.  The repetition must also be *really* adjacent: what
    `_mask` cuts out keeps the words on either side of it apart, or ``"removes `Cache` and
    `MathlibTest` and it adds"`` reads as a doubled `and`.

Deliberately left out:

  * Literals that fail the prose test are not examined at all, even for obvious-looking words.
    Mathlib's non-prose literals are syntax node kinds, `simp` lemma names, file paths and
    expected-output fixtures, and a spell-checker turned loose on them reports only identifiers.
    That is also why `Mathlib/Tactic/Linter/TextBased.lean`'s deliberately-split `"daptation
    note"` needs no special case: it is two words, in no message position, so it is never read.
  * Literals that open a Lean block comment, which are source quoted as test data rather than
    anything Mathlib says.
  * Any attempt to check the *content* of an interpolation or a code span.  `{e}` and `` `foo` ``
    hold expressions and identifiers; the naming audit owns those.
"""
from __future__ import annotations

import os
import re

import prose_typos as pt
from context import Finding, excerpt, line_of

SURFACE = "Lean string literals"

CATEGORIES = {
    "S1": "Misspelled word in a message string",
    "S2": "Misspelling the comments make too, repeated in a string",
    "S3": "Doubled word in a message string",
}

# Everything that holds Lean source. `Cache/` and `scripts/` are where the command-line help text
# and the `lake exe cache` security notices live; the root `.lean` files are added in `collect`.
DIRS = ("Mathlib", "Archive", "Counterexamples", "Cache", "MathlibTest", "Wanted",
        "DownstreamTest", "scripts", "docs")

# A literal on a line mentioning one of these is a message meant for a human to read. `panic`,
# `assert` and `unreachable` are written with a trailing `!`, which is not a word character, so
# `\b` already keeps `assert_not_exists` out.
MESSAGE_SITE = re.compile(
    r'\b(?:throwError|throwErrorAt|logError|logWarning|logInfo|logInfoAt|logWarningAt'
    r'|panic|unreachable|assert|println|descr)\b'
    r'|[ms]!"'                 # `m!"…"` / `s!"…"` message interpolation
    r'|@\[deprecated'          # `@[deprecated "…" (since := …)]`
)

# `string_prose`'s own test for "a lowercase English word", applied at a lower bar where the
# position has already established that the literal is prose.
LOWER_WORD = re.compile(r"\b[a-z]{2,}\b")
MESSAGE_SITE_WORDS = 3

# An exact repetition of a word of three letters or more, across whitespace or a line break.
DOUBLED = re.compile(r"\b([A-Za-z]{3,})\s+\1\b")

# An identifier that leaked out of a code span: `isSimpleGroup`, `ERR_ADN`.
CAMEL = re.compile(r"[a-z][A-Z]")

# Mathlib's comments use a word at most this often: `prose_typos.scan`'s `--max-rare`, the count
# below which the naming audit treats an occurrence as a candidate typo rather than as evidence.
CORPUS_RARE = 2


def _blank(s: str) -> str:
    """`s` with every character replaced by `prose_typos`' cut marker, except newlines.

    The marker rather than a space, because a cut is not whitespace: blanking the code span in
    ``"removes `Cache` and `MathlibTest` and it adds"`` with spaces leaves two adjacent `and`s
    that were never adjacent.  Newlines stay so that line numbers survive.
    """
    return "".join("\n" if c == "\n" else pt.CUT for c in s)


def _mask(body: str) -> str:
    """The literal's body with everything that is not English cut out, character for character.

    Cutting in place instead of deleting keeps every offset and every newline where it was, so
    that `line_of` and `excerpt` still point at the right place inside a literal that spans
    lines — which deprecation messages and `Cache/`'s help text routinely do.
    """
    for rx in (pt.STRING_GAP, pt.ANTIQUOT, pt.ESCAPE, pt.INLINE_CODE, pt.URL):
        body = rx.sub(lambda m: _blank(m.group(0)), body)
    return body


def _ascii(s: str) -> str:
    """`s` with non-ASCII escaped. Lean messages are full of `⊆`, `←` and `≠`, and the driver
    prints findings to whatever encoding the console happens to have."""
    return s.encode("ascii", "backslashreplace").decode("ascii")


def _suggest_rare(ctx, word: str, local: set):
    """`ctx.suggest`, but for a word the corpus itself uses a handful of times.

    `suggest` returns `None` for anything with a corpus count, so the count is hidden for the
    duration of the call and put straight back.  Nothing else depends on it: `ctx.common` and the
    deletion index were built once, and a word this rare was never in either.
    """
    count = ctx.freq.pop(word, 0)
    try:
        return ctx.suggest(word, local)
    finally:
        ctx.freq[word] = count


def _literal_prose(body: str, message_site: bool) -> str:
    """The masked body if the literal reads like prose, else ''."""
    # A literal that opens a Lean block comment is a *fixture*: a file header quoted as input to
    # a linter test, not something Mathlib says to anyone.  `MathlibTest/Linter/Header/Basic.lean`
    # feeds the header linter 27 of them, several corrupted on purpose, and they otherwise supply
    # seventeen findings nobody should ever act on.
    if body.lstrip().startswith("/-"):
        return ""
    masked = _mask(body)
    if pt.string_prose(body):
        return masked
    if message_site and len(LOWER_WORD.findall(masked)) >= MESSAGE_SITE_WORDS:
        return masked
    return ""


def collect(ctx):
    findings = []
    roots = list(DIRS) + sorted(f for f in os.listdir(ctx.root) if f.endswith(".lean"))
    for path in ctx.walk(*roots, ext=".lean"):
        src = ctx.read(path)
        if '"' not in src:
            continue
        rel = ctx.rel(path)
        lines = src.split("\n")
        # the file's own identifiers, so that a message naming a local tactic or option is not
        # read as a misspelling of an English word
        local: set = set()
        pt.code_fragments(pt.extract_comments(src)[1], local)

        for start, body in pt.extract_strings(src):
            head = lines[start - 1] if start <= len(lines) else ""
            prose = _literal_prose(body, bool(MESSAGE_SITE.search(head)))
            if not prose:
                continue

            for word, off in ctx.words(prose):
                lw = word.lower()
                if (word.isupper() and len(word) > 1) or CAMEL.search(word):
                    continue
                # a word glued to a cut is a fragment of what was cut, not a word: ``ependent``
                # is what ``a `d`ependent sum`` leaves behind.  `prose_words` drops these too.
                end = off + len(word)
                if (off and prose[off - 1] == pt.CUT) or prose[end:end + 1] == pt.CUT:
                    continue
                hit = ctx.suggest(word, local)
                cat = "S1"
                if hit is None and 0 < ctx.freq.get(lw, 0) <= CORPUS_RARE:
                    hit = _suggest_rare(ctx, lw, local)
                    cat = "S2"
                if hit is None:
                    continue
                corr, dist, uses = hit
                seen = (f'; a comment misspells it the same way {ctx.freq[lw]}x'
                        if cat == "S2" else "")
                # `_mask` preserves offsets, so the excerpt can quote the literal as written
                findings.append(Finding(
                    SURFACE, cat, lw, rel, start + line_of(body, off) - 1,
                    f'"{_ascii(excerpt(body, off))}": "{word}" -> "{corr}" '
                    f'({dist} edit{"s" if dist > 1 else ""}, "{corr}" used {uses}x '
                    f'in comments{seen})',
                    ctx.confidence(dist, uses)))

            for m in DOUBLED.finditer(prose):
                w = m.group(1)
                # a repeated token is only a doubled *word* if it is one; a repeated identifier in
                # a test fixture is not
                if w.lower() not in ctx.freq and w.lower() not in ctx.dictionary:
                    continue
                findings.append(Finding(
                    SURFACE, "S3", w.lower(), rel, start + line_of(body, m.start()) - 1,
                    f'"{_ascii(excerpt(body, m.start()))}": "{w}" is written twice in a row',
                    "high"))
    return findings
