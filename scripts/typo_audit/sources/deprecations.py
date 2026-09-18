#!/usr/bin/env python3
"""
Deprecation metadata: the `@[deprecated …]` attribute and the `deprecated_module` command.

This is the one piece of English in Mathlib that neither existing audit looks at.  The naming
audit refuses to consider a declaration that carries a deprecation (its `is_deprecated`), and the
comment audit only ever reads comments — a deprecation's message is a *string literal*, which
`extract_comments` deliberately drops from the code it returns.  So every word of every
deprecation message has gone unread: `auxilliary` and `superceded` sit in one message in
`Mathlib/GroupTheory/SpecificGroups/Alternating.lean` and have never been reported by anything.

The message matters more than an ordinary comment does.  It is not documentation a reader may
skip: Lean prints it verbatim at the use site of the deprecated declaration, so a misspelling
there is shown to every user of the old name until the alias is deleted.  The same goes for the
`(since := …)` stamp, which the deprecation tooling parses as a date, and for the declaration the
message tells the reader to use instead, which nothing checks because it is inside a string.

Five checks, all anchored on the attribute itself rather than on the enclosing declaration:

X1  a misspelled word in the message, judged by `ctx.suggest` like every other surface;
X2  a contraction written without its apostrophe (`dont` for "don't");
X3  a `since` that is missing, or that is not a real `YYYY-MM-DD` date;
X4  a name the message points the reader at that occurs nowhere in Mathlib's Lean code;
X5  an odd number of backticks — a code span in the message that is never closed.

Four decisions worth spelling out.

`pt.string_prose` is *not* used to decide whether a message is prose.  It requires five lowercase
words, and a deprecation message is typically three or four ("use `norm_coe`", "no replacement"),
so it would throw away most of the surface.  It is not needed either: a deprecation message is
prose by construction — Lean has exactly one place to put one — so the words are read directly,
through `pt.prose_words`, which still strips the backticked identifiers that fill these messages.

X1 calls `ctx.suggest` unchanged, but when the corpus turns out to use the word once or twice it
calls it a second time with that count set aside; `_suggest_rare` explains why, and why the
cut-off is `prose_typos`' own `max_rare` rather than a number invented here.  Without it the
surface reports nothing at all: `auxilliary` and `superceded`, the two misspellings this surface
exists to find, are each written once in a docstring elsewhere in Mathlib, which is enough for
`ctx.suggest` to clear them.

X2, X4 and X5 are checks `ctx.suggest` cannot make.  `ctx.suggest` ignores any word shorter than
five letters, so `dont` is invisible to it; X2 covers a short, closed list of contractions whose
apostrophe-less spelling is never a word Mathlib would mean.  X4 exists because `ctx.suggest` is
structurally blind to a misspelled *name*: every name a message mentions is harvested into
`ctx.idents` from the very code it appears in, so `suggest` sees them all as legitimate
identifiers.  Nor does edit distance help — `TensorProduction` is three edits from
`TensorProduct`.  What separates them is that `TensorProduction` is written exactly once in the
whole repository, inside that message, and never as code.  X4 therefore asks the only question
that discriminates: is this name written in Lean code anywhere?  X5 is purely structural.

X4 is kept precise by two restrictions, both of which cost recall.  Only a span that is a single
dotted name is looked up, so "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead"
is passed over — the span is a term, and nothing in the string says where the name ends.  And a
name `@[simps]` would have generated is skipped, because such a name is real but is written
nowhere (see `GENERATED_SUFFIXES`); without that rule the three `_apply` lemmas of
`Mathlib/Algebra/Star/Module.lean` and `Mathlib/Topology/Algebra/Module/Star.lean` were reported
and all three were wrong.

Deliberately left out: comparing a deprecated alias's own name against its target.  A deprecated
alias is a rename, so the old and new names differ by construction, and nothing in the pair says
whether the difference is a typo or the rename itself.  Every rule tried here (small edit
distance, one changed camelCase component) matched far more real renames than mistakes, and a
check that is mostly wrong is worse than no check.  Also left out: a `since` missing from a
deprecation that carries no message.  Every one of those in the tree belongs to a metaprogram
that builds or matches the attribute rather than uses it, and telling the two apart from the
source text alone was not possible without a rule that named the tactic directories.
"""
from __future__ import annotations

import datetime
import re

import prose_typos as pt
from context import Finding, line_of

SURFACE = "deprecation metadata"

CATEGORIES = {
    "X1": "Misspelled word in a deprecation message",
    "X2": "Contraction written without its apostrophe",
    "X3": "`since` missing, or not a real YYYY-MM-DD date",
    "X4": "Deprecation points at a name that occurs in no Lean code",
    "X5": "Code span in a deprecation message is never closed",
}

DIRS = ("Mathlib", "Archive", "Counterexamples")

# `deprecated` and `deprecated_module` as whole tokens.  The lookbehind excludes the dotted uses,
# which are not deprecations at all: `set_option linter.deprecated`, and the name literal
# ``Parser.Command.deprecated_module`` in the header linter.
TOKEN = re.compile(r"(?<![A-Za-z0-9_.'])deprecated(_module)?(?![A-Za-z0-9_.'])")
SINCE = re.compile(r"\(\s*since\s*:=\s*\"([^\"]*)\"\s*\)")
# The attribute form is only ever written inside an attribute list, so the keyword follows `[`
# (`@[deprecated …`, `attribute [deprecated …`), `,` (a second attribute in the list) or `:=`
# (`@[to_additive (attr := deprecated …)]`).  Requiring one of those drops the word "deprecated"
# where it is just a word — in a `section deprecated`, or inside an unrelated error message.
ATTR_LEAD = "[,="
# No deprecation in the tree is anywhere near this long; a span that does not terminate inside it
# is something this scanner has misread, and is dropped rather than guessed at.
SPAN_CAP = 1000

# A Lean name: one identifier, or several joined by dots.  Anything carrying a character outside
# this set (`⨆`, `≤`, a subscript, a space) is notation or a term, not a name to look up.
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
# A leading `←` marks a rewrite direction, not part of the name: "Use `← ofClass_eq_…`".
ARROW = re.compile(r"^[←\s]+")

# Contractions whose apostrophe-less form is not an English word Mathlib could mean.  Deliberately
# short: `wont`, `its`, `lets`, `thats` and `were` are all real words and are not on it.
CONTRACTIONS = {
    "dont": "don't", "doesnt": "doesn't", "didnt": "didn't", "isnt": "isn't",
    "arent": "aren't", "wasnt": "wasn't", "werent": "weren't", "hasnt": "hasn't",
    "havent": "haven't", "hadnt": "hadn't", "cant": "can't", "couldnt": "couldn't",
    "wouldnt": "wouldn't", "shouldnt": "shouldn't", "mustnt": "mustn't", "neednt": "needn't",
    "youre": "you're", "theyre": "they're", "weve": "we've", "youve": "you've",
    "theyve": "they've", "couldve": "could've", "wouldve": "would've", "shouldve": "should've",
}

# A component shorter than this is a namespace stub (`E`, `id`, `mk`) whose absence from the code
# says nothing; only longer components are worth asking about.
MIN_NAME_PART = 5

# `@[simps]` and friends declare lemmas that are never written down: `@[simps! apply] def starL`
# puts `starL_apply` in the environment without the string `starL_apply` appearing anywhere in the
# tree, so X4's "written in no Lean code" test would accuse a message that cites it.  A name ending
# in one of these, on a stem the code does write, is taken to be one of those and is passed over.
# The list is short on purpose: it can only ever hide a finding, never invent one.
GENERATED_SUFFIXES = ("apply", "coe", "symm_apply", "toFun", "invFun", "hom", "inv", "obj", "map")

# `prose_typos.scan`'s own `max_rare`: a word Mathlib's comments use at most this often is still a
# candidate misspelling there.  See `_suggest_rare`.
MAX_RARE = 2


def _comment_lines(src: str) -> set:
    """The line numbers covered by a comment.

    `@[deprecated …]` is quoted inside the docstrings that explain the convention —
    `Mathlib/Tactic/DeprecateTo.lean` prints `(since := "YYYY-MM-DD")` as an example, and
    `Mathlib/Tactic/Linter/FindDeprecations.lean` discusses `@[deprecated]` in a `--` comment.
    Those are not deprecations and must not be read as such.

    The mask is per line rather than per character because `extract_comments` reports the line a
    comment starts on, not its offset.  That would hide a real deprecation sharing a line with a
    trailing `--` comment; no deprecation in the tree does.
    """
    lines = set()
    for line, _kind, text in pt.extract_comments(src)[0]:
        lines.update(range(line, line + text.count("\n") + 1))
    return lines


def _span(src: str, start: int, module: bool):
    """The source of one deprecation, from just after the keyword to its end.

    Returns `(end, [(offset, body)])` listing the string literals inside it, or None if no
    terminator is found.  Attributes are read to the `]` that closes the enclosing attribute list,
    which is the first bracket to close without having been opened inside the span; messages often
    wrap onto the following line, so a newline cannot end one.  `deprecated_module` has no
    brackets of its own, so it ends with its `(since := …)` group, or at a blank line if it has
    none.
    """
    i, n = start, min(len(src), start + SPAN_CAP)
    depth = 0
    strings = []
    while i < n:
        c = src[i]
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            strings.append((i + 1, src[i + 1:j]))
            i = j + 1
            continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
            if depth < 0 or (module and depth == 0):
                return i + 1, strings
        elif c == "\n" and module and depth == 0 and src.startswith("\n", i + 1):
            return i, strings
        i += 1
    return None


def _deprecations(src: str):
    """Yield `(keyword_offset, since_match, message, message_offset)` for each deprecation.

    `message` is the first string literal in the attribute that is not the `since` value — Lean's
    syntax allows at most one, and it always precedes the `since` group — or None when there is
    none.
    """
    masked = _comment_lines(src)
    consumed = 0
    for m in TOKEN.finditer(src):
        # A `deprecated` inside a span already parsed is part of that deprecation's own message
        # (several messages read "`foo` is deprecated"), not a second attribute.
        if m.start() < consumed:
            continue
        line = line_of(src, m.start())
        if line in masked:
            continue
        module = m.group(1) is not None
        if not module:
            k = m.start() - 1
            while k >= 0 and src[k] in " \t\n":
                k -= 1
            if k < 0 or src[k] not in ATTR_LEAD:
                continue
        span = _span(src, m.end(), module)
        if span is None:
            continue
        end, strings = span
        consumed = end
        body = src[m.start():end]
        since = SINCE.search(body)
        # Offsets of the `since` value, so it is not mistaken for the message.
        skip = (m.start() + since.start(1), m.start() + since.end(1)) if since else (-1, -1)
        for off, text in strings:
            if skip[0] <= off < skip[1]:
                continue
            yield m.start(), since, text, off
            break
        else:
            yield m.start(), since, None, None


def _prose(message: str) -> str:
    """The readable text of a message: escapes, line continuations and holes removed."""
    t = pt.STRING_GAP.sub(" ", message)
    t = pt.ANTIQUOT.sub(" ", t)
    return pt.ESCAPE.sub(" ", t)


def _at_line(src: str, at: int, message: str, needle: str) -> int:
    """The line of the message on which `needle` sits.

    `prose_words` returns words without offsets, and a message may wrap over two lines — the one
    holding `superceded` in `Alternating.lean` does — so the word is located back in the raw
    literal.  A word flagged as a typo occurs once in a message of a handful of words.
    """
    m = re.search(r"(?<![A-Za-z0-9_'])" + re.escape(needle) + r"(?![A-Za-z0-9_'])", message)
    return line_of(src, at + (m.start() if m else 0))


def _names(message: str):
    """Yield every Lean name the message points the reader at.

    Two forms: a backticked span holding one name, which is how a message normally cites a
    declaration, and a bare dotted name ("Use Derivation.map_add").  A bare *undotted* word is not
    taken as a name — in "use balancedCore directly" it is, but in "no replacement" it is not, and
    nothing in the string tells them apart.
    """
    for m in pt.INLINE_CODE.finditer(message):
        text = ARROW.sub("", m.group(0).strip("`")).strip()
        if NAME.fullmatch(text):
            yield text
    for m in NAME.finditer(pt.INLINE_CODE.sub(" ", message)):
        if "." in m.group(0):
            yield m.group(0)


def _suggest_rare(ctx, word: str):
    """`ctx.suggest`, asked again about a word the comment corpus itself uses once or twice.

    `ctx.suggest` clears any word the corpus uses at all, which is right for a surface whose words
    are *in* the corpus.  A deprecation message is not: `extract_comments` drops string literals,
    so nothing in a message ever reached the corpus.  When the corpus turns out to contain the
    word once or twice anyway, those are separate occurrences of the same slip, not evidence that
    Mathlib means it — `auxilliary` and `superceded` each sit in one docstring and in this one
    deprecation message, which is exactly why neither has ever been reported here.

    So the judgement stays `ctx.suggest`, unchanged and called directly; only the corpus count
    that vetoes it is set aside for the length of the call, and the cut-off for doing so is
    `prose_typos.scan`'s own `max_rare`, the threshold the naming audit already uses to decide a
    word is rare enough to be a mistake.
    """
    lower = word.lower()
    count = ctx.freq.pop(lower, 0)
    try:
        return ctx.suggest(word)
    finally:
        if count:
            ctx.freq[lower] = count


def _generated(ctx, name: str) -> bool:
    """True if `name` looks like a lemma `@[simps]` produced rather than one anybody wrote."""
    for suffix in GENERATED_SUFFIXES:
        if not name.endswith("_" + suffix):
            continue
        stem = name[:-len(suffix) - 1]
        if stem and stem.lower() in ctx.idents:
            return True
    return False


def _by_length(ctx) -> dict:
    """`ctx.idents` bucketed by length, so a near-miss search need only look at plausible ones."""
    buckets: dict = {}
    for ident in ctx.idents:
        if len(ident) >= MIN_NAME_PART:
            buckets.setdefault(len(ident), []).append(ident)
    return buckets


def _nearest(buckets: dict, part: str):
    """The closest identifier fragment Mathlib's code does use, or None.

    Three edits, not the one or two `ctx.suggest` allows: a wrong name is not a slip of the
    fingers but a wrong word, and `TensorProduction` is three edits from `TensorProduct`.  Only
    used to make the finding readable — a name is reported because it is absent, not because
    something resembles it.
    """
    best = None
    for length in range(len(part) - 3, len(part) + 4):
        for cand in buckets.get(length, ()):
            dist = pt.damerau(part, cand, cap=3)
            if dist <= 3 and (best is None or dist < best[1]):
                best = (cand, dist)
    return best


def collect(ctx):
    findings = []
    buckets = _by_length(ctx)
    for path in ctx.walk(*DIRS, ext=".lean"):
        src = ctx.read(path)
        if "deprecated" not in src:
            continue
        rel = ctx.rel(path)
        for at, since, message, message_at in _deprecations(src):
            if not message:
                # Everything below reads the message, and so does X3: a deprecation with no
                # message and no `since` is, in this tree, never a real one — it is the
                # `@[deprecated]` of a metaprogram that builds the attribute
                # (`Mathlib/Tactic/Translate/Core.lean` matches on `deprecated%$tk $name …`) or a
                # quotation of one.  Reporting a missing `since` only where a message is present
                # keeps those out without a special case for the tactic directories.
                continue
            prose = _prose(message)
            quoted = " ".join(message.split())[:100]

            # ---- X3: the `since` stamp -------------------------------------------------
            if since is None:
                findings.append(Finding(
                    SURFACE, "X3", "since", rel, line_of(src, message_at),
                    f"the deprecation carrying \"{quoted}\" has no "
                    f"`(since := \"YYYY-MM-DD\")`; every dated deprecation in the tree stamps one",
                    "high"))
            else:
                value = since.group(1)
                try:
                    datetime.date.fromisoformat(value)
                    dated = len(value) == 10
                except ValueError:
                    dated = False
                if not dated:
                    findings.append(Finding(
                        SURFACE, "X3", value, rel, line_of(src, at + since.start(1)),
                        f"`since := \"{value}\"` is not a YYYY-MM-DD date; the rest of the tree "
                        f"writes e.g. \"2026-04-28\"", "high"))

            # ---- X5: an unclosed code span ---------------------------------------------
            if message.count("`") % 2:
                dangling = " ".join(message.rsplit("`", 1)[1].split())[:40]
                findings.append(Finding(
                    SURFACE, "X5", dangling, rel, line_of(src, message_at),
                    f"message \"{quoted}\" has an odd number of backticks: the span opened before "
                    f"\"{dangling}\" is never closed, and Lean prints the stray backtick to the "
                    f"user", "high"))

            for word, _hyphenated in pt.prose_words(prose):
                lower = word.lower()

                # ---- X2: a contraction missing its apostrophe --------------------------
                if lower in CONTRACTIONS:
                    findings.append(Finding(
                        SURFACE, "X2", word, rel,
                        _at_line(src, message_at, message, word),
                        f"message \"{quoted}\" writes \"{word}\" for "
                        f"\"{CONTRACTIONS[lower]}\"", "high"))
                    continue

                # ---- X1: an ordinary misspelling ---------------------------------------
                uses_here = ctx.freq.get(lower, 0)
                hit = (ctx.suggest(word) if uses_here == 0
                       else _suggest_rare(ctx, word) if uses_here <= MAX_RARE else None)
                if hit:
                    correction, dist, uses = hit
                    also = (f"Mathlib's comments write it {uses_here} other time(s)" if uses_here
                            else "Mathlib's comments never use it")
                    findings.append(Finding(
                        SURFACE, "X1", word, rel,
                        _at_line(src, message_at, message, word),
                        f"message \"{quoted}\" writes \"{word}\"; {also} and write "
                        f"\"{correction}\" {uses} times (distance {dist})",
                        ctx.confidence(dist, uses)))

            # ---- X4: a name that is written nowhere in the code ------------------------
            reported = set()      # a message may cite the same namespace in two names
            for name in _names(prose):
                for part in name.split("."):
                    if (len(part) < MIN_NAME_PART or part in reported
                            or part.lower() in ctx.idents or _generated(ctx, part)):
                        continue
                    reported.add(part)
                    near = _nearest(buckets, part.lower())
                    detail = (f"message \"{quoted}\" sends the reader to `{name}`, but "
                              f"`{part}` is written in no Lean code in the tree")
                    if near:
                        detail += f"; the closest name the code does use is `{near[0]}`"
                    findings.append(Finding(
                        SURFACE, "X4", part, rel,
                        _at_line(src, message_at, message, part), detail,
                        "high" if near else "medium"))
    findings.sort(key=lambda f: (f["file"], f["line"], f["cat"]))
    return findings
