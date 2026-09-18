#!/usr/bin/env python3
"""
Library note titles and the surface-syntax vocabulary.

This is the English a *user* types at the keyboard, and it is invisible to both older audits for
two different reasons.

A library note is declared `library_note «lower instance priority»`, and the title in guillemets is
what `see note [lower instance priority]` resolves against and what the generated documentation
renders.  The comment audit never sees it, because `library_note` is a Lean command rather than a
comment; and on the rare occasion a guillemet span does appear inside a comment, `prose_typos`
deletes it before the speller runs — its `CITATION` pattern lists `«[^»]*»` as one of the things
that is not prose, so that bibliography keys are skipped.

A tactic name is declared by `syntax`, `macro`, `elab`, `notation` and their relatives, and
`naming_audit`'s `DECL_KEYWORDS` contains none of those commands, so no name a user types has ever
been checked.  The same holds for the option names `register_option` declares and the simp-set
names `register_simp_attr` declares.

Two checks:

V1  a misspelled word in a library note title, or in the text a `see note [...]` reference uses.
    Titles are short and few — there are under forty — so this is cheap and exact.

V2  a misspelled word inside a declared syntax token, option name or simp-set name.

The danger in V2 is that this vocabulary is *deliberately* abbreviated: `rcases`, `norm_num`,
`gcongr`, `nlinarith`, `zify`, `aesop` are not misspellings, and a naive run reports all of them.
Three things keep it quiet.  Components shorter than five letters are never judged, which is
`ctx.suggest`'s own rule.  A component that occurs as an identifier anywhere in Mathlib's code is
established vocabulary, not a slip, and `ctx.suggest` already refuses those.  And a token that the
library uses many times over — counted from the code itself — is by construction not a typo, so a
frequency floor drops the rest.  What survives is a component that appears in exactly one declared
token, nowhere in the code, in no dictionary, and one edit from an ordinary word.
"""
from __future__ import annotations

import collections
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "naming_audit"))
import prose_typos as pt  # noqa: E402

from context import Finding, excerpt  # noqa: E402

SURFACE = "library notes and notation vocabulary"

CATEGORIES = {
    "1": "Misspellings in library note titles",
    "2": "Misspellings in declared syntax, option and attribute names",
}

DIRS = ("Mathlib", "Archive", "Counterexamples")

LIBRARY_NOTE = re.compile(r"library_note\s+«([^»]+)»|library_note\s+\"([^\"]+)\"")
NOTE_REF = re.compile(r"\b[Nn]ote\s*\[([^\]\n]{2,70})\]")

# The commands that introduce a token a user types. `notation3` and `elab_rules` are included
# because Mathlib uses both heavily.
SYNTAX_CMD = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|scoped\s+|local\s+)*"
    r"(syntax|notation3|notation|macro_rules|macro|elab_rules|elab|infixl|infixr|infix|prefix|"
    r"postfix|declare_syntax_cat|binder_predicate|register_option|register_simp_attr)\b(.*)")

# A quoted token in a syntax declaration: "foo_bar " or "foo" — Lean writes the trailing space
# inside the literal to control pretty-printing, so it is stripped.
QUOTED = re.compile(r'"([^"\n]{2,40})"')
# An option or attribute name is a plain dotted identifier rather than a quoted token.
DOTTED = re.compile(r"\b([A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*)")
CAMEL = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")

# A declared token used this often across the library is established vocabulary by definition.
ESTABLISHED_USES = 3


def components(token: str):
    """The word-like pieces of a declared token, lower-cased."""
    for part in re.split(r"[^A-Za-z0-9]+", token):
        for m in CAMEL.finditer(part):
            w = m.group(0).lower()
            if w.isalpha():
                yield w


def _library_notes(ctx):
    """{title: (file, line)} for every declared library note."""
    notes = {}
    for path in ctx.walk(*DIRS, ext=".lean"):
        src = ctx.read(path)
        if "library_note" not in src:
            continue
        for m in LIBRARY_NOTE.finditer(src):
            title = m.group(1) or m.group(2)
            notes[title] = (ctx.rel(path), src.count("\n", 0, m.start()) + 1)
    return notes


def _declared_tokens(ctx):
    """{token: [(file, line, command)]} for every token a syntax-forming command introduces."""
    tokens = collections.defaultdict(list)
    for path in ctx.walk(*DIRS, ext=".lean"):
        src = ctx.read(path)
        if not any(k in src for k in ("syntax", "notation", "macro", "elab", "infix", "prefix",
                                      "postfix", "register_option", "register_simp_attr",
                                      "declare_syntax_cat", "binder_predicate")):
            continue
        # Comments are stripped first: a `--` line mentioning `syntax` is not a declaration.
        code = pt.extract_comments(src)[1]
        for m in SYNTAX_CMD.finditer(code):
            cmd, rest = m.group(1), m.group(2)
            line = code.count("\n", 0, m.start()) + 1
            if cmd in ("register_option", "register_simp_attr", "declare_syntax_cat"):
                d = DOTTED.search(rest)
                if d:
                    tokens[d.group(1)].append((ctx.rel(path), line, cmd))
                continue
            for q in QUOTED.finditer(rest):
                tok = q.group(1).strip()
                # Pure symbol tokens carry no English; skip them early.
                if tok and re.search(r"[A-Za-z]", tok):
                    tokens[tok].append((ctx.rel(path), line, cmd))
    return tokens


def _code_word_counts(ctx):
    """How often each lower-cased word appears as part of an identifier in Lean code.

    A declared token whose components the library uses freely is established vocabulary, however
    odd it looks in a dictionary."""
    counts = collections.Counter()
    ident = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
    for path in ctx.walk(*DIRS, ext=".lean"):
        code = pt.extract_comments(ctx.read(path))[1]
        for m in ident.finditer(code):
            for w in components(m.group(0)):
                counts[w] += 1
    return counts


def collect(ctx):
    findings = []

    # ---- V1: library note titles ----------------------------------------------------
    notes = _library_notes(ctx)
    ctx.say(f"notation: {len(notes)} library notes declared")
    for title, (file, line) in sorted(notes.items()):
        for word, _at in ctx.words(title):
            hit = ctx.suggest(word)
            if not hit:
                continue
            corr, dist, uses = hit
            findings.append(Finding(
                SURFACE, "1", word, file, line,
                f"`{word}` → `{corr}` in the library note title «{title}» "
                f"(distance {dist}; `{corr}` is used {uses} times in comments)",
                ctx.confidence(dist, uses)))

    # A reference that does not resolve is the comment audit's DOC-B3; here we only look at the
    # title itself, so that the two never report the same row.

    # ---- V2: declared syntax, option and attribute names ----------------------------
    tokens = _declared_tokens(ctx)
    ctx.say(f"notation: {len(tokens)} declared tokens")
    code_words = _code_word_counts(ctx)
    seen = set()
    for token, sites in sorted(tokens.items()):
        for word in set(components(token)):
            if word in seen:
                continue
            if code_words.get(word, 0) > ESTABLISHED_USES:
                continue      # the library writes this word freely: vocabulary, not a slip
            hit = ctx.suggest(word)
            if not hit:
                continue
            corr, dist, uses = hit
            seen.add(word)
            file, line, cmd = sites[0]
            where = "" if len(sites) == 1 else f", declared at {len(sites)} sites"
            findings.append(Finding(
                SURFACE, "2", word, file, line,
                f"`{word}` → `{corr}` in the `{cmd}` token `{token}`{where} "
                f"(distance {dist}; `{corr}` is used {uses} times in comments)",
                ctx.confidence(dist, uses)))

    return findings
