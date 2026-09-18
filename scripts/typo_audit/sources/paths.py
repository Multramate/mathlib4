#!/usr/bin/env python3
"""
File and directory names under `Mathlib/`, `Archive/` and `Counterexamples/`.

A path component is the one piece of English in the repository that neither of the other audits
can see.  The naming audit reads declaration names, so it never looks at the file a declaration
lives in; the comment audit only checks that a path *mentioned in prose* resolves on disk, so a
name misspelled consistently — in the file's own name, in the `import` lines that reach it and in
its module docstring — passes both untouched.  Yet it is what every `import` line spells out, and
it is the one string in a Lean file that no compiler ever checks.

Everything here turns on one fact about Lean naming: the term-level spelling of a name *lowercases*
letters that the type-level spelling capitalises — `ZPow`/`zpow`, `AEMeasurable`/`aeMeasurable`,
`LIntegral`/`lintegral` — and never the other way round.  So a lowercase letter in a declaration
name is no evidence about how a file should be capitalised, while a capital always is.  Ignoring
that asymmetry is what makes the naive comparison useless: it condemns two dozen files called
`SMul.lean`, `PID.lean`, `CDF.lean` for the crime of containing `smul`, `pid` and `cdf`.

P1 spells the component itself: each camelCase token goes through `ctx.suggest`, the judgement
    every other surface is held to.  In practice it finds nothing, and it cannot: `Mathlib.lean`
    imports every file in the library, `import` lines are code, and `ctx.idents` is built from
    code — so every token of every path component is already an identifier fragment as far as
    `ctx.suggest` is concerned, and no misspelling in a path can be rare enough to report.  The
    check is kept because it costs nothing and would fire on a component that no import echoes,
    but its zero is a property of the corpus and not a clean bill of health; P2 and P3 are what
    actually catch the misspellings.

P2 asks whether the file name contradicts the file.  Mathlib names a file after what it declares,
    so its declarations are the authority.  They are parsed with `naming_audit.extract_file`, and
    every contiguous run of name tokens *within a single dotted component* is collected — runs,
    because a file is named after part of what it declares (`ClopenNhdsOfOne` is the tail of
    `exist_openNormalSubgroup_sub_clopen_nhds_of_one`); within one component, because a run that
    straddles a `.` glues a namespace to a declaration and matches things by accident.  Two arms:

    * casing — reported only when the stem is *missing* capitals that a declaration writes
      (`Widesubcategory` against `WideSubcategory`, `Condexp` against `condExpKernel`).  A stem
      with a capital the code lacks is never reported: that is the term-level convention above,
      not a defect.  One declaration spelling the name the file's way makes the evidence ambiguous
      and the file is left alone.  The missing capitals must also be isolated from one another: a
      block of adjacent ones is an acronym styled differently — `Imo2005Q4.lean` opening
      `namespace IMO2005Q4` where forty-five siblings write `Imo` — and Mathlib styles acronyms
      both ways on purpose.
    * a dropped letter — when nothing in the file matches the stem at all but one name is a single
      edit away (`ClopenNhdofOne` against `clopen_nhds_of_one`).  Here the snake_case segmentation
      supplies the capitals, which is sound: the word boundaries are written down.  This arm is
      confined to stems of twelve characters or more, needs the near match to be unique and to
      begin and end with the stem's own letters, and refuses inflection pairs, since
      `BinaryProducts.lean` declaring `binary_product` is a plural and not a typo.

    P2 reports the disagreement and phrases the fix as a rename of the file, which is the usual
    resolution; occasionally it is the declaration that should move instead.

P3 is the check `ctx.suggest` cannot make, because it is about capitalisation rather than
    spelling.  A census of every identifier component in the code of the three directories
    (comments stripped, `import` lines dropped — an import merely restates the name under
    suspicion and is not independent evidence) records how the library actually writes each
    identifier.  Three filters make it an authority rather than a word count:

    * only spellings beginning with a capital are consulted.  An UpperCamelCase name is written as
      its author intended, whereas `zpowers` and `mfderiv` are term names whose capitalisation was
      thrown away, and reading those as authorities is what would condemn the perfectly good
      directories `ZPowers/` and `MFDeriv/`;
    * the spelling must occur in at least two files, so that one file disagreeing with its own
      name cannot rename it;
    * it must appear at least once as part of a dotted name (`ULift.up`, `Endofunctor.Algebra`).
      Without that, `Heval` — a hypothesis binder in two unrelated proofs — outvotes the file
      `HEval.lean`.

Left out deliberately: a frequency comparison between sibling path components — three files named
`Ulift.lean` against twelve named `ULift.lean` — reads well but is not precise.  `AB`
(Grothendieck's axioms) against `Ab` (the category of abelian groups), and `lpSpace` against
`LpSpace`, are genuinely different names that differ only in case, and a count cannot tell them
apart from a slip.  Requiring the code itself to disown the spelling, as P3 does, can.

A path reported by P2 is not reported again by P3: the two would be saying the same thing, and P2
says it with the better evidence.
"""
from __future__ import annotations

import collections
import os
import re
import sys

from context import Finding

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "naming_audit"))
import naming_audit as na  # noqa: E402
import prose_typos as pt  # noqa: E402

SURFACE = "file and directory names"
CATEGORIES = {
    "P1": "Misspelled word in a path component",
    "P2": "File name contradicted by the declarations inside it",
    "P3": "Path component cased against Mathlib's own spelling of the identifier",
}

DIRS = ("Mathlib", "Archive", "Counterexamples")

# camelCase, ALLCAPS and digit runs of a path component or of a Lean name segment:
# `ULift` -> U | Lift, `EllAdicCohomology` -> Ell | Adic | Cohomology, `L2Space` -> L | 2 | Space.
TOKEN = re.compile(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+")
# A dotted Lean name in code; its `.`-separated components are what the census counts.
DOTTED = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
IMPORT = re.compile(r"\s*(?:(?:public|private|protected|meta)\s+)*import\b")
# `_` and `.` come out so that `clopen_nhds_of_one` reads as one word while the P2 pre-filter
# looks for the stem; nothing else about the code matters at that stage.
GLUE = re.compile(r"[_.]")

# P2: the dropped-letter arm is only tried on a stem at least this long.  Below it, near misses
# between short words are common and mean nothing.
FUZZY_MIN = 12
# P3: how many uses of the rival spelling are needed before the code counts as an authority.
CENSUS_MIN = 3


def _norm(s: str) -> str:
    """A name with the case of its first letter normalised away.

    Lean writes types `UpperCamelCase` and terms `lowerCamelCase` and a file may be named after
    either, so the leading capital carries no information.  Everything after it does.
    """
    return s[:1].upper() + s[1:]


def _tokens(name: str) -> list:
    """The atomic tokens of one dotted component, snake_case and camelCase alike."""
    out = []
    for seg in name.split("_"):
        out.extend(TOKEN.findall(seg))
    return out


def _render(run) -> str:
    """The path-component spelling of a run of snake_case/camelCase tokens.

    A token that carries case keeps it; an all-lowercase token is a written-down word boundary and
    is capitalised, which is how `clopen nhds of one` becomes `ClopenNhdsOfOne`.
    """
    return "".join(t if not t.islower() else t.capitalize() for t in run)


def _inflection(a: str, b: str) -> bool:
    """True if `a` and `b` differ only by a plural or third-person `s`."""
    return b in (a + "s", a + "es") or a in (b + "s", b + "es")


def _same_casing(name: str, other: str) -> bool:
    """True if two spellings agree everywhere the first letter's case is not in question."""
    return name[1:] == other[1:]


def _missing_capitals(name: str, other: str):
    """The positions where `name` lacks a capital that `other` writes, or None.

    None whenever that is not the whole of the difference — in particular whenever `name` has a
    capital `other` lacks, which is Lean's term-naming convention (`SMul` against `smul`) rather
    than a defect.
    """
    if len(name) != len(other):
        return None
    at = []
    for i in range(1, len(name)):        # the first letter's case is never in question
        if name[i] == other[i]:
            continue
        if not (other[i].isupper() and name[i].islower()):
            return None
        at.append(i)
    return at or None


def _isolated(at) -> bool:
    """True if no two of the positions are adjacent — see the acronym caveat in the docstring."""
    return all(b - a > 1 for a, b in zip(at, at[1:]))


def _survey(ctx):
    """(census, candidates): how the code spells each identifier, and the files P2 must parse.

    One pass over the tree does both jobs, because both need each file's code with its comments
    stripped, and that strip is the expensive part.  A census entry is
    `[uses, a file it was seen in, seen in a second file, seen inside a dotted name]`: the last
    two are all P3 asks beyond the count, and keeping them as flags costs nothing per identifier.
    """
    census = collections.defaultdict(dict)
    candidates = []
    for path in ctx.walk(*DIRS, ext=".lean"):
        _comments, code = pt.extract_comments(ctx.read(path))
        # An `import` line only repeats a file name, so it cannot vote on how that name is spelled.
        code = "\n".join(ln for ln in code.split("\n") if not IMPORT.match(ln))
        rel = ctx.rel(path)
        for m in DOTTED.finditer(code):
            parts = m.group(0).split(".")
            qualified = len(parts) > 1
            for part in parts:
                if not part:
                    continue
                seen = census[part.lower()]
                rec = seen.get(part)
                if rec is None:
                    seen[part] = [1, rel, False, qualified]
                    continue
                rec[0] += 1
                rec[2] = rec[2] or rec[1] != rel
                rec[3] = rec[3] or qualified
        stem = os.path.basename(path)[:-len(".lean")]
        key = stem.lower()
        if not key.isalnum():
            continue
        # Pre-filter for P2.  `extract_file` costs tens of milliseconds a file, which is minutes
        # over the whole tree, so it only runs where the glued-up code plausibly disagrees with
        # the stem: either it writes the stem with some other casing, or (for the dropped-letter
        # arm) it never writes the stem at all but does write both of its ends.
        flat = GLUE.sub("", code)
        low = flat.lower()
        if any(not _same_casing(stem, m.group(0))
               for m in re.finditer(re.escape(key), flat, re.I)):
            candidates.append(path)
        elif len(key) >= FUZZY_MIN and key not in low and key[:6] in low and key[-5:] in low:
            candidates.append(path)
    return census, candidates


def _runs(decls) -> dict:
    """{glued lowercase: {spelling as written: path-component rendering}} for a file's names."""
    out = collections.defaultdict(dict)
    seen = set()
    for d in decls:
        for name in (d.get("full"), d.get("ns")):
            if not name or name in seen:
                continue
            seen.add(name)
            for part in name.split("."):
                toks = _tokens(part)
                for i in range(len(toks)):
                    for j in range(i + 1, len(toks) + 1):
                        run = toks[i:j]
                        out["".join(run).lower()]["".join(run)] = _render(run)
    return out


def _decl_line(decls, spelling: str) -> int:
    """The line of the first declaration whose name contains `spelling`, or 1."""
    want = spelling.lower()
    for d in decls:
        for name in (d.get("full"), d.get("ns")):
            if name and want in GLUE.sub("", name).lower():
                return d["line"]
    return 1


def _contradiction(path, ctx):
    """(spelling, why, line, confidence) if the file's declarations disown its name, else None."""
    stem = os.path.basename(path)[:-len(".lean")]
    key = stem.lower()
    try:
        decls = na.extract_file(path, ctx.root)
    except (OSError, UnicodeDecodeError, RecursionError):
        return None
    runs = _runs(decls)
    if key in runs:
        written = runs[key]
        if any(_same_casing(stem, w) for w in written):
            return None          # some declaration spells it the file's way: no contradiction
        targets = {_norm(w) for w in written
                   if (at := _missing_capitals(stem, w)) and _isolated(at)}
        if len(targets) != 1:
            return None
        hit = targets.pop()
        quoted = ", ".join(sorted(repr(w) for w in written))
        return (hit, f"its declarations write {quoted}", _decl_line(decls, hit), "high")
    if len(key) < FUZZY_MIN:
        return None
    # A single dropped letter, with both ends of the name intact so that the match is anchored.
    near = [k for k in runs
            if k[0] == key[0] and k[-1] == key[-1] and abs(len(k) - len(key)) <= 1
            and not _inflection(k, key) and pt.damerau(key, k) == 1]
    if len(near) != 1:
        return None
    renderings = set(runs[near[0]].values())
    if len(renderings) != 1:
        return None
    hit = renderings.pop()
    return (hit, f"no declaration mentions {stem!r}; the nearest is "
                 f"{sorted(runs[near[0]])[0]!r}, one letter away",
            _decl_line(decls, hit), "medium")


def _components(ctx):
    """(relative path, component name, is_dir) for every distinct path component of the tree."""
    seen = {}
    for path in ctx.walk(*DIRS, ext=".lean"):
        parts = ctx.rel(path).split("/")
        for i in range(1, len(parts)):          # skip the three top-level directories themselves
            last = i == len(parts) - 1
            seen["/".join(parts[:i + 1])] = (parts[i][:-len(".lean")] if last else parts[i],
                                             not last)
    for rel in sorted(seen):
        name, is_dir = seen[rel]
        yield rel, name, is_dir


def collect(ctx):
    findings = []
    census, candidates = _survey(ctx)
    ctx.say(f"census: {len(census)} identifiers; {len(candidates)} files for the declaration check")

    renamed = {}
    for path in candidates:
        hit = _contradiction(path, ctx)
        if not hit:
            continue
        spelling, why, line, conf = hit
        rel = ctx.rel(path)
        renamed[rel] = spelling
        findings.append(Finding(
            SURFACE, "P2", os.path.basename(path), rel, line,
            f"{os.path.basename(path)!r} contradicts what it declares: {why}; "
            f"rename to {spelling}.lean", conf))

    for rel, name, is_dir in _components(ctx):
        what = "directory" if is_dir else "file"
        for tok in TOKEN.findall(name):
            s = ctx.suggest(tok.lower())
            if not s:
                continue
            corr, dist, uses = s
            findings.append(Finding(
                SURFACE, "P1", name, rel, 1,
                f"{what} component {name!r}: {tok!r} is not a word Mathlib's prose uses; "
                f"{corr!r} ({uses} uses) is {dist} edit(s) away", ctx.confidence(dist, uses)))
        if rel in renamed or len(name) < 4 or not name.isalnum():
            continue
        # Only UpperCamelCase spellings are consulted; see the module docstring.
        auth = {w: rec for w, rec in census.get(name.lower(), {}).items() if w[:1].isupper()}
        if not auth or any(_same_casing(name, w) for w in auth):
            continue
        best, rec = max(auth.items(), key=lambda kv: kv[1][0])
        uses, _first, many_files, qualified = rec
        if uses < CENSUS_MIN or not many_files or not qualified:
            continue
        findings.append(Finding(
            SURFACE, "P3", name, rel, 1,
            f"{what} component {name!r}: Mathlib's code writes this identifier {best!r} "
            f"({uses} uses in several files, qualified) and never {name!r}; "
            f"rename to {_norm(best)}", "high" if uses >= 20 else "medium"))

    findings.sort(key=lambda f: (f["cat"], f["file"]))
    return findings
