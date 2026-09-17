#!/usr/bin/env python3
"""
Comment- and docstring-consistency audit for Mathlib.

The companion of `scripts/naming_audit/naming_audit.py`: that script audits *declarations*, this
one audits the *prose* around them.  It scans every `.lean` file under `Mathlib/`, `Archive/` and
`Counterexamples/` (no Lean toolchain needed), runs a collection of consistency checks on module
docstrings, declaration docstrings and ordinary comments, and (re)writes `docs/comment_audit.md`.

Plain misspellings are *not* checked here: they are category F1 of `docs/naming_audit.md`, which
uses Mathlib's own comment corpus as its dictionary (see `scripts/naming_audit/prose_typos.py`).
This script looks for the other ways in which comments disagree with each other: module docstrings
that spell a standard section heading differently, cross-references that no longer resolve, prose
that picks the minority spelling of a word Mathlib otherwise writes one way, and markup or marker
conventions applied inconsistently.

Most thresholds are derived from the corpus rather than hard-coded: a spelling is reported because
Mathlib overwhelmingly writes it the other way, not because a dictionary prefers one form.  That
keeps the report to genuine inconsistencies within Mathlib and away from matters of taste.

The markdown file is a *living* document, exactly as `docs/naming_audit.md` is: every finding has a
stable key and a `Status` column.  When the script is re-run, the `Status` and `Note` columns of
rows that are still present are preserved, new findings are added with status `open`, and findings
that no longer apply are dropped (their count is reported in the summary).  Triage therefore
happens by editing the markdown file directly.

Usage:
    python3 scripts/comment_audit/comment_audit.py [--root .] [--out docs/comment_audit.md]
"""
from __future__ import annotations

import argparse
import collections
import datetime
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "naming_audit"))
import naming_audit  # noqa: E402
import prose_typos  # noqa: E402

DIRS = ["Mathlib", "Archive", "Counterexamples"]

# --------------------------------------------------------------------------------------------
# Part 1: extraction
# --------------------------------------------------------------------------------------------

# A comment is stored with the line its `/-`, `/--`, `/-!` or `--` sits on, so that a finding
# inside it can report an absolute line number.
Comment = collections.namedtuple("Comment", "file line kind text")


def body_offset(kind: str) -> int:
    """`prose_typos.extract_comments` returns the text just after `/-`, so a docstring body starts
    one character later (after the third `-`) and a module docstring after the `!`."""
    return 1 if kind in ("doc", "mod") else 0


def collect(root: str):
    """Return (comments, code_by_file): every comment in the tree, and the non-comment text."""
    comments: list = []
    code: dict = {}
    for d in DIRS:
        for dp, _dn, fn in os.walk(os.path.join(root, d)):
            for f in sorted(fn):
                if not f.endswith(".lean"):
                    continue
                path = os.path.join(dp, f)
                rel = os.path.relpath(path, root).replace(os.sep, "/")
                with open(path, encoding="utf-8") as fh:
                    src = fh.read()
                try:
                    cs, plain = prose_typos.extract_comments(src)
                except Exception as e:  # pragma: no cover - keep going on parse failures
                    print(f"warning: failed to parse {rel}: {e}", file=sys.stderr)
                    continue
                code[rel] = plain
                for (line, kind, text) in cs:
                    comments.append(Comment(rel, line, kind, text[body_offset(kind):]))
    return comments, code


def modules(root: str):
    """Every Lean source file in the tree, as a path and as a module name."""
    paths, names = set(), set()
    for d in DIRS:
        for dp, _dn, fn in os.walk(os.path.join(root, d)):
            for f in fn:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dp, f), root).replace(os.sep, "/")
                    paths.add(rel)
                    names.add(rel[:-5].replace("/", "."))
    return paths, names


def bib_keys(root: str) -> set:
    path = os.path.join(root, "docs", "references.bib")
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8") as f:
        return {m.group(1) for m in re.finditer(r"@\w+\s*\{\s*([^,\s]+)\s*,", f.read())}


# --------------------------------------------------------------------------------------------
# Part 2: prose extraction helpers
# --------------------------------------------------------------------------------------------

FENCED = re.compile(r"```.*?```", re.S)
DOUBLE_SPAN = re.compile(r"``[^`]+``")
SPAN = re.compile(r"`[^`\n]*`")
# Display maths wraps onto several lines in practice, so `$…$` may span line breaks; the length
# bound keeps a stray `$` from swallowing the rest of a docstring.
MATH = re.compile(r"\$\$.{0,600}?\$\$|\$[^$]{0,400}?\$|\\\(.{0,400}?\\\)|\\\[.{0,600}?\\\]", re.S)
URL = re.compile(r"https?://\S+|www\.\S+")
# `[F. Trèves, *Topological vector spaces*][treves1967]` and `[crans2017]`: bibliography entries
# are titles and author names, not English prose.
CITATION = re.compile(r"\[[^\[\]]*\]\[[^\]]*\]|\[[A-Za-z][A-Za-z0-9_.'-]*\]|«[^»]*»", re.S)


def blank(rx: re.Pattern, text: str) -> str:
    """Replace every match of `rx` by spaces, keeping every character position and line break."""
    def sub(m):
        return "".join("\n" if c == "\n" else " " for c in m.group(0))
    return rx.sub(sub, text)


def prose(text: str, drop_citations: bool = True) -> str:
    """Blank out everything that is not English prose, preserving offsets so that a match in the
    result still points at the right line of the original comment."""
    for rx in (FENCED, DOUBLE_SPAN, SPAN, MATH, URL):
        text = blank(rx, text)
    if drop_citations:
        text = blank(CITATION, text)
    return text


def code_only(text: str) -> str:
    """The inverse: only the contents of code spans, everything else blanked out."""
    out = ["\n" if c == "\n" else " " for c in text]
    for rx in (DOUBLE_SPAN, SPAN):
        for m in rx.finditer(text):
            for i in range(m.start(), m.end()):
                if text[i] != "\n":
                    out[i] = text[i]
    return "".join(out)


def line_at(c: Comment, offset: int) -> int:
    """Absolute line number of character `offset` of comment `c`'s text."""
    return c.line + c.text.count("\n", 0, offset)


SENTENCE_END = re.compile(r"[.!?:;]\s*$|^\s*$|[#*\-–—(\[]\s*$|[.!?]['\")]?\s+$")


def mid_sentence(text: str, at: int) -> bool:
    """Whether the word at `at` sits inside a sentence, rather than opening one (or a heading, or a
    list item). Only mid-sentence occurrences say anything about how a word is capitalised."""
    start = text.rfind("\n", 0, at) + 1
    before = text[start:at]
    if not before.strip():
        return False
    return not SENTENCE_END.search(before)


def excerpt(text: str, at: int, width: int = 46) -> str:
    """A short one-line quotation of `text` around `at`, for the Detail column."""
    start = text.rfind("\n", 0, at) + 1
    end = text.find("\n", at)
    if end == -1:
        end = len(text)
    s = text[start:end].strip()
    if len(s) > width:
        s = s[:width].rstrip() + "…"
    return s


# --------------------------------------------------------------------------------------------
# Part 3: the checks
# --------------------------------------------------------------------------------------------

# The section headings Mathlib's documentation style prescribes for module docstrings.  The check
# does not rely on this list to decide what is canonical (the corpus does that); it only records
# which spellings are blessed, so that a rare heading which happens to be canonical is not
# reported against a more frequent non-canonical one.
CANONICAL_HEADINGS = {
    "Main definitions", "Main statements", "Main results", "Main declarations", "Notation",
    "Implementation notes", "References", "Tags", "TODO", "See also",
}

# Headings that Mathlib's style guide replaces by another heading outright.
HEADING_SYNONYMS = {
    "keywords": "Tags",
    "implementation": "Implementation notes",
    "implementation detail": "Implementation notes",
    "implementation details": "Implementation notes",
    "implementation note": "Implementation notes",
    "reference": "References",
    "tag": "Tags",
    "notations": "Notation",
    "main theorem": "Main results",
    "main theorems": "Main results",
}

# British/American and other spelling pairs that no morphological rule catches.  Each pair is only
# reported when the corpus itself is lopsided, so listing a pair here is not a vote for either form.
SPELLING_PAIRS = [
    ("neighbourhood", "neighborhood"), ("neighbourhoods", "neighborhoods"),
    ("behaviour", "behavior"), ("behaviours", "behaviors"),
    ("colour", "color"), ("favour", "favor"), ("honour", "honor"),
    ("centre", "center"), ("centres", "centers"), ("fibre", "fiber"), ("fibres", "fibers"),
    ("metre", "meter"), ("litre", "liter"),
    ("analyse", "analyze"), ("analysed", "analyzed"), ("analysing", "analyzing"),
    ("labelled", "labeled"), ("labelling", "labeling"),
    ("modelled", "modeled"), ("modelling", "modeling"),
    ("travelling", "traveling"), ("cancelled", "canceled"),
    ("fulfil", "fulfill"), ("skilful", "skillful"),
    ("judgement", "judgment"), ("acknowledgement", "acknowledgment"),
    ("programme", "program"), ("catalogue", "catalog"), ("dialogue", "dialog"),
    ("grey", "gray"), ("practise", "practice"),
]

# `-ise`/`-ize` and friends: generated rather than listed, because Mathlib's vocabulary of
# `-ize` verbs is large and grows.
ISE_SUFFIXES = [("ise", "ize"), ("ised", "ized"), ("ises", "izes"), ("ising", "izing"),
                ("isable", "izable"), ("isation", "ization"), ("isations", "izations"),
                ("iser", "izer"), ("isers", "izers")]

# Markers whose casing is a convention rather than a matter of sentence position, checked only
# where the marker opens a comment or a line of one.
MARKER_FAMILIES = [
    ("TODO", [r"TODO", r"Todo", r"todo", r"ToDo", r"TODo"]),
    ("Porting note", [r"Porting note", r"porting note", r"Porting Note", r"PORTING NOTE"]),
    ("Adaptation note", [r"Adaptation note", r"adaptation note", r"Adaptation Note"]),
    ("See also", [r"See also", r"see also", r"See Also"]),
]

# ASCII and LaTeX stand-ins for the notation Mathlib writes in Unicode.  Only matches outside code
# spans and outside `$…$` count, so legitimate LaTeX in display maths is never reported.
NOTATION_STANDINS = [
    (r"(?<![-<>=!:~])->(?!>)", "->", "→", "low"),
    (r"<->", "<->", "↔", "high"),
    (r"<=>", "<=>", "↔", "high"),
    (r"(?<![<>=!])<=(?![>=])", "<=", "≤", "medium"),
    (r"(?<![<>=!])>=(?![>=])", ">=", "≥", "medium"),
    (r"!=", "!=", "≠", "medium"),
    (r"(?<![\\/])/\\(?![\\/])", r"/\\", "∧", "medium"),
    (r"(?<![\\/])\\/(?![\\/])", r"\\/", "∨", "medium"),
    (r"\\mathbb\s*\{?", r"\mathbb", "ℝ, ℕ, ℤ, …", "high"),
    (r"\\to(?![A-Za-z])", r"\to", "→", "high"),
    (r"\\mapsto(?![A-Za-z])", r"\mapsto", "↦", "high"),
    (r"\\forall(?![A-Za-z])", r"\forall", "∀", "high"),
    (r"\\exists(?![A-Za-z])", r"\exists", "∃", "high"),
    (r"\\subseteq(?![A-Za-z])", r"\subseteq", "⊆", "high"),
    (r"\\circ(?![A-Za-z])", r"\circ", "∘", "high"),
    (r"\\otimes(?![A-Za-z])", r"\otimes", "⊗", "high"),
    (r"\\le(?![A-Za-z])", r"\le", "≤", "high"),
    (r"\\ge(?![A-Za-z])", r"\ge", "≥", "high"),
    (r"\\infty(?![A-Za-z])", r"\infty", "∞", "high"),
]

# Lean tokens that a doubled-word check must ignore: a docstring that shows an example often has
# `rfl` or `qify` on two consecutive lines, which is code, not a slip of the pen.
LEAN_TOKENS = {
    "rfl", "simp", "omega", "qify", "zify", "rify", "norm_num", "push_cast", "gcongr", "aesop",
    "grind", "rwa", "rcases", "constructor", "refine", "assumption", "linarith", "nlinarith",
    "positivity", "fin_cases", "exact", "apply", "intros", "inl", "inr", "fst", "snd", "obj",
    "hom", "inv", "comp", "mul", "sub", "neg",
}

HEADING_RE = re.compile(r"(?m)^[ \t]*(#+)[ \t]+(.+?)[ \t]*$")
WORD_RE = re.compile(r"[A-Za-z]+(?:[-'][A-Za-z]+)*")
DOUBLED_RE = re.compile(r"\b([A-Za-z]{2,})([ \t]+|\n[ \t]*)\1\b")
DIAGRAM_RE = re.compile(r"\|.*\||-->|==>|\S {4,}\S|/\\|\\/|↗|↘|⟶")
FILE_REF_RE = re.compile(r"\b((?:Mathlib|Archive|Counterexamples)(?:/[A-Za-z0-9_'+.-]+)*\.lean)\b")
MODULE_REF_RE = re.compile(r"`((?:Mathlib|Archive|Counterexamples)(?:\.[A-Za-z0-9_'₀-₉]+){2,})`")
NOTE_REF_RE = re.compile(r"\b([Nn]ote|NOTE)\s*\[([^\]\n]{2,70})\]")
LIBRARY_NOTE_RE = re.compile(r"library_note\s+«([^»]+)»|library_note\s+\"([^\"]+)\"")
DOTTED_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+)`")
CITE_RE = re.compile(r"\[([^\[\]`$\n]{2,80})\]\[([^\]\n]{2,60})\]|\[([^\[\]`$\n]{3,60})\]")
CITEKEY_RE = re.compile(r"^[A-Za-z][A-Za-z.'-]*(?:\d{2,4}[a-z]?|-[A-Za-z]{2,})$")

CATEGORY_INFO = collections.OrderedDict([
    ("A1", ("Section headings that differ only in letter case", "Heading",
            "Module docstrings are divided by `##` headings. Mathlib writes `## Main definitions`, "
            "`## Implementation notes`, `## References`, `## Tags`; a heading that differs from the "
            "dominant spelling only in capitalisation (`## Main Definitions`, `## Implementation "
            "Notes`) is a pure inconsistency. The dominant spelling is taken from the corpus, not "
            "from a fixed list, and the ratio of the two counts sets the confidence.")),
    ("A2", ("Section headings with trailing punctuation", "Heading",
            "A `##` heading is a title, not a sentence: `## Main definitions:` and `## References:` "
            "render the colon as part of the heading. The overwhelming majority of Mathlib's "
            "headings carry no trailing punctuation.")),
    ("A3", ("Rare variants of a standard section heading", "Heading",
            "A heading that is a singular/plural variant of a common one (`## Main definition`, "
            "`## Reference`), or a synonym that Mathlib's documentation style replaces by another "
            "heading (`## Keywords` → `## Tags`, `## Implementation details` → `## Implementation "
            "notes`). Headings that are genuinely specific to one file (`## Proof outline`, "
            "`## Mathematical background`) are not variants of anything and are not reported.")),
    ("A4", ("Heading structure anomalies in a module docstring", "Anomaly",
            "A module docstring opens with a single `#` title and subdivides it with `##`. Reported "
            "here: a header docstring with no `#` title, one with more than one `#` title (two "
            "documents in one file), and a `###` subsection that is not inside any `##` section.")),
    ("A5", ("Citations with no entry in `docs/references.bib`", "Citation key",
            "A `## References` section cites sources by bibliography key, as "
            "`* [Author, *Title*][authorYEAR]`. A key with no entry in `docs/references.bib` "
            "produces a dangling link in the generated documentation. Only citation-shaped keys "
            "(a name followed by a year, or a hyphenated name) are checked, so that `[R]` and "
            "`[simp]` are not mistaken for citations.")),
    ("B1", ("References to source files that do not exist", "Path",
            "A comment naming a file as `Mathlib/Foo/Bar.lean` where no such file exists: the file "
            "was renamed, split or deleted and the cross-reference was not updated.")),
    ("B2", ("References to modules that do not exist", "Module",
            "A code span naming a module as `Mathlib.Foo.Bar` that is neither a module of the "
            "library nor a declaration. Directory prefixes (`Mathlib.Algebra.Order`) are not "
            "reported, since a comment may legitimately name a whole subtree.")),
    ("B3", ("References to library notes that are not defined", "Library note",
            "`see note [foo]` is resolved against the notes declared by `library_note «foo»`. A "
            "reference to a note that no longer exists under that name is dead: the reader is sent "
            "to documentation they cannot find. The `Detail` column names the closest note that "
            "does exist.")),
    ("B4", ("Lean 3 identifiers in code spans", "Identifier",
            "A dotted identifier in a code span whose first component is the Lean 3 `snake_case` "
            "spelling of a namespace that now exists in `UpperCamelCase` (`direct_sum.one_mul`, "
            "`category_theory.monoidal_closed.functor_closed`). These are mathlib3 names that "
            "survived the port inside prose, where no linter looks.")),
    ("C1", ("Minority spelling of a word Mathlib writes one way", "Word",
            "Hyphenation (`non-zero` vs `nonzero`) and British/American spelling (`normalised` vs "
            "`normalized`, `neighbourhood` vs `neighborhood`) counted over the whole comment "
            "corpus: a form is reported only when the other one is at least five times as common "
            "and used at least ten times. One row per word and file. Mathlib has no rule on either "
            "axis, so these rows document an inconsistency rather than an error; a hyphenated word "
            "whose closed form is a different word (`re-cover` vs `recover`) is an `fp`.")),
    ("C2", ("Proper nouns written in lower case", "Word",
            "A word that Mathlib's comments capitalise at least five times as often as not "
            "(`Noetherian`, `Hausdorff`, `Lipschitz`, `Boolean`), written in lower case outside a "
            "code span. Adjectives that Mathlib deliberately keeps lower case (`abelian`) are "
            "dominated by the lower-case form and are therefore never reported.")),
    ("C3", ("Doubled words", "Word",
            "The same word twice in a row in prose (`the the`, `that that`). Code spans, fenced "
            "blocks and lines that look like ASCII diagrams are excluded. A few rows are correct "
            "English (`at at most one point`, `two two-pointings`) and are `fp`.")),
    ("D1", ("ASCII or LaTeX stand-ins for Mathlib's notation", "Notation",
            "Mathlib writes mathematics in Unicode. An ASCII `->`, `<->`, `<=`, `>=`, `!=` or a "
            "LaTeX `\\mathbb{R}`, `\\to`, `\\forall` that is neither inside a code span nor inside "
            "`$…$` maths is a stand-in that escaped, and renders literally in the generated "
            "documentation. Every LaTeX command Mathlib's comments contain is currently inside "
            "maths mode, so only the ASCII rows remain; the LaTeX patterns are kept as a guard. "
            "`->` is `low` throughout: it is also how a rename note (`succ n -> n + 1`) and an "
            "ASCII diagram are written, both of which are `fp`.")),
    ("D2", ("Unbalanced code-span delimiters", "Excerpt",
            "A docstring with an odd number of backticks: one code span is never closed, so the "
            "rest of the docstring renders as code (or the following prose is swallowed). Fenced "
            "blocks and ``double spans`` are accounted for first.")),
    ("D3", ("Nonstandard casing of a comment marker", "Marker",
            "`TODO`, `Porting note`, `Adaptation note` and `See also` open a comment or one of its "
            "lines with a fixed spelling. Only line-initial occurrences are checked, so `see also` "
            "in the middle of a sentence is not reported.")),
    ("D4", ("`--` comments without a space after the dashes", "Excerpt",
            "Mathlib writes `-- comment`, not `--comment`. Separator lines (`---`), `--!` and "
            "`--#` are not reported.")),
])

NEAR_IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


def edit_distance_le(a: str, b: str, limit: int) -> bool:
    """Whether the Levenshtein distance between `a` and `b` is at most `limit`."""
    if abs(len(a) - len(b)) > limit:
        return False
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i] + [0] * len(b)
        for j, cb in enumerate(b, 1):
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb))
        if min(cur) > limit:
            return False
        prev = cur
    return prev[-1] <= limit


def snake_of(camel: str) -> str:
    """The Lean 3 spelling of a `UpperCamelCase` name: `DirectSum` -> `direct_sum`."""
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", camel).lower()


class Audit:
    def __init__(self, root: str):
        self.root = root
        self.comments, self.code = collect(root)
        self.paths, self.modules = modules(root)
        self.bib = bib_keys(root)
        self.decls = naming_audit.extract_tree(root, DIRS)
        self.findings: list = []
        self._build_name_tables()
        self._build_corpus()

    # ---- tables -------------------------------------------------------------------------
    def _build_name_tables(self):
        """`known`: every suffix of every declaration's full name, i.e. every way a comment may
        legitimately refer to it. `namespaces`: the components that act as namespaces."""
        self.known: set = set()
        self.namespaces: set = set()
        for d in self.decls:
            full = d.get("full") or d.get("name")
            if not full:
                continue
            parts = full.split(".")
            for i in range(len(parts)):
                self.known.add(".".join(parts[i:]))
            for p in parts[:-1]:
                self.namespaces.add(p)
        self.snake_to_namespace: dict = collections.defaultdict(set)
        for n in self.namespaces:
            s = snake_of(n)
            if s != n:
                self.snake_to_namespace[s].add(n)
        # Library notes are declared with a guillemet-quoted name.
        self.notes: set = set()
        for text in self.code.values():
            for m in LIBRARY_NOTE_RE.finditer(text):
                self.notes.add(m.group(1) or m.group(2))

    def _build_corpus(self):
        """Word frequencies over the comment corpus: the yardstick every spelling check uses.

        `mid` counts only occurrences that are neither sentence- nor heading-initial, so that the
        capitalisation check is not fooled by `## References` or by an ordinary word opening a
        sentence."""
        self.exact: collections.Counter = collections.Counter()
        self.folded: collections.Counter = collections.Counter()
        self.mid: collections.Counter = collections.Counter()
        for c in self.comments:
            text = prose(c.text)
            for m in WORD_RE.finditer(text):
                w = m.group(0)
                self.exact[w] += 1
                self.folded[w.lower()] += 1
                if mid_sentence(text, m.start()):
                    self.mid[w] += 1
        self.headings: collections.Counter = collections.Counter()
        for c in self.comments:
            if c.kind != "mod":
                continue
            for m in HEADING_RE.finditer(self._headable(c.text)):
                if len(m.group(1)) == 2:
                    self.headings[m.group(2).strip()] += 1
        # The dominant spelling of each heading, keyed by its case- and punctuation-free form.
        # An unpunctuated spelling always wins the tie: `## Main results:` must never be held up
        # as the form the rest of the library should follow (that is what A2 is for).
        self.heading_norm: dict = collections.defaultdict(list)
        for h, n in self.headings.items():
            self.heading_norm[self._norm_heading(h)].append((n, h))
        for k in self.heading_norm:
            self.heading_norm[k].sort(key=lambda p: (p[1] != p[1].rstrip(" \t:.;,"), -p[0], p[1]))

    @staticmethod
    def _headable(text: str) -> str:
        """A module docstring's first heading sits on the `/-!` line, so make that line look like
        any other by replacing the leading `!` with a space."""
        return (" " + text[1:]) if text[:1] == "!" else text

    @staticmethod
    def _norm_heading(h: str) -> str:
        return h.lower().rstrip(" \t:.;,!")

    # ---- reporting ----------------------------------------------------------------------
    def add(self, cat: str, name: str, file: str, line: int, conf: str, detail: str):
        self.findings.append({"cat": cat, "name": name, "file": file, "line": line,
                              "conf": conf, "detail": detail})

    def run(self) -> list:
        self.check_headings()
        self.check_heading_structure()
        self.check_citations()
        self.check_file_refs()
        self.check_module_refs()
        self.check_note_refs()
        self.check_lean3_idents()
        self.check_spelling_variants()
        self.check_proper_nouns()
        self.check_doubled_words()
        self.check_notation_standins()
        self.check_backticks()
        self.check_markers()
        self.check_dash_space()
        return self.findings

    # ---- A1, A2, A3: module docstring section headings ----------------------------------
    def check_headings(self):
        seen: set = set()
        for c in self.comments:
            if c.kind != "mod":
                continue
            text = self._headable(c.text)
            for m in HEADING_RE.finditer(text):
                if len(m.group(1)) != 2:
                    continue
                h = m.group(2).strip()
                line = line_at(c, m.start())
                key = (h, c.file)
                if key in seen:
                    continue
                norm = self._norm_heading(h)
                best_n, best = self.heading_norm[norm][0]
                mine = self.headings[h]
                # A2: trailing punctuation.
                if h != h.rstrip(" \t:.;,"):
                    stripped = h.rstrip(" \t:.;,")
                    n = self.headings.get(stripped, 0)
                    if n:
                        seen.add(key)
                        self.add("A2", h, c.file, line, "high",
                                 f"trailing punctuation; `{stripped}` is used {n} times")
                        continue
                    seen.add(key)
                    self.add("A2", h, c.file, line, "medium", "trailing punctuation in a heading")
                    continue
                # A1: differs from the dominant spelling only in case. A handful of uses either way
                # says nothing about which spelling Mathlib prefers, so the winner must be used at
                # least five times and at least twice as often as the loser.
                if h != best and best_n >= 5 and best_n >= 2 * mine:
                    if h in CANONICAL_HEADINGS and best not in CANONICAL_HEADINGS:
                        continue
                    ratio = best_n / max(mine, 1)
                    conf = "high" if ratio >= 5 else "medium" if ratio >= 2 else "low"
                    seen.add(key)
                    self.add("A1", h, c.file, line, conf,
                             f"`{h}` ({mine}) vs `{best}` ({best_n} uses)")
                    continue
                # A3: singular/plural or a style-guide synonym.
                target = HEADING_SYNONYMS.get(norm)
                if target is None:
                    for cand in (norm + "s", norm[:-1] if norm.endswith("s") else None):
                        if not cand or cand == norm or cand not in self.heading_norm:
                            continue
                        cand_n, cand_h = self.heading_norm[cand][0]
                        if cand_n >= 10 * max(mine, 1):
                            target = cand_h
                            break
                if target and target != h:
                    n = self.headings.get(target, 0)
                    ratio = n / max(mine, 1)
                    conf = "high" if ratio >= 10 else "medium" if ratio >= 3 else "low"
                    seen.add(key)
                    self.add("A3", h, c.file, line, conf,
                             f"`{h}` ({mine}) — Mathlib writes `{target}` ({n} uses)")

    # ---- A4: heading structure ----------------------------------------------------------
    def check_heading_structure(self):
        first_mod: dict = {}
        for c in self.comments:
            if c.kind == "mod" and c.file not in first_mod:
                first_mod[c.file] = c
        for rel, c in first_mod.items():
            text = self._headable(c.text)
            hs = [(len(m.group(1)), m.group(2).strip(), m.start()) for m in HEADING_RE.finditer(text)]
            titles = [h for h in hs if h[0] == 1]
            if not titles:
                self.add("A4", "no `#` title", rel, c.line, "medium",
                         "the header docstring of this file has no `#` title")
            elif len(titles) > 1:
                self.add("A4", "several `#` titles", rel, line_at(c, titles[1][2]), "high",
                         f"{len(titles)} `#` titles in one module docstring: "
                         + ", ".join(f"`{t[1]}`" for t in titles[:3]))
            levels = [h[0] for h in hs]
            for i, lvl in enumerate(levels):
                if lvl >= 3 and 2 not in levels[:i]:
                    self.add("A4", "`###` outside any `##`", rel, line_at(c, hs[i][2]), "medium",
                             f"`{'#' * lvl} {hs[i][1]}` is not inside any `##` section")
                    break

    # ---- A5: bibliography citations -----------------------------------------------------
    def check_citations(self):
        if not self.bib:
            return
        seen: set = set()
        for c in self.comments:
            if c.kind != "mod":
                continue
            text = self._headable(c.text)
            for sec_start, sec in self._sections(text):
                head = re.sub(r"^[ \t]*##[ \t]+", "", sec.split("\n", 1)[0]).strip().lower()
                if not head.startswith("reference"):
                    continue
                for m in CITE_RE.finditer(sec):
                    key = (m.group(2) or m.group(3) or "").strip()
                    if not key or not CITEKEY_RE.match(key) or key in self.bib:
                        continue
                    if (key, c.file) in seen:
                        continue
                    seen.add((key, c.file))
                    near = [b for b in self.bib if edit_distance_le(b.lower(), key.lower(), 2)]
                    hint = f"; did you mean `{near[0]}`?" if near else ""
                    self.add("A5", key, c.file, line_at(c, sec_start + m.start()),
                             "high" if near else "medium",
                             f"`[{key}]` has no entry in `docs/references.bib`{hint}")

    @staticmethod
    def _sections(text: str):
        """Yield (offset, section text) for every `##` section of a module docstring. The text is
        returned verbatim, heading and all, so that an offset into it is still an offset into the
        comment."""
        marks = [m.start() for m in re.finditer(r"(?m)^[ \t]*##[ \t]+", text)]
        for i, s in enumerate(marks):
            end = marks[i + 1] if i + 1 < len(marks) else len(text)
            yield s, text[s:end]

    # ---- B1: file references ------------------------------------------------------------
    def check_file_refs(self):
        seen: set = set()
        for c in self.comments:
            for m in FILE_REF_RE.finditer(c.text):
                path = m.group(1)
                if path in self.paths or (path, c.file) in seen:
                    continue
                # `Mathlib.lean` and `Archive.lean` are the generated import-all files.
                if path.count("/") == 0:
                    continue
                seen.add((path, c.file))
                stem = path.rsplit("/", 1)[-1]
                near = [p for p in self.paths if p.rsplit("/", 1)[-1] == stem]
                # Only a unique basename identifies where the file went: pointing at one of the
                # four hundred `Basic.lean`s would be worse than saying nothing.
                hint = f"; the only file of that name is `{near[0]}`" if len(near) == 1 else ""
                self.add("B1", path, c.file, line_at(c, m.start()),
                         "medium" if hint else "high", f"no such file{hint}")

    # ---- B2: module references ----------------------------------------------------------
    def check_module_refs(self):
        prefixes = {".".join(n.split(".")[:i]) for n in self.modules
                    for i in range(1, len(n.split(".")))}

        def resolves(name: str) -> bool:
            if name in self.modules or name in prefixes or name in self.known:
                return True
            # `Mathlib.Foo.Bar.baz`: a module followed by a declaration inside it.
            parts = name.split(".")
            for i in range(2, len(parts)):
                if ".".join(parts[:i]) in self.modules and ".".join(parts[i:]) in self.known:
                    return True
            return False

        seen: set = set()
        for c in self.comments:
            for m in MODULE_REF_RE.finditer(c.text):
                name = m.group(1)
                if resolves(name):
                    continue
                if (name, c.file) in seen:
                    continue
                seen.add((name, c.file))
                near = sorted(x for x in self.modules if edit_distance_le(x, name, 2))
                hint = f"; closest module is `{near[0]}`" if near else ""
                self.add("B2", name, c.file, line_at(c, m.start()),
                         "medium" if near else "high",
                         f"neither a module nor a declaration{hint}")

    # ---- B3: library notes --------------------------------------------------------------
    def check_note_refs(self):
        if not self.notes:
            return
        seen: set = set()
        for c in self.comments:
            for m in NOTE_REF_RE.finditer(c.text):
                name = m.group(2).strip()
                if name in self.notes or (name, c.file) in seen:
                    continue
                seen.add((name, c.file))
                near = sorted(n for n in self.notes if edit_distance_le(n.lower(), name.lower(), 3))
                if not near:
                    # Otherwise only a note that shares most of its words is worth suggesting.
                    words = set(name.lower().split())
                    near = sorted((n for n in self.notes
                                   if len(words & set(n.lower().split())) >= 2),
                                  key=lambda n: -len(words & set(n.lower().split())))
                hint = f"; closest note is `{near[0]}`" if near else ""
                self.add("B3", name, c.file, line_at(c, m.start()),
                         "high" if near else "medium",
                         f"no `library_note «{name}»` exists{hint}")

    # ---- B4: Lean 3 identifiers ---------------------------------------------------------
    def check_lean3_idents(self):
        seen: set = set()
        for c in self.comments:
            for m in DOTTED_RE.finditer(c.text):
                name = m.group(1)
                if name in self.known or (name, c.file) in seen:
                    continue
                head = name.split(".")[0]
                if "_" not in head or head != head.lower():
                    continue
                if head in self.namespaces or head not in self.snake_to_namespace:
                    continue
                seen.add((name, c.file))
                now = sorted(self.snake_to_namespace[head])[0]
                self.add("B4", name, c.file, line_at(c, m.start()), "high",
                         f"Lean 3 spelling; the namespace is now `{now}`")

    # ---- C1: spelling variants ----------------------------------------------------------
    def _variant_pairs(self):
        """Pairs (minority, majority) that the corpus itself decides, with their counts."""
        pairs: dict = {}

        def consider(a: str, b: str, why: str):
            na, nb = self.folded.get(a, 0), self.folded.get(b, 0)
            if not na or not nb:
                return
            lo, hi = (a, b) if na <= nb else (b, a)
            nlo, nhi = min(na, nb), max(na, nb)
            if nhi < 10 or nhi < 5 * nlo:
                return
            pairs[lo] = (hi, nlo, nhi, why)

        for w in list(self.folded):
            if "-" in w and w.count("-") == 1 and len(w) > 4:
                consider(w, w.replace("-", ""), "hyphenation")
            for s_uk, s_us in ISE_SUFFIXES:
                if w.endswith(s_uk) and len(w) > len(s_uk) + 2:
                    consider(w, w[:-len(s_uk)] + s_us, "British/American spelling")
        for a, b in SPELLING_PAIRS:
            consider(a, b, "British/American spelling")
        return pairs

    def check_spelling_variants(self):
        pairs = self._variant_pairs()
        seen: set = set()
        for c in self.comments:
            text = prose(c.text)
            for m in WORD_RE.finditer(text):
                w = m.group(0).lower()
                hit = pairs.get(w)
                if not hit or (w, c.file) in seen:
                    continue
                other, nlo, nhi, why = hit
                seen.add((w, c.file))
                ratio = nhi / max(nlo, 1)
                conf = "high" if ratio >= 20 else "medium" if ratio >= 8 else "low"
                self.add("C1", m.group(0), c.file, line_at(c, m.start()), conf,
                         f"{why}: `{w}` ({nlo}) vs `{other}` ({nhi} uses in comments)")

    # ---- C2: proper nouns ---------------------------------------------------------------
    def check_proper_nouns(self):
        nouns: dict = {}
        for w, n in self.mid.items():
            if len(w) < 4 or not w.isalpha() or not w[0].isupper() or not w[1:].islower():
                continue
            lo = w.lower()
            nlo = self.mid.get(lo, 0)
            if nlo and n >= 20 and n >= 5 * nlo:
                nouns[lo] = (w, nlo, n)
        seen: set = set()
        for c in self.comments:
            text = prose(c.text)
            for m in WORD_RE.finditer(text):
                w = m.group(0)
                hit = nouns.get(w)
                if not hit or w != w.lower() or (w, c.file) in seen:
                    continue
                if not mid_sentence(text, m.start()):
                    continue
                # `.lean`, `foo_bar` and `Mathlib/Data/...` never reach here (code spans and URLs
                # are blanked out), but a bare `lean` in a path-like context still might.
                if m.start() and text[m.start() - 1] in "._/-":
                    continue
                cap, nlo, nhi = hit
                seen.add((w, c.file))
                ratio = nhi / max(nlo, 1)
                conf = "high" if ratio >= 20 else "medium" if ratio >= 10 else "low"
                self.add("C2", w, c.file, line_at(c, m.start()), conf,
                         f"`{w}` ({nlo}) vs `{cap}` ({nhi} mid-sentence uses in comments)")

    # ---- C3: doubled words --------------------------------------------------------------
    def check_doubled_words(self):
        # One row per word, file and quoted line: an example block that repeats `rfl rfl` six times
        # is one finding, not six.
        hits: dict = {}
        for c in self.comments:
            # Matched on the raw text: blanking a code span out would splice the words on either
            # side of it together and invent doublings (``a` and `b` and `c`` -> `and and`).
            text = c.text
            masked = prose(text, drop_citations=False)
            for m in DOUBLED_RE.finditer(text):
                w = m.group(1)
                if w.lower() in LEAN_TOKENS:
                    continue    # `rfl rfl`, `qify qify`: Lean code in an example, not prose
                if masked[m.start()] == " " or masked[m.end() - 1] == " ":
                    continue    # inside a code span, a fenced block or display maths
                quote = excerpt(c.text, m.start())
                if DIAGRAM_RE.search(excerpt(c.text, m.start(), width=200)):
                    continue
                # `two two-pointings`, `non-zero zero-divisors`: the second copy opens a compound.
                if m.end() < len(text) and text[m.end()] == "-":
                    conf = "low"
                elif self.folded.get(w.lower(), 0) < 30:
                    conf = "low"
                else:
                    conf = "high" if w.lower() not in ("at", "of", "in", "to") else "medium"
                key = (w, c.file, quote)
                if key in hits:
                    hits[key][1] += 1
                else:
                    hits[key] = [line_at(c, m.start()), 1, conf]
        for (w, rel, quote), (line, n, conf) in hits.items():
            times = f" ({n} times in this file)" if n > 1 else ""
            self.add("C3", w, rel, line, conf, f"`{w} {w}` in `{quote}`{times}")

    # ---- D1: ASCII / LaTeX stand-ins ----------------------------------------------------
    def check_notation_standins(self):
        seen: set = set()
        for c in self.comments:
            text = prose(c.text, drop_citations=False)
            for rx, shown, unicode_form, conf in NOTATION_STANDINS:
                for m in re.finditer(rx, text):
                    if (shown, c.file) in seen:
                        break
                    # An ASCII arrow inside an ASCII diagram is part of the drawing.
                    if shown in ("->", "<->") and DIAGRAM_RE.search(excerpt(c.text, m.start(), 200)):
                        continue
                    seen.add((shown, c.file))
                    self.add("D1", shown, c.file, line_at(c, m.start()), conf,
                             f"`{shown}` for `{unicode_form}` in `{excerpt(c.text, m.start())}`")

    # ---- D2: unbalanced backticks -------------------------------------------------------
    def check_backticks(self):
        for c in self.comments:
            if c.kind not in ("doc", "mod"):
                continue
            text = blank(FENCED, c.text)
            text = blank(DOUBLE_SPAN, text)
            if text.count("`") % 2 == 0:
                continue
            at = text.rfind("`")
            self.add("D2", excerpt(c.text, at, width=40), c.file, line_at(c, at), "high",
                     f"odd number of backticks in this {'module ' if c.kind == 'mod' else ''}"
                     f"docstring; the last one is at this line")

    # ---- D3: marker casing --------------------------------------------------------------
    def check_markers(self):
        counts: dict = {}
        sites: dict = collections.defaultdict(list)
        for family, spellings in MARKER_FAMILIES:
            rx = re.compile(r"(?m)^[\s*\-]*(" + "|".join(spellings) + r")\b")
            counts[family] = collections.Counter()
            for c in self.comments:
                for m in rx.finditer(c.text):
                    counts[family][m.group(1)] += 1
                    sites[(family, m.group(1))].append((c, m.start()))
        for family, spellings in MARKER_FAMILIES:
            if not counts[family]:
                continue
            best, nbest = counts[family].most_common(1)[0]
            for spelling, n in counts[family].items():
                if spelling == best or n * 5 > nbest:
                    continue
                # One row per file, with the repeat count: a file that writes `todo` four times is
                # one thing to fix.
                per_file: dict = {}
                for (c, at) in sites[(family, spelling)]:
                    per_file.setdefault(c.file, [line_at(c, at), 0])[1] += 1
                for rel, (line, k) in per_file.items():
                    times = f", {k} times in this file" if k > 1 else ""
                    self.add("D3", spelling, rel, line,
                             "high" if nbest >= 20 * n else "medium",
                             f"`{spelling}` ({n}) vs `{best}` ({nbest} uses){times}")

    # ---- D4: `--` without a space -------------------------------------------------------
    def check_dash_space(self):
        hits: dict = {}
        for c in self.comments:
            if c.kind != "line" or not c.text:
                continue
            if c.text[0].isspace() or c.text[0] in "-!#":
                continue
            key = (excerpt(c.text, 0, width=40), c.file)
            if key in hits:
                hits[key][1] += 1
            else:
                hits[key] = [c.line, 1]
        for (text, rel), (line, n) in hits.items():
            times = f" ({n} times in this file)" if n > 1 else ""
            self.add("D4", text, rel, line, "high", f"`--{text}`{times}")


# --------------------------------------------------------------------------------------------
# Part 4: markdown rendering with triage preservation
# --------------------------------------------------------------------------------------------

STATUSES = ("open", "confirmed", "fp", "fixed", "wontfix")
# Categories where one file may hold several rows for the same token: the quoted excerpt in the
# `Detail` cell is what tells them apart, so it goes into the key too.
DETAIL_KEYED = {"C3"}


def row_key(cat: str, name: str, file: str, detail: str = "") -> str:
    """Stable identity of a row, computed from its visible cells (line numbers may change)."""
    if cat in DETAIL_KEYED:
        quoted = re.findall(r"`([^`]*)`", detail)
        return f"{cat}|{name}|{file}|{quoted[-1] if quoted else ''}"
    return f"{cat}|{name}|{file}"


def split_row(line: str):
    cells = re.split(r"(?<!\\)\|", line.strip())
    return [c.strip().replace("\\|", "|") for c in cells[1:-1]]


def read_existing(path: str) -> dict:
    """Return {key: (status, note)} from an existing audit file."""
    out: dict = {}
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


def anchor(cat: str, title: str) -> str:
    """GitHub's slug for the heading `### {cat}: {title}`: lower-cased, with everything that is
    neither a word character, a hyphen nor a space dropped (not replaced), and spaces turned into
    hyphens. Getting this exactly right is what makes the summary table's links work."""
    s = f"{cat}: {title}".lower()
    return re.sub(r"[^\w\- ]", "", s).replace(" ", "-")


def render(findings: list, existing: dict, out_path: str, stats: dict):
    by_cat: dict = collections.defaultdict(list)
    for f in findings:
        f["key"] = row_key(f["cat"], f["name"], f["file"], f["detail"])
        by_cat[f["cat"]].append(f)
    seen = {f["key"] for f in findings}
    dropped = sum(1 for k in existing if k not in seen)
    conf_rank = {"high": 0, "medium": 1, "low": 2}
    status_rank = {"confirmed": 0, "open": 1, "wontfix": 2, "fixed": 3, "fp": 4}
    status_of = {f["key"]: existing.get(f["key"], ("open", "")) for f in findings}
    today = datetime.date.today().isoformat()
    L: list = []
    L.append("# Mathlib comment- and docstring-consistency audit")
    L.append("")
    L.append(f"_Generated by `scripts/comment_audit/comment_audit.py` on {today}; "
             f"{stats['comments']} comments in {stats['files']} files scanned._")
    L.append("")
    L.append("The companion of [`naming_audit.md`](naming_audit.md), which audits declarations:")
    L.append("this document audits the prose around them — module docstrings, declaration")
    L.append("docstrings and ordinary comments.")
    L.append("")
    L.append("This is a living document. Every row is identified by its category, token and file")
    L.append("(not the line number). Re-running the script keeps the `Status` and `Note` cells of rows that are")
    L.append("still present, adds new rows as `open`, and drops rows that no longer apply. Triage by editing")
    L.append("the `Status`/`Note` cells in place.")
    L.append("")
    L.append("Statuses: `open` (not yet looked at), `confirmed` (checked by hand, should be fixed), `fp`")
    L.append("(false positive or accepted exception), `fixed` (corrected; the row disappears on the next run),")
    L.append("`wontfix` (real but deliberately left alone).")
    L.append("")
    L.append("Confidence (`conf`) is the scanner's own estimate of how likely a row is a genuine problem; it is")
    L.append("not a triage verdict.")
    L.append("")
    L.append("## Scope")
    L.append("")
    L.append("- **Not** plain misspellings: those are category")
    L.append("  [F1](naming_audit.md#f1-probable-spelling-errors-in-comments-and-docstrings) of the naming")
    L.append("  audit, which spell-checks the corpus against itself. This document covers the ways in which")
    L.append("  comments disagree with *each other*.")
    L.append("- Every threshold that could be a matter of taste is derived from the corpus instead: a")
    L.append("  spelling, heading or marker is reported because Mathlib overwhelmingly writes it another")
    L.append("  way, not because a style guide or a dictionary prefers one form. The counts behind each")
    L.append("  verdict are in the `Detail` column, so a row can be argued with.")
    L.append("- Checks that a linter already enforces (`lake exe lint-style`, the `docString`, `docPrime`")
    L.append("  and `header` linters: empty docstrings, a docstring ending in a comma, trailing")
    L.append("  whitespace, the copyright header, Verso syntax) are left to the linter and not repeated.")
    L.append("")
    L.append("## Conventions applied")
    L.append("")
    L.append("- A module docstring is `/-! # Title … -/`, subdivided by `##` sections whose spellings are")
    L.append("  fixed: `Main definitions`, `Main statements`/`Main results`, `Notation`,")
    L.append("  `Implementation notes`, `References`, `Tags`, `TODO`.")
    L.append("- A cross-reference resolves: a file path names a file, `Mathlib.Foo.Bar` names a module or a")
    L.append("  declaration, `note [foo]` names a `library_note «foo»`, and `[authorYEAR]` names an entry")
    L.append("  of `docs/references.bib`.")
    L.append("- Comments are English prose in Mathlib's own spelling, and mathematics inside them is")
    L.append("  written in Unicode (`ℝ`, `→`, `⊆`), not in ASCII or LaTeX.")
    L.append("- A word is spelled the same way throughout: hyphenation and British/American endings are")
    L.append("  not chosen per file.")
    L.append("- `TODO`, `Porting note`, `Adaptation note` and `See also` are written one way.")
    L.append("")
    L.append("## Summary")
    L.append("")
    L.append("| Category | Description | Rows | open | confirmed | fp | wontfix |")
    L.append("|---|---|---:|---:|---:|---:|---:|")
    for cat, (title, _col, _desc) in CATEGORY_INFO.items():
        rows = by_cat.get(cat, [])
        cnt = collections.Counter(status_of[r["key"]][0] for r in rows)
        L.append(f"| [{cat}](#{anchor(cat, title)}) | {title} | {len(rows)} | "
                 f"{cnt['open']} | {cnt['confirmed']} | {cnt['fp']} | {cnt['wontfix']} |")
    L.append("")
    if dropped:
        L.append(f"_{dropped} row(s) from the previous version of this file no longer apply and were dropped._")
        L.append("")
    L.append("## Findings")
    L.append("")
    for cat, (title, col, desc) in CATEGORY_INFO.items():
        rows = by_cat.get(cat, [])
        L.append(f"### {cat}: {title}")
        L.append("")
        L.append(desc)
        L.append("")
        L.append(f"{len(rows)} row(s).")
        L.append("")
        if not rows:
            continue
        rows.sort(key=lambda r: (status_rank[status_of[r["key"]][0]], conf_rank[r["conf"]],
                                 r["file"], r["line"], r["name"]))
        L.append(f"| Status | {col} | Location | Detail | Note |")
        L.append("|---|---|---|---|---|")
        for r in rows:
            st, note = status_of[r["key"]]
            L.append(f"| {st} | `{md_escape(r['name'])}` | `{r['file']}:{r['line']}` | "
                     f"({r['conf']}) {md_escape(r['detail'])} | {md_escape(note)} |")
        L.append("")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    return status_of


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".", help="Mathlib checkout")
    ap.add_argument("--out", default=None, help="output markdown (default docs/comment_audit.md)")
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    out = args.out or os.path.join(root, "docs", "comment_audit.md")
    audit = Audit(root)
    findings = audit.run()
    stats = {"comments": len(audit.comments), "files": len(audit.code)}
    existing = read_existing(out)
    status_of = render(findings, existing, out, stats)
    counts = collections.Counter(f["cat"] for f in findings)
    print(f"{stats['comments']} comments in {stats['files']} files, {len(findings)} findings -> {out}")
    for cat in CATEGORY_INFO:
        rows = [f for f in findings if f["cat"] == cat]
        c = collections.Counter(status_of[f["key"]][0] for f in rows)
        print(f"  {cat:4} {counts[cat]:5}  open={c['open']} confirmed={c['confirmed']} fp={c['fp']}")


if __name__ == "__main__":
    main()
