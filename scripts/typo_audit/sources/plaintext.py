#!/usr/bin/env python3
"""
Prose that lives outside Lean: repository markdown, the CI tree, the tooling scripts.

Everything a contributor reads before they ever open a `.lean` file is here — `README.md`,
`.github/CONTRIBUTING.md`, the `Cache/` manuals, `scripts/README.md`, the `--help` text of the
Python and shell tools, the Dockerfiles, the workflow names GitHub prints in its own UI.  None of
it is reachable by a Lean-aware scanner, so it has never been spell-checked, and it is exactly the
prose that new contributors and outside readers see first.

Extracting it needs one small extractor per file format, because "the prose" means something
different in each:

* **Markdown** — the whole file, minus fenced blocks, inline code spans, link targets, reference
  definitions, HTML comments and raw tags.
* **Python** — comments and string literals, via `tokenize`, so that a `#` inside a regex or a
  quote inside a docstring cannot confuse a line-based scan.  A string counts as prose only if
  `prose_typos.string_prose` accepts it, which keeps format strings and option names out.
* **Shell, Dockerfiles and the extensionless `scripts/bench/` runners** — `#` comments, quoted
  message strings, and heredoc bodies (`: <<'BASH_MODULE_DOC'`, `cat <<EOF`), which is where these
  scripts keep their module documentation and their usage text.
* **YAML and TOML** — `#` comments (including the shell comments inside a workflow's `run:` block)
  and the `name:`/`description:`/`title:` values, block scalars included.  Other values are data.

Two checks run over the result.

**M1, misspellings.**  `ctx.suggest`, unchanged, so this surface is judged by the same yardstick as
every other.  Each file contributes its own identifiers — everything its extractor did *not* keep —
as `local_idents`, so a variable name quoted in a comment is not read as a misspelling.  One check
`ctx.suggest` does not make is added: a word this surface only ever writes capitalised is a name,
not a typo, which is the rule `prose_typos.scan` applies to the comment corpus and which `README.md`
needs, since its author list is a page of surnames.

**M2, proper nouns written with the wrong case.**  `Github` for GitHub, `python` for Python: not
misspellings, so `ctx.suggest` cannot see them, but just as wrong.  No list of proper nouns is
hard-coded.  Instead the dominant spelling of every word is measured across this surface: a word
has a *settled* capitalisation when one capitalised spelling is used at least 8 times in at least
two files, and the word is one the repository really uses (those uses plus `ctx.freq`, at least 12).
Evidence is only taken from positions where the capital was a choice — never the first word of a
sentence, line, list item or table cell, and never on a heading, a title-cased line or a shouty
all-caps one.  A rival spelling is then reported only if it is used at most three times in the whole
surface: more than that is a second legitimate usage rather than a slip, which is what saves the
`lean` binary, the `mathlib` package and the `github.` context objects from being "corrected".
Deviant spellings that are all-caps are never reported, so `GITHUB` in a banner is not a finding.

Deliberately left out:

* **Grammar.**  `push then to the repository` (`scripts/docker_push.sh`), `the we assign`
  (`scripts/add_deprecations.sh`), `the state after of a freshly cloned fork`
  (`scripts/README.md`) and `useful in right place` (`Archive/README.md`) are all real, and all
  invisible to a word-level check: every word in them is spelled and cased correctly.  Catching
  them needs a parser, and the cheap approximations (doubled words, article before verb) fire
  mostly on legitimate text.
* **Lean files.**  `scripts/*.lean` is a Lean tree; its comments and string literals belong to the
  `wider_lean` and `lean_strings` surfaces, not to this one.
* **Trailing `#` comments** are read only after the quoted spans of the line are masked, so
  `${#arr}` and `"a # b"` do not become comments.
* **The audit's own files** — `docs/naming_audit.md`, `docs/comment_audit.md`, `docs/typos.md`,
  `docs/tickets.md`, `docs/audit_fix_plan.md`, and the code under `scripts/*_audit/` and
  `scripts/audit_plan/` — are skipped: they quote misspellings as examples and would report
  themselves.
"""
from __future__ import annotations

import collections
import io
import os
import re
import tokenize

import prose_typos as pt
from context import Finding, excerpt, line_of

SURFACE = "repository markdown, scripts and CI files"

CATEGORIES = {
    "M1": "Misspelled word in repository prose",
    "M2": "Proper noun written with the wrong case",
}

# ------------------------------------------------------------------ what to read

# Directories searched for markdown.  `Mathlib/` and `Counterexamples/` hold none, and are the
# corpus besides, so they are not walked.
MD_DIRS = (".github", "Archive", "Cache", "DownstreamTest", "docs", "scripts", "widget")
LOOSE = ("bors.toml", ".gitpod.yml", "scripts/downstream_repos.yml")
SKIP_FILES = frozenset((
    "docs/naming_audit.md", "docs/comment_audit.md", "docs/typos.md", "docs/tickets.md",
    "docs/audit_fix_plan.md",
))
SKIP_DIRS = ("scripts/naming_audit/", "scripts/comment_audit/", "scripts/typo_audit/",
             "scripts/audit_plan/")


def _shebang(path: str) -> bool:
    """An extensionless executable script, as `scripts/bench/*/run` are."""
    if "." in os.path.basename(path):
        return False
    try:
        with open(path, "rb") as f:
            return f.read(2) == b"#!"
    except OSError:
        return False


def _files(ctx):
    out = list(ctx.walk(*MD_DIRS, ext=".md"))
    for name in sorted(os.listdir(ctx.root)):
        if name.endswith(".md") and os.path.isfile(os.path.join(ctx.root, name)):
            out.append(os.path.join(ctx.root, name))
    out += ctx.walk(".github", ext=".yml")
    out += ctx.walk(".github", ext=".yaml")
    out += ctx.walk("scripts", ext=".py")
    out += ctx.walk("scripts", ext=".sh")
    out += [p for p in ctx.walk(".docker") if os.path.basename(p) == "Dockerfile"]
    out += [p for p in ctx.walk("scripts/bench") if _shebang(p)]
    for loose in LOOSE:
        p = os.path.join(ctx.root, loose)
        if os.path.exists(p):
            out.append(p)
    keep = []
    for p in dict.fromkeys(out):
        rel = ctx.rel(p)
        if rel in SKIP_FILES or "__pycache__" in rel or rel.startswith(SKIP_DIRS):
            continue
        keep.append(p)
    return sorted(keep)


# ------------------------------------------------------------------ masking

# Every extractor returns a string the same length as the file, with every non-prose character
# replaced by CUT and every newline kept.  Offsets therefore still address the original file, and a
# word touching a CUT can be recognised as a fragment of whatever was cut out — the trick
# `prose_typos.prose_words` uses, made offset-preserving so that line numbers survive.
CUT = pt.CUT

MD_FENCE = re.compile(r"^[ \t]*(```|~~~)[\s\S]*?^[ \t]*\1[^\n]*", re.M)
MD_HTML_COMMENT = re.compile(r"<!--[\s\S]*?-->")
MD_REFDEF = re.compile(r"^\[[^\]\n]+\]:[^\n]*", re.M)
MD_LINK_TARGET = re.compile(r"\]\([^)\n]*\)")
MD_TAG = re.compile(r"</?[A-Za-z][^>\n]*>")
INLINE_CODE = re.compile(r"``[^`]*``|`[^`\n]*`")
# A whitespace-delimited token carrying a path separator, an identifier character, a dotted name
# (`github.repository`, `lean.nvim`), a range (`prev..sha`) or a version digit (`python3`, `lean4`)
# is a name, not an English word — even in the middle of a sentence.  `|` is deliberately not in
# the set: it has to stay visible for table cells to be recognisable.
CODEY = re.compile(r"(?<!\S)\S*(?:[\\/_=$@]|\.\.|::|\w\.\w|[A-Za-z]\d)\S*")
NOISE = re.compile("|".join(x.pattern for x in (
    INLINE_CODE, pt.URL, pt.LATEX, pt.TEXCMD, pt.ANTIQUOT, pt.ESCAPE, MD_TAG, CODEY)))


def _mask(text: str, rx: re.Pattern) -> str:
    """Replace every match of `rx` by CUT, keeping the length and the line breaks."""
    return rx.sub(lambda m: "".join("\n" if c == "\n" else CUT for c in m.group(0)), text)


def _blank(text: str) -> list:
    return ["\n" if c == "\n" else CUT for c in text]


def _keep(buf: list, text: str, start: int, end: int) -> None:
    if start < end:
        buf[start:end] = list(text[start:end])


def _line_starts(text: str) -> list:
    starts = [0]
    for i, c in enumerate(text):
        if c == "\n":
            starts.append(i + 1)
    return starts


# ------------------------------------------------------------------ the extractors

def _markdown(text: str) -> str:
    for rx in (MD_FENCE, MD_HTML_COMMENT, MD_REFDEF, MD_LINK_TARGET):
        text = _mask(text, rx)
    return text


STR_OPEN = re.compile(r"^[a-zA-Z]*('''|\"\"\"|'|\")")
FSTRING_MIDDLE = getattr(tokenize, "FSTRING_MIDDLE", None)


def _python(text: str) -> str:
    buf = _blank(text)
    starts = _line_starts(text)

    def at(pos):
        row, col = pos
        return starts[row - 1] + col if row <= len(starts) else len(text)

    try:
        toks = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except (tokenize.TokenError, SyntaxError, IndentationError, ValueError):
        # An unparseable script contributes nothing rather than half a file of guesses.
        return "".join(buf)
    for tok in toks:
        a, b = at(tok.start), at(tok.end)
        if tok.type == tokenize.COMMENT:
            if tok.start[0] == 1 and tok.string.startswith("#!"):
                continue                        # the shebang is not prose
            _keep(buf, text, a + 1, b)          # everything after the `#`
        elif tok.type == tokenize.STRING:
            m = STR_OPEN.match(tok.string)
            if m and pt.string_prose(tok.string[m.end():len(tok.string) - len(m.group(1))]):
                _keep(buf, text, a + m.end(), b - len(m.group(1)))
        elif FSTRING_MIDDLE is not None and tok.type == FSTRING_MIDDLE:
            # Python 3.12 tokenises an f-string into pieces; the literal text arrives unquoted.
            if pt.string_prose(tok.string):
                _keep(buf, text, a, b)
    return "".join(buf)


QUOTED = re.compile(r"\"(?:[^\"\\\n]|\\.)*\"|'[^'\n]*'")
HEREDOC = re.compile(r"<<[-~]?\s*(['\"]?)([A-Za-z_][A-Za-z0-9_]*)\1")


def _hash_comment(line: str) -> int:
    """Offset just past the `#` that opens a comment on `line`, or -1.

    Quoted spans are masked out first, so `${#n}`, `s/#a/b/` and `"a # b"` are not comments.  A `#`
    opens a comment only at the start of a word, which is the rule in both shell and YAML.
    """
    probe = _mask(line, QUOTED)
    for m in re.finditer(r"#+", probe):
        if m.start() == 0 or probe[m.start() - 1] in " \t":
            return m.end()
    return -1


def _script(text: str) -> str:
    """Shell scripts, Dockerfiles and the `scripts/bench` runners."""
    buf = _blank(text)
    starts = _line_starts(text)
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line, base = lines[i], starts[i]
        if i == 0 and line.startswith("#!"):
            i += 1
            continue
        cut = _hash_comment(line)
        if cut >= 0:
            _keep(buf, text, base + cut, base + len(line))
            if not line[:cut].strip("# \t"):
                i += 1
                continue
            line = line[:cut]                   # a trailing comment: the rest of the line is code
        m = HEREDOC.search(_mask(line, QUOTED))
        if m:
            # The body of a heredoc is the script's own documentation or its `--help` output.
            j = i + 1
            while j < len(lines) and lines[j].strip() != m.group(2):
                j += 1
            _keep(buf, text, starts[min(i + 1, len(starts) - 1)],
                  starts[j] if j < len(starts) else len(text))
            i = j + 1
            continue
        for q in QUOTED.finditer(line):
            if pt.string_prose(q.group(0)[1:-1]):
                _keep(buf, text, base + q.start() + 1, base + q.end() - 1)
        i += 1
    return "".join(buf)


PROSE_KEY = re.compile(r"^(\s*)(?:-\s+)?(?:name|description|title):\s*(.*)$")


def _config(text: str) -> str:
    """YAML and TOML: `#` comments, and the values that are meant to be read by a human."""
    buf = _blank(text)
    starts = _line_starts(text)
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line, base = lines[i], starts[i]
        cut = _hash_comment(line)
        if cut >= 0:
            _keep(buf, text, base + cut, base + len(line))
            i += 1
            continue
        m = PROSE_KEY.match(line)
        if m:
            value = m.group(2)
            if value[:1] in ("|", ">"):
                # a block scalar: every following line indented past the key belongs to it
                indent = len(m.group(1))
                i += 1
                while i < len(lines) and (not lines[i].strip()
                                          or len(lines[i]) - len(lines[i].lstrip()) > indent):
                    _keep(buf, text, starts[i], starts[i] + len(lines[i]))
                    i += 1
                continue
            _keep(buf, text, base + len(line) - len(value), base + len(line))
        i += 1
    return "".join(buf)


def _prose(path: str, text: str) -> str:
    ext = os.path.splitext(path)[1]
    if ext == ".md":
        masked = _markdown(text)
    elif ext == ".py":
        masked = _python(text)
    elif ext in (".yml", ".yaml", ".toml"):
        masked = _config(text)
    else:
        masked = _script(text)
    return _mask(masked, NOISE)


# ------------------------------------------------------------------ reading the masked text

def _tokens(ctx, masked: str):
    """(word, offset) for each word of the prose, dropping fragments of what was masked out."""
    for w, off in ctx.words(masked):
        end = off + len(w)
        if off and masked[off - 1] == CUT:
            continue
        if end < len(masked) and masked[end] == CUT:
            continue
        yield w, off


def _line_at(text: str, at: int) -> str:
    start = text.rfind("\n", 0, at) + 1
    end = text.find("\n", at)
    return text[start:len(text) if end == -1 else end]


QUOTE = 70


def _quote(text: str, at: int) -> str:
    """The offending line, safe to drop into a markdown table cell.

    `excerpt` keeps the head of the line, which shows the wrong thing when the word sits far down a
    long markdown table row, so a word past the cut gets a window centred on it instead.
    """
    start = text.rfind("\n", 0, at) + 1
    if at - start < QUOTE - 12:
        s = excerpt(text, at, QUOTE)
    else:
        line = _line_at(text, at)
        lo = at - start - QUOTE // 2
        s = "…" + line[lo:lo + QUOTE] + ("…" if lo + QUOTE < len(line) else "")
    return " ".join(s.replace("|", r"\|").replace("`", "'").split())


# ------------------------------------------------------------------ how the surface spells things

def _forced(masked: str, at: int) -> bool:
    """True if a capital at `at` is forced by position rather than chosen by the writer."""
    i = at - 1
    while i >= 0 and masked[i] in " \t*+->#(\"'[":
        i -= 1
    if i < 0 or masked[i] in ("\n", CUT):
        # Start of a line, or the start of what survived masking — which is where a YAML value
        # begins, and `name: Extract cache key` capitalises its first word whatever the word is.
        return True
    return masked[i] in ".!?:;|"          # end of a sentence, or the start of a table cell


def _compound(masked: str, at: int, word: str) -> bool:
    """True if the word is glued into a compound name: `zulip-contact`, `--deps-json`."""
    end = at + len(word)
    return ((at > 0 and masked[at - 1] in "-_")
            or (end < len(masked) and masked[end] in "-_"))


def _invocation(line: str) -> bool:
    """A line of one or two words beside masked-out code is a command, not a sentence.

    `python verify_version_tags.py v4.24.1` in a usage block is three names, and the `python` in it
    is the interpreter, correctly lower case; `Print all errors of the python style linter` is a
    sentence, and the `python` in it is the language.
    """
    return CUT in line and len(re.findall(r"[A-Za-z]{2,}", line.replace(CUT, " "))) <= 2


def _uninformative(line: str) -> bool:
    """A heading, a shouty line or a title-cased one: capitals there say nothing about the word."""
    s = line.replace(CUT, " ").strip()
    if s.startswith("#"):
        return True
    letters = [c for c in s if c.isalpha()]
    if letters and sum(c.isupper() for c in letters) / len(letters) > 0.6:
        return True
    words = [w for w in re.findall(r"[A-Za-z][A-Za-z'-]*", s) if len(w) > 2]
    return len(words) >= 3 and sum(w[0].isupper() for w in words) / len(words) >= 0.8


def _spellings(ctx, scanned):
    """How this surface spells each word: (evidence, uses, files, ever-lower-case).

    `evidence` counts only the positions where the capital was a choice; `uses` counts every
    occurrence of every exact spelling, and decides whether a rival spelling is a slip or a second,
    legitimate usage; `lower_seen` is every word that is written in lower case somewhere at all.
    Only `lower_seen`, which M1 uses to recognise names, counts words inside compounds.
    """
    evidence = collections.defaultdict(collections.Counter)
    uses: collections.Counter = collections.Counter()
    files = collections.defaultdict(set)
    lower_seen = set()
    for rel, _text, masked, _idents in scanned:
        for w, off in _tokens(ctx, masked):
            if not w.isalpha():
                continue
            if w == w.lower():
                lower_seen.add(w)
            if _compound(masked, off, w):
                continue
            uses[w] += 1
            if len(w) < 3 or _uninformative(_line_at(masked, off)):
                continue
            if w[0].isupper() and _forced(masked, off):
                continue
            evidence[w.lower()][w] += 1
            files[w].add(rel)
    return evidence, uses, files, lower_seen


MIN_USES = 8        # uses of the dominant spelling before it counts as settled
MIN_FILES = 2       # ... in at least this many files, so one author's habit does not make a rule
MIN_KNOWN = 12      # ... and the word must be one the repository uses (here plus the corpus)
MAX_SLIPS = 3       # a rival spelling used more often than this is a usage, not a slip


def _settled(ctx, evidence, files):
    """{lowercased word: (spelling, uses of it, uses of the word)} for the settled proper nouns."""
    out = {}
    for key, counter in evidence.items():
        spelling, n = counter.most_common(1)[0]
        total = sum(counter.values())
        if spelling == spelling.lower():
            continue                                  # the repository writes it in lower case
        if n < MIN_USES or len(files[spelling]) < MIN_FILES:
            continue
        if total + ctx.freq.get(key, 0) < MIN_KNOWN:
            continue
        out[key] = (spelling, n, total)
    return out


# ------------------------------------------------------------------ the two checks

def _misspellings(ctx, scanned, lower_seen):
    out = []
    for rel, text, masked, idents in scanned:
        seen = set()
        for w, off in _tokens(ctx, masked):
            # identifiers that escaped a code span: internal capitals, or all caps
            if (w.isupper() and len(w) > 1) or re.search(r"[a-z][A-Z]", w):
                continue
            # a word this surface only ever capitalises is a name, as in the author list of
            # `README.md` — the rule `prose_typos.scan` applies to the comment corpus
            if w[0].isupper() and w.lower() not in lower_seen:
                continue
            hit = ctx.suggest(w, idents)
            if hit is None:
                continue
            corr, dist, uses = hit
            line = line_of(text, off)
            if (w.lower(), line) in seen:
                continue
            seen.add((w.lower(), line))
            out.append(Finding(
                SURFACE, "M1", w, rel, line,
                f"`{w}` is not a word Mathlib uses; probably `{corr}` "
                f'({uses} uses in the comment corpus, {dist} edit away): "{_quote(text, off)}"',
                ctx.confidence(dist, uses)))
    return out


def _miscased(ctx, scanned, settled, uses):
    out = []
    for rel, text, masked, idents in scanned:
        seen = set()
        for w, off in _tokens(ctx, masked):
            hit = settled.get(w.lower())
            if hit is None or w == hit[0] or w.isupper() or uses[w] > MAX_SLIPS:
                continue
            if _compound(masked, off, w):
                continue
            # A Python docstring is the one place where prose and code are genuinely mixed: it
            # documents parameters by name and shows worked examples (`dag: The DAG to traverse`),
            # so there a word that is also an identifier of the file is a name, not a mis-casing.
            if rel.endswith(".py") and w.lower() in idents:
                continue
            spelling, n, total = hit
            line = line_of(text, off)
            if (w.lower(), line) in seen:
                continue
            seen.add((w.lower(), line))
            share = n / total
            conf = "high" if share >= 0.95 and n >= 20 else "medium" if share >= 0.85 else "low"
            out.append(Finding(
                SURFACE, "M2", w, rel, line,
                f"written `{w}`, but the repository writes this word `{spelling}` "
                f'({n} of {total} uses here): "{_quote(text, off)}"', conf))
    return out


# ------------------------------------------------------------------ entry point

def collect(ctx):
    scanned = []
    for path in _files(ctx):
        text = ctx.read(path)
        if not text:
            continue
        masked = _prose(path, text)
        # Everything the extractor refused is code: its identifiers must not be read as prose.
        idents = set()
        pt.code_fragments("".join(c if m == CUT else " " for c, m in zip(text, masked)), idents)
        scanned.append((ctx.rel(path), text, masked, idents))
    evidence, uses, files, lower_seen = _spellings(ctx, scanned)
    settled = _settled(ctx, evidence, files)
    ctx.say(f"plaintext: {len(scanned)} files, {len(settled)} words with a settled capitalisation")
    findings = _misspellings(ctx, scanned, lower_seen) + _miscased(ctx, scanned, settled, uses)
    findings.sort(key=lambda f: (f["cat"], f["file"], f["line"]))
    return findings
