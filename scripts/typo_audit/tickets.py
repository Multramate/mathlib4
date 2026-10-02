#!/usr/bin/env python3
"""
Build `docs/tickets.md` — the open findings of `docs/typos.md`, grouped into tickets that are each
meant to become one pull request.

A ticket is one category in one tier: every finding of that kind, however many files it touches.
There is no file cap — a reviewer reads one kind of change throughout, so splitting a category only
multiplies the pull requests.

Tickets are tiered, because several thousand findings is a backlog rather than a plan:

  T1  findings already marked `confirmed` in `typos.md` — checked by hand, ready to write today
  T2  untriaged findings in mechanical categories — one skim per ticket, not one judgement per row
  T3  untriaged findings needing a decision at every site — triage them in `typos.md` first

Two kinds of finding cost more than the file they sit in:

  * a **declaration rename** moves every call site.  Mathlib keeps the old name working with
    `@[deprecated (since := "...")] alias old := new`, so the pull request edits only the declaring
    file and the call sites become a later sweep.  `Sweep` bounds that follow-up; it is a token
    match, so a name whose last component is an ordinary word reports a number far larger than the
    truth — which is itself the signal that the alias is mandatory.
  * a **file rename** moves every `import` of it, plus the entry in `Mathlib.lean`.  There `Sweep`
    counts the importing files exactly, and they must all be in the same pull request, because a
    dangling import does not compile.

Usage:
    python3 scripts/typo_audit/tickets.py [--root .] [--out docs/tickets.md] [--no-sweep]
"""
from __future__ import annotations

import argparse
import collections
import datetime
import os
import re

CELL = re.compile(r"(?<!\\)\|")
STATUSES = ("open", "confirmed", "fp", "fixed", "wontfix")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")

# Categories where every row applies the identical textual substitution, so one ticket is one
# decision however many files it spans.  No declaration-name category belongs here: whether
# `preserves_limit_cone` means `PreservesLimit`, or `pow_succ` should say `add_one`, depends on the
# statement at every site (#44329 was such a false positive).
MECHANICAL = {
    "DOC-A1", "DOC-A2", "DOC-A3", "DOC-A5", "DOC-B4", "DOC-C1", "DOC-C2", "DOC-D3", "DOC-D4",
    "TEXT-2", "DATA-2",
}

PR_TITLE = {
    "DOC-A1": "chore: normalise module docstring section headings",
    "DOC-A2": "chore: drop trailing punctuation from module docstring headings",
    "DOC-A3": "chore: use the standard module docstring section heading",
    "DOC-A4": "chore: fix module docstring heading structure",
    "DOC-A5": "chore: fix bibliography citation keys",
    "DOC-B1": "chore: fix stale file cross-references in comments",
    "DOC-B2": "chore: fix stale module cross-references in comments",
    "DOC-B3": "chore: fix stale library note references",
    "DOC-B4": "chore: update Lean 3 identifiers in docstrings",
    "DOC-C1": "chore: use Mathlib's usual spelling in comments",
    "DOC-C2": "chore: capitalise proper nouns in comments",
    "DOC-C3": "chore: fix doubled words in comments",
    "DOC-D1": "chore: use Unicode notation in comments",
    "DOC-D2": "chore: close unbalanced code spans in docstrings",
    "DOC-D3": "chore: normalise comment marker casing",
    "DOC-D4": "chore: add a space after `--` in comments",
    "NAME-A1": "chore: lowerCamelCase tokens in theorem names",
    "NAME-A2": "chore: UpperCamelCase for Prop-valued definitions",
    "NAME-A3": "chore: UpperCamelCase for Type-valued definitions",
    "NAME-A4": "chore: lowerCamelCase for data definitions",
    "NAME-A5": "chore: UpperCamelCase for structures and classes",
    "NAME-A6": "chore: drop the names of snake_case data instances",
    "NAME-A7": "chore: drop the names of UpperCamelCase instances",
    "NAME-A8": "chore: fix casing of structure fields",
    "NAME-A9": "chore: fix casing of inductive constructors",
    "NAME-A10": "chore: remove underscores from namespaces",
    "NAME-A11": "chore: remove stray underscores from names",
    "NAME-B1": "chore: fix typos in declaration names",
    "NAME-B2": "chore: fix unknown camelCase tokens in names",
    "NAME-B3": "chore: un-flatten camelCase in names",
    "NAME-C1": "chore: use camelCase spellings in names",
    "NAME-C2": "chore: replace outdated name components",
    "NAME-D1": "chore: align names with their statements",
    "NAME-D2": "chore: name `n + 1` statements without `succ`",
    "NAME-E1": "chore: deduplicate identical statements",
    "NAME-F1": "chore: fix typos in comments and docstrings",
}
PREFIX_TITLE = {
    "STR": "chore: fix typos in error messages and other string literals",
    "TREE": "chore: fix typos in comments outside Mathlib",
    "PATH": "chore: fix misspelled file names",
    "TEXT": "chore: fix typos in documentation and scripts",
    "DATA": "chore: fix typos in the curated data files",
    "DEP": "chore: fix typos in deprecation messages",
    "VOCAB": "chore: fix typos in library note titles and notation",
}

TIER_BLURB = {
    "T1": ("Ready to write", "Findings already marked `confirmed` in `typos.md`: someone has "
           "checked them by hand. Start here."),
    "T2": ("Mechanical, needs a skim", "Untriaged findings in categories where every row is the "
           "same substitution. A ticket is one decision plus a read-through."),
    "T3": ("Needs triage first", "Untriaged findings needing a judgement at every site. Triage "
           "them in `typos.md` before opening a pull request; they graduate to T1 as you do."),
}


def parse_typos(path: str) -> tuple:
    rows, titles, cat = [], {}, None
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"### ([A-Z]+-[A-Z]?\d+): (.+)", line)
            if m:
                cat, titles[m.group(1)] = m.group(1), m.group(2).strip()
                continue
            if cat is None or not line.startswith("| "):
                continue
            cells = [c.strip() for c in CELL.split(line.rstrip("\n"))[1:-1]]
            if len(cells) < 5 or cells[0] not in STATUSES:
                continue
            loc = cells[2].strip("`")
            file, _, lineno = loc.rpartition(":")
            rows.append({"cat": cat, "cat_title": titles[cat], "status": cells[0],
                         "name": cells[1].strip("`"), "file": file or loc,
                         "line": int(lineno) if lineno.isdigit() else 0,
                         "detail": cells[3], "note": cells[4].replace("\\|", "|")})
    return rows, titles


def is_decl_rename(cat: str) -> bool:
    return cat.startswith("NAME-") and cat != "NAME-F1"


def is_file_rename(cat: str) -> bool:
    return cat.startswith("PATH-")


def name_sweep(root: str, wanted: set) -> dict:
    """{final name component: files mentioning it} — the bound on a declaration rename's sweep."""
    hits = collections.defaultdict(set)
    for d in ("Mathlib", "Archive", "Counterexamples"):
        for dp, _dn, fn in os.walk(os.path.join(root, d)):
            for f in sorted(fn):
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, root).replace(os.sep, "/")
                with open(p, encoding="utf-8") as fh:
                    for tok in set(TOKEN.findall(fh.read())):
                        if tok in wanted:
                            hits[tok].add(rel)
    return hits


def import_sweep(root: str) -> dict:
    """{module name: files importing it} — a file rename must move all of these at once."""
    hits = collections.defaultdict(set)
    rx = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)")
    for d in ("Mathlib", "Archive", "Counterexamples", "MathlibTest", "Cache", "Wanted"):
        base = os.path.join(root, d)
        if not os.path.isdir(base):
            continue
        for dp, _dn, fn in os.walk(base):
            for f in sorted(fn):
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, root).replace(os.sep, "/")
                with open(p, encoding="utf-8") as fh:
                    for m in rx.finditer(fh.read()):
                        hits[m.group(1)].add(rel)
    for top in ("Mathlib.lean", "Archive.lean", "Counterexamples.lean"):
        p = os.path.join(root, top)
        if os.path.exists(p):
            with open(p, encoding="utf-8") as fh:
                for m in rx.finditer(fh.read()):
                    hits[m.group(1)].add(top)
    return hits


# A replacement written into the `Note` column by whoever triaged the row, e.g. "should be
# `entirety`" or "→ `exists_isMaximumClique`".  It overrides the scanner's guess in `Detail`.
NOTE_FIX = re.compile(r"(?:should be|→|fix:)\s*`([^`]+)`")
# ... or, for a duplicate statement (`NAME-E1`), which of the two names to deprecate.
NOTE_DEPRECATE = re.compile(r"^deprecate\s*`([^`]+)`")


# Categories whose finding is a word written twice in a row; the fix deletes one copy.
DOUBLED = {"DOC-C3", "DATA-Y2", "STR-S3"}


def change_key(r: dict) -> tuple:
    if r["cat"] in DOUBLED:
        return ("doubled", r["name"])
    dep = NOTE_DEPRECATE.search(r["note"])
    if dep:
        return ("deprecate", dep.group(1))
    fix = NOTE_FIX.search(r["note"])
    if fix:
        return (r["name"], fix.group(1))
    quoted = re.findall(r"`([^`]*)`", r["detail"])
    if len(quoted) >= 2:
        return (quoted[0], quoted[1])
    return (quoted[0],) if quoted else (r["name"],)


def describe(key: tuple) -> str:
    if key[0] == "doubled":
        return f"`{key[1]} {key[1]}` → `{key[1]}`"
    if key[0] == "deprecate":
        return f"deprecate `{key[1]}`"
    return f"`{key[0]}` → `{key[1]}`" if len(key) >= 2 else f"`{key[0]}`"


def tier_of(r: dict) -> str:
    if r["status"] == "confirmed":
        return "T1"
    return "T2" if r["cat"] in MECHANICAL else "T3"


def title_for(cat: str) -> str:
    if cat in PR_TITLE:
        return PR_TITLE[cat]
    return PREFIX_TITLE.get(cat.split("-")[0], "chore: fix typos")


def build(live, names, imports):
    def sweep_of(rs):
        cat = rs[0]["cat"]
        if is_decl_rename(cat):
            t = set()
            for r in rs:
                t |= names.get(r["name"].split(".")[-1], set())
            return len(t)
        if is_file_rename(cat):
            t = set()
            for r in rs:
                mod = r["file"][:-5].replace("/", ".") if r["file"].endswith(".lean") else None
                if mod:
                    t |= imports.get(mod, set())
            return len(t)
        return 0

    tickets = []
    for tier in ("T1", "T2", "T3"):
        trows = [r for r in live if tier_of(r) == tier]
        for cat in list(dict.fromkeys(r["cat"] for r in trows)):
            crows = sorted((r for r in trows if r["cat"] == cat),
                           key=lambda r: (r["file"], r["line"]))
            keys = list(dict.fromkeys(change_key(r) for r in crows))
            tickets.append({"tier": tier, "cat": cat, "cat_title": crows[0]["cat_title"],
                            "kind": "one substitution" if len(keys) == 1 else "mixed",
                            "changes": [describe(k) for k in keys],
                            "files": sorted({r["file"] for r in crows}), "rows": crows,
                            "sweep": sweep_of(crows)})

    order = {"T1": 0, "T2": 1, "T3": 2}
    tickets.sort(key=lambda t: (order[t["tier"]], t["cat"], t["files"][0]))
    seq = collections.Counter()
    for t in tickets:
        seq[t["tier"]] += 1
        t["id"] = f"{t['tier']}-{seq[t['tier']]:03d}"
        t["title"] = title_for(t["cat"])
    return tickets


def md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def render(tickets, live, out_path, swept):
    today = datetime.date.today().isoformat()
    L = []
    L.append("# Mathlib typo tickets")
    L.append("")
    L.append(f"_Generated by `scripts/typo_audit/tickets.py` on {today} from "
             f"[`typos.md`](typos.md); {len(live)} open findings in {len(tickets)} tickets._")
    L.append("")
    L.append("**Each ticket is one pull request.** Work a ticket by opening `typos.md`, making the")
    L.append("edits its rows describe, and marking those rows `fixed`; the row disappears from both")
    L.append("documents on the next run.")
    L.append("")
    L.append("## Sizing")
    L.append("")
    L.append("A ticket is one category in one tier — every finding of that kind, however many files")
    L.append("it touches. There is no file cap: a reviewer reads one kind of change throughout, so")
    L.append("splitting a category would only multiply the pull requests.")
    L.append("")
    L.append("Two kinds of ticket cost more than the files they list. A **declaration rename** moves")
    L.append("every call site: keep the old name with `@[deprecated (since := \"…\")] alias old := new`")
    L.append("for a theorem, or `@[deprecated new (since := \"…\")] abbrev old := new` for a `def`, so the")
    L.append("pull request stays in the declaring file; a named instance instead loses its name, with no")
    L.append("alias. Treat `Sweep` as the size of the follow-up. A")
    L.append("**file rename** (`PATH-*`) moves every `import` of it and the entry in `Mathlib.lean`,")
    L.append("and those must all be in the same pull request, because a dangling import does not")
    L.append("compile — for those, `Sweep` is part of the ticket, not a follow-up.")
    L.append("")
    L.append("## Tiers")
    L.append("")
    for tier in ("T1", "T2", "T3"):
        name, blurb = TIER_BLURB[tier]
        tt = [t for t in tickets if t["tier"] == tier]
        L.append(f"- **{tier} — {name}.** {blurb}  ")
        L.append(f"  {len(tt)} tickets, {sum(len(t['rows']) for t in tt)} findings, "
                 f"{len({f for t in tt for f in t['files']})} files.")
    L.append("")

    for tier in ("T1", "T2", "T3"):
        tt = [t for t in tickets if t["tier"] == tier]
        if not tt:
            continue
        L.append(f"## {tier} — {TIER_BLURB[tier][0]}")
        L.append("")
        L.append("| Ticket | Suggested PR title | Category | Change | Files | Rows | Sweep |")
        L.append("|---|---|---|---|---:|---:|---:|")
        for t in tt:
            ch = t["changes"][0] if len(t["changes"]) == 1 else f"{len(t['changes'])} substitutions"
            L.append(f"| [{t['id']}](#{t['id'].lower()}) | {md_escape(t['title'])} | {t['cat']} | "
                     f"{md_escape(ch)} | {len(t['files'])} | {len(t['rows'])} | "
                     f"{t['sweep'] or '—'} |")
        L.append("")

    L.append("## Tickets")
    L.append("")
    for t in tickets:
        L.append(f"### {t['id']}")
        L.append("")
        L.append(f"**{t['title']}** — {t['cat_title']} (`{t['cat']}`), {t['kind']}, "
                 f"{len(t['files'])} file(s), {len(t['rows'])} finding(s).")
        L.append("")
        if is_file_rename(t["cat"]) and t["sweep"]:
            L.append(f"File rename: {t['sweep']} file(s) import these modules and must be updated in "
                     f"the same pull request, along with the entry in `Mathlib.lean`.")
            L.append("")
        elif t["sweep"]:
            L.append(f"Declaration rename: add a deprecated alias so the pull request stays in the "
                     f"declaring file; up to {t['sweep']} file(s) mention these names and are a "
                     f"follow-up sweep.")
            L.append("")
        L.append("Change: " + (t["changes"][0] if len(t["changes"]) == 1
                               else ", ".join(t["changes"])))
        L.append("")
        L.append("| Location | Finding | Detail | Note |")
        L.append("|---|---|---|---|")
        for r in sorted(t["rows"], key=lambda r: (r["file"], r["line"])):
            L.append(f"| `{r['file']}:{r['line']}` | `{md_escape(r['name'])}` | "
                     f"{md_escape(r['detail'])} | {md_escape(r['note'])} |")
        L.append("")
    if not swept:
        L.append("_Sweep sizes were not computed (`--no-sweep`)._")
        L.append("")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(L))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default=None)
    ap.add_argument("--no-sweep", action="store_true")
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    out = args.out or os.path.join(root, "docs", "tickets.md")

    rows, _titles = parse_typos(os.path.join(root, "docs", "typos.md"))
    live = [r for r in rows if r["status"] in ("open", "confirmed")]
    print(f"{len(rows)} findings, {len(live)} still open")

    names, imports = {}, {}
    if not args.no_sweep:
        wanted = {r["name"].split(".")[-1] for r in live if is_decl_rename(r["cat"])}
        wanted = {w for w in wanted if len(w) >= 3}
        print(f"indexing {len(wanted)} name components ...")
        names = name_sweep(root, wanted)
        if any(is_file_rename(r["cat"]) for r in live):
            print("indexing imports ...")
            imports = import_sweep(root)

    tickets = build(live, names, imports)
    render(tickets, live, out, not args.no_sweep)

    print(f"{len(tickets)} tickets -> {out}")
    for tier in ("T1", "T2", "T3"):
        tt = [t for t in tickets if t["tier"] == tier]
        print(f"  {tier}: {len(tt):4} tickets, {sum(len(t['rows']) for t in tt):5} findings, "
              f"{len({f for t in tt for f in t['files']}):5} files")


if __name__ == "__main__":
    main()
