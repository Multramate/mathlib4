#!/usr/bin/env python3
"""
Build `docs/tickets.md` — the open findings of `docs/typos.md`, grouped into batches sized for
individual pull requests.

The grouping rule comes from review practice: a machine-generated pull request should not edit more
than **10 files**, because a reviewer forms a separate judgement about each one.  The exception is a
pull request applying a **single mechanical substitution** — the same wrong spelling replaced by the
same right one everywhere — where reading the whole diff is reading one decision; those may span up
to **100 files**.  So a substitution touching more than ten files becomes a ticket of its own, split
at a hundred, and everything else is packed in path order into tickets of at most ten files, which
keeps a ticket inside one area of the library.

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
import sys

UNIFORM_CAP, BESPOKE_CAP = 100, 10
CELL = re.compile(r"(?<!\\)\|")
STATUSES = ("open", "confirmed", "fp", "fixed", "wontfix")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")

# Categories where every row applies the identical textual substitution, so one ticket is one
# decision however many files it spans.
MECHANICAL = {
    "DOC-A1", "DOC-A2", "DOC-A3", "DOC-A5", "DOC-B4", "DOC-C1", "DOC-C2", "DOC-D3", "DOC-D4",
    "NAME-B3", "NAME-C1", "NAME-C2", "NAME-D2",
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
    "NAME-A6": "chore: lowerCamelCase for data-valued instances",
    "NAME-A7": "chore: lowerCamelCase for instance names",
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
                         "detail": cells[3], "note": cells[4]})
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


def change_key(r: dict) -> tuple:
    if r["cat"] in ("DOC-C3",):
        return (r["name"],)
    quoted = re.findall(r"`([^`]*)`", r["detail"])
    if len(quoted) >= 2:
        return (quoted[0], quoted[1])
    return (quoted[0],) if quoted else (r["name"],)


def describe(key: tuple) -> str:
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
            groups = collections.OrderedDict()
            for r in crows:
                groups.setdefault(change_key(r), []).append(r)
            leftovers = []
            for key, grp in groups.items():
                files = list(dict.fromkeys(r["file"] for r in grp))
                if len(files) <= BESPOKE_CAP:
                    leftovers.append((key, grp))
                    continue
                parts = (len(files) + UNIFORM_CAP - 1) // UNIFORM_CAP
                for i in range(0, len(files), UNIFORM_CAP):
                    chunk = set(files[i:i + UNIFORM_CAP])
                    sub = [r for r in grp if r["file"] in chunk]
                    tickets.append({"tier": tier, "cat": cat, "cat_title": grp[0]["cat_title"],
                                    "kind": "one substitution", "changes": [describe(key)],
                                    "files": sorted(chunk), "rows": sub,
                                    "part": i // UNIFORM_CAP + 1, "parts": parts,
                                    "sweep": sweep_of(sub)})
            cf, cr, ck = [], [], []
            for key, grp in sorted(leftovers, key=lambda kg: kg[1][0]["file"]):
                gf = list(dict.fromkeys(r["file"] for r in grp))
                if cf and len(set(cf) | set(gf)) > BESPOKE_CAP:
                    tickets.append({"tier": tier, "cat": cat, "cat_title": cr[0]["cat_title"],
                                    "kind": "mixed", "changes": [describe(k) for k in ck],
                                    "files": sorted(set(cf)), "rows": cr, "part": 0, "parts": 0,
                                    "sweep": sweep_of(cr)})
                    cf, cr, ck = [], [], []
                cf.extend(gf)
                cr.extend(grp)
                ck.append(key)
            if cr:
                tickets.append({"tier": tier, "cat": cat, "cat_title": cr[0]["cat_title"],
                                "kind": "mixed", "changes": [describe(k) for k in ck],
                                "files": sorted(set(cf)), "rows": cr, "part": 0, "parts": 0,
                                "sweep": sweep_of(cr)})

    order = {"T1": 0, "T2": 1, "T3": 2}
    tickets.sort(key=lambda t: (order[t["tier"]], t["cat"], t["files"][0]))
    seq = collections.Counter()
    for t in tickets:
        seq[t["tier"]] += 1
        t["id"] = f"{t['tier']}-{seq[t['tier']]:03d}"
        t["title"] = title_for(t["cat"])
        if t["parts"] > 1:
            t["title"] += f" ({t['part']}/{t['parts']})"
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
    L.append("At most **10 files** per ticket — a reviewer forms a separate judgement about each file.")
    L.append("A ticket applying a **single mechanical substitution** may span up to **100 files**,")
    L.append("because reading that whole diff is reading one decision; the `Kind` column says which")
    L.append("rule a ticket is under. Tickets are packed in path order, so one ticket stays inside one")
    L.append("area of the library.")
    L.append("")
    L.append("Two kinds of ticket cost more than the files they list. A **declaration rename** moves")
    L.append("every call site: do it with `@[deprecated (since := \"…\")] alias old := new` so the pull")
    L.append("request stays in the declaring file, and treat `Sweep` as the size of the follow-up. A")
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
        L.append("| Location | Finding | Detail |")
        L.append("|---|---|---|")
        for r in sorted(t["rows"], key=lambda r: (r["file"], r["line"])):
            L.append(f"| `{r['file']}:{r['line']}` | `{md_escape(r['name'])}` | "
                     f"{md_escape(r['detail'])} |")
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

    bad = [t for t in tickets if t["kind"] != "one substitution" and len(t["files"]) > BESPOKE_CAP]
    worse = [t for t in tickets if len(t["files"]) > UNIFORM_CAP]
    print(f"{len(tickets)} tickets -> {out}")
    for tier in ("T1", "T2", "T3"):
        tt = [t for t in tickets if t["tier"] == tier]
        print(f"  {tier}: {len(tt):4} tickets, {sum(len(t['rows']) for t in tt):5} findings, "
              f"{len({f for t in tt for f in t['files']}):5} files")
    print(f"  over the 10-file cap: {len(bad)}; over the 100-file cap: {len(worse)}")
    if bad or worse:
        sys.exit(1)


if __name__ == "__main__":
    main()
