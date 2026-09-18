#!/usr/bin/env python3
"""
Turn the two audit documents into a plan of PR-sized batches.

`docs/naming_audit.md` and `docs/comment_audit.md` between them list several thousand findings.
That is a backlog, not a plan: nobody can open a pull request against "7000 rows".  This script
reads both documents and groups their still-open findings into batches, each of which is meant to
become one pull request.

The grouping rule comes from review practice: a machine-generated pull request should not edit more
than ten files, because a reviewer has to form a separate judgement about each one.  The exception
is a pull request that applies a single mechanical substitution — the same wrong spelling replaced
by the same right one everywhere — where reviewing the whole diff is reviewing one decision.  Those
may span up to a hundred files.  So:

  * a substitution that touches MORE than ten files becomes a batch of its own, split at a hundred;
  * everything else is packed, in path order, into batches of at most ten files, which keeps a
    batch inside one area of the library.

The batches are sorted into three tiers, because most of the backlog is not ready to be written up:

  T1  findings already marked `confirmed` in the audit — checked by hand, ready to write today.
  T2  untriaged findings in mechanical categories (heading spellings, minority spellings, marker
      casing, …) — one skim per batch rather than one judgement per row.
  T3  untriaged findings that need a decision at every site — triage them in the audit first.

A naming-audit finding is a rename, and Mathlib renames keep the old name working with
`@[deprecated (since := ...)] alias old := new`.  The pull request therefore edits only the file
that declares the name, and the use sites become a later mechanical sweep.  The `sweep` column
records how many files mention the name at all, as an upper bound on that follow-up: it is a token
match, so a name whose last component is a common word (`map`, `symm`, `trans`) reports a number
far larger than the real count, which is itself the signal that the rename needs the alias.

Usage:
    python3 scripts/audit_plan/fix_plan.py [--root .] [--out docs/audit_fix_plan.md] [--no-sweep]
"""
from __future__ import annotations

import argparse
import collections
import datetime
import json
import os
import re
import sys

UNIFORM_CAP = 100      # files in a one-substitution batch
BESPOKE_CAP = 10       # files in any other batch

CELL = re.compile(r"(?<!\\)\|")
STATUSES = ("open", "confirmed", "fp", "fixed", "wontfix")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")

# Categories where every row applies the identical textual substitution.
MECHANICAL = {
    ("comment", "A1"), ("comment", "A2"), ("comment", "A3"), ("comment", "A5"),
    ("comment", "B4"), ("comment", "C1"), ("comment", "C2"), ("comment", "D3"),
    ("comment", "D4"),
    ("naming", "B3"), ("naming", "C1"), ("naming", "C2"), ("naming", "D2"),
}

PR_TITLE = {
    ("comment", "A1"): "chore: normalise module docstring section headings",
    ("comment", "A2"): "chore: drop trailing punctuation from module docstring headings",
    ("comment", "A3"): "chore: use the standard module docstring section heading",
    ("comment", "A4"): "chore: fix module docstring heading structure",
    ("comment", "A5"): "chore: fix bibliography citation keys",
    ("comment", "B1"): "chore: fix stale file cross-references in comments",
    ("comment", "B2"): "chore: fix stale module cross-references in comments",
    ("comment", "B3"): "chore: fix stale library note references",
    ("comment", "B4"): "chore: update Lean 3 identifiers in docstrings",
    ("comment", "C1"): "chore: use Mathlib's usual spelling in comments",
    ("comment", "C2"): "chore: capitalise proper nouns in comments",
    ("comment", "C3"): "chore: fix doubled words in comments",
    ("comment", "D1"): "chore: use Unicode notation in comments",
    ("comment", "D2"): "chore: close unbalanced code spans in docstrings",
    ("comment", "D3"): "chore: normalise comment marker casing",
    ("comment", "D4"): "chore: add a space after `--` in comments",
    ("naming", "A1"): "chore: lowerCamelCase tokens in theorem names",
    ("naming", "A2"): "chore: UpperCamelCase for Prop-valued definitions",
    ("naming", "A3"): "chore: UpperCamelCase for Type-valued definitions",
    ("naming", "A4"): "chore: lowerCamelCase for data definitions",
    ("naming", "A5"): "chore: UpperCamelCase for structures and classes",
    ("naming", "A6"): "chore: lowerCamelCase for data-valued instances",
    ("naming", "A7"): "chore: lowerCamelCase for instance names",
    ("naming", "A8"): "chore: fix casing of structure fields",
    ("naming", "A9"): "chore: fix casing of inductive constructors",
    ("naming", "A10"): "chore: remove underscores from namespaces",
    ("naming", "A11"): "chore: remove stray underscores from names",
    ("naming", "B1"): "chore: fix typos in declaration names",
    ("naming", "B2"): "chore: fix unknown camelCase tokens in names",
    ("naming", "B3"): "chore: un-flatten camelCase in names",
    ("naming", "C1"): "chore: use camelCase spellings in names",
    ("naming", "C2"): "chore: replace outdated name components",
    ("naming", "D1"): "chore: align names with their statements",
    ("naming", "D2"): "chore: name `n + 1` statements without `succ`",
    ("naming", "E1"): "chore: deduplicate identical statements",
    ("naming", "F1"): "chore: fix typos in comments and docstrings",
}

TIER_BLURB = {
    "T1": ("Ready to write", "Findings already marked `confirmed` in the audit: someone has "
           "checked them by hand. Start here."),
    "T2": ("Mechanical, needs a skim", "Untriaged findings in categories where every row is the "
           "same substitution. A batch is one decision plus a read-through, not a per-row triage."),
    "T3": ("Needs triage first", "Untriaged findings that need a judgement at every site. Triage "
           "them in the audit document (set `Status` to `confirmed` or `fp`) before opening a PR; "
           "they graduate to T1 as you do."),
}


# ---------------------------------------------------------------------------- reading the audits

def parse_audit(path: str, audit: str) -> list:
    rows, cat, titles = [], None, {}
    if not os.path.exists(path):
        print(f"warning: {path} not found", file=sys.stderr)
        return rows
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"### ([A-Z]\d+): (.+)", line)
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
            rows.append({"audit": audit, "cat": cat, "cat_title": titles[cat],
                         "status": cells[0], "name": cells[1].strip("`"),
                         "file": file or loc, "line": int(lineno) if lineno.isdigit() else 0,
                         "detail": cells[3], "note": cells[4]})
    return rows


def sweep_index(root: str, wanted: set) -> dict:
    """{name component: [files mentioning it]} — the upper bound on a rename's follow-up sweep."""
    hits = collections.defaultdict(list)
    for d in ("Mathlib", "Archive", "Counterexamples"):
        for dp, _dn, fn in os.walk(os.path.join(root, d)):
            for f in sorted(fn):
                if not f.endswith(".lean"):
                    continue
                path = os.path.join(dp, f)
                rel = os.path.relpath(path, root).replace(os.sep, "/")
                with open(path, encoding="utf-8") as fh:
                    for tok in set(TOKEN.findall(fh.read())):
                        if tok in wanted:
                            hits[tok].append(rel)
    return hits


# ---------------------------------------------------------------------------- grouping

def change_key(r: dict) -> tuple:
    """What this row changes: the first two backticked tokens of the detail, else the row's name."""
    if r["audit"] == "comment" and r["cat"] == "C3":
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
    return "T2" if (r["audit"], r["cat"]) in MECHANICAL else "T3"


def is_rename(audit: str, cat: str) -> bool:
    return audit == "naming" and cat != "F1"


def build_batches(live: list, sweep: dict) -> list:
    def sweep_size(rs):
        if not is_rename(rs[0]["audit"], rs[0]["cat"]):
            return 0
        touched = set()
        for r in rs:
            touched |= set(sweep.get(r["name"].split(".")[-1], []))
        return len(touched)

    batches = []
    for tier in ("T1", "T2", "T3"):
        trows = [r for r in live if tier_of(r) == tier]
        cats = list(dict.fromkeys((r["audit"], r["cat"]) for r in trows))
        for (audit, cat) in cats:
            crows = sorted((r for r in trows if r["audit"] == audit and r["cat"] == cat),
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
                    batches.append({"tier": tier, "audit": audit, "cat": cat,
                                    "cat_title": grp[0]["cat_title"], "kind": "one substitution",
                                    "changes": [describe(key)], "files": sorted(chunk),
                                    "rows": sub, "part": i // UNIFORM_CAP + 1, "parts": parts,
                                    "sweep": sweep_size(sub)})

            cur_files, cur_rows, cur_keys = [], [], []
            for key, grp in sorted(leftovers, key=lambda kg: kg[1][0]["file"]):
                gfiles = list(dict.fromkeys(r["file"] for r in grp))
                if cur_files and len(set(cur_files) | set(gfiles)) > BESPOKE_CAP:
                    batches.append({"tier": tier, "audit": audit, "cat": cat,
                                    "cat_title": cur_rows[0]["cat_title"], "kind": "mixed",
                                    "changes": [describe(k) for k in cur_keys],
                                    "files": sorted(set(cur_files)), "rows": cur_rows,
                                    "part": 0, "parts": 0, "sweep": sweep_size(cur_rows)})
                    cur_files, cur_rows, cur_keys = [], [], []
                cur_files.extend(gfiles)
                cur_rows.extend(grp)
                cur_keys.append(key)
            if cur_rows:
                batches.append({"tier": tier, "audit": audit, "cat": cat,
                                "cat_title": cur_rows[0]["cat_title"], "kind": "mixed",
                                "changes": [describe(k) for k in cur_keys],
                                "files": sorted(set(cur_files)), "rows": cur_rows,
                                "part": 0, "parts": 0, "sweep": sweep_size(cur_rows)})

    order = {"T1": 0, "T2": 1, "T3": 2}
    batches.sort(key=lambda b: (order[b["tier"]], b["audit"] != "comment", b["cat"], b["files"][0]))
    seq = collections.Counter()
    for b in batches:
        seq[b["tier"]] += 1
        b["id"] = f"{b['tier']}-{seq[b['tier']]:03d}"
        b["title"] = PR_TITLE.get((b["audit"], b["cat"]), "chore: audit fixes")
        if b["parts"] > 1:
            b["title"] += f" ({b['part']}/{b['parts']})"
    return batches


# ---------------------------------------------------------------------------- rendering

def md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def render(batches: list, live: list, out_path: str, swept: bool) -> None:
    today = datetime.date.today().isoformat()
    L = []
    L.append("# Mathlib audit fix plan")
    L.append("")
    L.append(f"_Generated by `scripts/audit_plan/fix_plan.py` on {today} from "
             f"[`naming_audit.md`](naming_audit.md) and [`comment_audit.md`](comment_audit.md); "
             f"{len(live)} open findings grouped into {len(batches)} batches._")
    L.append("")
    L.append("Each batch is meant to become one pull request.")
    L.append("")
    L.append("## The batching rule")
    L.append("")
    L.append("A machine-generated pull request should not edit more than **10 files**: a reviewer has")
    L.append("to form a separate judgement about each one. The exception is a pull request that applies")
    L.append("a **single mechanical substitution** — the same wrong spelling replaced by the same right")
    L.append("one everywhere — where reading the whole diff is reading one decision. Those may span up")
    L.append("to **100 files**. So a substitution touching more than ten files becomes a batch of its")
    L.append("own (split at a hundred), and everything else is packed in path order into batches of at")
    L.append("most ten files, which keeps a batch inside one area of the library.")
    L.append("")
    L.append("The `Kind` column says which rule a batch is under: `one substitution` batches are the")
    L.append("ones allowed past ten files; `mixed` batches are capped at ten.")
    L.append("")
    L.append("## Renames and the sweep column")
    L.append("")
    L.append("Every naming-audit finding is a rename, and Mathlib renames keep the old name working")
    L.append("with `@[deprecated (since := \"…\")] alias old := new`. The pull request therefore edits")
    L.append("only the file that declares the name, which is what the `Files` column counts; updating")
    L.append("the call sites is a later mechanical sweep, and `Sweep` is an upper bound on its size.")
    L.append("It is a token match, so a name whose last component is an ordinary word (`map`, `symm`,")
    L.append("`trans`) reports a number far larger than the true one — which is itself the signal that")
    L.append("the rename must not be done without the alias.")
    L.append("")
    L.append("## Tiers")
    L.append("")
    for tier in ("T1", "T2", "T3"):
        name, blurb = TIER_BLURB[tier]
        tb = [b for b in batches if b["tier"] == tier]
        tf = len({f for b in tb for f in b["files"]})
        rws = sum(len(b["rows"]) for b in tb)
        L.append(f"- **{tier} — {name}.** {blurb}  ")
        L.append(f"  {len(tb)} batches, {rws} findings, {tf} files.")
    L.append("")
    L.append("Re-run the script after triaging: rows you mark `fp` or `wontfix` drop out, rows you mark")
    L.append("`confirmed` move up to T1, and the batches renumber.")
    L.append("")

    for tier in ("T1", "T2", "T3"):
        tb = [b for b in batches if b["tier"] == tier]
        if not tb:
            continue
        name, _ = TIER_BLURB[tier]
        L.append(f"## {tier} — {name}")
        L.append("")
        L.append("| Batch | Suggested PR title | Category | Change | Files | Rows | Sweep |")
        L.append("|---|---|---|---:|---:|---:|---:|")
        for b in tb:
            ch = b["changes"][0] if len(b["changes"]) == 1 else f"{len(b['changes'])} substitutions"
            sweep = str(b["sweep"]) if b["sweep"] else "—"
            L.append(f"| [{b['id']}](#{b['id'].lower()}) | {md_escape(b['title'])} | "
                     f"{b['audit'][0].upper()}{b['cat']} | {md_escape(ch)} | {len(b['files'])} | "
                     f"{len(b['rows'])} | {sweep} |")
        L.append("")

    L.append("## Batches")
    L.append("")
    for b in batches:
        L.append(f"### {b['id']}")
        L.append("")
        L.append(f"**{b['title']}** — {b['cat_title']} "
                 f"(`{b['audit']}_audit.md` {b['cat']}), {b['kind']}, "
                 f"{len(b['files'])} file(s), {len(b['rows'])} finding(s).")
        if b["sweep"]:
            L.append("")
            L.append(f"Rename: the declaring files are edited here; up to {b['sweep']} files mention "
                     f"these names and would be updated by the follow-up sweep.")
        L.append("")
        if len(b["changes"]) == 1:
            L.append(f"Change: {b['changes'][0]}")
        else:
            L.append("Changes: " + ", ".join(b["changes"]))
        L.append("")
        L.append("| Location | Finding | Detail |")
        L.append("|---|---|---|")
        for r in sorted(b["rows"], key=lambda r: (r["file"], r["line"])):
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
    ap.add_argument("--no-sweep", action="store_true",
                    help="skip the rename sweep index (much faster)")
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    out = args.out or os.path.join(root, "docs", "audit_fix_plan.md")

    rows = (parse_audit(os.path.join(root, "docs", "naming_audit.md"), "naming")
            + parse_audit(os.path.join(root, "docs", "comment_audit.md"), "comment"))
    live = [r for r in rows if r["status"] in ("open", "confirmed")]
    print(f"{len(rows)} rows, {len(live)} still open")

    sweep = {}
    if not args.no_sweep:
        wanted = {r["name"].split(".")[-1] for r in live if is_rename(r["audit"], r["cat"])}
        wanted = {w for w in wanted if len(w) >= 3}
        print(f"indexing {len(wanted)} name components for the sweep bound...")
        sweep = sweep_index(root, wanted)

    batches = build_batches(live, sweep)
    render(batches, live, out, not args.no_sweep)

    bad = [b for b in batches if b["kind"] != "one substitution" and len(b["files"]) > BESPOKE_CAP]
    worse = [b for b in batches if len(b["files"]) > UNIFORM_CAP]
    print(f"{len(batches)} batches -> {out}")
    for tier in ("T1", "T2", "T3"):
        tb = [b for b in batches if b["tier"] == tier]
        print(f"  {tier}: {len(tb):4} batches, {sum(len(b['rows']) for b in tb):5} findings, "
              f"{len({f for b in tb for f in b['files']}):5} files")
    print(f"  over the 10-file cap: {len(bad)}; over the 100-file cap: {len(worse)}")
    if bad or worse:
        sys.exit(1)


if __name__ == "__main__":
    main()
