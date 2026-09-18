#!/usr/bin/env python3
"""Run a single source module and print what it finds — the development loop for a new surface.

    python3 scripts/typo_audit/run_one.py lean_strings [--root .] [--limit 20]
"""
from __future__ import annotations

import argparse
import collections
import importlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "sources"))

from context import Context  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("--root", default=os.path.join(HERE, "..", ".."))
    ap.add_argument("--limit", type=int, default=20)
    args = ap.parse_args()

    mod = importlib.import_module(args.module)
    ctx = Context(args.root, verbose=True)
    findings = mod.collect(ctx)
    by_cat = collections.Counter(f["cat"] for f in findings)
    print(f"\n{mod.SURFACE}: {len(findings)} finding(s)")
    for cat, title in getattr(mod, "CATEGORIES", {}).items():
        print(f"  {cat}: {by_cat[cat]:5}  {title}")
    print()
    for f in findings[:args.limit]:
        print(f"  [{f['cat']}/{f['conf']}] {f['file']}:{f['line']}  {f['name']}")
        print(f"        {f['detail']}")


if __name__ == "__main__":
    main()
