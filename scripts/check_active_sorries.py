#!/usr/bin/env python3
"""Approximate active gap/trust checker for Lean files.

This strips nested Lean block comments (`/- ... -/`) and line comments (`-- ...`),
then reports active occurrences of gap/trust keywords. It is intentionally
simple; `lake build` and `#print axioms` remain the source of truth.
"""
from __future__ import annotations
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGETS = [ROOT / "KaltonRoberts.lean", ROOT / "KaltonRoberts"]
KEYWORDS = [
    "sorry",
    "admit",
    "axiom",
    "constant",
    "opaque",
    "unsafe",
    "extern",
    "implemented_by",
    "native_decide",
]
PAT = re.compile(r"\b(" + "|".join(map(re.escape, KEYWORDS)) + r")\b")

def strip_comments_with_map(text: str):
    out = []
    line_map = []
    i = 0
    line = 1
    depth = 0
    while i < len(text):
        ch = text[i]
        nxt = text[i:i+2]
        if ch == "\n":
            line += 1
            if depth == 0:
                out.append(ch)
                line_map.append(line - 1)
            i += 1
            continue
        if depth > 0:
            if nxt == "/-":
                depth += 1
                i += 2
            elif nxt == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if nxt == "/-":
            depth = 1
            i += 2
            continue
        if nxt == "--":
            # skip to newline, keeping newline handled by the main loop
            j = text.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(ch)
        line_map.append(line)
        i += 1
    return "".join(out), line_map

def main() -> int:
    hits = []
    paths = []
    for target in TARGETS:
        if target.is_file():
            paths.append(target)
        elif target.is_dir():
            paths.extend(target.rglob("*.lean"))
    for p in sorted(paths):
        text = p.read_text(errors="replace")
        stripped, line_map = strip_comments_with_map(text)
        # Create offset->line function through line_map list indexed per char.
        for m in PAT.finditer(stripped):
            line_no = line_map[m.start()] if m.start() < len(line_map) else stripped[:m.start()].count("\n") + 1
            orig_line = text.splitlines()[line_no - 1].strip() if 0 <= line_no - 1 < len(text.splitlines()) else ""
            hits.append((p.relative_to(ROOT), line_no, m.group(1), orig_line))
    if not hits:
        print("No active gap/trust keywords found in KaltonRoberts/*.lean")
        return 0
    print(f"Found {len(hits)} active gap/trust keyword occurrence(s):")
    for rel, line, kw, ctx in hits:
        print(f"{rel}:{line}: {kw}: {ctx}")
    return 1

if __name__ == "__main__":
    sys.exit(main())
