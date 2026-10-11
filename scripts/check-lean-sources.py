#!/usr/bin/env python3
"""Non-executing check of Palomar's Lean source rules (minimal local stand-in for the
PalomarTemplate checker of the same name).

* every regular `.lean` file outside `.git`/`.lake` uses the module system: the first
  non-comment token is `module` (ordinary comments may precede it);
* no `.lean` symbolic links;
* at most 10,000 physical lines per file; `Challenge.lean` at most 1,000 lines and 100 KiB.
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
failed = False


def fail(message):
    global failed
    print(message)
    failed = True


def strip_leading_comments(text):
    i = 0
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith("/-!", i):
            depth, i = 1, i + 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            return text[i:]


for path in sorted(root.rglob("*.lean")):
    rel = path.relative_to(root)
    if ".git" in rel.parts or ".lake" in rel.parts:
        continue
    if path.is_symlink():
        fail(f"{rel}: .lean symbolic links are rejected")
        continue
    data = path.read_bytes()
    lines = len(re.split(rb"\r\n|\n", data)) - (1 if data.endswith(b"\n") else 0)
    if lines > 10_000:
        fail(f"{rel}: {lines} lines exceeds the 10,000-line limit")
    if rel == pathlib.Path("Challenge.lean") and (lines > 1_000 or len(data) > 100 * 1024):
        fail(f"{rel}: Challenge must have at most 1,000 lines and 100 KiB ({lines} lines, {len(data)} bytes)")
    if path.name == "lakefile.lean":
        continue
    if not re.match(r"module\b", strip_leading_comments(data.decode("utf-8"))):
        fail(f"{rel}: does not start with a `module` header")

if not failed:
    print("Lean source requirements satisfied")
sys.exit(1 if failed else 0)
