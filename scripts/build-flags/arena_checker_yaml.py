#!/usr/bin/env python3
"""Write the proposed arena checker file with a concrete revision.

    arena_checker_yaml.py <proposal.yaml> <rev> <out.yaml>
"""
import re
import sys

proposal, rev, out = sys.argv[1:4]
text = open(proposal, encoding="utf-8").read()
if not re.fullmatch(r"[0-9a-f]{40}", rev):
    sys.exit(f"not a full commit hash: {rev}")
new, n = re.subn(r"(?m)^rev: REV$", f"rev: {rev}", text)
if n != 1:
    sys.exit("the proposal must have exactly one `rev: REV` line")
open(out, "w", encoding="utf-8").write(new)
