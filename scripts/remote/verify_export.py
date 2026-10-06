#!/usr/bin/env python3
"""Compare a regenerated arena export with the hash the live board publishes.

Byte identity (sha256 and size) is the gate. Line count and the header's Lean
and exporter versions are reported to explain a mismatch, not to pass one.
"""
import hashlib
import json
import os
import sys

path = sys.argv[1]
want = {
    "sha256": os.environ["WANT_SHA256"],
    "size": int(os.environ["WANT_SIZE"]),
    "lines": int(os.environ["WANT_LINES"]),
}

digest = hashlib.sha256()
size = newlines = 0
last = b"\n"
header = None
with open(path, "rb") as fh:
    first = fh.readline()
    header = json.loads(first) if first else None
with open(path, "rb") as fh:
    for chunk in iter(lambda: fh.read(1 << 24), b""):
        digest.update(chunk)
        size += len(chunk)
        newlines += chunk.count(b"\n")
        last = chunk[-1:]
lines = newlines + (0 if last == b"\n" else 1)

got = {"sha256": digest.hexdigest(), "size": size, "lines": lines}
meta = (header or {}).get("meta", {})
print(json.dumps({
    "name": os.environ.get("NAME"),
    "byte_identical": got["sha256"] == want["sha256"] and got["size"] == want["size"],
    "got": got,
    "want": want,
    "header": {"lean": meta.get("lean"), "exporter": meta.get("exporter")},
    "export_seconds": int(os.environ.get("EXPORT_SECONDS", "0") or 0),
}, indent=2))
