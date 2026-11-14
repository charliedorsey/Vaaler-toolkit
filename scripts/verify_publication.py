#!/usr/bin/env python3
"""Verify or write the SHA-256 source manifest of the exact tracked release.

Manifest deliberately excludes itself; it hashes the current tracked
release payload only.
"""
from pathlib import Path
import hashlib, os, re, subprocess, sys
R=Path(__file__).resolve().parent.parent
M=R/"SHA256SUMS"
if not (R/".git").exists():
 sys.exit("FAIL: run manifest verifier from a Git checkout, not a partial copy")
tracked=[Path(n.decode()) for n in subprocess.check_output(
 ["git","ls-files","-z"],cwd=R).split(b"\0") if n]
files={}
for path in tracked:
 if path.as_posix()=="SHA256SUMS":continue
 if path.is_absolute() or ".." in path.parts:
  sys.exit("FAIL: unsafe tracked path "+str(path))
 full=R/path
 if full.is_symlink() or not full.is_file():
  sys.exit("FAIL: expected regular tracked payload file "+str(path))
 files[path.as_posix()]=hashlib.sha256(full.read_bytes()).hexdigest()
expected="".join(d+"  "+n+"\n" for n,d in sorted(files.items()))
if sys.argv[1:]==["--write"]:
 M.write_text(expected)
 print("WROTE",len(files),"source payload hashes to",M)
 sys.exit(0)
if len(sys.argv)!=1:
 sys.exit("usage: python3 scripts/verify_publication.py [--write]")
if not M.is_file() or M.is_symlink():
 sys.exit("FAIL: manifest missing or not a regular file")
actual=M.read_text()
if actual!=expected:
 import difflib
 print("".join(difflib.unified_diff(actual.splitlines(True),
      expected.splitlines(True),fromfile="SHA256SUMS",tofile="CURRENT_TREE"))[:3500])
 sys.exit("FAIL: source manifest stale, invalid, or incomplete")
print("PASS:",len(files),"file SHA-256 values, exactly the tracked source payload")
