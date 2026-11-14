#!/usr/bin/env python3
"""Check a source-only release ZIP equals the exact committed Git tree and SHA256SUMS.

No network requests or git mutations; no dependence on compiler cache.
"""
from pathlib import Path
import hashlib
import io
import subprocess
import sys
import zipfile

R = Path(__file__).resolve().parent.parent
if len(sys.argv) != 2:
    sys.exit("usage: python3 scripts/verify_release_archive.py PATH_TO_SOURCE_ZIP")
archive = Path(sys.argv[1])
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=R, text=True).strip()
if subprocess.check_output(["git", "status", "--porcelain"], cwd=R):
    sys.exit("FAIL: source worktree not clean")
filenames = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", head], cwd=R, text=True).splitlines()
with zipfile.ZipFile(archive) as z:
    membernames={x.filename for x in z.infolist() if not x.is_dir()}
    if membernames != set(filenames):
        sys.exit("FAIL: archive members differ from exact Git tree; missing="+str(sorted(set(filenames)-membernames))+" extra="+str(sorted(membernames-set(filenames))))
    manifest={}
    for row in z.read("SHA256SUMS").decode().splitlines():
        digest, name = row.split("  ",1)
        if name in manifest:
            sys.exit("FAIL: duplicate manifest entry "+name)
        manifest[name]=digest
    if set(manifest) != membernames - {"SHA256SUMS"}:
        sys.exit("FAIL: SHA manifest has missing or extraneous paths")
    for path in filenames:
        expected=subprocess.check_output(["git", "show", head+":"+path], cwd=R)
        archived=z.read(path)
        if expected != archived:
            sys.exit("FAIL: byte mismatch at "+path)
        if path != "SHA256SUMS" and hashlib.sha256(archived).hexdigest()!=manifest[path]:
            sys.exit("FAIL: SHA256 mismatch at "+path)
    required=[
       ".github/workflows/lean.yml", "scripts/verify_publication.py",
       "scripts/static_audit.py", "scripts/test_static_audit.py",
       "scripts/verify_palomar_candidate.py", "scripts/verify_challenge.py",
       "scripts/check_palomar_challenge_mirror.py",
       "scripts/check_palomar_definition_identity.py",
       "scripts/test_comparator_safety.py",
       "audit/DefinitionIdentity.lean",
       "Challenge.lean", "Solution.lean", "comparator.json",
       "formalization.yaml", "lakefile.toml", "lake-manifest.json"
    ]
    if any(p not in membernames for p in required):
        sys.exit("FAIL: required CI/Comparator files absent from ZIP")
print("PASS: exact source archive",head,len(membernames),"files, all payload hashes, required CI scripts")
