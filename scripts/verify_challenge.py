#!/usr/bin/env python3
"""Proof-leak and theorem contract check for optional challenge/solution."""
from pathlib import Path
import re,subprocess,sys
R=Path(__file__).resolve().parent.parent
c=(R/"challenge/Challenge.lean").read_text()
s=(R/"challenge/Solution.lean").read_text()
# Lean 4.35 module syntax: challenge imports must be public to preserve the
# intended mathematical interface, but remain the same *single* unsigned module.
if not c.startswith("module\n\n"):
 sys.exit("FAIL: auxiliary challenge missing Lean module header")
ci=re.findall(r"(?m)^public import\s+(\S+)",c)
if re.search(r"(?m)^(?:import|meta import|public meta import|import all)\s+",c):
 sys.exit("FAIL: auxiliary challenge has unexpected noncanonical import")
if ci!=["RML.Fourier.Vaaler.Discrepancy.TorusBox"]:
 sys.exit("FAIL: challenge imports target proof or changed dependencies: "+str(ci))
if "sorry" not in c or "sorry" in s or "#print axioms" not in s:
 sys.exit("FAIL: challenge/solution proof-hole separation changed")
name="theorem signed_torus_box_discrepancy\n"
if c.count(name)!=1 or s.count(name)!=1:
 sys.exit("FAIL: missing unique signed challenge theorem")
def contract(t):
 return t.split(name,1)[1].split(" := by\n",1)[0]
if contract(c)!=contract(s):
 sys.exit("FAIL: challenge and solution statements differ")
out=subprocess.run(["lake","env","lean","challenge/Solution.lean"],
 cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
 text=True,errors="replace")
print(out.stdout,end="")
if out.returncode or "sorryAx" in out.stdout:
 sys.exit("FAIL: solution proof does not kernel-check")
print("PASS: identical challenge/solution statements; no challenge proof leak; solution kernel-checked")
