#!/usr/bin/env python3
"""Kernel-audit named public theorems from the pinned RML umbrella."""
from pathlib import Path
import re, subprocess, sys
R=Path(__file__).resolve().parent.parent
names=[
 "RML.Fourier.Vaaler.Positive.weighted_torus_box_etk",
 "RML.Fourier.Vaaler.Positive.weighted_torus_box_etk_complex",
 "RML.Fourier.Vaaler.Positive.weighted_torus_box_etk_signed",
 "RML.Fourier.Vaaler.Positive.signed_oneDim_etk_exponential",
 "RML.Fourier.Vaaler.Positive.signed_oneDim_arc_etk_exponential",
 "RML.Fourier.Vaaler.Positive.signed_torus_box_etk_frequency",
 "RML.Fourier.Vaaler.Positive.signed_torus_box_etk_external_bounds",
 "RML.Fourier.Vaaler.Positive.weighted_tensor_expansion_labelled",
 "RML.Fourier.Vaaler.Positive.weighted_tensor_expansion_labelled_uniform",
 "RML.Fourier.Vaaler.Positive.mainFaceValue_abs_le_complexBound",
 "RML.Fourier.Vaaler.Positive.fejerFaceValue_eq_signed_box",
 "ETKd.etk_signed_abstract",
 "ETKd.signedWeightVariation_nonneg",
]
D=R/".local-replay"
D.mkdir(exist_ok=True)
source=D/"PUBLIC_AXIOM_AUDIT.lean"
source.write_text("import RML.Fourier.Vaaler.Toolkit\n"+
    "\n".join("#print axioms "+name for name in names)+"\n")
p=subprocess.run(["lake","env","lean",str(source)],
    cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
    text=True,errors="replace")
(D/"PUBLIC_AXIOM_AUDIT.log").write_text(p.stdout)
print(p.stdout,end="")
if p.returncode:
 sys.exit("FAIL: Lean axiom audit exited "+str(p.returncode))
if "sorryAx" in p.stdout:
 sys.exit("FAIL: sorryAx reported")
allowed={"propext","Classical.choice","Quot.sound"}
for name in names:
 pattern=re.compile(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",re.S)
 found=pattern.findall(p.stdout)
 if len(found)!=1:
  sys.exit("FAIL: missing or duplicate axiom result for "+name)
 actual={s.strip() for s in found[0].split(",") if s.strip()}
 if not actual <= allowed:
  sys.exit("FAIL: unexpected axioms for "+name+": "+str(actual-allowed))
print("PASS: all",len(names),"public theorem axioms are ordinary Lean foundations")
