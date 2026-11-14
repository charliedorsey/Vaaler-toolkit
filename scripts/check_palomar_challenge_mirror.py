#!/usr/bin/env python3
"""Exact source-text mirror for the Mathlib-only Palomar challenge; never calls network."""
from pathlib import Path
import sys
R = Path(__file__).resolve().parent.parent
BLOCKS = [
 ("RML/Fourier/Vaaler/Internal/H3VaalerCoeff.lean", "h3VaalerJHat", "RML.Fourier.Vaaler.Internal"),
 ("RML/Fourier/Vaaler/Positive/Core.lean", "saw", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Positive/Core.lean", "realVaalerMode", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Positive/Internal/VaalerCoefficients.lean", "yevorin_vaalerMainCoeff", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Positive/Internal/VaalerCoefficients.lean", "yevorin_vaalerErrorCoeff", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Positive/Coefficients.lean", "mainCoeff", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Positive/Coefficients.lean", "errorCoeff", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean", "approxMain", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean", "approxError", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean", "intervalSigma", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean", "intervalMain", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean", "intervalError", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/TorusBox.lean", "torusArcLength", "RML.Fourier.Vaaler.Positive"),
 ("RML/Fourier/Vaaler/Discrepancy/TorusBox.lean", "torusArcIndicator", "RML.Fourier.Vaaler.Positive"),
]
def extract(path, name):
    txt = (R/path).read_text()
    lines=txt.splitlines()
    matches=[i for i,x in enumerate(lines) if x.startswith(("noncomputable def "+name+" ", "noncomputable abbrev "+name+" "))]
    if len(matches)!=1:
        raise ValueError(f"{path}:{name}: expected one source definition, got {len(matches)}")
    start=matches[0]
    end=start+1
    while end<len(lines) and lines[end].strip():
        end+=1
    return "\n".join(lines[start:end])+"\n"
def generate():
    sections=['import Mathlib\n\n/-!\nCanonical candidate: exact source-definition mirror from the pinned toolkit.\nThe proof hole appears ONLY in this Challenge file.\nDo not modify generated definitions: run scripts/check_palomar_challenge_mirror.py.\n-/\n']
    current=None
    for path,name,namespace in BLOCKS:
        if namespace != current:
            if current: sections.append(f"end {current}\n")
            sections.append(f"namespace {namespace}\n")
            if namespace == "RML.Fourier.Vaaler.Positive":
                sections.append("open RML.Fourier.Vaaler.Internal\n")
            current=namespace
        sections.append(f"\n-- Source: {path} :: {name}\n")
        sections.append(extract(path,name))
    sections.append(f"end {current}\n")
    source=(R/'challenge/Challenge.lean').read_text()
    theorem=source[source.index("namespace VaalerETKChallenge\n"):]
    sections.append('\n'+theorem)
    baseline='\n'.join(sections)
    if not baseline.startswith('import Mathlib\n'):
        raise ValueError('source Challenge header changed unexpectedly')
    return ('module\n\n' +
            baseline.replace('import Mathlib\n',
              'public import Mathlib\n\n@[expose] public section\n',1))
if __name__=='__main__':
    expected=generate()
    target=R/'Challenge.lean'
    if '--generate' in sys.argv:
        target.write_text(expected)
        print("GENERATED: exact Mathlib-only Challenge source mirror")
    elif not target.exists() or target.read_text()!=expected:
        sys.exit("FAIL: canonical challenge differs from exact source-definition/theorem mirror")
    else:
        print(f"PASS: {len(BLOCKS)} exact source definitions and challenge theorem match frozen source")
