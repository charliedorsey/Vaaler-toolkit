#!/usr/bin/env python3
"""Offline, side-effect-free Palomar source-layout checks (NOT a Comparator PASS)."""
from pathlib import Path
import json
import re
import subprocess
import sys
R=Path(__file__).resolve().parent.parent
challenge=(R/'Challenge.lean').read_text()
solution=(R/'Solution.lean').read_text()
original_challenge=(R/'challenge/Challenge.lean').read_text()
original_solution=(R/'challenge/Solution.lean').read_text()
if solution!=original_solution:
    sys.exit('FAIL: root Solution differs from required educational Solution mirror')
if len(re.findall(r'(?m)^public import\s+',challenge))!=1 or not challenge.startswith(
        'module\n\npublic import Mathlib\n'):
    sys.exit('FAIL: Palomar Challenge must be a Mathlib-only public module')
if len(re.findall(r'\bsorry\b',challenge))!=1:
    # Exactly one intentional proof hole, confined to the canonical Challenge.
    sys.exit('FAIL: unexpected proof-hole count in Challenge')
if re.search(r'\bsorry\b|\badmit\b',solution):
    sys.exit('FAIL: proof hole in the proved Solution')
if 'import Challenge' in solution or 'import RML.Fourier.Vaaler.Discrepancy.SignedTorusBox' in challenge:
    sys.exit('FAIL: forbidden proof import')
target='theorem signed_torus_box_discrepancy\n'
def signature(src):
    if src.count(target)!=1:sys.exit('FAIL: missing unique target theorem')
    return src.split(target,1)[1].split(' := by\n',1)[0]
if signature(challenge)!=signature(solution) or signature(challenge)!=signature(original_challenge):
    sys.exit('FAIL: signed theorem signature altered')
config=json.loads((R/'comparator.json').read_text())
if config['challenge_module']!='Challenge' or config['solution_module']!='Solution':
    sys.exit('FAIL: unexpected comparator modules')
if config['theorem_names']!=['VaalerETKChallenge.signed_torus_box_discrepancy']:
    sys.exit('FAIL: Comparator theorem target changed')
if set(config['permitted_axioms'])!={'propext','Quot.sound','Classical.choice'}:
    sys.exit('FAIL: Comparator axiom budget changed')
# NO DEFINITION HOLES. This field is a Comparator exemption list, not a list
# of definitions to protect. Nonempty values can accept vacuous fake proofs.
if config.get('definition_names',[]) != []:
    sys.exit('FAIL: unsafe Comparator definition holes; must be []')
from test_comparator_safety import strict_config
try:
    strict_config(config)
except ValueError as e:
    sys.exit('FAIL: '+str(e))
lakefile=(R/'lakefile.toml').read_text()
for target in ('Challenge','Solution'):
    import re as _re
    if not _re.search(r'(?m)^\[\[lean_lib\]\]\s*\nname = "'+target+r'"', lakefile):
        sys.exit('FAIL: missing Lake Comparator module '+target)

work=(R/'.github/workflows/palomar-manual-preflight.yml').read_text()
if 'workflow_dispatch:' not in work or '\n  push:' in work or '\n  pull_request:' in work:
    sys.exit('FAIL: Palomar workflow is not manually gated')
if 'submission.yml@14aa8d6b3c2f14a8540605e37144560b9a00e7e7' not in work:
    sys.exit('FAIL: Palomar workflow pipeline pin changed')
if "mode: full" not in work or "execution_profile: palomar-standard-v1" not in work:
    sys.exit('FAIL: Palomar workflow profile changed')
if subprocess.run([sys.executable,str(R/'scripts/check_palomar_challenge_mirror.py')],
                  cwd=R,check=False).returncode!=0:
    sys.exit('FAIL: challenge source definition mirror')
print('PASS: strict no-hole Comparator config, Lake targets, Mathlib-only signed Challenge, mirrored source, proof isolation, manual workflow')
print('NOT_CHECKED: official Comparator, independent cold checkout, or any live Palomar service')
