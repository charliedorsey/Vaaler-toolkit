#!/usr/bin/env python3
"""Kernel-checked comparison of 14 isolated source-definition copies.

A text match does not prove isolated elaboration. The original source
definitions and separately named copies are imported together, then
Lean is asked to establish equality of functions by definitional reduction
(rfl), with no sorry or axioms added.
This is local evidence, not a substitute for the official Comparator.
"""
from pathlib import Path
import subprocess
import sys
from check_palomar_challenge_mirror import BLOCKS

R = Path(__file__).resolve().parent.parent
assert len(BLOCKS) == 14
source = R / 'Challenge.lean'
actual = source.read_text()
start = 'namespace RML.Fourier.Vaaler.Internal'
end = '\nnamespace VaalerETKChallenge\n'
assert actual.count(start) == 1 and actual.count(end) == 1
shadow = start + actual.split(start,1)[1].split(end,1)[0]
for source_ns,target_ns in [
    ('RML.Fourier.Vaaler.Internal','VaalerETKShadow.Internal'),
    ('RML.Fourier.Vaaler.Positive','VaalerETKShadow.Positive')
]:
    shadow = shadow.replace('namespace '+source_ns, 'namespace '+target_ns)
    shadow = shadow.replace('end '+source_ns, 'end '+target_ns)
    shadow = shadow.replace('open '+source_ns, 'open '+target_ns)
statements = []
for _, name, ns in BLOCKS:
    target_ns = ('VaalerETKShadow.Internal'
                 if ns == 'RML.Fourier.Vaaler.Internal'
                 else 'VaalerETKShadow.Positive')
    theorem = 'vaaler_etk_definition_identity_' + name
    statements.append(
        'theorem '+theorem+' :\n'
        '    '+ns+'.'+name+' = '+target_ns+'.'+name+' := by rfl\n'
        '#print axioms '+theorem+'\n'
    )
text = ('module\n\n'
        'public import RML.Fourier.Vaaler.Toolkit\n\n'
        '@[expose] public section\n\n'
        '/-! Generated kernel equality obligations for source-derived definitions. -/\n'
        + shadow + '\n' + '\n'.join(statements))
# The exact generated Lean court is a committed source artifact. A change in
# either the generator or its generated body must be deliberately reviewed.
committed = R / 'audit/DefinitionIdentity.lean'
if sys.argv[1:] == ['--generate']:
    committed.write_text(text)
    print('GENERATED: module-system definition identity court')
    sys.exit(0)
if not committed.is_file() or committed.read_text() != text:
    sys.exit('FAIL: audit/DefinitionIdentity.lean differs from generated Lean court')
out = R / '.local-replay/PALOMAR_DEFINITION_IDENTITY.lean'
out.parent.mkdir(exist_ok=True)
out.write_text(text)
if sys.argv[1:] == ['--source-only']:
    print('PASS: committed audit/DefinitionIdentity.lean is exact generated court')
    sys.exit(0)
p = subprocess.run(['lake','env','lean',str(out)],cwd=R,
                   stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                   text=True,errors='replace')
log = R / '.local-replay/PALOMAR_DEFINITION_IDENTITY.log'
log.write_text(p.stdout)
print(p.stdout,end='')
if p.returncode or 'sorryAx' in p.stdout or 'error:' in p.stdout:
    sys.exit('FAIL: isolated source-definition identity court')
for _,name,_ in BLOCKS:
    token = "'vaaler_etk_definition_identity_"+name+"'"
    if not (token+' depends on axioms' in p.stdout or
            token+' does not depend on any axioms' in p.stdout):
        sys.exit('FAIL: missing theorem axiom receipt '+name)
print('PASS: 14/14 Lean kernel-checked definitional-equality obligations')
print('NOT CHECKED: official Palomar Comparator execution')
