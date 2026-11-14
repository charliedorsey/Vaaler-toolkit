#!/usr/bin/env python3
"""Source-static gate only. Does not compile Lean or certify mathematical claims."""
import argparse
import importlib.util
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / 'upstream/BASELINE_LEAN_SHA256.json'
# Load the migration checker from the same source checkout (also when copied
# into a negative-control test fixture), never from the caller's Python path.
_MSPEC = importlib.util.spec_from_file_location(
    'candidate_module_integrity', ROOT / 'scripts/module_migration_integrity.py')
_MODULE_CHECK = importlib.util.module_from_spec(_MSPEC)
_MSPEC.loader.exec_module(_MODULE_CHECK)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def strip_comments(s):
    """Remove Lean line and nested block comments for a conservative token scan."""
    i, depth, chars = 0, 0, []
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and s.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth:
            if s[i] == '\n':
                chars.append('\n')
            i += 1
            continue
        if s.startswith('--', i):
            end = s.find('\n', i)
            if end < 0:
                break
            chars.append('\n')
            i = end + 1
            continue
        chars.append(s[i])
        i += 1
    if depth:
        raise ValueError('unclosed block comment')
    return ''.join(chars)

def audit():
    problems = []
    frozen = json.loads(BASELINE.read_text())['lean_files_sha256']
    # Module headers are allowed transport edits; the exact R0023 source
    # material is independently pinned by the inverse-translation manifest.
    for violation in _MODULE_CHECK.audit():
        problems.append('proof source was edited or module wrapper invalid: '+violation)
    actual = {p.relative_to(ROOT).as_posix(): p for p in (ROOT / 'RML').rglob('*.lean')}
    missing = set(frozen)-set(actual)
    if missing:
        problems.append('Missing frozen proof files: '+str(sorted(missing)))
    # R0006 additions are allowlisted extensions; all R0001 source hashes remain immutable.
    new_modules = set(actual)-set(frozen)
    allowed_extensions = {
        'RML/Fourier/Vaaler/Positive/Coefficients.lean',
        'RML/Fourier/Vaaler/Positive/Interval.lean',
        'RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean',
        'RML/Fourier/Vaaler/Toolkit.lean',
        'RML/Fourier/Vaaler/Positive/ExplicitPointwise.lean',
        'RML/Fourier/Vaaler/Discrepancy/AbstractETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/WeightedETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/ExplicitInterval.lean',
        'RML/Fourier/Vaaler/Discrepancy/ExplicitWeightedETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/WrappedInterval.lean',
        'RML/Fourier/Vaaler/Discrepancy/ExplicitWrappedInterval.lean',
        'RML/Fourier/Vaaler/Discrepancy/Frequency.lean',
        'RML/Fourier/Vaaler/Discrepancy/FrequencyBox.lean',
        'RML/Fourier/Vaaler/Discrepancy/TorusBox.lean',
        'RML/Fourier/Vaaler/Discrepancy/WeightedExponential.lean',
        'RML/Fourier/Vaaler/Discrepancy/OneDimETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedScalar.lean',
        'RML/Fourier/Vaaler/Discrepancy/LabelledTensor.lean',
        'RML/Fourier/Vaaler/Discrepancy/RealTensorBridge.lean',
        'RML/Fourier/Vaaler/Discrepancy/FejerFaceCompact.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedFrequencyBox.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedTorusBox.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedNegativeControl.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedOneDimETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedETK.lean',
        'RML/Fourier/Vaaler/Discrepancy/ETKComplex.lean',
        'RML/Fourier/Vaaler/Discrepancy/MainFaceCompact.lean',
        'RML/Fourier/Vaaler/Discrepancy/FejerTensorComplex.lean',
        'RML/Fourier/Vaaler/Discrepancy/FejerErrorLabels.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedTensor.lean',
        'RML/Fourier/Vaaler/Discrepancy/SignedFrequency.lean',
        'RML/Fourier/Vaaler/Discrepancy/ArcChoice.lean',
    }
    if new_modules != allowed_extensions:
        problems.append('Unexpected approved extension set: '+str(sorted(new_modules ^ allowed_extensions)))
    # Exception ONLY for the two source-level Apache-2.0 change notices.
    # A released file must contain the exact approved notice once, and
    # removing only that notice must restore the frozen source byte-for-byte.
    approved_bialer_notices = {
        'RML/Fourier/Vaaler/Internal/Analytic/FejerTriangle.lean': 'MODIFIED for VAALER toolkit, 2026-11-12, by Charlie Dorsey: relocated the enclosing namespace from the upstream MathExtras module to RML.Fourier.Vaaler.Internal.Analytic.FejerTriangle; mathematical proof bodies unchanged.\n',
        'RML/Fourier/Vaaler/Internal/Analytic/SincSquare.lean': 'MODIFIED for VAALER toolkit, 2026-11-12, by Charlie Dorsey: relocated the namespace, rewrote the FejerTriangle import path, and opened the corresponding local namespace; mathematical proof bodies unchanged.\n',
    }
    for rel, expected in frozen.items():
        if rel not in actual:
            continue
        actual_bytes = None
        try:
            actual_bytes = _MODULE_CHECK.original_bytes(actual[rel])
        except (ValueError, UnicodeDecodeError) as e:
            problems.append('proof source was edited: '+rel+' ('+str(e)+')')
            continue
        if rel in approved_bialer_notices:
            insertion = approved_bialer_notices[rel].encode()
            if actual_bytes.count(insertion) != 1:
                problems.append('missing or repeated approved Bialer modification notice: ' + rel)
            elif hashlib.sha256(actual_bytes.replace(insertion, b'', 1)).hexdigest() != expected:
                problems.append('proof source was edited beyond allowed Bialer notice: ' + rel)
        elif hashlib.sha256(actual_bytes).hexdigest() != expected:
            problems.append('proof source was edited: ' + rel)
    modules = {'.'.join(Path(rel).with_suffix('').parts): rel for rel in actual}
    deps = {}
    external = set()
    for module, rel in modules.items():
        content = actual[rel].read_text()
        try:
            stripped = strip_comments(content)
        except ValueError as e:
            problems.append(f'{module}: {e}')
            continue
        found = re.search(r'\b(sorry|admit|axiom|unsafe|opaque)\b',stripped)
        if found:
            problems.append(f'potential Lean admission/unsafe token {found.group(1)} in {rel}')
        imports = []
        for line in stripped.splitlines():
            match = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+(\S+)\s*$',line)
            if match:
                imports.append(match.group(1))
        deps[module]=imports
        for imp in imports:
            if imp.startswith('PaperB.') or imp.startswith('Gate3.'):
                problems.append(f'forbidden legacy import {imp} in {module}')
            elif imp.startswith('RML.') and imp not in modules:
                problems.append(f'unresolved local import {imp} in {module}')
            elif imp not in modules:
                external.add(imp)
    root='RML.Fourier.Vaaler.Toolkit'
    seen={root}
    pending=[root]
    while pending:
        mod=pending.pop()
        for dep in deps.get(mod,[]):
            if dep in modules and dep not in seen:
                seen.add(dep);pending.append(dep)
    if set(modules) != seen:
        problems.append('modules not reachable from umbrella root: '+str(sorted(set(modules)-seen)))
    if not (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0':
        problems.append('Lean toolchain differs from source pin')
    if not (ROOT/'lake-manifest.json').is_file():
        problems.append('missing pinned lake-manifest.json')
    required = ['sign_approx_error_le','kernel_fourier_fejer','error_fourier_transform_nonzero',
                'periodized_identity','positive_pointwise']
    facades='\n'.join((ROOT/path).read_text() for path in [
      'RML/Fourier/Vaaler/Pointwise.lean','RML/Fourier/Vaaler/Fejer.lean',
      'RML/Fourier/Vaaler/Transform.lean','RML/Fourier/Vaaler/Periodization.lean',
      'RML/Fourier/Vaaler/Positive.lean'])
    for theorem in required:
        if not re.search(r'\btheorem\s+'+theorem+r'\b',facades):
            problems.append('missing facade theorem '+theorem)
    return {'status':'PASS_STATIC_ONLY' if not problems else 'FAIL_STATIC',
            'source_baseline':'upstream/BASELINE_LEAN_SHA256.json',
            'frozen_source_count':len(frozen),
            'extension_module_count':len(new_modules),
            'import_reachable_source_count':len(seen),
            'external_import_modules':len(external),
            'proof_source_hashes_preserved':not any('proof source was edited' in x for x in problems),
            'release_notice_exceptions':list(approved_bialer_notices),
            'lean_compilation':'NOT_RUN',
            'fresh_axiom_audit':'NOT_RUN',
            'public_release':'HOLD',
            'problems':problems}

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json-out',type=Path)
    args=parser.parse_args()
    result=audit()
    print(json.dumps(result,sort_keys=True,indent=2))
    if args.json_out:
        args.json_out.parent.mkdir(parents=True,exist_ok=True)
        args.json_out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    sys.exit(0 if result['status']=='PASS_STATIC_ONLY' else 1)
