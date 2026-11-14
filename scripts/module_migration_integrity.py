#!/usr/bin/env python3
"""Exact R0023 source preservation through authorized module headers only.

Each tracked Lean file must be byte-identical to its pre-module source after
reversing precisely the header, public-import, and exposed-public-section
migration. Any other edit (even comments or proof text) is rejected.
No network access or Git history is required for source-only audit.
"""
from pathlib import Path
import hashlib,json,re,sys
ROOT = Path(__file__).resolve().parent.parent
BASELINE=ROOT/'upstream/R0024_PRE_MODULE_SOURCE_SHA256.json'
PREFIX='module\n\n'
SECTION='\n@[expose] public section\n'
IMPORT=re.compile(r'(?m)^public import ([^\r\n]+)$')
EXTRA_PRIVATE_IMPORTS = {
    'RML/Fourier/Vaaler/Internal/DivisorExpansion.lean':
        'Mathlib.Data.Nat.Squarefree',
    'RML/Fourier/Vaaler/Internal/H3CscSq.lean':
        'Mathlib.Analysis.PSeries',
}

def original_bytes(path):
    data=path.read_bytes()
    if b'\r' in data or not data.startswith(PREFIX.encode()):
        raise ValueError('missing exact module prefix or non-LF source')
    body=data[len(PREFIX):].decode('utf-8')
    rel=path.relative_to(ROOT).as_posix()
    extra=EXTRA_PRIVATE_IMPORTS.get(rel)
    if extra:
        clause='public import '+extra+'\nimport all '+extra+'\n'
        if body.count(clause)!=1:
            raise ValueError('missing or repeated approved private mathlib import')
        body=body.replace(clause,'',1)
    if body.count(SECTION)!=1:
        raise ValueError('missing or repeated exposed public section')
    body=body.replace(SECTION,'',1)
    imports=IMPORT.findall(body)
    if not imports or re.search(r'(?m)^import\s+',body):
        raise ValueError('all imports must be public')
    body=IMPORT.sub(lambda m:'import '+m.group(1),body)
    return body.encode('utf-8')

def audit():
    expected=json.loads(BASELINE.read_text())['pre_module_source_sha256']
    actual={p.relative_to(ROOT).as_posix():p for p in ROOT.rglob('*.lean')
            if not any(x in p.parts for x in ('.lake','.git','.local-replay'))}
    problems=[]
    if set(actual)!=set(expected):
        problems.append('tracked Lean set mismatch: '+str(sorted(set(actual)^set(expected))))
    for name in sorted(set(expected)&set(actual)):
        p=actual[name]
        if p.is_symlink():
            problems.append('symlink forbidden: '+name);continue
        try:
            normalized=original_bytes(p)
            if hashlib.sha256(normalized).hexdigest()!=expected[name]:
                problems.append('unauthorized source change beyond module wrapper: '+name)
        except (ValueError,UnicodeDecodeError) as e:
            problems.append(name+': '+str(e))
        if len(p.read_bytes().splitlines())>10000:
            problems.append('over 10000 physical lines: '+name)
    return problems

if __name__=='__main__':
    failures=audit()
    print('MIGRATED_LEAN_SOURCES='+str(len(json.loads(BASELINE.read_text())['pre_module_source_sha256'])))
    if failures:
        print('MODULE_MIGRATION_INTEGRITY=FAIL')
        for item in failures:print(item)
        sys.exit(1)
    print('MODULE_MIGRATION_INTEGRITY=PASS (exact pre-module sources restored by canonical inverse)')
