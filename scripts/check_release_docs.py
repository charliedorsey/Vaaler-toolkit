#!/usr/bin/env python3
"""Offline release-currentness and local-link guard, not a proof checker."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parent.parent
docs=[R/'README.md',R/'CONTRIBUTING.md',R/'CHANGELOG.md',
      R/'docs/API.md',R/'docs/provenance.md',R/'docs/attribution.md',
      R/'docs/release_gate.md',R/'docs/verification.md',
      R/'docs/theorems.md',R/'docs/scope.md',R/'docs/proof_guide.md',
      R/'examples/README.md',R/'challenge/README.md',R/'receipts/README.md']
# The last path is deliberately optional: old receipts are excluded.
docs=[p for p in docs if p.is_file()]
issues=[]
def add(p,msg):issues.append(str(p.relative_to(R))+': '+msg)
for p in docs:
    s=p.read_text()
    if re.search(r'Lean (?:v)?4\.34\.0|leanprover/lean4:v4\.34\.0',s):
        add(p,'obsolete Lean toolchain')
    if re.search(r'(?:docs/)?(?:TIER4_INTEGRATED_API_AND_SCOPE_R0020|PROVENANCE_PUBLIC_R0007|REPLAY_STANDING|RIGHTS_REVIEW_R0002)\.md',s):
        add(p,'removed historical documentation reference')
    if re.search(r'\bR002[0-3]\b',s):
        add(p,'historical candidate revision in current consumer documentation')
    for match in re.finditer(r'(?<!!)\[[^\]]+\]\(([^)]+)\)',s):
        target=match.group(1).split('#',1)[0].strip()
        if not target or target.startswith(('http://','https://','mailto:','#')):
            continue
        if not (p.parent/target).exists():
            add(p,'broken relative Markdown link: '+target)
if (R/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.35.0':
    issues.append('supported Lean compiler pin changed')
if not (R/'docs/provenance.md').exists():
    issues.append('missing current provenance document')
if issues:
    print('RELEASE_DOC_CURRENTNESS=FAIL')
    for issue in issues:print(issue)
    sys.exit(1)
print('RELEASE_DOC_CURRENTNESS=PASS ('+str(len(docs))+' current guides, local links and toolchain)')
