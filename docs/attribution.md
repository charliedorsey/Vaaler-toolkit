# Attribution and redistribution

Vaaler–ETK Toolkit is software assembled under the human
publication responsibility of Charlie Dorsey (Raccoon Labs).
Lean proof assistance from AI models is described as AI-assisted
formalization, not invented as human authorship or claimed as a
novel historical mathematical theorem.

The original analytic lemmas are based on classical work in
Vaaler-type Fourier approximation, Fejer summation and
Erdős-Turán-Koksma discrepancy. This toolkit formalizes and
extends usable theorem interfaces; it makes no priority claim
on the underlying historical mathematics.

Two adapted files retain the Gershon Bialer notices:
RML/Fourier/Vaaler/Internal/Analytic/FejerTriangle.lean and
RML/Fourier/Vaaler/Internal/Analytic/SincSquare.lean.
Both include dated source-level modification notices. The
Apache-2.0 LICENSE and NOTICE retain third-party attribution,
upstream repository identity and the scope of namespace/import
modifications. Underlying mathematical proof bodies are unchanged.

The 61 originally protected source modules are checked against immutable
SHA-256 baselines with two approved Bialer notices. The separate
module-system inverse check covers all 115 Lean files after conversion
to Lean 4.35. For auditable source lineage, see the
[provenance guide](provenance.md), immutable baseline manifests
and source-level attribution notices.

The owner's rights declaration is part of private provenance
review; no private authorization receipts need be exposed in
the public Git tree. Dependency code obtained by Lake keeps
its own licenses and is not copied into this source distribution.

Independent source verification and publication acceptance are distinct
from mathematical correctness; see [release gates](release_gate.md).
