# Release and registry acceptance gates

Raccoon Labs maintains separate acceptance decisions for source,
mathematics, external software use, public publication, and Palomar
registration. A passing check in one category does not imply a pass in
the next.

## Current release standing

Version 0.1.0 is the first public source release. The public source commit
and its CI results establish public-release reproducibility; historical
private staging receipts do not automatically certify edited source.
**No Palomar submission, review or registration is implied by this release.**

## Required technical checks

1. Stable Lean 4.35.0 and the exact pinned Mathlib dependency graph;
   `module` headers on every Lean file, with the source line cap respected.
2. Byte-accurate SHA-256 manifest; frozen original-source and
   module-system inverse-integrity checks; original Bialer notices intact.
3. Full `RML.Fourier.Vaaler.Toolkit` build; all sixteen bundled examples;
   the named axiom suite; and all fourteen definitional-identity obligations.
4. Root Challenge restricted to Mathlib with its one intentionally unproved
   statement; root Solution proved with ordinary Lean foundations and
   exactly the same theorem statement.
5. Official `lake comparator --paranoid` with an active Bubblewrap
   sandbox, zero definition exemptions and **two outcomes**:
   genuine Solution **accepted**; deliberate counterfeit **rejected for
   a definition-body mismatch**. Never bypass the sandbox.
6. A separate-checkout, Git-pinned downstream Lake consumer that compiles
   actual public APIs, not merely a `#check` in the package's build.
7. Independent publication review of rights, provenance, API documentation,
   citations, currentness, release contents, URLs and source-archive
   correspondence, on the final exact commit.

## Release sequencing

**Private technical CI acceptance does not authorize publication.**
Publication requires explicit approval of the exact final source commit
and target public GitHub repository, followed by the public repository's
own CI check. Palomar's official predictive preflight, any closed
submission or queue entry, and permanent registration each need
separate approval. The Palomar CLI remains separately subject to
Bindwright's security review, installation approval and cURL-only
transaction protections.

For the concrete commands, see [verification](verification.md). Reviewer
reports and CI logs should be pinned to full commit hashes, not described
as timeless proof of whatever branch happens to be checked out.
