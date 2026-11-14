# Signed torus-box ETK challenge and solution

The theorem is the exact signed-weight arbitrary finite-dimensional directed torus-box ETK inequality from `RML.Fourier.Vaaler.Positive.weighted_torus_box_etk_signed`. Signed oscillatory terms keep `w`, while approximation errors use `|w|`. Coordinate cutoffs, mixed wrapping and endpoint restrictions are unchanged.

Two intentionally separate interfaces are maintained:

- `challenge/Challenge.lean` and `challenge/Solution.lean` are an educational adapter, with a challenge import of the *unsigned* torus-box module. They are **not** self-contained Palomar Comparator inputs.
- Root `Challenge.lean` imports **Mathlib only** and mirrors fourteen actual source definitions, including the full cotangent-based Vaaler coefficient, with one intentionally unproved target theorem. Root `Solution.lean` imports the accepted signed theorem and proves the **same exact theorem signature**.

Run `python3 scripts/check_palomar_challenge_mirror.py` to detect drift of copied definitions and of the theorem statement. The root Challenge's `sorry` is deliberately excluded from the verified library and the source axiom audit. The official strict Comparator is exercised in Linux CI using zero definition holes, a genuine-Solution positive control, and a counterfeit-Solution negative control rejected for a definition-body mismatch. Every release commit requires its own receipts.

No external submission is authorized.
