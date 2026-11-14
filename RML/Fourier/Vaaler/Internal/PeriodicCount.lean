module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

@[expose] public section

/-!
# Paper B: exact periodic admissible count

Frozen paper source:
* `manuscript/paper_b_frozen.tex`
* SHA-256: `9004c20d63218b529ea392d13914c17a347c485fd43814eb88bf8612a8512070`
* labels: `lem:Nq`, `eq:Nq-periodic`

Mathematical role: exact finite arithmetic only.
No analytic or asymptotic theorem is imported or used.
-/

namespace RML.Fourier.Vaaler.Internal

/-- Exact admissible interior count in the translated variable `x = a + t`.

The frozen paper writes
`I_q(a;h) = {0 < t < h : gcd(a+t,q)=1}`.
Translation by `a` is a bijection from those `t` to the filtered interval
`a < x < a+h`, so this is the same finite cardinality without introducing
residue-class quotient types in M2.
-/
def admissibleInteriorCount (q a h : ℕ) : ℕ :=
  ((Finset.Ioo a (a + h)).filter fun x => q.Coprime x).card

/-- A positive canonical representative of the gap class `b-a (mod q)`.
For residue zero we choose `q` itself rather than `0`, because the paper's
height representatives are positive.
-/
def positiveGapRepresentative (q a b : ℕ) : ℕ :=
  let r := (b % q + q - a % q) % q
  if r = 0 then q else r

/-- The canonical representative is positive whenever the modulus is positive.
-/
theorem positiveGapRepresentative_pos
    {q a b : ℕ} (hq : 0 < q) :
    0 < positiveGapRepresentative q a b := by
  dsimp [positiveGapRepresentative]
  split_ifs with hr
  · exact hq
  · exact Nat.pos_of_ne_zero hr

/-- Every complete block of `q` consecutive translated positions contributes
exactly `phi(q)` coprime residues.
-/
theorem completePeriodCount (q start : ℕ) :
    ((Finset.Ico start (start + q)).filter fun x => q.Coprime x).card =
      Nat.totient q := by
  simpa using Nat.filter_coprime_Ico_eq_totient q start

/-- Increasing a positive height by one full modulus adds exactly one complete
period and hence `phi(q)` admissible interior positions.
-/
theorem admissibleInteriorCount_add_period
    (q a h : ℕ) (hh : 0 < h) :
    admissibleInteriorCount q a (h + q) =
      admissibleInteriorCount q a h + Nat.totient q := by
  unfold admissibleInteriorCount
  have hUnion :
      Finset.Ioo a (a + (h + q)) =
        Finset.Ioo a (a + h) ∪ Finset.Ico (a + h) ((a + h) + q) := by
    ext x
    simp
    omega
  have hDisjoint :
      Disjoint
        ((Finset.Ioo a (a + h)).filter fun x => q.Coprime x)
        ((Finset.Ico (a + h) ((a + h) + q)).filter fun x => q.Coprime x) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico] at hx₁ hx₂
    omega
  rw [hUnion, Finset.filter_union, Finset.card_union_of_disjoint hDisjoint]
  rw [completePeriodCount q (a + h)]

/-- Iteration of the complete-period increment.
-/
theorem admissibleInteriorCount_progression
    (q a h0 n : ℕ) (hh0 : 0 < h0) :
    admissibleInteriorCount q a (h0 + n * q) =
      admissibleInteriorCount q a h0 + n * Nat.totient q := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        admissibleInteriorCount q a (h0 + Nat.succ n * q) =
            admissibleInteriorCount q a ((h0 + n * q) + q) := by
              rw [Nat.succ_mul, ← Nat.add_assoc]
        _ = admissibleInteriorCount q a (h0 + n * q) + Nat.totient q := by
              exact admissibleInteriorCount_add_period q a (h0 + n * q) (by omega)
        _ = (admissibleInteriorCount q a h0 + n * Nat.totient q) +
              Nat.totient q := by rw [ih]
        _ = admissibleInteriorCount q a h0 + Nat.succ n * Nat.totient q := by
              simpa [Nat.succ_mul, Nat.add_assoc]

/-- Frozen-paper periodic defect `epsilon_q(a,b)`, using the canonical positive
representative of the compatible gap class.
-/
def periodicError (q a b : ℕ) : ℚ :=
  let h0 := positiveGapRepresentative q a b
  (admissibleInteriorCount q a h0 : ℚ) -
    (Nat.totient q : ℚ) / q * h0

/-- Frozen paper `lem:Nq` / `eq:Nq-periodic`.

For every positive modulus and fixed residue data `(a,b)`, every positive
height on the canonical compatible progression has the exact form

`N_q(a;h) = phi(q)/q * h + epsilon_q(a,b)`.

No squarefreeness or analytic hypothesis is needed for this counting identity.
-/
theorem exactPeriodicCount
    {q a b : ℕ} (hq : 0 < q) (n : ℕ) :
    (admissibleInteriorCount q a
        (positiveGapRepresentative q a b + n * q) : ℚ) =
      (Nat.totient q : ℚ) / q *
          (positiveGapRepresentative q a b + n * q) +
        periodicError q a b := by
  let h0 := positiveGapRepresentative q a b
  have hh0 : 0 < h0 := by
    dsimp [h0]
    exact positiveGapRepresentative_pos hq
  rw [show positiveGapRepresentative q a b = h0 by rfl]
  rw [admissibleInteriorCount_progression q a h0 n hh0]
  unfold periodicError
  rw [show positiveGapRepresentative q a b = h0 by rfl]
  push_cast
  have hq0 : (q : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  field_simp [hq0]
  ring

end RML.Fourier.Vaaler.Internal
