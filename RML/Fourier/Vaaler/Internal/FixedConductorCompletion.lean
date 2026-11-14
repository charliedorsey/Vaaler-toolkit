module

public import RML.Fourier.Vaaler.Internal.RowReduction
public import Mathlib.Data.Int.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# Paper B fixed-conductor completion: exact arithmetic substrate

Frozen Paper B source:
* `paper_b_frozen.tex`
* label: `lem:fixed-conductor-completion`
* equations: `eq:combined-reciprocal-phase`,
  `eq:fixed-conductor-completion`, `eq:fixed-conductor-resonance`

This module presently formalizes the exact reduced-modulus/resonance arithmetic
which is independent of the analytic centered completion estimate.
-/

namespace RML.Fourier.Vaaler.Internal

def combinedModulus (r L : ℕ) : ℕ := r * L

def combinedNumeratorInt (A B : ℤ) (r L : ℕ) : ℤ :=
  A * (L : ℤ) + B * (r : ℤ)

def reciprocalReducedModulusInt (A B : ℤ) (r L : ℕ) : ℕ :=
  combinedModulus r L /
    Nat.gcd (combinedNumeratorInt A B r L).natAbs
      (combinedModulus r L)

/-- Exact full-resonance criterion for the combined reciprocal phase.
This is the arithmetic content of `eq:fixed-conductor-resonance`. -/
theorem reciprocalReducedModulusInt_eq_one_iff
    {A B : ℤ} {r L : ℕ}
    (hr : 0 < r) (hL : 0 < L) (hcop : r.Coprime L) :
    reciprocalReducedModulusInt A B r L = 1 ↔
      (r : ℤ) ∣ A ∧ (L : ℤ) ∣ B := by
  have hQ : 0 < combinedModulus r L := by
    unfold combinedModulus
    exact Nat.mul_pos hr hL
  constructor
  · intro hrho
    have hgcd :
        Nat.gcd (combinedNumeratorInt A B r L).natAbs
            (combinedModulus r L) =
          combinedModulus r L := by
      exact Nat.eq_of_dvd_of_div_eq_one
        (Nat.gcd_dvd_right _ _) hrho
    have hQdvdCabs :
        combinedModulus r L ∣
          (combinedNumeratorInt A B r L).natAbs :=
      Nat.gcd_eq_right_iff_dvd.mp hgcd
    have hQdvdC :
        (combinedModulus r L : ℤ) ∣
          combinedNumeratorInt A B r L :=
      Int.natCast_dvd.mpr hQdvdCabs
    have hrdvdC : (r : ℤ) ∣ combinedNumeratorInt A B r L := by
      rcases hQdvdC with ⟨k, hk⟩
      refine ⟨(L : ℤ) * k, ?_⟩
      unfold combinedModulus at hk
      push_cast at hk
      calc
        combinedNumeratorInt A B r L =
            (r : ℤ) * (L : ℤ) * k := hk
        _ = (r : ℤ) * ((L : ℤ) * k) := by ring
    have hLdvdC : (L : ℤ) ∣ combinedNumeratorInt A B r L := by
      rcases hQdvdC with ⟨k, hk⟩
      refine ⟨(r : ℤ) * k, ?_⟩
      unfold combinedModulus at hk
      push_cast at hk
      calc
        combinedNumeratorInt A B r L =
            (r : ℤ) * (L : ℤ) * k := hk
        _ = (L : ℤ) * ((r : ℤ) * k) := by ring
    have hrdvdAL : (r : ℤ) ∣ A * (L : ℤ) := by
      rcases hrdvdC with ⟨k, hk⟩
      refine ⟨k - B, ?_⟩
      unfold combinedNumeratorInt at hk
      nlinarith [hk]
    have hLdvdBr : (L : ℤ) ∣ B * (r : ℤ) := by
      rcases hLdvdC with ⟨k, hk⟩
      refine ⟨k - A, ?_⟩
      unfold combinedNumeratorInt at hk
      nlinarith [hk]
    have hrdvdAabs : r ∣ A.natAbs := by
      have hn : r ∣ (A * (L : ℤ)).natAbs :=
        Int.natCast_dvd.mp hrdvdAL
      rw [Int.natAbs_mul, Int.natAbs_natCast] at hn
      exact (hcop.dvd_mul_right).mp hn
    have hLdvdBabs : L ∣ B.natAbs := by
      have hn : L ∣ (B * (r : ℤ)).natAbs :=
        Int.natCast_dvd.mp hLdvdBr
      rw [Int.natAbs_mul, Int.natAbs_natCast] at hn
      exact (hcop.symm.dvd_mul_right).mp hn
    exact ⟨Int.natCast_dvd.mpr hrdvdAabs,
      Int.natCast_dvd.mpr hLdvdBabs⟩
  · rintro ⟨hrA, hLB⟩
    rcases hrA with ⟨a, ha⟩
    rcases hLB with ⟨b, hb⟩
    have hQdvdC :
        (combinedModulus r L : ℤ) ∣ combinedNumeratorInt A B r L := by
      refine ⟨a + b, ?_⟩
      unfold combinedModulus combinedNumeratorInt
      push_cast
      rw [ha, hb]
      ring
    have hQdvdCabs :
        combinedModulus r L ∣
          (combinedNumeratorInt A B r L).natAbs :=
      Int.natCast_dvd.mp hQdvdC
    have hgcd :
        Nat.gcd (combinedNumeratorInt A B r L).natAbs
            (combinedModulus r L) =
          combinedModulus r L :=
      Nat.gcd_eq_right_iff_dvd.mpr hQdvdCabs
    unfold reciprocalReducedModulusInt
    rw [hgcd]
    exact Nat.div_self hQ

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Predicate form of the manuscript's unit-preserving squarefree-removal
identity. This is exactly the support bookkeeping needed before the weighted
Möbius expansion: under squarefree/unit hypotheses on `d`, admissibility of
`d*n` is equivalent to admissibility of `n` with the new forbidden factor
`d*R`. -/
theorem fixedQ_squarefree_removal_support_iff
    {d n q R : ℕ}
    (hdsq : Squarefree d)
    (hdunit : d.Coprime (6 * q * R)) :
    (Squarefree (d * n) ∧
      (d * n).Coprime (6 * R) ∧
      (d * n).Coprime q) ↔
    (n.Coprime (6 * q) ∧
      Squarefree n ∧
      n.Coprime (d * R)) := by
  have hd_atoms : d.Coprime 6 ∧ d.Coprime q ∧ d.Coprime R := by
    simpa [Nat.coprime_mul_iff_right, mul_assoc] using hdunit
  constructor
  · rintro ⟨hdsn, hdn6R, hdnq⟩
    have hdn_atoms : d.Coprime n ∧ Squarefree d ∧ Squarefree n :=
      Nat.squarefree_mul_iff.mp hdsn
    have hn6R : n.Coprime (6 * R) :=
      (Nat.coprime_mul_iff_left.mp hdn6R).2
    have hnq : n.Coprime q :=
      (Nat.coprime_mul_iff_left.mp hdnq).2
    have hn6 : n.Coprime 6 :=
      (Nat.coprime_mul_iff_right.mp hn6R).1
    have hnR : n.Coprime R :=
      (Nat.coprime_mul_iff_right.mp hn6R).2
    have hnd : n.Coprime d := hdn_atoms.1.symm
    refine ⟨?_, hdn_atoms.2.2, ?_⟩
    · exact Nat.Coprime.mul_right hn6 hnq
    · exact Nat.Coprime.mul_right hnd hnR
  · rintro ⟨hn6q, hnsq, hndR⟩
    have hn_atoms : n.Coprime 6 ∧ n.Coprime q :=
      Nat.coprime_mul_iff_right.mp hn6q
    have hnd_atoms : n.Coprime d ∧ n.Coprime R :=
      Nat.coprime_mul_iff_right.mp hndR
    have hdn : d.Coprime n := hnd_atoms.1.symm
    have hdsn : Squarefree (d * n) :=
      (Nat.squarefree_mul hdn).2 ⟨hdsq, hnsq⟩
    have hd6R : d.Coprime (6 * R) :=
      Nat.Coprime.mul_right hd_atoms.1 hd_atoms.2.2
    have hn6R : n.Coprime (6 * R) :=
      Nat.Coprime.mul_right hn_atoms.1 hnd_atoms.2
    have hdn6R : (d * n).Coprime (6 * R) :=
      Nat.Coprime.mul_left hd6R hn6R
    have hdnq : (d * n).Coprime q :=
      Nat.Coprime.mul_left hd_atoms.2.1 hn_atoms.2
    exact ⟨hdsn, hdn6R, hdnq⟩

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

open scoped ArithmeticFunction.Moebius

def intIndicator (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

lemma intIndicator_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    intIndicator P * intIndicator Q = intIndicator (P ∧ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [intIndicator, hP, hQ]

lemma intIndicator_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) :
    intIndicator P = intIndicator Q := by
  by_cases hP : P
  · have hQ : Q := h.mp hP
    simp [intIndicator, hP, hQ]
  · have hQ : ¬Q := fun hq => hP (h.mpr hq)
    simp [intIndicator, hP, hQ]

/-- Literal integer-valued form of `eq:fixed-q-squarefree-removal`.
It is the manuscript identity
`μ²(dn) 1_(dn,6R)=1 1_(dn,q)=1 =
  1_(n,6q)=1 μ²(n) 1_(n,dR)=1`
under the stated squarefree/unit hypotheses on `d`. -/
theorem fixedQ_squarefree_removal_exact
    {d n q R : ℕ}
    (hdsq : Squarefree d)
    (hdunit : d.Coprime (6 * q * R)) :
    ArithmeticFunction.moebius (d * n) ^ 2 *
        intIndicator ((d * n).Coprime (6 * R)) *
        intIndicator ((d * n).Coprime q) =
      intIndicator (n.Coprime (6 * q)) *
        ArithmeticFunction.moebius n ^ 2 *
        intIndicator (n.Coprime (d * R)) := by
  rw [ArithmeticFunction.moebius_sq, ArithmeticFunction.moebius_sq]
  change
    intIndicator (Squarefree (d * n)) *
        intIndicator ((d * n).Coprime (6 * R)) *
        intIndicator ((d * n).Coprime q) =
      intIndicator (n.Coprime (6 * q)) *
        intIndicator (Squarefree n) *
        intIndicator (n.Coprime (d * R))
  calc
    intIndicator (Squarefree (d * n)) *
          intIndicator ((d * n).Coprime (6 * R)) *
          intIndicator ((d * n).Coprime q) =
        intIndicator
          (Squarefree (d * n) ∧
            (d * n).Coprime (6 * R) ∧
            (d * n).Coprime q) := by
              rw [intIndicator_mul, intIndicator_mul]
              simp [and_assoc]
    _ = intIndicator
          (n.Coprime (6 * q) ∧
            Squarefree n ∧
            n.Coprime (d * R)) := by
              exact intIndicator_congr
                (fixedQ_squarefree_removal_support_iff hdsq hdunit)
    _ = intIndicator (n.Coprime (6 * q)) *
          intIndicator (Squarefree n) *
          intIndicator (n.Coprime (d * R)) := by
              rw [intIndicator_mul, intIndicator_mul]
              simp [and_assoc]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Exact combined additive-phase identity on a common integer representative.
If `t` represents the reciprocal of a supported `ℓ` modulo `r*L`, this is
the manuscript identity
`e_r(A ℓ̄) e_L(B ℓ̄) = e_{rL}((A L + B r) ℓ̄)`. -/
theorem combined_reciprocal_phase_intCast
    {r L : ℕ}
    [NeZero r] [NeZero L] [NeZero (combinedModulus r L)]
    (A B t : ℤ) :
    ZMod.stdAddChar (((A * t : ℤ)) : ZMod r) *
        ZMod.stdAddChar (((B * t : ℤ)) : ZMod L) =
      ZMod.stdAddChar
        ((((combinedNumeratorInt A B r L) * t : ℤ)) :
          ZMod (combinedModulus r L)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  unfold combinedNumeratorInt combinedModulus
  push_cast
  have hr0 : (r : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne r)
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne L)
  field_simp [hr0, hL0]

end RML.Fourier.Vaaler.Internal
namespace RML.Fourier.Vaaler.Internal

noncomputable def kloostermanSumPrime (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) : ℂ :=
  ∑ x : ZMod p, if x = 0 then 0 else ZMod.stdAddChar (b * x + a * x⁻¹)

noncomputable def zmodInvEquiv (p : ℕ) [Fact p.Prime] : ZMod p ≃ ZMod p where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

lemma kloostermanSumPrime_zero_left (p : ℕ) [Fact p.Prime]
    (b : ZMod p) (hb : b ≠ 0) :
    kloostermanSumPrime p 0 b = -1 := by
  unfold kloostermanSumPrime
  rw [← gaussSum_one_left (ψ := (ZMod.stdAddChar (N := p)).mulShift b)]
  · rw [gaussSum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h0 : x = 0
    · subst x
      simp [MulChar.map_zero]
    · have hxunit : IsUnit x := isUnit_iff_ne_zero.mpr h0
      simp [h0, AddChar.mulShift_apply, MulChar.one_apply hxunit]
  · intro h
    have hp : (ZMod.stdAddChar (N := p)).IsPrimitive :=
      ZMod.isPrimitive_stdAddChar p
    exact hp hb h

lemma kloostermanSumPrime_comm (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) :
    kloostermanSumPrime p a b = kloostermanSumPrime p b a := by
  unfold kloostermanSumPrime
  apply Fintype.sum_equiv (zmodInvEquiv p)
  intro x
  by_cases h0 : x = 0
  · subst x
    simp [zmodInvEquiv]
  · have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero h0
    simp [zmodInvEquiv, h0, hinv0, add_comm]

lemma kloostermanSumPrime_zero_right (p : ℕ) [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    kloostermanSumPrime p a 0 = -1 := by
  rw [kloostermanSumPrime_comm]
  exact kloostermanSumPrime_zero_left p a ha

lemma kloostermanSumPrime_zero_zero (p : ℕ) [Fact p.Prime] :
    kloostermanSumPrime p 0 0 = (p : ℂ) - 1 := by
  unfold kloostermanSumPrime
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one]
  have hone :
      (∑ x : ZMod p, if x = 0 then (1 : ℂ) else 0) = 1 := by
    exact Fintype.sum_ite_eq' 0 (fun _ : ZMod p => (1 : ℂ))
  calc
    (∑ x : ZMod p, if x = 0 then 0 else (1 : ℂ)) =
        ∑ x : ZMod p, ((1 : ℂ) - if x = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h0 : x = 0 <;> simp [h0]
    _ = (∑ _x : ZMod p, (1 : ℂ)) -
        (∑ x : ZMod p, if x = 0 then (1 : ℂ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = (p : ℂ) - 1 := by
          rw [hone]
          simp

def PrimeNondegenerateWeil : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    a ≠ 0 → b ≠ 0 →
      ‖kloostermanSumPrime p a b‖ ≤ 2 * Real.sqrt p

end RML.Fourier.Vaaler.Internal




namespace RML.Fourier.Vaaler.Internal

theorem kloostermanSumPrime_le_two_sqrt_of_not_both_zero
    (hWeil : PrimeNondegenerateWeil)
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ‖kloostermanSumPrime p a b‖ ≤ 2 * Real.sqrt p := by
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt p := (Real.one_le_sqrt).2 hp1
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := hnot.resolve_left (by simp)
    rw [kloostermanSumPrime_zero_left p b hb]
    norm_num
    nlinarith
  · by_cases hb : b = 0
    · subst b
      rw [kloostermanSumPrime_zero_right p a ha]
      norm_num
      nlinarith
    · exact hWeil p a b ha hb

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def crtLeftCoeff (m n : ℕ) : ℤ := n.gcdA m

def crtRightCoeff (m n : ℕ) : ℤ := n.gcdB m

lemma crt_bezout
    {m n : ℕ} (hcop : m.Coprime n) :
    (n : ℤ) * crtLeftCoeff m n + (m : ℤ) * crtRightCoeff m n = 1 := by
  unfold crtLeftCoeff crtRightCoeff
  have h := Nat.gcd_eq_gcd_ab n m
  rw [Nat.Coprime.gcd_eq_one hcop.symm] at h
  simpa [add_comm] using h.symm

lemma stdAddChar_mul_eq_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (t : ℤ) :
    ZMod.stdAddChar
        (((crtLeftCoeff m n) * t : ℤ) : ZMod m) *
      ZMod.stdAddChar
        (((crtRightCoeff m n) * t : ℤ) : ZMod n) =
      ZMod.stdAddChar ((t : ℤ) : ZMod (m * n)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hbez := crt_bezout hcop
  have hbezC :
      (n : ℂ) * (crtLeftCoeff m n : ℂ) +
          (m : ℂ) * (crtRightCoeff m n : ℂ) = 1 := by
    exact_mod_cast hbez
  have hfrac :
      (crtLeftCoeff m n : ℂ) / (m : ℂ) +
          (crtRightCoeff m n : ℂ) / (n : ℂ) =
        1 / ((m : ℂ) * (n : ℂ)) := by
    field_simp [hm0, hn0]
    linear_combination hbezC
  push_cast
  calc
    2 * ↑Real.pi * Complex.I * (↑(crtLeftCoeff m n) * ↑t) / ↑m +
          2 * ↑Real.pi * Complex.I * (↑(crtRightCoeff m n) * ↑t) / ↑n =
        (2 * ↑Real.pi * Complex.I * ↑t) *
          (↑(crtLeftCoeff m n) / ↑m + ↑(crtRightCoeff m n) / ↑n) := by ring
    _ = (2 * ↑Real.pi * Complex.I * ↑t) *
          (1 / ((m : ℂ) * (n : ℂ))) := by rw [hfrac]
    _ = 2 * ↑Real.pi * Complex.I * ↑t / (↑m * ↑n) := by ring

noncomputable def kloostermanSum
    (N : ℕ) [NeZero N] (a b : ZMod N) : ℂ :=
  ∑ x : ZMod N,
    if IsUnit x then ZMod.stdAddChar (b * x + a * x⁻¹) else 0

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def kloostermanUnitSum
    (N : ℕ) [NeZero N] (a b : ZMod N) : ℂ :=
  ∑ x : (ZMod N)ˣ,
    ZMod.stdAddChar
      (b * (x : ZMod N) + a * ((x⁻¹ : (ZMod N)ˣ) : ZMod N))

lemma stdAddChar_mul_eq_crt_zmod
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (z : ZMod (m * n)) :
    ZMod.stdAddChar
        (((crtLeftCoeff m n : ℤ) : ZMod m) *
          (ZMod.chineseRemainder hcop z).1) *
      ZMod.stdAddChar
        (((crtRightCoeff m n : ℤ) : ZMod n) *
          (ZMod.chineseRemainder hcop z).2) =
      ZMod.stdAddChar z := by
  rw [← ZMod.natCast_zmod_val z]
  have hleft :
      (ZMod.chineseRemainder hcop ((z.val : ℕ) : ZMod (m * n))).1 =
        (z.val : ZMod m) := by
    simp [ZMod.chineseRemainder]
  have hright :
      (ZMod.chineseRemainder hcop ((z.val : ℕ) : ZMod (m * n))).2 =
        (z.val : ZMod n) := by
    simp [ZMod.chineseRemainder]
  rw [hleft, hright]
  simpa using (stdAddChar_mul_eq_crt hcop (z.val : ℤ))

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def crtUnitsEquiv
    {m n : ℕ} (hcop : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans
    MulEquiv.prodUnits

theorem kloostermanUnitSum_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (a b : ZMod (m * n)) :
    kloostermanUnitSum (m * n) a b =
      kloostermanUnitSum m
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop a).1)
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop b).1) *
        kloostermanUnitSum n
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop a).2)
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop b).2) := by
  let e := crtUnitsEquiv hcop
  let α : ZMod m := ((crtLeftCoeff m n : ℤ) : ZMod m)
  let β : ZMod n := ((crtRightCoeff m n : ℤ) : ZMod n)
  let am : ZMod m := α * (ZMod.chineseRemainder hcop a).1
  let bm : ZMod m := α * (ZMod.chineseRemainder hcop b).1
  let an : ZMod n := β * (ZMod.chineseRemainder hcop a).2
  let bn : ZMod n := β * (ZMod.chineseRemainder hcop b).2
  let f : (ZMod m)ˣ → ℂ := fun x =>
    ZMod.stdAddChar (bm * (x : ZMod m) + am * ((x⁻¹ : (ZMod m)ˣ) : ZMod m))
  let g : (ZMod n)ˣ → ℂ := fun x =>
    ZMod.stdAddChar (bn * (x : ZMod n) + an * ((x⁻¹ : (ZMod n)ˣ) : ZMod n))
  change
    (∑ x : (ZMod (m * n))ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod (m * n)) + a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))) =
      (∑ x : (ZMod m)ˣ, f x) * (∑ y : (ZMod n)ˣ, g y)
  calc
    (∑ x : (ZMod (m * n))ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod (m * n)) + a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))) =
        ∑ y : (ZMod m)ˣ × (ZMod n)ˣ, f y.1 * g y.2 := by
          apply Fintype.sum_equiv e.toEquiv
          intro x
          have hx1 :
              (((e x).1 : (ZMod m)ˣ) : ZMod m) =
                (ZMod.chineseRemainder hcop (x : ZMod (m * n))).1 := by
            rfl
          have hx2 :
              (((e x).2 : (ZMod n)ˣ) : ZMod n) =
                (ZMod.chineseRemainder hcop (x : ZMod (m * n))).2 := by
            rfl
          have heinv : e (x⁻¹) = (e x)⁻¹ := map_inv e x
          have h1u : (e (x⁻¹)).1 = (e x).1⁻¹ :=
            congrArg Prod.fst heinv
          have h2u : (e (x⁻¹)).2 = (e x).2⁻¹ :=
            congrArg Prod.snd heinv
          have hxinv1 :
              ((((e x).1)⁻¹ : (ZMod m)ˣ) : ZMod m) =
                (ZMod.chineseRemainder hcop
                  ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n))).1 := by
            rw [← h1u]
            rfl
          have hxinv2 :
              ((((e x).2)⁻¹ : (ZMod n)ˣ) : ZMod n) =
                (ZMod.chineseRemainder hcop
                  ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n))).2 := by
            rw [← h2u]
            rfl
          have hchar := stdAddChar_mul_eq_crt_zmod hcop
            (b * (x : ZMod (m * n)) +
              a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))
          rw [← hchar]
          dsimp [f, g, am, bm, an, bn, α, β]
          rw [hx1, hx2, hxinv1, hxinv2]
          simp
          apply congrArg₂ (· * ·)
          · congr 1
            ring
          · congr 1
            ring
    _ = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod n)ˣ, f x * g y := by
          rw [Fintype.sum_prod_type]
    _ = (∑ x : (ZMod m)ˣ, f x) * (∑ y : (ZMod n)ˣ, g y) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem kloostermanUnitSum_prime_eq
    (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    kloostermanUnitSum p a b = kloostermanSumPrime p a b := by
  unfold kloostermanUnitSum kloostermanSumPrime
  calc
    (∑ x : (ZMod p)ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod p) + a * ((x⁻¹ : (ZMod p)ˣ) : ZMod p))) =
      ∑ y : {x : ZMod p // x ≠ 0},
        ZMod.stdAddChar (b * y.1 + a * y.1⁻¹) := by
          apply Fintype.sum_equiv unitsEquivNeZero
          intro x
          rw [unitsEquivNeZero_apply_coe, ZMod.inv_coe_unit]
    _ = ∑ x : ZMod p,
        if x = 0 then 0 else ZMod.stdAddChar (b * x + a * x⁻¹) := by
          rw [show (∑ y : {x : ZMod p // x ≠ 0},
              ZMod.stdAddChar (b * y.1 + a * y.1⁻¹)) =
              ∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ≠ 0),
                ZMod.stdAddChar (b * x + a * x⁻¹) by
                simpa using
                  (Finset.sum_subtype_eq_sum_filter
                    (s := (Finset.univ : Finset (ZMod p)))
                    (f := fun x : ZMod p =>
                      ZMod.stdAddChar (b * x + a * x⁻¹))
                    (p := fun x : ZMod p => x ≠ 0))]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h0 : x = 0 <;> simp [h0]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem norm_kloostermanUnitSum_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (a b : ZMod (m * n)) :
    ‖kloostermanUnitSum (m * n) a b‖ =
      ‖kloostermanUnitSum m
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop a).1)
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop b).1)‖ *
        ‖kloostermanUnitSum n
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop a).2)
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop b).2)‖ := by
  rw [kloostermanUnitSum_crt hcop]
  exact norm_mul _ _

theorem kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
    (hWeil : PrimeNondegenerateWeil)
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ‖kloostermanUnitSum p a b‖ ≤ 2 * Real.sqrt p := by
  rw [kloostermanUnitSum_prime_eq]
  exact kloostermanSumPrime_le_two_sqrt_of_not_both_zero
    hWeil p a b hnot

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma crtLeftCoeff_isUnit
    {m n : ℕ} [NeZero m] (hcop : m.Coprime n) :
    IsUnit (((crtLeftCoeff m n : ℤ) : ZMod m)) := by
  have hmul :
      (n : ZMod m) * (((crtLeftCoeff m n : ℤ) : ZMod m)) = 1 := by
    unfold crtLeftCoeff
    rw [CharP.intCast_mul_natCast_gcdA_eq_gcd]
    simp [Nat.Coprime.gcd_eq_one hcop.symm]
  exact IsUnit.of_mul_eq_one (n : ZMod m) (by simpa [mul_comm] using hmul)

lemma crtRightCoeff_isUnit
    {m n : ℕ} [NeZero n] (hcop : m.Coprime n) :
    IsUnit (((crtRightCoeff m n : ℤ) : ZMod n)) := by
  have hbez := crt_bezout hcop
  have hbezZ :
      (n : ZMod n) * (((crtLeftCoeff m n : ℤ) : ZMod n)) +
          (m : ZMod n) * (((crtRightCoeff m n : ℤ) : ZMod n)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod n)) hbez
    simpa using h
  have hmul :
      (m : ZMod n) * (((crtRightCoeff m n : ℤ) : ZMod n)) = 1 := by
    simpa using hbezZ
  exact IsUnit.of_mul_eq_one (m : ZMod n) (by simpa [mul_comm] using hmul)

lemma crt_local_left_isUnit
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) {a : ZMod (m * n)} (ha : IsUnit a) :
    IsUnit
      ((((crtLeftCoeff m n : ℤ) : ZMod m) *
        (ZMod.chineseRemainder hcop a).1)) := by
  have hpair : IsUnit (ZMod.chineseRemainder hcop a) :=
    ha.map (ZMod.chineseRemainder hcop).toMonoidHom
  have hproj : IsUnit (ZMod.chineseRemainder hcop a).1 :=
    (Prod.isUnit_iff.mp hpair).1
  exact (crtLeftCoeff_isUnit hcop).mul hproj

lemma crt_local_right_isUnit
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) {a : ZMod (m * n)} (ha : IsUnit a) :
    IsUnit
      ((((crtRightCoeff m n : ℤ) : ZMod n) *
        (ZMod.chineseRemainder hcop a).2)) := by
  have hpair : IsUnit (ZMod.chineseRemainder hcop a) :=
    ha.map (ZMod.chineseRemainder hcop).toMonoidHom
  have hproj : IsUnit (ZMod.chineseRemainder hcop a).2 :=
    (Prod.isUnit_iff.mp hpair).2
  exact (crtRightCoeff_isUnit hcop).mul hproj

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem kloostermanUnitSum_prod_primes_le
    (hWeil : PrimeNondegenerateWeil) :
    ∀ (s : Finset ℕ) (Q : ℕ)
      (hQ : Q = ∏ p ∈ s, p) (hQ0 : Q ≠ 0)
      (hsprime : ∀ p ∈ s, p.Prime)
      (a b : ZMod Q), IsUnit a →
        ‖@kloostermanUnitSum Q ⟨hQ0⟩ a b‖ ≤
          (2 : ℝ) ^ s.card * Real.sqrt Q := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro Q hQ hQ0 hsprime a b ha
      subst Q
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero,
        Nat.cast_one, Real.sqrt_one, one_mul] at a b ha ⊢
      simpa [kloostermanUnitSum, Subsingleton.elim a 0,
        Subsingleton.elim b 0]
  | @insert p s hpnot ih =>
      intro Q hQ hQ0 hsprime a b ha
      have hpP : p.Prime := hsprime p (by simp)
      have hsP : ∀ r ∈ s, r.Prime := by
        intro r hr
        exact hsprime r (by simp [hr])
      let M : ℕ := ∏ r ∈ s, r
      have hM0 : M ≠ 0 := by
        dsimp [M]
        exact Finset.prod_ne_zero_iff.mpr fun r hr => (hsP r hr).ne_zero
      have hQeq : Q = p * M := by
        calc
          Q = ∏ r ∈ insert p s, r := hQ
          _ = p * M := by simp [M, hpnot]
      clear hQ
      subst Q
      letI : NeZero M := ⟨hM0⟩
      letI : Fact p.Prime := ⟨hpP⟩
      letI : NeZero (p * M) := ⟨mul_ne_zero hpP.ne_zero hM0⟩
      have hcop : p.Coprime M := by
        apply hpP.coprime_iff_not_dvd.mpr
        intro hpd
        have hex := (hpP.prime.dvd_finsetProd_iff (fun r : ℕ => r)).mp hpd
        rcases hex with ⟨r, hr, hpr⟩
        have hrP := hsP r hr
        have hrpeq : r = p := (hrP.dvd_iff_eq hpP.ne_one).mp hpr
        exact hpnot (hrpeq ▸ hr)
      have haP :
          IsUnit
            ((((crtLeftCoeff p M : ℤ) : ZMod p) *
              (ZMod.chineseRemainder hcop a).1)) :=
        crt_local_left_isUnit hcop ha
      have haM :
          IsUnit
            ((((crtRightCoeff p M : ℤ) : ZMod M) *
              (ZMod.chineseRemainder hcop a).2)) :=
        crt_local_right_isUnit hcop ha
      have hprime :
          ‖kloostermanUnitSum p
              (((crtLeftCoeff p M : ℤ) : ZMod p) *
                (ZMod.chineseRemainder hcop a).1)
              (((crtLeftCoeff p M : ℤ) : ZMod p) *
                (ZMod.chineseRemainder hcop b).1)‖ ≤
            2 * Real.sqrt p := by
        apply kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
          hWeil p
        exact Or.inl haP.ne_zero
      have hrec :
          ‖kloostermanUnitSum M
              (((crtRightCoeff p M : ℤ) : ZMod M) *
                (ZMod.chineseRemainder hcop a).2)
              (((crtRightCoeff p M : ℤ) : ZMod M) *
                (ZMod.chineseRemainder hcop b).2)‖ ≤
            (2 : ℝ) ^ s.card * Real.sqrt M := by
        exact ih M rfl hM0 hsP _ _ haM
      rw [norm_kloostermanUnitSum_crt hcop]
      calc
        _ ≤ (2 * Real.sqrt p) *
              ((2 : ℝ) ^ s.card * Real.sqrt M) :=
          mul_le_mul hprime hrec (norm_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (insert p s).card *
              Real.sqrt ((p : ℝ) * (M : ℝ)) := by
          rw [Finset.card_insert_of_notMem hpnot, pow_succ]
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ p)]
          ring
        _ = (2 : ℝ) ^ (insert p s).card *
              Real.sqrt (((p * M : ℕ) : ℝ)) := by
          rw [Nat.cast_mul]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem kloostermanUnitSum_squarefree_unit_le
    (hWeil : PrimeNondegenerateWeil)
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (a b : ZMod q) (ha : IsUnit a) :
    ‖kloostermanUnitSum q a b‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q := by
  exact kloostermanUnitSum_prod_primes_le hWeil
    q.primeFactors q
    (Nat.prod_primeFactors_of_squarefree hsq).symm
    (NeZero.ne q)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    a b ha

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def reducedDivisor (A q : ℕ) : ℕ := Nat.gcd A q

def reducedModulus (A q : ℕ) : ℕ := q / reducedDivisor A q

def reducedNumerator (A q : ℕ) : ℕ := A / reducedDivisor A q

lemma reducedNumerator_coprime_reducedModulus
    {A q : ℕ} (hq : 0 < q) :
    (reducedNumerator A q).Coprime (reducedModulus A q) := by
  unfold reducedNumerator reducedModulus reducedDivisor
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right A hq)

lemma reducedModulus_dvd
    {A q : ℕ} :
    reducedModulus A q ∣ q := by
  unfold reducedModulus reducedDivisor
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right A q)

lemma reducedModulus_pos
    {A q : ℕ} (hq : 0 < q) :
    0 < reducedModulus A q := by
  unfold reducedModulus reducedDivisor
  apply Nat.div_pos
  · exact Nat.gcd_le_right A hq
  · exact Nat.gcd_pos_of_pos_right A hq

lemma reducedModulus_squarefree
    {A q : ℕ} (hsq : Squarefree q) :
    Squarefree (reducedModulus A q) :=
  hsq.squarefree_of_dvd reducedModulus_dvd

lemma reducedNumerator_isUnit
    {A q : ℕ} (hq : 0 < q) :
    IsUnit ((reducedNumerator A q : ℕ) : ZMod (reducedModulus A q)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact reducedNumerator_coprime_reducedModulus hq

theorem kloostermanUnitSum_reduced_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (b : ZMod (reducedModulus A q)) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖kloostermanUnitSum (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q)) b‖ ≤
      (2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
        Real.sqrt (reducedModulus A q) := by
  letI : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  exact kloostermanUnitSum_squarefree_unit_le hWeil
    (reducedModulus_squarefree hsq)
    (reducedNumerator A q : ZMod (reducedModulus A q)) b
    (reducedNumerator_isUnit hq)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def zmodFrequencyDistance {N : ℕ} [NeZero N] (h : ZMod N) : ℕ :=
  min h.val (N - h.val)

lemma zmodFrequencyDistance_pos
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) :
    0 < zmodFrequencyDistance h := by
  unfold zmodFrequencyDistance
  have hv0 : 0 < h.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero h).2 hh)
  have hvlt : h.val < N := ZMod.val_lt h
  exact lt_min hv0 (Nat.sub_pos_of_lt hvlt)

lemma two_mul_zmodFrequencyDistance_le
    {N : ℕ} [NeZero N] (h : ZMod N) :
    2 * zmodFrequencyDistance h ≤ N := by
  unfold zmodFrequencyDistance
  have h1 : min h.val (N - h.val) ≤ h.val := min_le_left _ _
  have h2 : min h.val (N - h.val) ≤ N - h.val := min_le_right _ _
  have hvlt : h.val < N := ZMod.val_lt h
  omega

lemma stdAddChar_chord_lower
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) :
    (4 : ℝ) * zmodFrequencyDistance h / N ≤
      ‖ZMod.stdAddChar h - 1‖ := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (NeZero.pos N)
  have hkpos : (0 : ℝ) < zmodFrequencyDistance h := by
    exact_mod_cast zmodFrequencyDistance_pos hh
  have h2k : (2 : ℝ) * zmodFrequencyDistance h ≤ N := by
    exact_mod_cast two_mul_zmodFrequencyDistance_le h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  let x : ℝ := Real.pi * (h.val : ℝ) / N
  let k : ℕ := zmodFrequencyDistance h
  have hsin :
      (2 : ℝ) * k / N ≤ |Real.sin x| := by
    by_cases hsmall : h.val ≤ N - h.val
    · have hk : k = h.val := by
        dsimp [k, zmodFrequencyDistance]
        exact min_eq_left hsmall
      have hx0 : 0 ≤ x := by
        dsimp [x]
        positivity
      have hxhalf : x ≤ Real.pi / 2 := by
        dsimp [x]
        have hv : (2 : ℝ) * h.val ≤ N := by
          exact_mod_cast (by omega : 2 * h.val ≤ N)
        apply (div_le_iff₀ hNpos).2
        nlinarith
      have hs := Real.mul_le_sin hx0 hxhalf
      have hsin0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0
        (hxhalf.trans (by linarith [Real.pi_pos]))
      rw [abs_of_nonneg hsin0, hk]
      calc
        (2 : ℝ) * h.val / N =
            (2 / Real.pi) * x := by
              dsimp [x]
              field_simp [hNpos.ne', Real.pi_ne_zero]
        _ ≤ Real.sin x := hs
    · have hbig : N - h.val ≤ h.val := by omega
      have hk : k = N - h.val := by
        dsimp [k, zmodFrequencyDistance]
        exact min_eq_right hbig
      let y : ℝ := Real.pi * ((N - h.val : ℕ) : ℝ) / N
      have hy0 : 0 ≤ y := by
        dsimp [y]
        positivity
      have hyhalf : y ≤ Real.pi / 2 := by
        dsimp [y]
        have hv : (2 : ℝ) * (N - h.val : ℕ) ≤ N := by
          exact_mod_cast (by omega : 2 * (N - h.val) ≤ N)
        apply (div_le_iff₀ hNpos).2
        nlinarith
      have hxy : y = Real.pi - x := by
        dsimp [x, y]
        have hvlt : h.val < N := ZMod.val_lt h
        rw [Nat.cast_sub (Nat.le_of_lt hvlt)]
        field_simp [hNpos.ne']
      have hs := Real.mul_le_sin hy0 hyhalf
      have hsin0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0
        (hyhalf.trans (by linarith [Real.pi_pos]))
      have hsineq : Real.sin y = Real.sin x := by
        rw [hxy, Real.sin_pi_sub]
      rw [← hsineq, abs_of_nonneg hsin0, hk]
      calc
        (2 : ℝ) * (N - h.val : ℕ) / N =
            (2 / Real.pi) * y := by
              dsimp [y]
              field_simp [hNpos.ne', Real.pi_ne_zero]
        _ ≤ Real.sin y := hs
  have hnorm :
      ‖ZMod.stdAddChar h - 1‖ =
        2 * |Real.sin x| := by
    rw [← ZMod.natCast_zmod_val h]
    have hcast :
        ((h.val : ℕ) : ZMod N) = ((h.val : ℤ) : ZMod N) := by
      norm_cast
    rw [hcast, ZMod.stdAddChar_coe]
    have hexp :
        Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((h.val : ℤ) : ℂ) / (N : ℂ)) =
          Complex.exp (Complex.I * ((2 * x : ℝ) : ℂ)) := by
      congr 1
      dsimp [x]
      push_cast
      ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs]
  rw [hnorm]
  calc
    (4 : ℝ) * zmodFrequencyDistance h / N =
        2 * ((2 : ℝ) * k / N) := by
          dsimp [k]
          ring
    _ ≤ 2 * |Real.sin x| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def unitsEquivIsUnitSubtype (M : Type*) [Monoid M] :
    Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := by
    apply Units.ext
    simp [IsUnit.unit_of_val_units]
  right_inv x := by
    apply Subtype.ext
    exact x.2.unit_spec

noncomputable def reciprocalPhase
    (N : ℕ) [NeZero N] (a x : ZMod N) : ℂ :=
  if IsUnit x then ZMod.stdAddChar (a * x⁻¹) else 0

noncomputable def reciprocalMean
    (N : ℕ) [NeZero N] (a : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, reciprocalPhase N a x

noncomputable def centeredReciprocalPhase
    (N : ℕ) [NeZero N] (a x : ZMod N) : ℂ :=
  reciprocalPhase N a x - reciprocalMean N a

lemma sum_centeredReciprocalPhase_eq_zero
    (N : ℕ) [NeZero N] (a : ZMod N) :
    ∑ x : ZMod N, centeredReciprocalPhase N a x = 0 := by
  unfold centeredReciprocalPhase reciprocalMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp [nsmul_eq_mul, hN]

lemma sum_reciprocalPhase_eq_kloostermanUnitSum
    (N : ℕ) [NeZero N] (a b : ZMod N) :
    (∑ x : ZMod N,
      ZMod.stdAddChar (b * x) * reciprocalPhase N a x) =
      kloostermanUnitSum N a b := by
  unfold reciprocalPhase kloostermanUnitSum
  calc
    (∑ x : ZMod N,
      ZMod.stdAddChar (b * x) *
        (if IsUnit x then ZMod.stdAddChar (a * x⁻¹) else 0)) =
      ∑ x ∈ (Finset.univ.filter fun x : ZMod N => IsUnit x),
        ZMod.stdAddChar (b * x + a * x⁻¹) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hu : IsUnit x
          · simp [hu, AddChar.map_add_eq_mul]
          · simp [hu]
    _ = ∑ y : {x : ZMod N // IsUnit x},
        ZMod.stdAddChar (b * y.1 + a * y.1⁻¹) := by
          symm
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (ZMod N)))
              (f := fun x : ZMod N =>
                ZMod.stdAddChar (b * x + a * x⁻¹))
              (p := fun x : ZMod N => IsUnit x))
    _ = ∑ u : (ZMod N)ˣ,
        ZMod.stdAddChar
          (b * (u : ZMod N) +
            a * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
          symm
          apply Fintype.sum_equiv (unitsEquivIsUnitSubtype (ZMod N))
          intro u
          simp [unitsEquivIsUnitSubtype, ZMod.inv_coe_unit]

lemma dft_centeredReciprocalPhase_nonzero
    (N : ℕ) [NeZero N] (a : ZMod N) {h : ZMod N} (hh : h ≠ 0) :
    ZMod.dft (centeredReciprocalPhase N a) h =
      kloostermanUnitSum N a (-h) := by
  rw [ZMod.dft_apply]
  unfold centeredReciprocalPhase
  simp only [smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hchar :
      (∑ j : ZMod N, ZMod.stdAddChar (-(j * h))) = 0 := by
    have hprim : (ZMod.stdAddChar (N := N)).IsPrimitive :=
      ZMod.isPrimitive_stdAddChar N
    have hne :
        (ZMod.stdAddChar (N := N)).mulShift (-h) ≠ 1 :=
      hprim (neg_ne_zero.mpr hh)
    have hz := AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm] using hz
  calc
    (∑ j : ZMod N,
      ZMod.stdAddChar (-(j * h)) *
        reciprocalPhase N a j) -
        ∑ j : ZMod N,
          ZMod.stdAddChar (-(j * h)) *
            reciprocalMean N a =
      ∑ j : ZMod N,
        ZMod.stdAddChar ((-h) * j) *
          reciprocalPhase N a j := by
            have hconst :
                (∑ j : ZMod N,
                  ZMod.stdAddChar (-(j * h)) *
                    reciprocalMean N a) = 0 := by
              rw [← Finset.sum_mul, hchar, zero_mul]
            rw [hconst, sub_zero]
            apply Finset.sum_congr rfl
            intro j hj
            congr 2
            ring
    _ = kloostermanUnitSum N a (-h) := by
          simpa [neg_mul, mul_comm] using
            sum_reciprocalPhase_eq_kloostermanUnitSum N a (-h)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Bézout/CRT factorization of the standard additive character on a coprime
product modulus. The local shifts are units modulo the opposite factors. -/
theorem stdAddChar_crt_bezout
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (y : ℤ) :
    ZMod.stdAddChar (y : ZMod (m * n)) =
      ZMod.stdAddChar ((n.gcdA m * y : ℤ) : ZMod m) *
      ZMod.stdAddChar ((n.gcdB m * y : ℤ) : ZMod n) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hbez : (1 : ℤ) =
      (n : ℤ) * n.gcdA m + (m : ℤ) * n.gcdB m := by
    simpa [hcop.symm.gcd_eq_one] using (Nat.gcd_eq_gcd_ab n m)
  have hbezC : (1 : ℂ) =
      (n : ℂ) * (n.gcdA m : ℂ) + (m : ℂ) * (n.gcdB m : ℂ) := by
    exact_mod_cast hbez
  push_cast
  field_simp [hm0, hn0]
  rw [← hbezC]
  ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma norm_stdAddChar_eq_one
    (N : ℕ) [NeZero N] (h : ZMod N) :
    ‖ZMod.stdAddChar h‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Geometric kernel bound for a nonzero Fourier frequency. This is the
finite-completion denominator estimate used after centering. -/
theorem geometricKernel_norm_le
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) (L : ℕ) :
    ‖∑ j ∈ Finset.range L, (ZMod.stdAddChar h) ^ j‖ ≤
      (N : ℝ) / (2 * zmodFrequencyDistance h) := by
  let z : ℂ := ZMod.stdAddChar h
  let S : ℂ := ∑ j ∈ Finset.range L, z ^ j
  have hz1 : ‖z‖ = 1 := by
    dsimp [z]
    exact norm_stdAddChar_eq_one N h
  have hnum : ‖z ^ L - 1‖ ≤ 2 := by
    calc
      ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hz1]
  have hgeom : S * (z - 1) = z ^ L - 1 := by
    dsimp [S]
    exact geom_sum_mul z L
  have hprod : ‖S‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hnum
  have hchord :
      (4 : ℝ) * zmodFrequencyDistance h / N ≤ ‖z - 1‖ := by
    dsimp [z]
    exact stdAddChar_chord_lower hh
  have hS : 0 ≤ ‖S‖ := norm_nonneg _
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hd : (0 : ℝ) < zmodFrequencyDistance h := by
    exact_mod_cast zmodFrequencyDistance_pos hh
  have haux :
      ‖S‖ * ((4 : ℝ) * zmodFrequencyDistance h / N) ≤ 2 := by
    calc
      ‖S‖ * ((4 : ℝ) * zmodFrequencyDistance h / N) ≤
          ‖S‖ * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_left hchord hS
      _ ≤ 2 := hprod
  apply (le_div_iff₀ (show 0 < (2 : ℝ) * zmodFrequencyDistance h by positivity)).2
  have hscaled := mul_le_mul_of_nonneg_left haux hN.le
  field_simp [hN.ne'] at hscaled
  nlinarith

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma sum_Ico_one_inv_le_harmonic (N : ℕ) :
    (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) ≤ (harmonic N : ℝ) := by
  have hsub : Finset.Ico 1 N ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, hi.2.le⟩
  calc
    (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) ≤
        ∑ i ∈ Finset.Icc 1 N, ((i : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro i hi hin
          positivity
    _ = (harmonic N : ℝ) := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast]

lemma sum_Ico_reflected_inv_eq (N : ℕ) :
    (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹) := by
  apply Finset.sum_bij (fun i hi => N - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    refine ⟨N - j, ?_, ?_⟩
    · simp only [Finset.mem_Ico] at hj ⊢
      omega
    · simp only [Finset.mem_Ico] at hj
      omega
  · intro i hi
    rfl

lemma zmod_finEquiv_val
    {N : ℕ} [NeZero N] (i : Fin N) :
    ((ZMod.finEquiv N) i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

lemma zmod_finEquiv_eq_zero_iff
    {N : ℕ} [NeZero N] (i : Fin N) :
    (ZMod.finEquiv N) i = 0 ↔ i.val = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [zmod_finEquiv_val] using hv
  · intro h
    have hi : i = 0 := by
      apply Fin.ext
      simpa using h
    subst i
    simp

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma fin_sum_inv_val_eq_Ico (N : ℕ) :
    (∑ i : Fin N, if i.val = 0 then (0 : ℝ) else (i.val : ℝ)⁻¹) =
      ∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹ := by
  calc
    (∑ i : Fin N, if i.val = 0 then (0 : ℝ) else (i.val : ℝ)⁻¹) =
        ∑ i ∈ Finset.range N, if i = 0 then (0 : ℝ) else (i : ℝ)⁻¹ := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun i : ℕ => if i = 0 then (0 : ℝ) else (i : ℝ)⁻¹) N)
    _ = ∑ i ∈ (Finset.range N).filter (fun i => i ≠ 0), (i : ℝ)⁻¹ := by
          symm
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h0 : i = 0 <;> simp [h0]
    _ = ∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹ := by
          congr 1
          ext i
          simp
          omega

lemma fin_sum_inv_complement_eq_Ico_reflected (N : ℕ) :
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ) else (((N - i.val : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹) := by
  calc
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ) else (((N - i.val : ℕ) : ℝ)⁻¹)) =
        ∑ i ∈ Finset.range N,
          if i = 0 then (0 : ℝ) else (((N - i : ℕ) : ℝ)⁻¹) := by
            simpa using
              (Fin.sum_univ_eq_sum_range
                (fun i : ℕ =>
                  if i = 0 then (0 : ℝ)
                  else (((N - i : ℕ) : ℝ)⁻¹)) N)
    _ = ∑ i ∈ (Finset.range N).filter (fun i => i ≠ 0),
          (((N - i : ℕ) : ℝ)⁻¹) := by
            symm
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h0 : i = 0 <;> simp [h0]
    _ = ∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹) := by
            congr 1
            ext i
            simp
            omega

/-- Harmonic mass of all nonzero Fourier frequencies, in the symmetric
distance normalization used by the geometric kernel. -/
theorem frequencyReciprocalMass_le_two_harmonic
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then (0 : ℝ)
      else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic N : ℝ) := by
  have hfin :
      (∑ h : ZMod N,
        if h = 0 then (0 : ℝ)
        else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) =
      ∑ i : Fin N,
        if i.val = 0 then (0 : ℝ)
        else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹ := by
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
    intro i
    change
      (if i.val = 0 then (0 : ℝ)
       else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) =
      (if (ZMod.finEquiv N) i = 0 then (0 : ℝ)
       else ((zmodFrequencyDistance ((ZMod.finEquiv N) i) : ℕ) : ℝ)⁻¹)
    by_cases h0 : i.val = 0
    · have hz : (ZMod.finEquiv N) i = 0 :=
        (zmod_finEquiv_eq_zero_iff i).2 h0
      simp [h0, hz]
    · have hz : (ZMod.finEquiv N) i ≠ 0 := by
        intro hz
        exact h0 ((zmod_finEquiv_eq_zero_iff i).1 hz)
      simp [h0, hz, zmodFrequencyDistance, zmod_finEquiv_val]
  rw [hfin]
  have hterm : ∀ i : Fin N,
      (if i.val = 0 then (0 : ℝ)
        else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) ≤
      (if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
      (if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹)) := by
    intro i
    by_cases h0 : i.val = 0
    · simp [h0]
    · simp only [h0, if_false]
      have hiv : 0 < i.val := Nat.pos_of_ne_zero h0
      have hic : 0 < N - i.val := Nat.sub_pos_of_lt i.isLt
      by_cases hle : i.val ≤ N - i.val
      · rw [min_eq_left hle]
        have hnon : 0 ≤ (((N - i.val : ℕ) : ℝ)⁻¹) := by positivity
        linarith
      · have hge : N - i.val ≤ i.val := Nat.le_of_not_ge hle
        rw [min_eq_right hge]
        have hnon : 0 ≤ ((i.val : ℝ)⁻¹) := by positivity
        linarith
  calc
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ)
      else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) ≤
        ∑ i : Fin N,
          ((if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
           (if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹))) := by
            exact Finset.sum_le_sum fun i hi => hterm i
    _ = (∑ i : Fin N, if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
        (∑ i : Fin N,
          if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹) +
        (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) := by
          rw [fin_sum_inv_val_eq_Ico, fin_sum_inv_complement_eq_Ico_reflected]
    _ = 2 * (∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹) := by
          rw [sum_Ico_reflected_inv_eq]
          ring
    _ ≤ 2 * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (sum_Ico_one_inv_le_harmonic N) (by norm_num)

theorem frequencyReciprocalMass_le_log
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then (0 : ℝ)
      else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) ≤
      2 * (1 + Real.log N) := by
  calc
    _ ≤ 2 * (harmonic N : ℝ) :=
      frequencyReciprocalMass_le_two_harmonic N
    _ ≤ 2 * (1 + Real.log N) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def intervalCharacterKernel
    (N : ℕ) [NeZero N] (h x : ZMod N) (L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    ZMod.stdAddChar (h * (x + (j : ZMod N)))

lemma intervalCharacterKernel_eq
    (N : ℕ) [NeZero N] (h x : ZMod N) (L : ℕ) :
    intervalCharacterKernel N h x L =
      ZMod.stdAddChar (h * x) *
        (∑ j ∈ Finset.range L, (ZMod.stdAddChar h) ^ j) := by
  unfold intervalCharacterKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_add, AddChar.map_add_eq_mul]
  congr 1
  have hpow :
      ZMod.stdAddChar (h * (j : ZMod N)) =
        (ZMod.stdAddChar h) ^ j := by
    rw [mul_comm]
    simpa [nsmul_eq_mul] using
      (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := N)) j h)
  exact hpow

theorem intervalCharacterKernel_norm_le
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0)
    (x : ZMod N) (L : ℕ) :
    ‖intervalCharacterKernel N h x L‖ ≤
      (N : ℝ) / (2 * zmodFrequencyDistance h) := by
  rw [intervalCharacterKernel_eq, norm_mul, norm_stdAddChar_eq_one, one_mul]
  exact geometricKernel_norm_le hh L

noncomputable def centeredIntervalSum
    (N : ℕ) [NeZero N] (a x : ZMod N) (L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    centeredReciprocalPhase N a (x + (j : ZMod N))

lemma centeredReciprocalPhase_fourier_inversion
    (N : ℕ) [NeZero N] (a y : ZMod N) :
    centeredReciprocalPhase N a y =
      (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.stdAddChar (h * y) *
            ZMod.dft (centeredReciprocalPhase N a) h := by
  have hInv := congrFun
    (ZMod.dft.symm_apply_apply (centeredReciprocalPhase N a)) y
  rw [ZMod.invDFT_apply] at hInv
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hInv.symm

lemma centeredIntervalSum_fourier
    (N : ℕ) [NeZero N] (a x : ZMod N) (L : ℕ) :
    centeredIntervalSum N a x L =
      (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L := by
  unfold centeredIntervalSum
  calc
    (∑ j ∈ Finset.range L,
      centeredReciprocalPhase N a (x + (j : ZMod N))) =
        ∑ j ∈ Finset.range L,
          ((N : ℂ)⁻¹ *
            ∑ h : ZMod N,
              ZMod.stdAddChar (h * (x + (j : ZMod N))) *
                ZMod.dft (centeredReciprocalPhase N a) h) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [centeredReciprocalPhase_fourier_inversion]
    _ = (N : ℂ)⁻¹ *
        ∑ j ∈ Finset.range L,
          ∑ h : ZMod N,
            ZMod.stdAddChar (h * (x + (j : ZMod N))) *
              ZMod.dft (centeredReciprocalPhase N a) h := by
          rw [Finset.mul_sum]
    _ = (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h hh
          unfold intervalCharacterKernel
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Generic centered finite Fourier completion. The analytic input is only a
uniform bound on nonzero Fourier coefficients. -/
theorem centeredIntervalSum_norm_le_of_dft_bound
    {N : ℕ} [NeZero N] (a x : ZMod N) (L : ℕ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ h : ZMod N, h ≠ 0 →
      ‖ZMod.dft (centeredReciprocalPhase N a) h‖ ≤ B) :
    ‖centeredIntervalSum N a x L‖ ≤
      B * (1 + Real.log N) := by
  have hzero :
      ZMod.dft (centeredReciprocalPhase N a) 0 = 0 := by
    rw [ZMod.dft_apply_zero, sum_centeredReciprocalPhase_eq_zero]
  have hsum :
      ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
        ∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h)) := by
    calc
      ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
        ∑ h : ZMod N,
          ‖ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h)) := by
            apply Finset.sum_le_sum
            intro h hhmem
            by_cases hh : h = 0
            · subst h
              simp [hzero]
            · rw [if_neg hh, norm_mul]
              exact mul_le_mul
                (hB h hh)
                (intervalCharacterKernel_norm_le hh x L)
                (norm_nonneg _)
                hB0
  have hmass :
      (∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h))) ≤
        B * ((N : ℝ) / 2) * (2 * (1 + Real.log N)) := by
    calc
      (∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h))) =
        B * ((N : ℝ) / 2) *
          (∑ h : ZMod N,
            if h = 0 then 0
            else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h hhmem
              by_cases hh : h = 0
              · simp [hh]
              · simp only [hh, ite_false]
                have hd : (0 : ℝ) < zmodFrequencyDistance h := by
                  exact_mod_cast zmodFrequencyDistance_pos hh
                field_simp [hd.ne']
      _ ≤ B * ((N : ℝ) / 2) * (2 * (1 + Real.log N)) := by
            apply mul_le_mul_of_nonneg_left
              (frequencyReciprocalMass_le_log N)
            positivity
  rw [centeredIntervalSum_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ *
        ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
      (N : ℝ)⁻¹ *
        (B * ((N : ℝ) / 2) * (2 * (1 + Real.log N))) := by
          exact mul_le_mul_of_nonneg_left (hsum.trans hmass) (by positivity)
    _ = B * (1 + Real.log N) := by
          have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
          field_simp [hN]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Centered incomplete reciprocal-phase completion on the reduced squarefree
modulus. There is no interval-length restriction. The sole external
mathematical input is PrimeNondegenerateWeil. -/
theorem centeredReducedIntervalSum_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q)) (L : ℕ) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖centeredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x L‖ ≤
      ((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
          Real.sqrt (reducedModulus A q)) *
        (1 + Real.log (reducedModulus A q)) := by
  letI : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  apply centeredIntervalSum_norm_le_of_dft_bound
    (a := (reducedNumerator A q : ZMod (reducedModulus A q)))
    (x := x) (L := L)
  · positivity
  · intro h hh
    rw [dft_centeredReciprocalPhase_nonzero
      (reducedModulus A q)
      (reducedNumerator A q : ZMod (reducedModulus A q)) hh]
    exact kloostermanUnitSum_reduced_le hWeil hq hsq (-h)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def reciprocalNatWeight (Y i : ℕ) : ℂ :=
  ((((Y + i : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)

/-- Discrete partial summation for reciprocal weights. A uniform bound C on
all initial partial sums over a consecutive interval starting at Y>0 gives
an explicit 2C/Y weighted bound. -/
theorem partialSummation_reciprocal_weight_le
    (Y L : ℕ) (hY : 0 < Y) (c : ℕ → ℂ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hprefix : ∀ k ≤ L,
      ‖∑ j ∈ Finset.range k, c j‖ ≤ C) :
    ‖∑ j ∈ Finset.range L,
        c j * reciprocalNatWeight Y j‖ ≤
      2 * C / Y := by
  let r : ℕ → ℝ := fun i => (((Y + i : ℕ) : ℝ)⁻¹)
  let w : ℕ → ℂ := fun i => (r i : ℂ)
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hr_nonneg : ∀ i, 0 ≤ r i := by
    intro i
    dsimp [r]
    positivity
  have hr_mono : ∀ i, r (i + 1) ≤ r i := by
    intro i
    dsimp [r]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by norm_num)
  have hw_norm : ∀ i, ‖w i‖ = r i := by
    intro i
    dsimp [w]
    exact Complex.norm_of_nonneg (hr_nonneg i)
  have hdiff_norm : ∀ i, ‖w (i + 1) - w i‖ = r i - r (i + 1) := by
    intro i
    dsimp [w]
    have hneg :
        ((r (i + 1) : ℂ) - (r i : ℂ)) =
          -((r i - r (i + 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hneg, norm_neg]
    exact Complex.norm_of_nonneg (sub_nonneg.mpr (hr_mono i))
  have hr0 : r 0 = ((Y : ℝ)⁻¹) := by
    dsimp [r]
  have hr_le_r0 : ∀ i, r i ≤ r 0 := by
    intro i
    dsimp [r]
    exact (inv_le_inv₀ (by positivity) hYreal).2 (by norm_num)
  have hparts := Finset.sum_range_by_parts' c w L
  simp only [smul_eq_mul] at hparts
  have hboundary :
      ‖(∑ i ∈ Finset.range L, c i) * w (L - 1)‖ ≤
        C * r 0 := by
    rw [norm_mul, hw_norm]
    exact mul_le_mul
      (hprefix L le_rfl)
      (hr_le_r0 (L - 1))
      (hr_nonneg _)
      hC0
  have htail :
      ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
        C * r 0 := by
    calc
      ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
        ∑ i ∈ Finset.range (L - 1),
          ‖(∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (L - 1),
          C * (r i - r (i + 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul, hdiff_norm]
            apply mul_le_mul_of_nonneg_right
            · apply hprefix (i + 1)
              have hil : i < L - 1 := Finset.mem_range.mp hi
              omega
            · exact sub_nonneg.mpr (hr_mono i)
      _ = C * (r 0 - r (L - 1)) := by
            rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ C * r 0 := by
            have hlast : 0 ≤ r (L - 1) := hr_nonneg _
            nlinarith
  change
    ‖∑ j ∈ Finset.range L, c j * w j‖ ≤ 2 * C / Y
  rw [hparts]
  calc
    ‖(∑ i ∈ Finset.range L, c i) * w (L - 1) -
        ∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
      ‖(∑ i ∈ Finset.range L, c i) * w (L - 1)‖ +
        ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ := norm_sub_le _ _
    _ ≤ C * r 0 + C * r 0 := add_le_add hboundary htail
    _ = 2 * C / Y := by
          rw [hr0]
          field_simp [hYreal.ne']
          ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def weightedCenteredIntervalSum
    (N : ℕ) [NeZero N] (a x : ZMod N) (Y L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    centeredReciprocalPhase N a (x + (j : ZMod N)) *
      reciprocalNatWeight Y j

/-- Partial summation applied to the centered reduced-modulus completion.
The interval length remains unrestricted. -/
theorem weightedCenteredReducedIntervalSum_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q))
    (Y L : ℕ) (hY : 0 < Y) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖weightedCenteredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x Y L‖ ≤
      2 *
        (((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
            Real.sqrt (reducedModulus A q)) *
          (1 + Real.log (reducedModulus A q))) / Y := by
  letI : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  unfold weightedCenteredIntervalSum
  apply partialSummation_reciprocal_weight_le
    (Y := Y) (L := L)
    (c := fun j =>
      centeredReciprocalPhase
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        (x + (j : ZMod (reducedModulus A q))))
    hY
  · positivity
  · intro k hk
    exact centeredReducedIntervalSum_le hWeil hq hsq x k

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma inv_sq_le_inv_sub_inv_succ
    {m : ℕ} (hm : 0 < m) :
    ((m + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤
      (m : ℝ)⁻¹ - ((m + 1 : ℕ) : ℝ)⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmsR : (0 : ℝ) < m + 1 := by positivity
  field_simp [hmR.ne', hmsR.ne']
  norm_num

theorem finite_square_tail_le
    {F M : ℕ} (hF : 0 < F) (hFM : F ≤ M) :
    (∑ f ∈ Finset.Icc (F + 1) M, ((f : ℝ)⁻¹ ^ 2)) ≤
      (F : ℝ)⁻¹ - (M : ℝ)⁻¹ := by
  induction M, hFM using Nat.le_induction with
  | base =>
      simp
  | succ M hFM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      calc
        (∑ f ∈ Finset.Icc (F + 1) M, ((f : ℝ)⁻¹ ^ 2)) +
            (((M + 1 : ℕ) : ℝ)⁻¹ ^ 2) ≤
          ((F : ℝ)⁻¹ - (M : ℝ)⁻¹) +
            (((M + 1 : ℕ) : ℝ)⁻¹ ^ 2) := by
              exact add_le_add ih (le_refl _)
        _ ≤ ((F : ℝ)⁻¹ - (M : ℝ)⁻¹) +
            ((M : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹) := by
              exact add_le_add (le_refl _)
                (inv_sq_le_inv_sub_inv_succ (lt_of_lt_of_le hF hFM))
        _ = (F : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by ring

theorem finite_square_tail_le_inv
    {F M : ℕ} (hF : 0 < F) :
    (∑ f ∈ Finset.Icc (F + 1) M, ((f : ℝ)⁻¹ ^ 2)) ≤
      (F : ℝ)⁻¹ := by
  by_cases hFM : F ≤ M
  · calc
      (∑ f ∈ Finset.Icc (F + 1) M, ((f : ℝ)⁻¹ ^ 2)) ≤
          (F : ℝ)⁻¹ - (M : ℝ)⁻¹ :=
        finite_square_tail_le hF hFM
      _ ≤ (F : ℝ)⁻¹ := by
        have hMnon : 0 ≤ (M : ℝ)⁻¹ := by positivity
        linarith
  · have hempty : Finset.Icc (F + 1) M = ∅ := by
      apply Finset.Icc_eq_empty
      omega
    rw [hempty, Finset.sum_empty]
    positivity

lemma small_f_count_bound
    {F : ℕ} {X : ℝ} (hX : 0 ≤ X) :
    (∑ _f ∈ Finset.Icc 1 F, X) ≤ F * X := by
  simp

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Algebraic balancing lemma for the two finite-f costs.
If s^2 = U/(D*C) and F is chosen within a factor 2 of s, then
F*C/U + 1/(D*F) is at most 3/(D*s). -/
theorem f_split_balance_le
    {U D C s F : ℝ}
    (hU : 0 < U) (hD : 0 < D) (hC : 0 < C) (hs : 0 < s)
    (hsq : s ^ 2 = U / (D * C))
    (hsF : s ≤ F) (hF2 : F ≤ 2 * s) :
    F * C / U + 1 / (D * F) ≤ 3 / (D * s) := by
  have hF : 0 < F := lt_of_lt_of_le hs hsF
  have hden : 0 < D * C := mul_pos hD hC
  have hmul : s ^ 2 * (D * C) = U :=
    (eq_div_iff hden.ne').mp hsq
  have hrel : C / U = 1 / (D * s ^ 2) := by
    field_simp [hU.ne', hD.ne', hC.ne', hs.ne']
    calc
      C * D * s ^ 2 = s ^ 2 * (D * C) := by ring
      _ = U := hmul
  have hsmall : F * C / U ≤ 2 / (D * s) := by
    rw [mul_div_assoc, hrel]
    field_simp [hD.ne', hs.ne']
    nlinarith
  have hlarge : 1 / (D * F) ≤ 1 / (D * s) := by
    exact one_div_le_one_div_of_le (mul_pos hD hs)
      (mul_le_mul_of_nonneg_left hsF hD.le)
  calc
    F * C / U + 1 / (D * F) ≤
        2 / (D * s) + 1 / (D * s) := add_le_add hsmall hlarge
    _ = 3 / (D * s) := by ring

lemma natCeil_within_two_mul
    {s : ℝ} (hs : 1 ≤ s) :
    s ≤ (Nat.ceil s : ℝ) ∧ (Nat.ceil s : ℝ) ≤ 2 * s := by
  constructor
  · exact Nat.le_ceil s
  · have hlt : (Nat.ceil s : ℝ) < s + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one hs)
    linarith

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def invSqrtNat (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

noncomputable def forbiddenSurcharge (R : ℕ) : ℝ :=
  ∏ p ∈ R.primeFactors, (1 + invSqrtNat p)

lemma invSqrtNat_finset_prod (s : Finset ℕ) :
    invSqrtNat (∏ p ∈ s, p) =
      ∏ p ∈ s, invSqrtNat p := by
  unfold invSqrtNat
  rw [Nat.cast_prod, Real.sqrt_prod]
  · simp
  · intro p hp
    positivity

theorem sum_divisors_invSqrt_eq_forbiddenSurcharge
    {R : ℕ} (hR0 : R ≠ 0) (hsq : Squarefree R) :
    (∑ c ∈ R.divisors, invSqrtNat c) = forbiddenSurcharge R := by
  have hfilter :
      R.divisors.filter Squarefree = R.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  calc
    (∑ c ∈ R.divisors, invSqrtNat c) =
        ∑ c ∈ R.divisors.filter Squarefree, invSqrtNat c := by
          rw [hfilter]
    _ = ∑ s ∈ R.primeFactors.powerset,
          invSqrtNat s.val.prod := by
          simpa [Nat.factors_eq, Nat.toFinset_factors] using
            (Nat.sum_divisors_filter_squarefree
              (n := R) hR0 (f := invSqrtNat))
    _ = ∑ s ∈ R.primeFactors.powerset,
          ∏ p ∈ s, invSqrtNat p := by
          apply Finset.sum_congr rfl
          intro s hs
          have hsprod : s.val.prod = ∏ p ∈ s, p := by
            induction s using Finset.induction_on with
            | empty => simp
            | @insert a s ha ih =>
                simp [ha, ih]
          rw [hsprod]
          exact invSqrtNat_finset_prod s
    _ = ∏ p ∈ R.primeFactors, (invSqrtNat p + 1) := by
          symm
          simpa using
            (Finset.prod_add
              (fun p : ℕ => invSqrtNat p)
              (fun _p : ℕ => (1 : ℝ))
              R.primeFactors)
    _ = forbiddenSurcharge R := by
          unfold forbiddenSurcharge
          apply Finset.prod_congr rfl
          intro p hp
          ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_inv_frequencyDistance_le_two_harmonic
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then 0 else ((zmodFrequencyDistance h : ℝ)⁻¹)) ≤
      2 * (harmonic N : ℝ) := by
  have hrewrite :
      (∑ h : ZMod N,
        if h = 0 then 0 else ((zmodFrequencyDistance h : ℝ)⁻¹)) =
      ∑ i : Fin N,
        if i.val = 0 then 0
        else (((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) := by
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv N)
    intro i
    simp [zmod_finEquiv_eq_zero_iff, zmodFrequencyDistance,
      zmod_finEquiv_val]
  rw [hrewrite]
  rw [show (∑ i : Fin N,
      if i.val = 0 then 0
      else (((min i.val (N - i.val) : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.range N,
        if i = 0 then 0
        else (((min i (N - i) : ℕ) : ℝ)⁻¹) by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun i : ℕ =>
                if i = 0 then 0
                else (((min i (N - i) : ℕ) : ℝ)⁻¹)) N)]
  have hpoint :
      ∀ i ∈ Finset.Ico 1 N,
        (((min i (N - i) : ℕ) : ℝ)⁻¹) ≤
          ((i : ℝ)⁻¹) + (((N - i : ℕ) : ℝ)⁻¹) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hi0 : 0 < i := by omega
    have hNi : 0 < N - i := Nat.sub_pos_of_lt hi.2
    by_cases hle : i ≤ N - i
    · rw [min_eq_left hle]
      have hnon : 0 ≤ (((N - i : ℕ) : ℝ)⁻¹) := by positivity
      linarith
    · have hge : N - i ≤ i := Nat.le_of_not_ge hle
      rw [min_eq_right hge]
      have hnon : 0 ≤ ((i : ℝ)⁻¹) := by positivity
      linarith
  have hsum :
      (∑ i ∈ Finset.Ico 1 N,
        (((min i (N - i) : ℕ) : ℝ)⁻¹)) ≤
      (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) +
        (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpoint
  have hzero :
      (∑ i ∈ Finset.range N,
        if i = 0 then 0 else
          (((min i (N - i) : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N,
        (((min i (N - i) : ℕ) : ℝ)⁻¹) := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.insert_Ico_add_one_left_eq_Ico (NeZero.pos N)]
    change
      (∑ i ∈ insert 0 (Finset.Ico 1 N),
        if i = 0 then 0 else (((min i (N - i) : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N,
        (((min i (N - i) : ℕ) : ℝ)⁻¹)
    have h0not : 0 ∉ Finset.Ico 1 N := by simp
    rw [Finset.sum_insert h0not]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp [Nat.ne_of_gt hi.1]
  rw [hzero]
  calc
    (∑ i ∈ Finset.Ico 1 N,
      (((min i (N - i) : ℕ) : ℝ)⁻¹)) ≤
        (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) +
          (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) := hsum
    _ = 2 * (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) := by
          rw [sum_Ico_reflected_inv_eq]
          ring
    _ ≤ 2 * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (sum_Ico_one_inv_le_harmonic N) (by norm_num)

theorem sum_inv_frequencyDistance_le_two_one_add_log
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then 0 else ((zmodFrequencyDistance h : ℝ)⁻¹)) ≤
      2 * (1 + Real.log N) := by
  calc
    _ ≤ 2 * (harmonic N : ℝ) :=
      sum_inv_frequencyDistance_le_two_harmonic N
    _ ≤ 2 * (1 + Real.log N) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Source-faithful fixed-(d,c) balance socket. If the small-f and large-f
pieces are bounded by the two costs appearing in the companion argument,
then a balanced cutoff gives the expected square-root channel cost. -/
theorem fixedChannel_estimate_of_split_balance
    {G U D C s F small large : ℝ}
    (hG : 0 ≤ G)
    (hU : 0 < U) (hD : 0 < D) (hC : 0 < C) (hs : 0 < s)
    (hsq : s ^ 2 = U / (D * C))
    (hsF : s ≤ F) (hF2 : F ≤ 2 * s)
    (hsmall : small ≤ G * (F * C / U))
    (hlarge : large ≤ G * (1 / (D * F))) :
    small + large ≤ 3 * G / (D * s) := by
  have hbal := f_split_balance_le hU hD hC hs hsq hsF hF2
  calc
    small + large ≤
        G * (F * C / U) + G * (1 / (D * F)) :=
      add_le_add hsmall hlarge
    _ = G * (F * C / U + 1 / (D * F)) := by ring
    _ ≤ G * (3 / (D * s)) :=
      mul_le_mul_of_nonneg_left hbal hG
    _ = 3 * G / (D * s) := by ring

/-- Algebraic identification of the balanced denominator with the square-root
channel scale from the companion proof. -/
theorem fixedChannel_balanced_scale_eq
    {U D C s : ℝ}
    (hU : 0 < U) (hD : 0 < D) (hC : 0 < C) (hs : 0 < s)
    (hsq : s ^ 2 = U / (D * C)) :
    1 / (D * s) = Real.sqrt (C / (U * D)) := by
  have hleft : 0 < D * s := mul_pos hD hs
  have hratio : 0 < C / (U * D) := by positivity
  have hsqrt : 0 < Real.sqrt (C / (U * D)) := Real.sqrt_pos.2 hratio
  have hsquare :
      (1 / (D * s)) ^ 2 = C / (U * D) := by
    have hden : 0 < D * C := mul_pos hD hC
    have hmul : s ^ 2 * (D * C) = U :=
      (eq_div_iff hden.ne').mp hsq
    field_simp [hD.ne', hs.ne', hU.ne', hC.ne']
    nlinarith
  apply (sq_eq_sq₀ (by positivity) hsqrt.le).mp
  rw [hsquare, Real.sq_sqrt hratio.le]

theorem fixedChannel_estimate_sqrt
    {G U D C s F small large : ℝ}
    (hG : 0 ≤ G)
    (hU : 0 < U) (hD : 0 < D) (hC : 0 < C) (hs : 0 < s)
    (hsq : s ^ 2 = U / (D * C))
    (hsF : s ≤ F) (hF2 : F ≤ 2 * s)
    (hsmall : small ≤ G * (F * C / U))
    (hlarge : large ≤ G * (1 / (D * F))) :
    small + large ≤ 3 * G * Real.sqrt (C / (U * D)) := by
  calc
    small + large ≤ 3 * G / (D * s) :=
      fixedChannel_estimate_of_split_balance
        hG hU hD hC hs hsq hsF hF2 hsmall hlarge
    _ = 3 * G * (1 / (D * s)) := by ring
    _ = 3 * G * Real.sqrt (C / (U * D)) := by
      rw [fixedChannel_balanced_scale_eq hU hD hC hs hsq]

/-- Generic d,c summation court. The arithmetic d-sum remains an explicit
input; the c-sum is discharged exactly by the squarefree surcharge E(R). -/
theorem sum_fixedChannels_le_forbiddenSurcharge
    {R : ℕ} (hR0 : R ≠ 0) (hRsq : Squarefree R)
    (Dset : Finset ℕ) (gamma channel : ℕ → ℕ → ℝ)
    {K Gsum : ℝ} (hK : 0 ≤ K)
    (hgamma : ∀ d ∈ Dset, 0 ≤ gamma d 1)
    (hchan : ∀ d ∈ Dset, ∀ c ∈ R.divisors,
      channel d c ≤
        K * (gamma d 1 * invSqrtNat d) * invSqrtNat c)
    (hdSum :
      (∑ d ∈ Dset, gamma d 1 * invSqrtNat d) ≤ Gsum) :
    (∑ d ∈ Dset, ∑ c ∈ R.divisors, channel d c) ≤
      K * Gsum * forbiddenSurcharge R := by
  have hcinv : ∀ c ∈ R.divisors, 0 ≤ invSqrtNat c := by
    intro c hc
    unfold invSqrtNat
    positivity
  calc
    (∑ d ∈ Dset, ∑ c ∈ R.divisors, channel d c) ≤
        ∑ d ∈ Dset, ∑ c ∈ R.divisors,
          K * (gamma d 1 * invSqrtNat d) * invSqrtNat c := by
            apply Finset.sum_le_sum
            intro d hd
            apply Finset.sum_le_sum
            intro c hc
            exact hchan d hd c hc
    _ = K *
        (∑ d ∈ Dset, gamma d 1 * invSqrtNat d) *
        (∑ c ∈ R.divisors, invSqrtNat c) := by
          calc
            (∑ d ∈ Dset, ∑ c ∈ R.divisors,
              K * (gamma d 1 * invSqrtNat d) * invSqrtNat c) =
                ∑ d ∈ Dset,
                  (K * (gamma d 1 * invSqrtNat d)) *
                    (∑ c ∈ R.divisors, invSqrtNat c) := by
                      apply Finset.sum_congr rfl
                      intro d hd
                      rw [Finset.mul_sum]
            _ = (∑ d ∈ Dset,
                  K * (gamma d 1 * invSqrtNat d)) *
                    (∑ c ∈ R.divisors, invSqrtNat c) := by
                      rw [Finset.sum_mul]
            _ = K *
                (∑ d ∈ Dset, gamma d 1 * invSqrtNat d) *
                  (∑ c ∈ R.divisors, invSqrtNat c) := by
                    rw [← Finset.mul_sum]
    _ ≤ K * Gsum * (∑ c ∈ R.divisors, invSqrtNat c) := by
          have hcSum : 0 ≤ ∑ c ∈ R.divisors, invSqrtNat c :=
            Finset.sum_nonneg hcinv
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdSum hK) hcSum
    _ = K * Gsum * forbiddenSurcharge R := by
          rw [sum_divisors_invSqrt_eq_forbiddenSurcharge hR0 hRsq]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def quarterRootNat (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (n : ℝ))

lemma balancedScale_factor
    {C U D : ℝ} (hC : 0 ≤ C) (hU : 0 < U) (hD : 0 < D) :
    Real.sqrt (C / (U * D)) =
      Real.sqrt C * (Real.sqrt U)⁻¹ * (Real.sqrt D)⁻¹ := by
  rw [Real.sqrt_div hC]
  rw [Real.sqrt_mul hU.le]
  have hsu : Real.sqrt U ≠ 0 := (Real.sqrt_pos.2 hU).ne'
  have hsd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  field_simp [hsu, hsd]

lemma sqrt_sqrt_nat_eq_quarterRootNat (n : ℕ) :
    Real.sqrt (Real.sqrt (n : ℝ)) = quarterRootNat n := rfl

/-- Exact algebraic origin of the reduced-modulus quarter power and the
U^{-1/2}, D^{-1/2} factors after balancing. -/
theorem balancedScale_quarterRoot
    {T L U D : ℝ} {rho : ℕ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hU : 0 < U) (hD : 0 < D) :
    Real.sqrt ((T * Real.sqrt (rho : ℝ) * L) / (U * D)) =
      Real.sqrt T * quarterRootNat rho * Real.sqrt L *
        (Real.sqrt U)⁻¹ * (Real.sqrt D)⁻¹ := by
  rw [balancedScale_factor (mul_nonneg (mul_nonneg hT (Real.sqrt_nonneg _)) hL) hU hD]
  rw [show T * Real.sqrt (rho : ℝ) * L =
      T * (Real.sqrt (rho : ℝ) * L) by ring]
  rw [Real.sqrt_mul hT]
  rw [Real.sqrt_mul (Real.sqrt_nonneg _)]
  unfold quarterRootNat
  ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def gammaPrimeTerm (n : ℕ) : ℝ :=
  if 5 ≤ n then
    3 / (((n : ℝ) - 3) * Real.sqrt (n : ℝ))
  else 0

lemma gammaPrimeTerm_nonneg (n : ℕ) :
    0 ≤ gammaPrimeTerm n := by
  unfold gammaPrimeTerm
  by_cases hn : 5 ≤ n
  · rw [if_pos hn]
    have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hsub : (0 : ℝ) < (n : ℝ) - 3 := by linarith
    have hsqrt : 0 < Real.sqrt (n : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast (show 0 < n by omega)
    exact div_nonneg (by norm_num) (mul_nonneg hsub.le hsqrt.le)
  · rw [if_neg hn]

lemma gammaPrimeTerm_le_pseries (n : ℕ) :
    gammaPrimeTerm n ≤
      9 * (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
  unfold gammaPrimeTerm
  by_cases hn : 5 ≤ n
  · rw [if_pos hn]
    have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hsub : (0 : ℝ) < (n : ℝ) - 3 := by linarith
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hpow :
        (n : ℝ) ^ ((3 : ℝ) / 2) =
          (n : ℝ) * Real.sqrt (n : ℝ) := by
      calc
        (n : ℝ) ^ ((3 : ℝ) / 2) =
            (n : ℝ) ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by norm_num
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_add hnpos _ _
        _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
          rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hpowpos : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hnpos _
    calc
      3 / (((n : ℝ) - 3) * Real.sqrt (n : ℝ)) ≤
          9 / ((n : ℝ) ^ ((3 : ℝ) / 2)) := by
            apply (div_le_div_iff₀ (mul_pos hsub hsqrt) hpowpos).2
            rw [hpow]
            nlinarith
      _ = 9 * (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
            rw [inv_eq_one_div]
            ring
  · rw [if_neg hn]
    positivity

theorem summable_gammaPrimeTerm :
    Summable gammaPrimeTerm := by
  have hp :
      Summable (fun n : ℕ =>
        9 * (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) := by
    exact Summable.mul_left 9
      ((Real.summable_nat_rpow_inv).2 (by norm_num))
  exact Summable.of_nonneg_of_le
    gammaPrimeTerm_nonneg gammaPrimeTerm_le_pseries hp

theorem gammaPowerset_sum_eq_eulerProduct (S : Finset ℕ) :
    (∑ s ∈ S.powerset, ∏ p ∈ s, gammaPrimeTerm p) =
      ∏ p ∈ S, (1 + gammaPrimeTerm p) := by
  symm
  simpa [add_comm] using
    (Finset.prod_add
      (fun p : ℕ => gammaPrimeTerm p)
      (fun _p : ℕ => (1 : ℝ))
      S)

theorem gammaEulerProduct_uniform_bound (S : Finset ℕ) :
    (∏ p ∈ S, (1 + gammaPrimeTerm p)) ≤
      Real.exp (∑' n : ℕ, gammaPrimeTerm n) := by
  have hprod :
      (∏ p ∈ S, (1 + gammaPrimeTerm p)) ≤
        ∏ p ∈ S, Real.exp (gammaPrimeTerm p) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        have hlocal :
            1 + gammaPrimeTerm a ≤ Real.exp (gammaPrimeTerm a) := by
          simpa [add_comm] using Real.add_one_le_exp (gammaPrimeTerm a)
        have hleftProd :
            0 ≤ ∏ p ∈ S, (1 + gammaPrimeTerm p) := by
          apply Finset.prod_nonneg
          intro p hp
          linarith [gammaPrimeTerm_nonneg p]
        have hExp : 0 ≤ Real.exp (gammaPrimeTerm a) :=
          (Real.exp_pos _).le
        exact mul_le_mul hlocal ih hleftProd hExp
  calc
    (∏ p ∈ S, (1 + gammaPrimeTerm p)) ≤
        ∏ p ∈ S, Real.exp (gammaPrimeTerm p) := hprod
    _ = Real.exp (∑ p ∈ S, gammaPrimeTerm p) := by
          rw [Real.exp_sum]
    _ ≤ Real.exp (∑' n : ℕ, gammaPrimeTerm n) := by
          apply Real.exp_monotone
          exact summable_gammaPrimeTerm.sum_le_tsum S
            (fun n hn => gammaPrimeTerm_nonneg n)

theorem gammaDSum_uniform_bound (S : Finset ℕ) :
    (∑ s ∈ S.powerset, ∏ p ∈ s, gammaPrimeTerm p) ≤
      Real.exp (∑' n : ℕ, gammaPrimeTerm n) := by
  rw [gammaPowerset_sum_eq_eulerProduct]
  exact gammaEulerProduct_uniform_bound S

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Fully source-shaped finite d,c summation. The d-index is represented by
subsets of a finite active prime set, exactly as in the Euler-product
expansion of |gamma(d)| / sqrt(d). -/
theorem sum_gammaChannels_le_euler_forbidden
    {R : ℕ} (hR0 : R ≠ 0) (hRsq : Squarefree R)
    (S : Finset ℕ)
    (channel : Finset ℕ → ℕ → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hchan : ∀ s ∈ S.powerset, ∀ c ∈ R.divisors,
      channel s c ≤
        K * (∏ p ∈ s, gammaPrimeTerm p) * invSqrtNat c) :
    (∑ s ∈ S.powerset, ∑ c ∈ R.divisors, channel s c) ≤
      K * Real.exp (∑' n : ℕ, gammaPrimeTerm n) *
        forbiddenSurcharge R := by
  have hcNon : 0 ≤ ∑ c ∈ R.divisors, invSqrtNat c := by
    apply Finset.sum_nonneg
    intro c hc
    unfold invSqrtNat
    positivity
  calc
    (∑ s ∈ S.powerset, ∑ c ∈ R.divisors, channel s c) ≤
        ∑ s ∈ S.powerset, ∑ c ∈ R.divisors,
          K * (∏ p ∈ s, gammaPrimeTerm p) * invSqrtNat c := by
            apply Finset.sum_le_sum
            intro s hs
            apply Finset.sum_le_sum
            intro c hc
            exact hchan s hs c hc
    _ = K *
        (∑ s ∈ S.powerset, ∏ p ∈ s, gammaPrimeTerm p) *
        (∑ c ∈ R.divisors, invSqrtNat c) := by
          calc
            (∑ s ∈ S.powerset, ∑ c ∈ R.divisors,
              K * (∏ p ∈ s, gammaPrimeTerm p) * invSqrtNat c) =
                ∑ s ∈ S.powerset,
                  (K * (∏ p ∈ s, gammaPrimeTerm p)) *
                    (∑ c ∈ R.divisors, invSqrtNat c) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      rw [Finset.mul_sum]
            _ = (∑ s ∈ S.powerset,
                  K * (∏ p ∈ s, gammaPrimeTerm p)) *
                    (∑ c ∈ R.divisors, invSqrtNat c) := by
                      rw [Finset.sum_mul]
            _ = K *
                (∑ s ∈ S.powerset, ∏ p ∈ s, gammaPrimeTerm p) *
                  (∑ c ∈ R.divisors, invSqrtNat c) := by
                    rw [← Finset.mul_sum]
    _ ≤ K * Real.exp (∑' n : ℕ, gammaPrimeTerm n) *
        (∑ c ∈ R.divisors, invSqrtNat c) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (gammaDSum_uniform_bound S) hK)
            hcNon
    _ = K * Real.exp (∑' n : ℕ, gammaPrimeTerm n) *
        forbiddenSurcharge R := by
          rw [sum_divisors_invSqrt_eq_forbiddenSurcharge hR0 hRsq]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Finite-f composition court from the companion proof. A uniform small-f
term bound and the f^{-2} large-f tail feed directly into the balanced
fixed-channel square-root estimate. -/
theorem fixedChannel_estimate_from_f_split
    {G U D C s : ℝ} {F M : ℕ}
    (hG : 0 ≤ G)
    (hU : 0 < U) (hD : 0 < D) (hC : 0 < C) (hs : 0 < s)
    (hsq : s ^ 2 = U / (D * C))
    (hsF : s ≤ (F : ℝ)) (hF2 : (F : ℝ) ≤ 2 * s)
    (smallTerm largeTerm : ℕ → ℝ)
    (hsmallTerm : ∀ f ∈ Finset.Icc 1 F,
      smallTerm f ≤ G * C / U)
    (hlargeTerm : ∀ f ∈ Finset.Icc (F + 1) M,
      largeTerm f ≤ (G / D) * ((f : ℝ)⁻¹ ^ 2)) :
    (∑ f ∈ Finset.Icc 1 F, smallTerm f) +
      (∑ f ∈ Finset.Icc (F + 1) M, largeTerm f) ≤
        3 * G * Real.sqrt (C / (U * D)) := by
  have hFpos : 0 < F := by
    have : (0 : ℝ) < F := lt_of_lt_of_le hs hsF
    exact_mod_cast this
  have hsmall :
      (∑ f ∈ Finset.Icc 1 F, smallTerm f) ≤
        G * ((F : ℝ) * C / U) := by
    calc
      (∑ f ∈ Finset.Icc 1 F, smallTerm f) ≤
          ∑ _f ∈ Finset.Icc 1 F, (G * C / U) := by
            apply Finset.sum_le_sum
            intro f hf
            exact hsmallTerm f hf
      _ = (F : ℝ) * (G * C / U) := by simp
      _ = G * ((F : ℝ) * C / U) := by ring
  have hlarge :
      (∑ f ∈ Finset.Icc (F + 1) M, largeTerm f) ≤
        G * (1 / (D * (F : ℝ))) := by
    have hGD : 0 ≤ G / D := div_nonneg hG hD.le
    calc
      (∑ f ∈ Finset.Icc (F + 1) M, largeTerm f) ≤
          ∑ f ∈ Finset.Icc (F + 1) M,
            (G / D) * ((f : ℝ)⁻¹ ^ 2) := by
              apply Finset.sum_le_sum
              intro f hf
              exact hlargeTerm f hf
      _ = (G / D) *
          (∑ f ∈ Finset.Icc (F + 1) M, ((f : ℝ)⁻¹ ^ 2)) := by
            rw [Finset.mul_sum]
      _ ≤ (G / D) * (F : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_left
              (finite_square_tail_le_inv hFpos) hGD
      _ = G * (1 / (D * (F : ℝ))) := by
            field_simp [hD.ne', (show (F : ℝ) ≠ 0 by exact_mod_cast hFpos.ne')]
  exact fixedChannel_estimate_sqrt
    hG hU hD hC hs hsq hsF hF2 hsmall hlarge

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Source-normalized classical prime Kloosterman sum:
    S(m,n;p) = ∑_{x mod p, x ≠ 0} e_p(m x + n x⁻¹).
This matches Weil (1948), up to the standard additive-character notation. -/
noncomputable def weilKloostermanPrime
    (p : ℕ) [Fact p.Prime] (m n : ZMod p) : ℂ :=
  ∑ x : ZMod p,
    if x = 0 then 0 else ZMod.stdAddChar (m * x + n * x⁻¹)

/-- Exact normalization bridge: the Paper B local sum uses the same classical
Kloosterman sum with the two coefficients named in the opposite order. -/
theorem kloostermanSumPrime_eq_weilKloostermanPrime
    (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    kloostermanSumPrime p a b = weilKloostermanPrime p b a := by
  rfl

/-- Exact source-shaped statement of the prime Kloosterman Weil bound used by
Paper B. This proposition is not proved locally; it is the sole remaining
external mathematical obligation.

Source: André Weil, "On Some Exponential Sums",
Proc. Natl. Acad. Sci. U.S.A. 34 (1948), 204-207,
DOI 10.1073/pnas.34.5.204. -/
def Weil1948PrimeKloostermanBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ZMod p),
    m ≠ 0 → n ≠ 0 →
      ‖weilKloostermanPrime p m n‖ ≤ 2 * Real.sqrt p

/-- The manuscript socket and the source-shaped Weil statement are exactly
equivalent; there is no remaining normalization or convention gap. -/
theorem primeNondegenerateWeil_iff_weil1948 :
    PrimeNondegenerateWeil ↔ Weil1948PrimeKloostermanBound := by
  constructor
  · intro h p _ m n hm hn
    rw [← kloostermanSumPrime_eq_weilKloostermanPrime p n m]
    exact h p n m hn hm
  · intro h p _ a b ha hb
    rw [kloostermanSumPrime_eq_weilKloostermanPrime]
    exact h p b a hb ha

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- Elementary nonzero scaling reduction:
for nonzero m,n mod p, K_p(n,m) = K_p(m*n,1), equivalently in the
source-normalized order S(m,n;p) = S(1,m*n;p). -/
theorem weilKloostermanPrime_scaling
    (p : ℕ) [Fact p.Prime] (m n : ZMod p)
    (hm : m ≠ 0) :
    weilKloostermanPrime p m n =
      weilKloostermanPrime p 1 (m * n) := by
  unfold weilKloostermanPrime
  let e : ZMod p ≃ ZMod p :=
    Equiv.mulLeft₀ m hm
  apply Fintype.sum_equiv e
  intro x
  by_cases hx : x = 0
  · subst x
    simp [e, Equiv.mulLeft₀]
  · have hmx : m * x ≠ 0 := mul_ne_zero hm hx
    have hminv : m * m⁻¹ = (1 : ZMod p) := mul_inv_cancel₀ hm
    change
      (if x = 0 then 0 else ZMod.stdAddChar (m * x + n * x⁻¹)) =
      (if m * x = 0 then 0
       else ZMod.stdAddChar (1 * (m * x) + (m * n) * (m * x)⁻¹))
    rw [if_neg hx, if_neg hmx, one_mul, mul_inv_rev]
    congr 2
    calc
      n * x⁻¹ = (n * x⁻¹) * 1 := by rw [mul_one]
      _ = (n * x⁻¹) * (m * m⁻¹) := by rw [hminv]
      _ = m * n * (x⁻¹ * m⁻¹) := by ac_rfl

theorem kloostermanSumPrime_scaling
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hb : b ≠ 0) :
    kloostermanSumPrime p a b =
      kloostermanSumPrime p (b * a) 1 := by
  rw [kloostermanSumPrime_eq_weilKloostermanPrime]
  rw [weilKloostermanPrime_scaling p b a hb]
  rfl

def OneParameterPrimeWeil : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p),
    a ≠ 0 →
      ‖kloostermanSumPrime p a 1‖ ≤ 2 * Real.sqrt p

theorem primeNondegenerateWeil_iff_oneParameter :
    PrimeNondegenerateWeil ↔ OneParameterPrimeWeil := by
  constructor
  · intro h p _ a ha
    exact h p a 1 ha one_ne_zero
  · intro h p _ a b ha hb
    rw [kloostermanSumPrime_scaling p a b hb]
    exact h p (b * a) (mul_ne_zero hb ha)

end RML.Fourier.Vaaler.Internal
