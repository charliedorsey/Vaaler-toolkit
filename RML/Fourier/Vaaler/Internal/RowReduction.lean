module

public import RML.Fourier.Vaaler.Internal.DivisorExpansion
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Paper B fixed-q exact row reduction

Frozen Paper B source:
* `paper_b_frozen.tex`
* SHA-256: `9004c20d63218b529ea392d13914c17a347c485fd43814eb88bf8612a8512070`
* label: `lem:fixed-q-row-reduction`
* equations: `eq:Nlambda`, `eq:Dlambda`,
  `eq:fixed-q-row-reduction`, `eq:periodic-density-delta-q`

This module follows the manuscript's order: exact finite row algebra first,
then the source-specific change of variables and periodic-density bounds.
-/

open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal

noncomputable def rowWeightMass
    (lambda : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ y ∈ Finset.Ioo 0 H, lambda y

noncomputable def rowConstrainedMass
    (lambda : ℕ → ℝ) (H e1 e2 : ℕ) : ℝ :=
  ∑ y ∈ Finset.Ioo 0 H,
    if e1 ∣ y ∧ e2 ∣ H - y then lambda y else 0

noncomputable def rowDiscrepancy
    (lambda : ℕ → ℝ) (H e1 e2 : ℕ) : ℝ :=
  rowConstrainedMass lambda H e1 e2 -
    rowWeightMass lambda H / ((e1 : ℝ) * (e2 : ℝ))

noncomputable def rowPeriodicDensityDelta
    (lambda : ℕ → ℝ) (H : ℕ) (N : ℝ) (d : ℕ) : ℝ :=
  rowWeightMass lambda H - N / (d : ℝ)

/-- Exact algebraic core of frozen-paper `lem:fixed-q-row-reduction`.

Once the manuscript's literal change of variables identifies the constrained
row count before and after reduction, the centered discrepancy identity is
pure field algebra.  No density approximation enters this theorem.
-/
theorem exactRowReduction_of_constrainedMass_eq
    (lambda lambdaReduced : ℕ → ℝ)
    (h H d r e2 : ℕ) (N : ℝ)
    (hd : d ≠ 0) (hr : r ≠ 0) (he2 : e2 ≠ 0)
    (hMass :
      rowConstrainedMass lambda h (d * r) e2 =
        rowConstrainedMass lambdaReduced H r e2) :
    rowConstrainedMass lambda h (d * r) e2 -
        N / (((d : ℝ) * (r : ℝ)) * (e2 : ℝ)) =
      rowDiscrepancy lambdaReduced H r e2 +
        rowPeriodicDensityDelta lambdaReduced H N d /
          ((r : ℝ) * (e2 : ℝ)) := by
  rw [hMass]
  unfold rowDiscrepancy rowPeriodicDensityDelta
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have he2R : (e2 : ℝ) ≠ 0 := by exact_mod_cast he2
  field_simp [hdR, hrR, he2R]
  ring


def rowConstrainedSet (H e1 e2 : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 H).filter fun y => e1 ∣ y ∧ e2 ∣ H - y

theorem rowConstrainedMass_eq_sum_set
    (lambda : ℕ → ℝ) (H e1 e2 : ℕ) :
    rowConstrainedMass lambda H e1 e2 =
      ∑ y ∈ rowConstrainedSet H e1 e2, lambda y := by
  unfold rowConstrainedMass rowConstrainedSet
  exact (Finset.sum_filter
    (s := Finset.Ioo 0 H)
    (fun y => e1 ∣ y ∧ e2 ∣ H - y)
    lambda).symm


/-- Exact dilation of a constrained row by a positive factor d.

This is the first change of variables in the manuscript proof: y = d z.
The right congruence survives after division because d is coprime to e2.
-/
theorem rowConstrainedMass_dilate
    (lambda lambdaReduced : ℕ → ℝ)
    (d H r e2 : ℕ)
    (hd : 0 < d) (hcop : d.Coprime e2)
    (hscale :
      ∀ z ∈ rowConstrainedSet H r e2,
        lambda (d * z) = lambdaReduced z) :
    rowConstrainedMass lambda (d * H) (d * r) e2 =
      rowConstrainedMass lambdaReduced H r e2 := by
  rw [rowConstrainedMass_eq_sum_set, rowConstrainedMass_eq_sum_set]
  apply Finset.sum_bij (fun y _ => y / d)
  · intro y hy
    simp only [rowConstrainedSet, Finset.mem_filter,
      Finset.mem_Ioo] at hy ⊢
    rcases hy with ⟨⟨hy0, hylt⟩, ⟨hdry, he2y⟩⟩
    have hdy : d ∣ y := (dvd_mul_right d r).trans hdry
    have hdyLe : d ≤ y := Nat.le_of_dvd hy0 hdy
    have hz0 : 0 < y / d := Nat.div_pos hdyLe hd
    have hmuldiv : d * (y / d) = y := Nat.mul_div_cancel' hdy
    have hzlt : y / d < H := by
      apply (Nat.mul_lt_mul_left hd).mp
      rw [hmuldiv]
      exact hylt
    have hrdvd : r ∣ y / d :=
      (Nat.dvd_div_iff_mul_dvd hdy).2 hdry
    have he2scaled : e2 ∣ d * (H - y / d) := by
      rw [Nat.mul_sub_left_distrib, hmuldiv]
      exact he2y
    have he2dvd : e2 ∣ H - y / d :=
      (hcop.symm.dvd_mul_left).1 he2scaled
    exact ⟨⟨hz0, hzlt⟩, ⟨hrdvd, he2dvd⟩⟩
  · intro y1 hy1 y2 hy2 heq
    simp only [rowConstrainedSet, Finset.mem_filter,
      Finset.mem_Ioo] at hy1 hy2
    have hdy1 : d ∣ y1 :=
      (dvd_mul_right d r).trans hy1.2.1
    have hdy2 : d ∣ y2 :=
      (dvd_mul_right d r).trans hy2.2.1
    calc
      y1 = d * (y1 / d) := (Nat.mul_div_cancel' hdy1).symm
      _ = d * (y2 / d) := by rw [heq]
      _ = y2 := Nat.mul_div_cancel' hdy2
  · intro z hz
    simp only [rowConstrainedSet, Finset.mem_filter,
      Finset.mem_Ioo] at hz
    rcases hz with ⟨⟨hz0, hzlt⟩, ⟨hrz, he2z⟩⟩
    refine ⟨d * z, ?_, ?_⟩
    · simp only [rowConstrainedSet, Finset.mem_filter,
        Finset.mem_Ioo]
      have hy0 : 0 < d * z := Nat.mul_pos hd hz0
      have hylt : d * z < d * H :=
        (Nat.mul_lt_mul_left hd).2 hzlt
      have hdry : d * r ∣ d * z :=
        Nat.mul_dvd_mul_left d hrz
      have he2y : e2 ∣ d * H - d * z := by
        rw [← Nat.mul_sub_left_distrib]
        exact dvd_mul_of_dvd_right he2z d
      exact ⟨⟨hy0, hylt⟩, ⟨hdry, he2y⟩⟩
    · exact Nat.mul_div_cancel_left z hd
  · intro y hy
    have hyTarget :
        y / d ∈ rowConstrainedSet H r e2 := by
      simp only [rowConstrainedSet, Finset.mem_filter,
        Finset.mem_Ioo] at hy ⊢
      rcases hy with ⟨⟨hy0, hylt⟩, ⟨hdry, he2y⟩⟩
      have hdy : d ∣ y := (dvd_mul_right d r).trans hdry
      have hdyLe : d ≤ y := Nat.le_of_dvd hy0 hdy
      have hz0 : 0 < y / d := Nat.div_pos hdyLe hd
      have hmuldiv : d * (y / d) = y := Nat.mul_div_cancel' hdy
      have hzlt : y / d < H := by
        apply (Nat.mul_lt_mul_left hd).mp
        rw [hmuldiv]
        exact hylt
      have hrdvd : r ∣ y / d :=
        (Nat.dvd_div_iff_mul_dvd hdy).2 hdry
      have he2scaled : e2 ∣ d * (H - y / d) := by
        rw [Nat.mul_sub_left_distrib, hmuldiv]
        exact he2y
      have he2dvd : e2 ∣ H - y / d :=
        (hcop.symm.dvd_mul_left).1 he2scaled
      exact ⟨⟨hz0, hzlt⟩, ⟨hrdvd, he2dvd⟩⟩
    have hdy : d ∣ y := by
      simp only [rowConstrainedSet, Finset.mem_filter,
        Finset.mem_Ioo] at hy
      exact (dvd_mul_right d r).trans hy.2.1
    have hmuldiv : d * (y / d) = y := Nat.mul_div_cancel' hdy
    calc
      lambda y = lambda (d * (y / d)) := by rw [hmuldiv]
      _ = lambdaReduced (y / d) := hscale (y / d) hyTarget


def rowEvenConstrainedSet (H e1 e2 : ℕ) : Finset ℕ :=
  (rowConstrainedSet H e1 e2).filter fun z => 2 ∣ z

theorem rowConstrainedMass_eq_even_sum
    (lambda : ℕ → ℝ) (H e1 e2 : ℕ)
    (hOddZero :
      ∀ z ∈ rowConstrainedSet H e1 e2,
        ¬ 2 ∣ z → lambda z = 0) :
    rowConstrainedMass lambda H e1 e2 =
      ∑ z ∈ rowEvenConstrainedSet H e1 e2, lambda z := by
  rw [rowConstrainedMass_eq_sum_set]
  unfold rowEvenConstrainedSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h2z : 2 ∣ z
  · simp [h2z]
  · simp [h2z, hOddZero z hz h2z]

/-- Exact parity compression z = 2 x used in the frozen row reduction.

The row moduli r and e2 are odd, expressed as coprimality with 2.  Odd z
carry zero weight, so the constrained row may be restricted to even z and
then divided by 2 bijectively.
-/
theorem rowConstrainedMass_compress_even
    (lambda lambdaEven : ℕ → ℝ)
    (H r e2 : ℕ)
    (hr2 : r.Coprime 2) (he22 : e2.Coprime 2)
    (hOddZero :
      ∀ z ∈ rowConstrainedSet (2 * H) r e2,
        ¬ 2 ∣ z → lambda z = 0)
    (hscale :
      ∀ x ∈ rowConstrainedSet H r e2,
        lambda (2 * x) = lambdaEven x) :
    rowConstrainedMass lambda (2 * H) r e2 =
      rowConstrainedMass lambdaEven H r e2 := by
  rw [rowConstrainedMass_eq_even_sum lambda (2 * H) r e2 hOddZero]
  rw [rowConstrainedMass_eq_sum_set]
  apply Finset.sum_bij (fun z _ => z / 2)
  · intro z hz
    simp only [rowEvenConstrainedSet, Finset.mem_filter] at hz
    rcases hz with ⟨hzRow, h2z⟩
    simp only [rowConstrainedSet, Finset.mem_filter,
      Finset.mem_Ioo] at hzRow ⊢
    rcases hzRow with ⟨⟨hz0, hzlt⟩, ⟨hrz, he2z⟩⟩
    have h2Le : 2 ≤ z := Nat.le_of_dvd hz0 h2z
    have hx0 : 0 < z / 2 := Nat.div_pos h2Le (by norm_num)
    have hmuldiv : 2 * (z / 2) = z := Nat.mul_div_cancel' h2z
    have hxlt : z / 2 < H := by
      apply (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp
      rw [hmuldiv]
      exact hzlt
    have h2r : 2 * r ∣ z :=
      hr2.symm.mul_dvd_of_dvd_of_dvd h2z hrz
    have hrdvd : r ∣ z / 2 :=
      (Nat.dvd_div_iff_mul_dvd h2z).2 h2r
    have he2scaled : e2 ∣ 2 * (H - z / 2) := by
      rw [Nat.mul_sub_left_distrib, hmuldiv]
      exact he2z
    have he2dvd : e2 ∣ H - z / 2 :=
      (he22.dvd_mul_left).1 he2scaled
    exact ⟨⟨hx0, hxlt⟩, ⟨hrdvd, he2dvd⟩⟩
  · intro z1 hz1 z2 hz2 heq
    simp only [rowEvenConstrainedSet, Finset.mem_filter] at hz1 hz2
    have h2z1 : 2 ∣ z1 := hz1.2
    have h2z2 : 2 ∣ z2 := hz2.2
    calc
      z1 = 2 * (z1 / 2) := (Nat.mul_div_cancel' h2z1).symm
      _ = 2 * (z2 / 2) := by rw [heq]
      _ = z2 := Nat.mul_div_cancel' h2z2
  · intro x hx
    simp only [rowConstrainedSet, Finset.mem_filter,
      Finset.mem_Ioo] at hx
    rcases hx with ⟨⟨hx0, hxlt⟩, ⟨hrx, he2x⟩⟩
    refine ⟨2 * x, ?_, ?_⟩
    · simp only [rowEvenConstrainedSet, Finset.mem_filter]
      constructor
      · simp only [rowConstrainedSet, Finset.mem_filter,
          Finset.mem_Ioo]
        have hz0 : 0 < 2 * x := Nat.mul_pos (by norm_num) hx0
        have hzlt : 2 * x < 2 * H :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hxlt
        have hrz : r ∣ 2 * x := dvd_mul_of_dvd_right hrx 2
        have he2z : e2 ∣ 2 * H - 2 * x := by
          rw [← Nat.mul_sub_left_distrib]
          exact dvd_mul_of_dvd_right he2x 2
        exact ⟨⟨hz0, hzlt⟩, ⟨hrz, he2z⟩⟩
      · exact dvd_mul_right 2 x
    · exact Nat.mul_div_cancel_left x (by norm_num)
  · intro z hz
    simp only [rowEvenConstrainedSet, Finset.mem_filter] at hz
    rcases hz with ⟨hzRow, h2z⟩
    have hxTarget :
        z / 2 ∈ rowConstrainedSet H r e2 := by
      simp only [rowConstrainedSet, Finset.mem_filter,
        Finset.mem_Ioo] at hzRow ⊢
      rcases hzRow with ⟨⟨hz0, hzlt⟩, ⟨hrz, he2z⟩⟩
      have h2Le : 2 ≤ z := Nat.le_of_dvd hz0 h2z
      have hx0 : 0 < z / 2 := Nat.div_pos h2Le (by norm_num)
      have hmuldiv : 2 * (z / 2) = z := Nat.mul_div_cancel' h2z
      have hxlt : z / 2 < H := by
        apply (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp
        rw [hmuldiv]
        exact hzlt
      have h2r : 2 * r ∣ z :=
        hr2.symm.mul_dvd_of_dvd_of_dvd h2z hrz
      have hrdvd : r ∣ z / 2 :=
        (Nat.dvd_div_iff_mul_dvd h2z).2 h2r
      have he2scaled : e2 ∣ 2 * (H - z / 2) := by
        rw [Nat.mul_sub_left_distrib, hmuldiv]
        exact he2z
      have he2dvd : e2 ∣ H - z / 2 :=
        (he22.dvd_mul_left).1 he2scaled
      exact ⟨⟨hx0, hxlt⟩, ⟨hrdvd, he2dvd⟩⟩
    have hmuldiv : 2 * (z / 2) = z := Nat.mul_div_cancel' h2z
    calc
      lambda z = lambda (2 * (z / 2)) := by rw [hmuldiv]
      _ = lambdaEven (z / 2) := hscale (z / 2) hxTarget


/-- Exact finite row-reduction identity in the manuscript's two-stage
coordinates h = d * (2H).

The hypotheses expose exactly the two source-specific facts used in the paper:
dilation preserves the low-period weight, and the dilated row vanishes on odd
arguments before parity compression.  Everything else is proved here.
-/
theorem exactRowReduction
    (lambda lambdaDilated lambdaReduced : ℕ → ℝ)
    (d H r e2 : ℕ) (N : ℝ)
    (hd : 0 < d) (hr : 0 < r) (he2 : 0 < e2)
    (hcop : d.Coprime e2)
    (hr2 : r.Coprime 2) (he22 : e2.Coprime 2)
    (hDilate :
      ∀ z ∈ rowConstrainedSet (2 * H) r e2,
        lambda (d * z) = lambdaDilated z)
    (hOddZero :
      ∀ z ∈ rowConstrainedSet (2 * H) r e2,
        ¬ 2 ∣ z → lambdaDilated z = 0)
    (hEven :
      ∀ x ∈ rowConstrainedSet H r e2,
        lambdaDilated (2 * x) = lambdaReduced x) :
    rowConstrainedMass lambda (d * (2 * H)) (d * r) e2 -
        N / (((d : ℝ) * (r : ℝ)) * (e2 : ℝ)) =
      rowDiscrepancy lambdaReduced H r e2 +
        rowPeriodicDensityDelta lambdaReduced H N d /
          ((r : ℝ) * (e2 : ℝ)) := by
  apply exactRowReduction_of_constrainedMass_eq
    lambda lambdaReduced (d * (2 * H)) H d r e2 N
    (Nat.ne_of_gt hd) (Nat.ne_of_gt hr) (Nat.ne_of_gt he2)
  calc
    rowConstrainedMass lambda (d * (2 * H)) (d * r) e2 =
        rowConstrainedMass lambdaDilated (2 * H) r e2 :=
      rowConstrainedMass_dilate
        lambda lambdaDilated d (2 * H) r e2 hd hcop hDilate
    _ = rowConstrainedMass lambdaReduced H r e2 :=
      rowConstrainedMass_compress_even
        lambdaDilated lambdaReduced H r e2 hr2 he22
          hOddZero hEven


theorem coprime_right_iff_of_modEq
    {q a b : ℕ} (hab : a ≡ b [MOD q]) :
    q.Coprime a ↔ q.Coprime b := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_rec q a, Nat.gcd_rec q b]
  change a % q = b % q at hab
  rw [hab]

theorem highPrimeLocalRatio_mul_unit
    (p d h y : ℕ) (hpd : p.Coprime d) :
    highPrimeLocalRatio p (d * h) (d * y) =
      highPrimeLocalRatio p h y := by
  have hph : p ∣ d * h ↔ p ∣ h := hpd.dvd_mul_left
  have hpy : p ∣ d * y ↔ p ∣ y := hpd.dvd_mul_left
  have hphy : p ∣ d * h - d * y ↔ p ∣ h - y := by
    rw [← Nat.mul_sub_left_distrib]
    exact hpd.dvd_mul_left
  unfold highPrimeLocalRatio
  simp only [hph, hpy, hphy]


theorem fixedQLowWeight_dilate
    {q a aD d h z : ℕ}
    (hmod : d * aD ≡ a [MOD q])
    (hdq : d.Coprime q)
    (h2d : (2 : ℕ).Coprime d)
    (h3d : (3 : ℕ).Coprime d) :
    fixedQLowWeight q a (d * h) (d * z) =
      fixedQLowWeight q aD h z := by
  have hsum :
      d * (aD + z) ≡ a + d * z [MOD q] := by
    simpa [Nat.mul_add] using
      hmod.add (Nat.ModEq.refl (d * z))
  have hadm :
      q.Coprime (a + d * z) ↔ q.Coprime (aD + z) := by
    calc
      q.Coprime (a + d * z) ↔
          q.Coprime (d * (aD + z)) :=
        (coprime_right_iff_of_modEq hsum).symm
      _ ↔ q.Coprime d ∧ q.Coprime (aD + z) :=
        Nat.coprime_mul_iff_right
      _ ↔ q.Coprime (aD + z) := by
        constructor
        · exact And.right
        · intro hz
          exact ⟨hdq.symm, hz⟩
  have h2ratio :
      highPrimeLocalRatio 2 (d * h) (d * z) =
        highPrimeLocalRatio 2 h z :=
    highPrimeLocalRatio_mul_unit 2 d h z h2d
  have h3ratio :
      highPrimeLocalRatio 3 (d * h) (d * z) =
        highPrimeLocalRatio 3 h z :=
    highPrimeLocalRatio_mul_unit 3 d h z h3d
  unfold fixedQLowWeight lowPrimeLocalRatio lowPrimeSet
  simp [hadm, h2ratio, h3ratio]


theorem fixedQLowWeight_odd_zero
    {q a H z : ℕ}
    (haq : q.Coprime a)
    (hzOdd : ¬ 2 ∣ z) :
    fixedQLowWeight q a (2 * H) z = 0 := by
  by_cases h2q : 2 ∣ q
  · have h2copA : (2 : ℕ).Coprime a :=
      Nat.Coprime.of_dvd_left h2q haq
    have h2a : ¬ 2 ∣ a :=
      Nat.prime_two.coprime_iff_not_dvd.mp h2copA
    have haOdd : Odd a :=
      Nat.not_even_iff_odd.mp (fun haEven => h2a haEven.two_dvd)
    have hzOdd' : Odd z :=
      Nat.not_even_iff_odd.mp (fun hzEven => hzOdd hzEven.two_dvd)
    have h2sum : 2 ∣ a + z :=
      (haOdd.add_odd hzOdd').two_dvd
    have hnotAdm : ¬ q.Coprime (a + z) := by
      intro hc
      have h2cop : (2 : ℕ).Coprime (a + z) :=
        Nat.Coprime.of_dvd_left h2q hc
      exact (Nat.prime_two.coprime_iff_not_dvd.mp h2cop) h2sum
    simp [fixedQLowWeight, hnotAdm]
  · have h2h : 2 ∣ 2 * H := dvd_mul_right 2 H
    unfold fixedQLowWeight lowPrimeSet lowPrimeLocalRatio
    simp [h2q, h2h, hzOdd, highPrimeLocalRatio, c1]


noncomputable def reducedFixedQLowWeight
    (q aD H : ℕ) (x : ℕ) : ℝ :=
  fixedQLowWeight q aD (2 * H) (2 * x)

noncomputable def fixedQRowDelta
    (q a h e1 e2 : ℕ) : ℝ :=
  rowConstrainedMass (fixedQLowWeight q a h) h e1 e2 -
    (admissibleInteriorCount q a h : ℝ) /
      ((e1 : ℝ) * (e2 : ℝ))

noncomputable def fixedQRowPeriodicDensityDelta
    (q a aD d H : ℕ) : ℝ :=
  rowWeightMass (reducedFixedQLowWeight q aD H) H -
    (admissibleInteriorCount q a (d * (2 * H)) : ℝ) / (d : ℝ)

theorem fixedQReducedAnchor_coprime
    {q a aD d : ℕ}
    (ha : q.Coprime a)
    (hmod : d * aD ≡ a [MOD q]) :
    q.Coprime aD := by
  have hprod : q.Coprime (d * aD) :=
    (coprime_right_iff_of_modEq hmod).2 ha
  exact (Nat.coprime_mul_iff_right.mp hprod).2

theorem fixedQRowReduction_exact
    {q a aD d H r e2 : ℕ}
    (ha : q.Coprime a)
    (hmod : d * aD ≡ a [MOD q])
    (hd : 0 < d) (hr : 0 < r) (he2 : 0 < e2)
    (h2d : (2 : ℕ).Coprime d)
    (h3d : (3 : ℕ).Coprime d)
    (hcop : d.Coprime e2)
    (hr2 : r.Coprime 2)
    (he22 : e2.Coprime 2) :
    fixedQRowDelta q a (d * (2 * H)) (d * r) e2 =
      rowDiscrepancy (reducedFixedQLowWeight q aD H) H r e2 +
        fixedQRowPeriodicDensityDelta q a aD d H /
          ((r : ℝ) * (e2 : ℝ)) := by
  have hprod : q.Coprime (d * aD) :=
    (coprime_right_iff_of_modEq hmod).2 ha
  have hdq : d.Coprime q :=
    (Nat.coprime_mul_iff_right.mp hprod).1.symm
  have haD : q.Coprime aD :=
    (Nat.coprime_mul_iff_right.mp hprod).2
  have hrow := exactRowReduction
    (fixedQLowWeight q a (d * (2 * H)))
    (fixedQLowWeight q aD (2 * H))
    (reducedFixedQLowWeight q aD H)
    d H r e2
    (admissibleInteriorCount q a (d * (2 * H)) : ℝ)
    hd hr he2 hcop hr2 he22
    (fun z hz => fixedQLowWeight_dilate hmod hdq h2d h3d)
    (fun z hz hOdd => fixedQLowWeight_odd_zero haD hOdd)
    (fun x hx => rfl)
  simpa [fixedQRowDelta, fixedQRowPeriodicDensityDelta,
    rowPeriodicDensityDelta, Nat.cast_mul, mul_assoc] using hrow


/-!
## Generic periodic-density ledger

For a periodic row weight with known one-period mean, the prefix error depends
only on the remainder modulo the period.  The final theorem gives an explicit
one-period bound for the manuscript's O_q(1) step.
-/

noncomputable def rowPrefixMass
    (f : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ y ∈ Finset.range H, f y

theorem rowPrefixMass_mul_period
    (f : ℕ → ℝ) (P n : ℕ)
    (hper : Function.Periodic f P) :
    rowPrefixMass f (n * P) =
      (n : ℝ) * rowPrefixMass f P := by
  induction n with
  | zero => simp [rowPrefixMass]
  | succ n ih =>
      rw [Nat.succ_mul]
      unfold rowPrefixMass at ih ⊢
      rw [Finset.sum_range_add, ih]
      have hshift :
          (∑ x ∈ Finset.range P, f (n * P + x)) =
            ∑ x ∈ Finset.range P, f x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hp := (hper.nsmul n) x
        simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using hp
      rw [hshift]
      push_cast
      ring

theorem rowPrefixMass_div_mod
    (f : ℕ → ℝ) (P H : ℕ)
    (hper : Function.Periodic f P) :
    rowPrefixMass f H =
      ((H / P : ℕ) : ℝ) * rowPrefixMass f P +
        rowPrefixMass f (H % P) := by
  have hdecomp : (H / P) * P + H % P = H := by
    simpa [Nat.mul_comm] using Nat.div_add_mod H P
  calc
    rowPrefixMass f H =
        rowPrefixMass f ((H / P) * P + H % P) := by
          rw [hdecomp]
    _ = rowPrefixMass f ((H / P) * P) +
        (∑ x ∈ Finset.range (H % P),
          f ((H / P) * P + x)) := by
          unfold rowPrefixMass
          rw [Finset.sum_range_add]
    _ = ((H / P : ℕ) : ℝ) * rowPrefixMass f P +
        (∑ x ∈ Finset.range (H % P), f x) := by
          rw [rowPrefixMass_mul_period f P (H / P) hper]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          have hp := (hper.nsmul (H / P)) x
          simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using hp
    _ = _ := by rfl

theorem rowPrefixMass_sub_mean_eq_mod
    (f : ℕ → ℝ) (P H : ℕ) (mu : ℝ)
    (hper : Function.Periodic f P)
    (hmean : rowPrefixMass f P = mu * (P : ℝ)) :
    rowPrefixMass f H - mu * (H : ℝ) =
      rowPrefixMass f (H % P) -
        mu * ((H % P : ℕ) : ℝ) := by
  rw [rowPrefixMass_div_mod f P H hper, hmean]
  have hdecompR :
      (P : ℝ) * ((H / P : ℕ) : ℝ) +
          ((H % P : ℕ) : ℝ) = (H : ℝ) := by
    exact_mod_cast Nat.div_add_mod H P
  rw [← hdecompR]
  ring

noncomputable def rowPrefixPeriodErrorBound
    (f : ℕ → ℝ) (mu : ℝ) (P : ℕ) : ℝ :=
  ∑ x ∈ Finset.range P, |f x - mu|

theorem abs_rowPrefix_mod_error_le
    (f : ℕ → ℝ) (mu : ℝ) (P H : ℕ)
    (hP : 0 < P) :
    |rowPrefixMass f (H % P) -
        mu * ((H % P : ℕ) : ℝ)| ≤
      rowPrefixPeriodErrorBound f mu P := by
  have herr :
      rowPrefixMass f (H % P) -
          mu * ((H % P : ℕ) : ℝ) =
        ∑ x ∈ Finset.range (H % P), (f x - mu) := by
    unfold rowPrefixMass
    rw [Finset.sum_sub_distrib]
    simp
    ring
  rw [herr]
  calc
    |∑ x ∈ Finset.range (H % P), (f x - mu)| ≤
        ∑ x ∈ Finset.range (H % P), |f x - mu| :=
      Finset.abs_sum_le_sum_abs (fun x => f x - mu) _
    _ ≤ ∑ x ∈ Finset.range P, |f x - mu| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt (Nat.mod_lt H hP)))
      intro x hxP hxNot
      exact abs_nonneg _
    _ = rowPrefixPeriodErrorBound f mu P := by
      rfl

theorem abs_rowPrefix_error_le
    (f : ℕ → ℝ) (mu : ℝ) (P H : ℕ)
    (hP : 0 < P)
    (hper : Function.Periodic f P)
    (hmean : rowPrefixMass f P = mu * (P : ℝ)) :
    |rowPrefixMass f H - mu * (H : ℝ)| ≤
      rowPrefixPeriodErrorBound f mu P := by
  rw [rowPrefixMass_sub_mean_eq_mod f P H mu hper hmean]
  exact abs_rowPrefix_mod_error_le f mu P H hP

theorem rowPrefixMass_eq_zero_add_rowWeightMass
    (f : ℕ → ℝ) (H : ℕ) (hH : 0 < H) :
    rowPrefixMass f H = f 0 + rowWeightMass f H := by
  unfold rowPrefixMass rowWeightMass
  have hset :
      Finset.range H = insert 0 (Finset.Ioo 0 H) := by
    ext x
    simp
    omega
  rw [hset]
  have hzero : 0 ∉ Finset.Ioo 0 H := by simp
  rw [Finset.sum_insert hzero]

theorem abs_rowWeightMass_error_le
    (f : ℕ → ℝ) (mu : ℝ) (P H : ℕ)
    (hP : 0 < P) (hH : 0 < H)
    (hper : Function.Periodic f P)
    (hmean : rowPrefixMass f P = mu * (P : ℝ)) :
    |rowWeightMass f H - mu * (H : ℝ)| ≤
      rowPrefixPeriodErrorBound f mu P + |f 0| := by
  have hpref := abs_rowPrefix_error_le f mu P H hP hper hmean
  have hrow := rowPrefixMass_eq_zero_add_rowWeightMass f H hH
  have heq :
      rowWeightMass f H - mu * (H : ℝ) =
        (rowPrefixMass f H - mu * (H : ℝ)) - f 0 := by
    rw [hrow]
    ring
  rw [heq]
  calc
    |(rowPrefixMass f H - mu * (H : ℝ)) - f 0| =
        |(rowPrefixMass f H - mu * (H : ℝ)) + (-f 0)| := by
          rw [sub_eq_add_neg]
    _ ≤ |rowPrefixMass f H - mu * (H : ℝ)| + |-f 0| :=
      abs_add_le _ _
    _ = |rowPrefixMass f H - mu * (H : ℝ)| + |f 0| := by
      rw [abs_neg]
    _ ≤ rowPrefixPeriodErrorBound f mu P + |f 0| := by
      simpa [add_comm] using (add_le_add_right hpref |f 0|)

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def fixedQPeriod (q : ℕ) : ℕ :=
  Nat.lcm 6 q

theorem tripleOccupiedCount_add_period
    {p h y P : ℕ} (hpP : p ∣ P) :
    tripleOccupiedCount p h (y + P) =
      tripleOccupiedCount p h y := by
  have hPmod : P % p = 0 := Nat.mod_eq_zero_of_dvd hpP
  have hymod : (y + P) % p = y % p := by
    rw [Nat.add_mod, hPmod]
    simp
  unfold tripleOccupiedCount
  rw [hymod]

theorem occupiedAnchoredLocalFactorRatio_add_period
    {p h y P : ℕ} (hpP : p ∣ P) :
    occupiedAnchoredLocalFactorRatio p h (y + P) =
      occupiedAnchoredLocalFactorRatio p h y := by
  unfold occupiedAnchoredLocalFactorRatio
  rw [tripleOccupiedCount_add_period hpP]

theorem coprime_add_fixedQPeriod_iff
    {q a y : ℕ} :
    q.Coprime (a + (y + fixedQPeriod q)) ↔
      q.Coprime (a + y) := by
  have hqP : q ∣ fixedQPeriod q := by
    exact Nat.dvd_lcm_right 6 q
  have hPmod : fixedQPeriod q % q = 0 :=
    Nat.mod_eq_zero_of_dvd hqP
  have hyPmod :
      (y + fixedQPeriod q) % q = y % q := by
    rw [Nat.add_mod, hPmod]
    simp only [add_zero, Nat.mod_mod]
  have hmod :
      (a + (y + fixedQPeriod q)) % q =
        (a + y) % q := by
    calc
      (a + (y + fixedQPeriod q)) % q =
          (a % q + (y + fixedQPeriod q) % q) % q :=
        Nat.add_mod a (y + fixedQPeriod q) q
      _ = (a % q + y % q) % q := by rw [hyPmod]
      _ = (a + y) % q := (Nat.add_mod a y q).symm
  exact coprime_right_iff_of_modEq hmod

theorem occupiedFixedQLowWeight_add_period
    (q a h y : ℕ) :
    occupiedFixedQLowWeight q a h (y + fixedQPeriod q) =
      occupiedFixedQLowWeight q a h y := by
  have h2P : 2 ∣ fixedQPeriod q := by
    exact (show 2 ∣ 6 by norm_num).trans (Nat.dvd_lcm_left 6 q)
  have h3P : 3 ∣ fixedQPeriod q := by
    exact (show 3 ∣ 6 by norm_num).trans (Nat.dvd_lcm_left 6 q)
  unfold occupiedFixedQLowWeight lowPrimeSet
  have hcop := coprime_add_fixedQPeriod_iff (q := q) (a := a) (y := y)
  norm_num [Finset.prod_insert]
  simp only [hcop]
  by_cases h2q : 2 ∣ q
  · simp [h2q]
    by_cases h3q : 3 ∣ q
    · simp [h3q]
    · simp [h3q, occupiedAnchoredLocalFactorRatio_add_period h3P]
  · simp [h2q, occupiedAnchoredLocalFactorRatio_add_period h2P]
    by_cases h3q : 3 ∣ q
    · simp [h3q]
    · simp [h3q, occupiedAnchoredLocalFactorRatio_add_period h3P]

theorem occupiedFixedQLowWeight_periodic
    (q a h : ℕ) :
    Function.Periodic (occupiedFixedQLowWeight q a h)
      (fixedQPeriod q) :=
  occupiedFixedQLowWeight_add_period q a h

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def occupiedReducedFixedQLowWeight
    (q aD H : ℕ) (x : ℕ) : ℝ :=
  occupiedFixedQLowWeight q aD (2 * H) (2 * x)

theorem reducedFixedQLowWeight_eq_occupied
    {q aD H x : ℕ} (hx : x ≤ H)
    (h2admissible : ¬ 2 ∣ q → 2 ∣ 2 * H) :
    reducedFixedQLowWeight q aD H x =
      occupiedReducedFixedQLowWeight q aD H x := by
  unfold reducedFixedQLowWeight occupiedReducedFixedQLowWeight
  apply fixedQLowWeight_eq_occupied
  · exact Nat.mul_le_mul_left 2 hx
  · exact h2admissible

theorem occupiedReducedFixedQLowWeight_periodic
    (q aD H : ℕ) :
    Function.Periodic (occupiedReducedFixedQLowWeight q aD H)
      (fixedQPeriod q) := by
  intro x
  unfold occupiedReducedFixedQLowWeight
  let f := occupiedFixedQLowWeight q aD (2 * H)
  have hp := occupiedFixedQLowWeight_periodic q aD (2 * H)
  calc
    f (2 * (x + fixedQPeriod q)) =
        f ((2 * x + fixedQPeriod q) + fixedQPeriod q) := by
          congr 1
          omega
    _ = f (2 * x + fixedQPeriod q) := hp (2 * x + fixedQPeriod q)
    _ = f (2 * x) := hp (2 * x)

theorem rowWeightMass_reduced_eq_occupied
    (q aD H : ℕ)
    (h2admissible : ¬ 2 ∣ q → 2 ∣ 2 * H) :
    rowWeightMass (reducedFixedQLowWeight q aD H) H =
      rowWeightMass (occupiedReducedFixedQLowWeight q aD H) H := by
  unfold rowWeightMass
  apply Finset.sum_congr rfl
  intro x hx
  have hxI := Finset.mem_Ioo.mp hx
  exact reducedFixedQLowWeight_eq_occupied
    (Nat.le_of_lt hxI.2) h2admissible

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem exactPeriodicCount_real
    {q a b : ℕ} (hq : 0 < q) (n : ℕ) :
    (admissibleInteriorCount q a
        (positiveGapRepresentative q a b + n * q) : ℝ) =
      (Nat.totient q : ℝ) / (q : ℝ) *
          (positiveGapRepresentative q a b + n * q : ℝ) +
        (periodicError q a b : ℝ) := by
  have hRat := exactPeriodicCount (q := q) (a := a) (b := b) hq n
  have hReal := congrArg (fun x : ℚ => (x : ℝ)) hRat
  push_cast at hReal
  simpa using hReal

noncomputable def fixedQRowMean (q : ℕ) : ℝ :=
  2 * (Nat.totient q : ℝ) / (q : ℝ)

theorem fixedQRowPeriodicDensityDelta_decompose
    {q a aD b d H n : ℕ}
    (hq : 0 < q) (hd : 0 < d)
    (hcompat :
      d * (2 * H) =
        positiveGapRepresentative q a b + n * q) :
    fixedQRowPeriodicDensityDelta q a aD d H =
      (rowWeightMass (occupiedReducedFixedQLowWeight q aD H) H -
        fixedQRowMean q * (H : ℝ)) -
      (periodicError q a b : ℝ) / (d : ℝ) := by
  unfold fixedQRowPeriodicDensityDelta
  rw [rowWeightMass_reduced_eq_occupied q aD H
    (fun _ => dvd_mul_right 2 H)]
  rw [hcompat, exactPeriodicCount_real hq n]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hcompatR :
      (positiveGapRepresentative q a b + n * q : ℝ) =
        (d : ℝ) * (2 * (H : ℝ)) := by
    exact_mod_cast hcompat.symm
  rw [hcompatR]
  unfold fixedQRowMean
  field_simp [hdR]
  ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_occupiedAnchoredLocalFactorRatio_two
    {h : ℕ} (h2 : 2 ∣ h) :
    (∑ y ∈ Finset.range 2,
      occupiedAnchoredLocalFactorRatio 2 h y) = 2 := by
  norm_num [Finset.sum_range_succ, occupiedAnchoredLocalFactorRatio,
    tripleOccupiedCount, endpointOccupiedCount]
  have hh : h % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  rw [hh]
  norm_num

theorem sum_occupiedAnchoredLocalFactorRatio_three
    (h : ℕ) :
    (∑ y ∈ Finset.range 3,
      occupiedAnchoredLocalFactorRatio 3 h y) = 3 := by
  have hh : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
  rcases hh with hh | hh | hh <;>
    norm_num [Finset.sum_range_succ, occupiedAnchoredLocalFactorRatio,
      tripleOccupiedCount, endpointOccupiedCount, hh]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_coprime_indicator_period (q a : ℕ) :
    (∑ y ∈ Finset.range q,
      if q.Coprime (a + y) then (1 : ℝ) else 0) =
      (Nat.totient q : ℝ) := by
  calc
    (∑ y ∈ Finset.range q,
      if q.Coprime (a + y) then (1 : ℝ) else 0) =
      ∑ x ∈ Finset.Ico a (a + q),
        if q.Coprime x then (1 : ℝ) else 0 := by
          apply Finset.sum_bij (fun y _ => a + y)
          · intro y hy
            simp only [Finset.mem_range] at hy
            simp only [Finset.mem_Ico]
            omega
          · intro y1 hy1 y2 hy2 heq
            omega
          · intro x hx
            simp only [Finset.mem_Ico] at hx
            refine ⟨x - a, ?_, ?_⟩
            · simp only [Finset.mem_range]
              omega
            · omega
          · intro y hy
            rfl
    _ = (((Finset.Ico a (a + q)).filter fun x => q.Coprime x).card : ℝ) := by
          rw [Finset.sum_boole]
    _ = (Nat.totient q : ℝ) := by
          exact_mod_cast completePeriodCount q a

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_coprime_indicator_affine
    (q a m : ℕ) (hq : 0 < q) (hmq : m.Coprime q) :
    (∑ k ∈ Finset.range q,
      if q.Coprime (a + m * k) then (1 : ℝ) else 0) =
      (Nat.totient q : ℝ) := by
  let phi : Fin q → Fin q := fun k =>
    ⟨(m * k.val) % q, Nat.mod_lt _ hq⟩
  have hphi_inj : Function.Injective phi := by
    intro i j hij
    apply Fin.ext
    have hres : (m * i.val) % q = (m * j.val) % q := by
      exact congrArg Fin.val hij
    have hmod : m * i.val ≡ m * j.val [MOD q] := hres
    have hcancel : i.val ≡ j.val [MOD q] :=
      Nat.ModEq.cancel_left_of_coprime hmq.symm hmod
    exact Nat.ModEq.eq_of_lt_of_lt hcancel i.isLt j.isLt
  have hphi_surj : Function.Surjective phi :=
    Finite.injective_iff_surjective.mp hphi_inj
  calc
    (∑ k ∈ Finset.range q,
      if q.Coprime (a + m * k) then (1 : ℝ) else 0) =
      ∑ r ∈ Finset.range q,
        if q.Coprime (a + r) then (1 : ℝ) else 0 := by
          apply Finset.sum_bij (fun k _ => (m * k) % q)
          · intro k hk
            exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
          · intro k1 hk1 k2 hk2 heq
            have hk1lt := Finset.mem_range.mp hk1
            have hk2lt := Finset.mem_range.mp hk2
            have hmod : m * k1 ≡ m * k2 [MOD q] := heq
            have hc : k1 ≡ k2 [MOD q] :=
              Nat.ModEq.cancel_left_of_coprime hmq.symm hmod
            exact Nat.ModEq.eq_of_lt_of_lt hc hk1lt hk2lt
          · intro r hr
            have hrlt := Finset.mem_range.mp hr
            let rf : Fin q := ⟨r, hrlt⟩
            obtain ⟨kf, hkf⟩ := hphi_surj rf
            refine ⟨kf.val, Finset.mem_range.mpr kf.isLt, ?_⟩
            exact congrArg Fin.val hkf
          · intro k hk
            have hmod :
                (a + m * k) % q =
                  (a + (m * k) % q) % q := by
              calc
                (a + m * k) % q =
                    (a % q + (m * k) % q) % q :=
                  Nat.add_mod a (m * k) q
                _ = (a + (m * k) % q) % q := by
                  simpa only [Nat.mod_mod] using
                    (Nat.add_mod a ((m * k) % q) q).symm
            have hc :
                q.Coprime (a + m * k) ↔
                  q.Coprime (a + (m * k) % q) := by
              rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
              rw [Nat.gcd_rec q (a + m * k),
                Nat.gcd_rec q (a + (m * k) % q)]
              rw [hmod]
            simp only [hc]
    _ = (Nat.totient q : ℝ) := sum_coprime_indicator_period q a

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def lowActiveModulus (q : ℕ) : ℕ :=
  (if 2 ∣ q then 1 else 2) * (if 3 ∣ q then 1 else 3)

theorem fixedQPeriod_eq_lowActiveModulus_mul (q : ℕ) :
    fixedQPeriod q = lowActiveModulus q * q := by
  unfold fixedQPeriod
  by_cases h2 : 2 ∣ q
  · by_cases h3 : 3 ∣ q
    · have h6 : 6 ∣ q := by
        have hc : (2 : ℕ).Coprime 3 := by norm_num
        simpa using hc.mul_dvd_of_dvd_of_dvd h2 h3
      calc
        Nat.lcm 6 q = q := Nat.lcm_eq_right h6
        _ = lowActiveModulus q * q := by
          simp [lowActiveModulus, h2, h3]
    · have hc3q : (3 : ℕ).Coprime q :=
        Nat.prime_three.coprime_iff_not_dvd.mpr h3
      have h6target : 6 ∣ 3 * q := by
        have h2t : 2 ∣ 3 * q := by
          simpa [Nat.mul_comm] using dvd_mul_of_dvd_right h2 3
        have h3t : 3 ∣ 3 * q := dvd_mul_right 3 q
        have hc23 : (2 : ℕ).Coprime 3 := by norm_num
        simpa using hc23.mul_dvd_of_dvd_of_dvd h2t h3t
      have hqt : q ∣ 3 * q := dvd_mul_left q 3
      have h3lcm : 3 ∣ Nat.lcm 6 q :=
        (show 3 ∣ 6 by norm_num).trans (Nat.dvd_lcm_left 6 q)
      have heq : Nat.lcm 6 q = 3 * q := Nat.dvd_antisymm
        (Nat.lcm_dvd h6target hqt)
        (hc3q.mul_dvd_of_dvd_of_dvd h3lcm (Nat.dvd_lcm_right 6 q))
      calc
        Nat.lcm 6 q = 3 * q := heq
        _ = lowActiveModulus q * q := by
          simp [lowActiveModulus, h2, h3]
  · by_cases h3 : 3 ∣ q
    · have hc2q : (2 : ℕ).Coprime q :=
        Nat.prime_two.coprime_iff_not_dvd.mpr h2
      have h6target : 6 ∣ 2 * q := by
        have h2t : 2 ∣ 2 * q := dvd_mul_right 2 q
        have h3t : 3 ∣ 2 * q := by
          simpa [Nat.mul_comm] using dvd_mul_of_dvd_right h3 2
        have hc23 : (2 : ℕ).Coprime 3 := by norm_num
        simpa using hc23.mul_dvd_of_dvd_of_dvd h2t h3t
      have hqt : q ∣ 2 * q := dvd_mul_left q 2
      have h2lcm : 2 ∣ Nat.lcm 6 q :=
        (show 2 ∣ 6 by norm_num).trans (Nat.dvd_lcm_left 6 q)
      have heq : Nat.lcm 6 q = 2 * q := Nat.dvd_antisymm
        (Nat.lcm_dvd h6target hqt)
        (hc2q.mul_dvd_of_dvd_of_dvd h2lcm (Nat.dvd_lcm_right 6 q))
      calc
        Nat.lcm 6 q = 2 * q := heq
        _ = lowActiveModulus q * q := by
          simp [lowActiveModulus, h2, h3]
    · have hc2q : (2 : ℕ).Coprime q :=
        Nat.prime_two.coprime_iff_not_dvd.mpr h2
      have hc3q : (3 : ℕ).Coprime q :=
        Nat.prime_three.coprime_iff_not_dvd.mpr h3
      have hc6q : (6 : ℕ).Coprime q := by
        simpa using hc2q.mul_left hc3q
      have heq : Nat.lcm 6 q = 6 * q := Nat.dvd_antisymm
        (Nat.lcm_dvd (dvd_mul_right 6 q) (dvd_mul_left q 6))
        (hc6q.mul_dvd_of_dvd_of_dvd
          (Nat.dvd_lcm_left 6 q) (Nat.dvd_lcm_right 6 q))
      calc
        Nat.lcm 6 q = 6 * q := heq
        _ = lowActiveModulus q * q := by
          simp [lowActiveModulus, h2, h3]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_range_mul_blocks (f : ℕ → ℝ) (M q : ℕ) :
    (∑ y ∈ Finset.range (M * q), f y) =
      ∑ k ∈ Finset.range q,
        ∑ r ∈ Finset.range M, f (M * k + r) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      rw [Finset.sum_range_succ]

noncomputable def occupiedLowPrimeFactor (q h y : ℕ) : ℝ :=
  ∏ p ∈ lowPrimeSet,
    if p ∣ q then 1 else occupiedAnchoredLocalFactorRatio p h y

theorem occupiedFixedQLowWeight_eq_indicator_mul_factor
    (q a h y : ℕ) :
    occupiedFixedQLowWeight q a h y =
      (if q.Coprime (a + y) then 1 else 0) *
        occupiedLowPrimeFactor q h y := by
  rfl

theorem lowActiveModulus_coprime (q : ℕ) :
    (lowActiveModulus q).Coprime q := by
  by_cases h2 : 2 ∣ q
  · by_cases h3 : 3 ∣ q
    · simp [lowActiveModulus, h2, h3]
    · have hc3q : (3 : ℕ).Coprime q :=
        Nat.prime_three.coprime_iff_not_dvd.mpr h3
      simpa [lowActiveModulus, h2, h3] using hc3q
  · have hc2q : (2 : ℕ).Coprime q :=
      Nat.prime_two.coprime_iff_not_dvd.mpr h2
    by_cases h3 : 3 ∣ q
    · simpa [lowActiveModulus, h2, h3] using hc2q
    · have hc3q : (3 : ℕ).Coprime q :=
        Nat.prime_three.coprime_iff_not_dvd.mpr h3
      have hc6q : (6 : ℕ).Coprime q := by
        simpa using hc2q.mul_left hc3q
      simpa [lowActiveModulus, h2, h3] using hc6q

theorem occupiedLowPrimeFactor_add_modulus
    (q h y : ℕ) :
    occupiedLowPrimeFactor q h (y + lowActiveModulus q) =
      occupiedLowPrimeFactor q h y := by
  by_cases h2 : 2 ∣ q
  · by_cases h3 : 3 ∣ q
    · simp [occupiedLowPrimeFactor, lowPrimeSet,
        lowActiveModulus, h2, h3]
    · have h3M : 3 ∣ lowActiveModulus q := by
        simp [lowActiveModulus, h2, h3]
      unfold occupiedLowPrimeFactor lowPrimeSet
      norm_num [Finset.prod_insert]
      simp [h2, h3,
        occupiedAnchoredLocalFactorRatio_add_period h3M]
  · by_cases h3 : 3 ∣ q
    · have h2M : 2 ∣ lowActiveModulus q := by
        simp [lowActiveModulus, h2, h3]
      unfold occupiedLowPrimeFactor lowPrimeSet
      norm_num [Finset.prod_insert]
      simp [h2, h3,
        occupiedAnchoredLocalFactorRatio_add_period h2M]
    · have h2M : 2 ∣ lowActiveModulus q := by
        simp [lowActiveModulus, h2, h3]
      have h3M : 3 ∣ lowActiveModulus q := by
        simp [lowActiveModulus, h2, h3]
      unfold occupiedLowPrimeFactor lowPrimeSet
      norm_num [Finset.prod_insert]
      simp [h2, h3,
        occupiedAnchoredLocalFactorRatio_add_period h2M,
        occupiedAnchoredLocalFactorRatio_add_period h3M]

theorem occupiedLowPrimeFactor_periodic
    (q h : ℕ) :
    Function.Periodic (occupiedLowPrimeFactor q h)
      (lowActiveModulus q) :=
  occupiedLowPrimeFactor_add_modulus q h

theorem sum_occupiedLowPrimeFactor
    (q h : ℕ) (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    (∑ y ∈ Finset.range (lowActiveModulus q),
      occupiedLowPrimeFactor q h y) = (lowActiveModulus q : ℝ) := by
  by_cases h2 : 2 ∣ q
  · by_cases h3 : 3 ∣ q
    · simp [lowActiveModulus, occupiedLowPrimeFactor, lowPrimeSet, h2, h3]
    · simp [lowActiveModulus, occupiedLowPrimeFactor, lowPrimeSet, h2, h3]
      have hh : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
      rcases hh with hh | hh | hh <;>
        norm_num [Finset.sum_range_succ, occupiedAnchoredLocalFactorRatio,
          tripleOccupiedCount, endpointOccupiedCount, hh]
  · have h2h : 2 ∣ h := h2admissible h2
    by_cases h3 : 3 ∣ q
    · simp [lowActiveModulus, occupiedLowPrimeFactor, lowPrimeSet, h2, h3]
      norm_num [Finset.sum_range_succ, occupiedAnchoredLocalFactorRatio,
        tripleOccupiedCount, endpointOccupiedCount,
        Nat.mod_eq_zero_of_dvd h2h]
    · simp [lowActiveModulus, occupiedLowPrimeFactor, lowPrimeSet, h2, h3]
      have hh2 : h % 2 = 0 := Nat.mod_eq_zero_of_dvd h2h
      have hh3 : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
      rcases hh3 with hh3 | hh3 | hh3 <;>
        norm_num [Finset.sum_range_succ, occupiedAnchoredLocalFactorRatio,
          tripleOccupiedCount, endpointOccupiedCount, hh2, hh3]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem rowPrefixMass_occupiedFixedQLowWeight_period
    (q a h : ℕ) (hq : 0 < q)
    (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    rowPrefixMass (occupiedFixedQLowWeight q a h) (fixedQPeriod q) =
      (Nat.totient q : ℝ) / (q : ℝ) * (fixedQPeriod q : ℝ) := by
  unfold rowPrefixMass
  rw [fixedQPeriod_eq_lowActiveModulus_mul]
  rw [sum_range_mul_blocks]
  rw [Finset.sum_comm]
  have hMcop : (lowActiveModulus q).Coprime q :=
    lowActiveModulus_coprime q
  have hMper :
      Function.Periodic (occupiedLowPrimeFactor q h)
        (lowActiveModulus q) :=
    occupiedLowPrimeFactor_periodic q h
  calc
    (∑ r ∈ Finset.range (lowActiveModulus q),
      ∑ k ∈ Finset.range q,
        occupiedFixedQLowWeight q a h
          (lowActiveModulus q * k + r)) =
      ∑ r ∈ Finset.range (lowActiveModulus q),
        (Nat.totient q : ℝ) * occupiedLowPrimeFactor q h r := by
          apply Finset.sum_congr rfl
          intro r hr
          calc
            (∑ k ∈ Finset.range q,
              occupiedFixedQLowWeight q a h
                (lowActiveModulus q * k + r)) =
              ∑ k ∈ Finset.range q,
                (if q.Coprime
                    ((a + r) + lowActiveModulus q * k)
                  then (1 : ℝ) else 0) *
                  occupiedLowPrimeFactor q h r := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [occupiedFixedQLowWeight_eq_indicator_mul_factor]
                    have hper := (hMper.nsmul k) r
                    have hfactor :
                        occupiedLowPrimeFactor q h
                            (lowActiveModulus q * k + r) =
                          occupiedLowPrimeFactor q h r := by
                      simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using hper
                    rw [hfactor]
                    have hadd :
                        a + (lowActiveModulus q * k + r) =
                          (a + r) + lowActiveModulus q * k := by
                      ac_rfl
                    rw [hadd]
            _ = (∑ k ∈ Finset.range q,
                  if q.Coprime
                      ((a + r) + lowActiveModulus q * k)
                    then (1 : ℝ) else 0) *
                occupiedLowPrimeFactor q h r := by
                  rw [Finset.sum_mul]
            _ = (Nat.totient q : ℝ) *
                occupiedLowPrimeFactor q h r := by
                  rw [sum_coprime_indicator_affine
                    q (a + r) (lowActiveModulus q) hq hMcop]
    _ = (Nat.totient q : ℝ) *
        (∑ r ∈ Finset.range (lowActiveModulus q),
          occupiedLowPrimeFactor q h r) := by
          rw [Finset.mul_sum]
    _ = (Nat.totient q : ℝ) * (lowActiveModulus q : ℝ) := by
          rw [sum_occupiedLowPrimeFactor q h h2admissible]
    _ = (Nat.totient q : ℝ) / (q : ℝ) *
        (↑(lowActiveModulus q * q) : ℝ) := by
          have hqR : (q : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hq)
          push_cast
          field_simp [hqR]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem occupiedFixedQLowWeight_odd_zero
    {q a H y : ℕ}
    (ha : q.Coprime a) (hyOdd : ¬ 2 ∣ y) :
    occupiedFixedQLowWeight q a (2 * H) y = 0 := by
  by_cases h2q : 2 ∣ q
  · have h2copA : (2 : ℕ).Coprime a :=
      Nat.Coprime.of_dvd_left h2q ha
    have h2a : ¬ 2 ∣ a :=
      Nat.prime_two.coprime_iff_not_dvd.mp h2copA
    have haOdd : Odd a :=
      Nat.not_even_iff_odd.mp (fun haEven => h2a haEven.two_dvd)
    have hyOdd' : Odd y :=
      Nat.not_even_iff_odd.mp (fun hyEven => hyOdd hyEven.two_dvd)
    have h2sum : 2 ∣ a + y :=
      (haOdd.add_odd hyOdd').two_dvd
    have hnotAdm : ¬ q.Coprime (a + y) := by
      intro hc
      have h2cop : (2 : ℕ).Coprime (a + y) :=
        Nat.Coprime.of_dvd_left h2q hc
      exact (Nat.prime_two.coprime_iff_not_dvd.mp h2cop) h2sum
    simp [occupiedFixedQLowWeight, hnotAdm]
  · have hhmod : (2 * H) % 2 = 0 := by omega
    have hymod : y % 2 = 1 := by
      have hlt : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hnz : y % 2 ≠ 0 := by
        intro hz
        exact hyOdd (Nat.dvd_iff_mod_eq_zero.mpr hz)
      omega
    have h2factor :
        occupiedAnchoredLocalFactorRatio 2 (2 * H) y = 0 := by
      norm_num [occupiedAnchoredLocalFactorRatio,
        tripleOccupiedCount, endpointOccupiedCount, hhmod, hymod]
    unfold occupiedFixedQLowWeight lowPrimeSet
    norm_num [Finset.prod_insert]
    simp [h2q, h2factor]

theorem rowPrefixMass_occupiedReduced_eq_double_period
    (q aD H : ℕ) (haD : q.Coprime aD) :
    rowPrefixMass (occupiedReducedFixedQLowWeight q aD H)
        (fixedQPeriod q) =
      rowPrefixMass (occupiedFixedQLowWeight q aD (2 * H))
        (2 * fixedQPeriod q) := by
  unfold rowPrefixMass occupiedReducedFixedQLowWeight
  rw [sum_range_mul_blocks
    (occupiedFixedQLowWeight q aD (2 * H)) 2 (fixedQPeriod q)]
  symm
  apply Finset.sum_congr rfl
  intro k hk
  norm_num [Finset.sum_range_succ]
  have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
  rw [occupiedFixedQLowWeight_odd_zero haD hodd]

theorem rowPrefixMass_occupiedReduced_period
    (q aD H : ℕ) (hq : 0 < q) (haD : q.Coprime aD) :
    rowPrefixMass (occupiedReducedFixedQLowWeight q aD H)
        (fixedQPeriod q) =
      fixedQRowMean q * (fixedQPeriod q : ℝ) := by
  rw [rowPrefixMass_occupiedReduced_eq_double_period q aD H haD]
  have hper :=
    occupiedFixedQLowWeight_periodic q aD (2 * H)
  rw [rowPrefixMass_mul_period
    (occupiedFixedQLowWeight q aD (2 * H))
    (fixedQPeriod q) 2 hper]
  rw [rowPrefixMass_occupiedFixedQLowWeight_period
    q aD (2 * H) hq (fun _ => dvd_mul_right 2 H)]
  unfold fixedQRowMean
  ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem abs_fixedQRowPeriodicDensityDelta_le
    {q a aD b d H n : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hH : 0 < H)
    (haD : q.Coprime aD)
    (hcompat :
      d * (2 * H) =
        positiveGapRepresentative q a b + n * q) :
    |fixedQRowPeriodicDensityDelta q a aD d H| ≤
      rowPrefixPeriodErrorBound
          (occupiedReducedFixedQLowWeight q aD H)
          (fixedQRowMean q) (fixedQPeriod q) +
        |occupiedReducedFixedQLowWeight q aD H 0| +
        |(periodicError q a b : ℝ)| := by
  have hP : 0 < fixedQPeriod q := by
    unfold fixedQPeriod
    exact Nat.lcm_pos (by norm_num) hq
  have hrow :
      |rowWeightMass (occupiedReducedFixedQLowWeight q aD H) H -
          fixedQRowMean q * (H : ℝ)| ≤
        rowPrefixPeriodErrorBound
            (occupiedReducedFixedQLowWeight q aD H)
            (fixedQRowMean q) (fixedQPeriod q) +
          |occupiedReducedFixedQLowWeight q aD H 0| :=
    abs_rowWeightMass_error_le
      (occupiedReducedFixedQLowWeight q aD H)
      (fixedQRowMean q) (fixedQPeriod q) H
      hP hH
      (occupiedReducedFixedQLowWeight_periodic q aD H)
      (rowPrefixMass_occupiedReduced_period q aD H hq haD)
  have hdPosR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdOneR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hepsDiv :
      |(periodicError q a b : ℝ) / (d : ℝ)| ≤
        |(periodicError q a b : ℝ)| := by
    rw [abs_div, abs_of_pos hdPosR]
    apply (div_le_iff₀ hdPosR).2
    have hnon : 0 ≤ |(periodicError q a b : ℝ)| := abs_nonneg _
    nlinarith
  rw [fixedQRowPeriodicDensityDelta_decompose hq hd hcompat]
  calc
    |(rowWeightMass (occupiedReducedFixedQLowWeight q aD H) H -
          fixedQRowMean q * (H : ℝ)) -
        (periodicError q a b : ℝ) / (d : ℝ)| ≤
      |rowWeightMass (occupiedReducedFixedQLowWeight q aD H) H -
          fixedQRowMean q * (H : ℝ)| +
        |(periodicError q a b : ℝ) / (d : ℝ)| :=
      abs_sub _ _
    _ ≤
      (rowPrefixPeriodErrorBound
          (occupiedReducedFixedQLowWeight q aD H)
          (fixedQRowMean q) (fixedQPeriod q) +
        |occupiedReducedFixedQLowWeight q aD H 0|) +
        |(periodicError q a b : ℝ)| :=
      add_le_add hrow hepsDiv
    _ = _ := by ring

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem abs_occupiedAnchoredLocalFactorRatio_two_le
    {h y : ℕ} (h2 : 2 ∣ h) :
    |occupiedAnchoredLocalFactorRatio 2 h y| ≤ 2 := by
  have hh : h % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hy with hy | hy <;>
    norm_num [occupiedAnchoredLocalFactorRatio,
      tripleOccupiedCount, endpointOccupiedCount, hh, hy]

theorem abs_occupiedAnchoredLocalFactorRatio_three_le
    (h y : ℕ) :
    |occupiedAnchoredLocalFactorRatio 3 h y| ≤ 3 := by
  have hh : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
  have hy : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hh with hh | hh | hh <;>
    rcases hy with hy | hy | hy <;>
      norm_num [occupiedAnchoredLocalFactorRatio,
        tripleOccupiedCount, endpointOccupiedCount, hh, hy]

theorem abs_occupiedLowPrimeFactor_le_six
    (q h y : ℕ) (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    |occupiedLowPrimeFactor q h y| ≤ 6 := by
  by_cases h2q : 2 ∣ q
  · by_cases h3q : 3 ∣ q
    · simp [occupiedLowPrimeFactor, lowPrimeSet, h2q, h3q]
    · have h3b :=
        abs_occupiedAnchoredLocalFactorRatio_three_le h y
      simp [occupiedLowPrimeFactor, lowPrimeSet, h2q, h3q]
      linarith
  · have h2h : 2 ∣ h := h2admissible h2q
    have h2b := abs_occupiedAnchoredLocalFactorRatio_two_le
      (h := h) (y := y) h2h
    by_cases h3q : 3 ∣ q
    · simp [occupiedLowPrimeFactor, lowPrimeSet, h2q, h3q]
      linarith
    · have h3b :=
        abs_occupiedAnchoredLocalFactorRatio_three_le h y
      have h2non : 0 ≤ |occupiedAnchoredLocalFactorRatio 2 h y| :=
        abs_nonneg _
      have h3non : 0 ≤ |occupiedAnchoredLocalFactorRatio 3 h y| :=
        abs_nonneg _
      unfold occupiedLowPrimeFactor lowPrimeSet
      norm_num [Finset.prod_insert]
      simp only [h2q, h3q, if_false, abs_mul]
      calc
        |occupiedAnchoredLocalFactorRatio 2 h y| *
            |occupiedAnchoredLocalFactorRatio 3 h y| ≤
          (2 : ℝ) * 3 :=
            mul_le_mul h2b h3b h3non (by norm_num)
        _ = 6 := by norm_num

theorem abs_occupiedFixedQLowWeight_le_six
    (q a h y : ℕ) (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    |occupiedFixedQLowWeight q a h y| ≤ 6 := by
  rw [occupiedFixedQLowWeight_eq_indicator_mul_factor]
  by_cases hc : q.Coprime (a + y)
  · rw [if_pos hc, one_mul]
    exact abs_occupiedLowPrimeFactor_le_six q h y h2admissible
  · rw [if_neg hc, zero_mul, abs_zero]
    norm_num

theorem abs_occupiedReducedFixedQLowWeight_le_six
    (q aD H x : ℕ) :
    |occupiedReducedFixedQLowWeight q aD H x| ≤ 6 := by
  unfold occupiedReducedFixedQLowWeight
  exact abs_occupiedFixedQLowWeight_le_six q aD (2 * H) (2 * x)
    (fun _ => dvd_mul_right 2 H)

theorem rowPrefixPeriodErrorBound_reduced_le
    (q aD H : ℕ) :
    rowPrefixPeriodErrorBound
        (occupiedReducedFixedQLowWeight q aD H)
        (fixedQRowMean q) (fixedQPeriod q) ≤
      (fixedQPeriod q : ℝ) *
        (6 + |fixedQRowMean q|) := by
  unfold rowPrefixPeriodErrorBound
  calc
    (∑ x ∈ Finset.range (fixedQPeriod q),
      |occupiedReducedFixedQLowWeight q aD H x -
        fixedQRowMean q|) ≤
      ∑ x ∈ Finset.range (fixedQPeriod q),
        (6 + |fixedQRowMean q|) := by
          apply Finset.sum_le_sum
          intro x hx
          calc
            |occupiedReducedFixedQLowWeight q aD H x -
                fixedQRowMean q| ≤
              |occupiedReducedFixedQLowWeight q aD H x| +
                |fixedQRowMean q| := abs_sub _ _
            _ ≤ 6 + |fixedQRowMean q| := by
              exact add_le_add
                (abs_occupiedReducedFixedQLowWeight_le_six q aD H x)
                (le_refl _)
    _ = (fixedQPeriod q : ℝ) *
        (6 + |fixedQRowMean q|) := by
          simp
          ring

noncomputable def fixedQPeriodicDensityUniformBound
    (q a b : ℕ) : ℝ :=
  (fixedQPeriod q : ℝ) * (6 + |fixedQRowMean q|) +
    6 + |(periodicError q a b : ℝ)|

theorem abs_fixedQRowPeriodicDensityDelta_le_uniform
    {q a aD b d H n : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hH : 0 < H)
    (haD : q.Coprime aD)
    (hcompat :
      d * (2 * H) =
        positiveGapRepresentative q a b + n * q) :
    |fixedQRowPeriodicDensityDelta q a aD d H| ≤
      fixedQPeriodicDensityUniformBound q a b := by
  have hbase :=
    abs_fixedQRowPeriodicDensityDelta_le
      (q := q) (a := a) (aD := aD) (b := b)
      (d := d) (H := H) (n := n)
      hq hd hH haD hcompat
  unfold fixedQPeriodicDensityUniformBound
  calc
    |fixedQRowPeriodicDensityDelta q a aD d H| ≤
      rowPrefixPeriodErrorBound
          (occupiedReducedFixedQLowWeight q aD H)
          (fixedQRowMean q) (fixedQPeriod q) +
        |occupiedReducedFixedQLowWeight q aD H 0| +
        |(periodicError q a b : ℝ)| := hbase
    _ ≤
      ((fixedQPeriod q : ℝ) * (6 + |fixedQRowMean q|)) +
        6 + |(periodicError q a b : ℝ)| := by
          gcongr
          · exact rowPrefixPeriodErrorBound_reduced_le q aD H
          · exact abs_occupiedReducedFixedQLowWeight_le_six q aD H 0

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem normalizationWeightMass_nonneg
    (q h : ℕ) (e : Finset ℕ) :
    0 ≤ normalizationWeightMass q h e := by
  rw [normalizationWeightMass_eq_prod_correction q h e]
  exact Finset.prod_nonneg fun p hp =>
    normalizationCorrection_nonneg q h p

theorem summable_of_abs_le_normalizationWeightMass
    (q h : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (f : Finset ℕ → ℝ)
    (hf : ∀ e, |f e| ≤ C * normalizationWeightMass q h e) :
    Summable f := by
  have hmajor :
      Summable (fun e : Finset ℕ =>
        C * normalizationWeightMass q h e) :=
    Summable.mul_left C (summable_normalizationWeightMass q h)
  have habs :
      Summable (fun e : Finset ℕ => |f e|) :=
    Summable.of_nonneg_of_le
      (fun e => abs_nonneg (f e))
      hf hmajor
  exact Summable.of_norm (by
    simpa [Real.norm_eq_abs] using habs)

def decoratedHeightPrimeSet (q h : ℕ) : Finset ℕ :=
  h.primeFactors.filter fun p => 5 ≤ p ∧ ¬ p ∣ q

theorem finiteVWeightReal_eq_prod_of_subset_height
    (h : ℕ) (s : Finset ℕ)
    (hs : s ⊆ h.primeFactors) :
    finiteVWeightReal h s =
      ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
  unfold finiteVWeightReal
  apply Finset.prod_congr rfl
  intro p hp
  have hph : p ∣ h := Nat.dvd_of_mem_primeFactors (hs hp)
  simp [hph]

theorem decoratedHeightPrimeSet_subset_primeFactors
    (q h : ℕ) :
    decoratedHeightPrimeSet q h ⊆ h.primeFactors := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem sum_decorated_finiteVWeightReal
    (q h : ℕ) :
    (∑ s ∈ (decoratedHeightPrimeSet q h).powerset,
      finiteVWeightReal h s) =
      ∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) - 2)) := by
  calc
    (∑ s ∈ (decoratedHeightPrimeSet q h).powerset,
      finiteVWeightReal h s) =
      ∑ s ∈ (decoratedHeightPrimeSet q h).powerset,
        ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact finiteVWeightReal_eq_prod_of_subset_height h s
            ((Finset.mem_powerset.mp hs).trans
              (decoratedHeightPrimeSet_subset_primeFactors q h))
    _ = ∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) - 2)) := by
          symm
          exact Finset.prod_one_add (decoratedHeightPrimeSet q h)

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

theorem decorated_factor_split {p : ℕ} (hp : 5 ≤ p) :
    (1 + 1 / ((p : ℝ) - 2)) =
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
  have hp2 : (p : ℝ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 2 by omega))
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  field_simp [hp0, hp1, hp2]
  ring

noncomputable def correctionIntervalProd (h : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 5 h,
    (1 + 1 / ((n : ℝ) * ((n : ℝ) - 2)))

theorem correctionIntervalProd_eq
    {h : ℕ} (hh : 5 ≤ h) :
    correctionIntervalProd h =
      4 * ((h : ℝ) - 1) / (3 * (h : ℝ)) := by
  induction h, hh using Nat.le_induction with
  | base =>
      norm_num [correctionIntervalProd]
  | succ h hh ih =>
      unfold correctionIntervalProd at ih ⊢
      rw [Finset.prod_Icc_succ_top (by omega)]
      rw [ih]
      have hR : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
      have hm1 : (h : ℝ) - 1 ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast (show h ≠ 1 by omega))
      have hsR : ((h + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show h + 1 ≠ 0 by omega)
      have hshift : (((h + 1 : ℕ) : ℝ) - 2) = (h : ℝ) - 1 := by
        push_cast
        ring
      rw [hshift]
      field_simp [hR, hm1, hsR]
      push_cast
      ring

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

theorem decoratedHeightPrimeSet_subset_Icc
    {q h : ℕ} (hh : 0 < h) :
    decoratedHeightPrimeSet q h ⊆ Finset.Icc 5 h := by
  intro p hp
  have hpF := Finset.mem_filter.mp hp
  have hpdiv : p ∣ h := Nat.dvd_of_mem_primeFactors hpF.1
  exact Finset.mem_Icc.mpr ⟨hpF.2.1, Nat.le_of_dvd hh hpdiv⟩

theorem correction_factor_one_le
    {n : ℕ} (hn : 5 ≤ n) :
    (1 : ℝ) ≤ 1 + 1 / ((n : ℝ) * ((n : ℝ) - 2)) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := by linarith
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 2) := mul_pos hnPos hn2
  have hnon : 0 ≤ (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) :=
    div_nonneg (by norm_num) hden.le
  linarith

theorem decorated_correction_prod_lt_four_thirds
    {q h : ℕ} (hh : 5 ≤ h) :
    (∏ p ∈ decoratedHeightPrimeSet q h,
      (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) < (4 : ℝ) / 3 := by
  have hsub :
      decoratedHeightPrimeSet q h ⊆ Finset.Icc 5 h :=
    decoratedHeightPrimeSet_subset_Icc (show 0 < h by omega)
  have hle :
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
      correctionIntervalProd h := by
    unfold correctionIntervalProd
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hpS
      exact zero_le_one.trans
        (correction_factor_one_le
          (Finset.mem_Icc.mp (hsub hpS)).1)
    · intro p hpI hpNot
      exact correction_factor_one_le (Finset.mem_Icc.mp hpI).1
  rw [correctionIntervalProd_eq hh] at hle
  have hR : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hfrac : 4 * ((h : ℝ) - 1) / (3 * (h : ℝ)) < (4 : ℝ) / 3 := by
    have hden : 0 < 3 * (h : ℝ) := by positivity
    apply (div_lt_iff₀ hden).2
    field_simp
    nlinarith
  exact hle.trans_lt hfrac

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

theorem prime_totient_factor_one_le
    {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hden : 0 < (p : ℝ) - 1 := by linarith
  apply (le_div_iff₀ hden).2
  linarith

theorem decorated_main_prod_le_full
    (q h : ℕ) :
    (∏ p ∈ decoratedHeightPrimeSet q h,
      (p : ℝ) / ((p : ℝ) - 1)) ≤
      ∏ p ∈ h.primeFactors,
        (p : ℝ) / ((p : ℝ) - 1) := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀
    (decoratedHeightPrimeSet_subset_primeFactors q h)
  · intro p hp
    exact zero_le_one.trans
      (prime_totient_factor_one_le
        (Nat.prime_of_mem_primeFactors
          ((decoratedHeightPrimeSet_subset_primeFactors q h) hp)))
  · intro p hp hpNot
    exact prime_totient_factor_one_le
      (Nat.prime_of_mem_primeFactors hp)

theorem full_prime_factor_prod_eq_totient_ratio
    {h : ℕ} (hh : 0 < h) :
    (∏ p ∈ h.primeFactors,
      (p : ℝ) / ((p : ℝ) - 1)) =
      (h : ℝ) / (h.totient : ℝ) := by
  rw [Finset.prod_div_distrib]
  have hnat := Nat.totient_mul_prod_primeFactors h
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnat
  push_cast at hreal
  have hphi : (h.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hh))
  have hpred :
      (∏ p ∈ h.primeFactors, (((p - 1 : ℕ) : ℝ))) =
        ∏ p ∈ h.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    rw [Nat.cast_sub hpP.one_le]
    norm_num
  have hreal' :
      (h.totient : ℝ) * (∏ p ∈ h.primeFactors, (p : ℝ)) =
        (h : ℝ) * (∏ p ∈ h.primeFactors, ((p : ℝ) - 1)) := by
    rw [← hpred]
    exact hreal
  have hq :
      (∏ p ∈ h.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    exact sub_ne_zero.mpr (by exact_mod_cast hpP.ne_one)
  field_simp [hphi, hq]
  nlinarith [hreal']

theorem decorated_main_prod_le_totient_ratio
    {q h : ℕ} (hh : 0 < h) :
    (∏ p ∈ decoratedHeightPrimeSet q h,
      (p : ℝ) / ((p : ℝ) - 1)) ≤
      (h : ℝ) / (h.totient : ℝ) := by
  rw [← full_prime_factor_prod_eq_totient_ratio hh]
  exact decorated_main_prod_le_full q h

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def decoratedMertensProduct (q h : ℕ) : ℝ :=
  ∏ p ∈ decoratedHeightPrimeSet q h,
    (1 + 1 / ((p : ℝ) - 2))

theorem decoratedMertensProduct_lt_four_thirds_mul_totient_ratio
    {q h : ℕ} (hh : 5 ≤ h) :
    decoratedMertensProduct q h <
      (4 : ℝ) / 3 * ((h : ℝ) / (h.totient : ℝ)) := by
  have hmain :
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (p : ℝ) / ((p : ℝ) - 1)) ≤
        (h : ℝ) / (h.totient : ℝ) :=
    decorated_main_prod_le_totient_ratio (show 0 < h by omega)
  have hcorr :
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) < (4 : ℝ) / 3 :=
    decorated_correction_prod_lt_four_thirds hh
  have hcorr0 :
      0 ≤ ∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    apply Finset.prod_nonneg
    intro p hp
    exact zero_le_one.trans
      (correction_factor_one_le
        (Finset.mem_filter.mp hp).2.1)
  have hratioPos :
      0 < (h : ℝ) / (h.totient : ℝ) := by
    have hhR : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
    have hphiR : 0 < (h.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (show 0 < h by omega)
    exact div_pos hhR hphiR
  calc
    decoratedMertensProduct q h =
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) := by
          unfold decoratedMertensProduct
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro p hp
          exact decorated_factor_split (Finset.mem_filter.mp hp).2.1
    _ ≤ ((h : ℝ) / (h.totient : ℝ)) *
      (∏ p ∈ decoratedHeightPrimeSet q h,
        (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) :=
          mul_le_mul_of_nonneg_right hmain hcorr0
    _ < ((h : ℝ) / (h.totient : ℝ)) * ((4 : ℝ) / 3) :=
          mul_lt_mul_of_pos_left hcorr hratioPos
    _ = (4 : ℝ) / 3 * ((h : ℝ) / (h.totient : ℝ)) := by ring

theorem exp_one_lt_eleven_fourths :
    Real.exp 1 < (11 : ℝ) / 4 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem eleven_sixteenths_lt_log_two :
    (11 : ℝ) / 16 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound' (x := (11 : ℝ) / 16)
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem one_le_log_log_nat_of_sixteen_le
    {h : ℕ} (hh : 16 ≤ h) :
    (1 : ℝ) ≤ Real.log (Real.log (h : ℝ)) := by
  have hhR : (16 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hpos : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hlog16 :
      Real.exp 1 < Real.log (16 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
    have hlog2 := eleven_sixteenths_lt_log_two
    have hexp := exp_one_lt_eleven_fourths
    nlinarith
  have hlogmono :
      Real.log (16 : ℝ) ≤ Real.log (h : ℝ) :=
    (Real.log_le_log_iff (by norm_num) hpos).2 hhR
  have hexp_le : Real.exp 1 ≤ Real.log (h : ℝ) :=
    (hlog16.trans_le hlogmono).le
  have hlogpos : 0 < Real.log (h : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < h by omega))
  exact (Real.le_log_iff_exp_le hlogpos).2 hexp_le

noncomputable def rosserSchoenfeldCstar (gamma : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (Real.exp gamma + 2.50637)

def RosserSchoenfeldTotientRatioAt (gamma : ℝ) (h : ℕ) : Prop :=
  (h : ℝ) / (h.totient : ℝ) <
    Real.exp gamma * Real.log (Real.log (h : ℝ)) +
      2.50637 / Real.log (Real.log (h : ℝ))

theorem decoratedMertensProduct_lt_of_rosserSchoenfeld
    {gamma : ℝ} {q h : ℕ} (hh : 16 ≤ h)
    (hRS : RosserSchoenfeldTotientRatioAt gamma h) :
    decoratedMertensProduct q h <
      rosserSchoenfeldCstar gamma * Real.log (Real.log (h : ℝ)) := by
  have hbase :=
    decoratedMertensProduct_lt_four_thirds_mul_totient_ratio
      (q := q) (h := h) (by omega)
  have hL : (1 : ℝ) ≤ Real.log (Real.log (h : ℝ)) :=
    one_le_log_log_nat_of_sixteen_le hh
  have hLpos : 0 < Real.log (Real.log (h : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hL
  have hrecip :
      2.50637 / Real.log (Real.log (h : ℝ)) ≤
        2.50637 * Real.log (Real.log (h : ℝ)) := by
    apply (div_le_iff₀ hLpos).2
    have hsq : (1 : ℝ) ≤
        Real.log (Real.log (h : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hRS' :
      (h : ℝ) / (h.totient : ℝ) <
        (Real.exp gamma + 2.50637) *
          Real.log (Real.log (h : ℝ)) := by
    unfold RosserSchoenfeldTotientRatioAt at hRS
    calc
      (h : ℝ) / (h.totient : ℝ) <
          Real.exp gamma * Real.log (Real.log (h : ℝ)) +
            2.50637 / Real.log (Real.log (h : ℝ)) := hRS
      _ ≤ Real.exp gamma * Real.log (Real.log (h : ℝ)) +
            2.50637 * Real.log (Real.log (h : ℝ)) :=
          add_le_add_right hrecip _
      _ = (Real.exp gamma + 2.50637) *
          Real.log (Real.log (h : ℝ)) := by ring
  have h43 : (0 : ℝ) < 4 / 3 := by norm_num
  calc
    decoratedMertensProduct q h <
      (4 : ℝ) / 3 * ((h : ℝ) / (h.totient : ℝ)) := hbase
    _ < (4 : ℝ) / 3 *
        ((Real.exp gamma + 2.50637) *
          Real.log (Real.log (h : ℝ))) :=
      mul_lt_mul_of_pos_left hRS' h43
    _ = rosserSchoenfeldCstar gamma * Real.log (Real.log (h : ℝ)) := by
      unfold rosserSchoenfeldCstar
      ring

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

/-- The frozen-paper decorated outer norm, discharged from the single
Rosser--Schoenfeld totient-ratio input at the ambient height. -/
theorem sum_decorated_finiteVWeightReal_lt_of_rosserSchoenfeld
    {gamma : ℝ} {q h : ℕ} (hh : 16 ≤ h)
    (hRS : RosserSchoenfeldTotientRatioAt gamma h) :
    (∑ s ∈ (decoratedHeightPrimeSet q h).powerset,
      finiteVWeightReal h s) <
      rosserSchoenfeldCstar gamma * Real.log (Real.log (h : ℝ)) := by
  rw [sum_decorated_finiteVWeightReal]
  exact decoratedMertensProduct_lt_of_rosserSchoenfeld hh hRS

end RML.Fourier.Vaaler.Internal
namespace RML.Fourier.Vaaler.Internal

lemma sum_log_prime_divisors_le_log
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE,
      if p ∣ n then Real.log p else 0)
      ≤ Real.log n := by
  classical
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hfilter :
      N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpN, hpP⟩, hpd⟩
      exact ⟨hpP, hpd, hn0⟩
    · rintro ⟨hpP, hpd, _⟩
      exact ⟨⟨(Nat.le_of_dvd hn hpd).trans hnN, hpP⟩, hpd⟩
  have hsum :
      (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) =
        ∑ p ∈ n.primeFactors, Real.log p := by
    rw [← Finset.sum_filter]
    rw [hfilter]
  rw [hsum]
  let r : ℕ := ∏ p ∈ n.primeFactors, p
  have hdiv : r ∣ n := by
    simpa [r] using Nat.prod_primeFactors_dvd n
  have hprod_le : r ≤ n :=
    Nat.le_of_dvd hn hdiv
  have hprod_pos : 0 < r := by
    dsimp [r]
    apply Finset.prod_pos
    intro p hp
    exact Nat.pos_of_mem_primeFactors hp
  have hlogprod :
      Real.log (r : ℝ) = ∑ p ∈ n.primeFactors, Real.log p := by
    dsimp [r]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp))
  rw [← hlogprod]
  exact (Real.log_le_log_iff
    (by exact_mod_cast hprod_pos)
    (by exact_mod_cast hn)).2 (by exact_mod_cast hprod_le)


end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_prime_log_div_le
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p)
      ≤ Real.log N + Real.log 4 := by
  classical
  let T : ℝ :=
    ∑ n ∈ Finset.Ioc 0 N,
      ∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0
  have hT_upper : T ≤ (N : ℝ) * Real.log N := by
    dsimp [T]
    calc
      (∑ n ∈ Finset.Ioc 0 N,
        ∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0)
          ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log N := by
            apply Finset.sum_le_sum
            intro n hnmem
            have hnI := Finset.mem_Ioc.mp hnmem
            exact (sum_log_prime_divisors_le_log hnI.1 hnI.2).trans
              ((Real.log_le_log_iff
                (by exact_mod_cast hnI.1)
                (by exact_mod_cast (show 0 < N by omega))).2
                (by exact_mod_cast hnI.2))
      _ = (N : ℝ) * Real.log N := by
        simp
  have hT_swap :
      T = ∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p := by
    dsimp [T]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    simp [Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

  have hfloor_term :
      ∀ p ∈ N.primesLE,
        (N : ℝ) * (Real.log p / (p : ℝ)) - Real.log p ≤
          ((N / p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hpP : p.Prime := Nat.prime_of_mem_primesLE hp
    have hpPos : 0 < p := hpP.pos
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPos
    have hq_lt : N / p < N / p + 1 := Nat.lt_succ_self _
    have hnat : N < (N / p + 1) * p :=
      (Nat.div_lt_iff_lt_mul hpPos).mp hq_lt
    have hreal : (N : ℝ) <
        (((N / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
      exact_mod_cast hnat
    have hratio :
        (N : ℝ) / (p : ℝ) < ((N / p : ℕ) : ℝ) + 1 := by
      exact (div_lt_iff₀ hpR).2 (by simpa [mul_comm] using hreal)
    have hfloor :
        (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := by
      linarith
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpP.one_le)
    have hmul := mul_le_mul_of_nonneg_right hfloor hlog0
    calc
      (N : ℝ) * (Real.log p / (p : ℝ)) - Real.log p =
          ((N : ℝ) / (p : ℝ) - 1) * Real.log p := by ring
      _ ≤ ((N / p : ℕ) : ℝ) * Real.log p := hmul
  have hT_lower :
      (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / (p : ℝ)) -
          (∑ p ∈ N.primesLE, Real.log p) ≤ T := by
    calc
      (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / (p : ℝ)) -
          (∑ p ∈ N.primesLE, Real.log p) =
          ∑ p ∈ N.primesLE,
            ((N : ℝ) * (Real.log p / (p : ℝ)) - Real.log p) := by
              rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p := by
              exact Finset.sum_le_sum hfloor_term
      _ = T := hT_swap.symm
  have htheta :
      (∑ p ∈ N.primesLE, Real.log p) ≤
        Real.log 4 * (N : ℝ) := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hscaled :
      (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / (p : ℝ)) ≤
        (N : ℝ) * (Real.log N + Real.log 4) := by
    nlinarith [hT_lower, hT_upper, htheta]
  nlinarith [hscaled]

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

lemma sum_prime_recip_eq_abel_sum
    (N : ℕ) :
    (∑ p ∈ N.primesLE, (1 : ℝ) / p) =
      ∑ k ∈ Finset.Icc 0 N,
        (Real.log k)⁻¹ *
          (if k.Prime then Real.log k / k else 0) := by
  classical
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkP : k.Prime
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkP.pos
    have hkone : (k : ℝ) ≠ 1 := by exact_mod_cast hkP.ne_one
    have hlog : Real.log (k : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hkpos hkone
    simp only [hkP, if_pos]
    field_simp [hlog]
  · simp [hkP]

lemma prime_log_div_prefix_eq
    (m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m,
      (if k.Prime then Real.log k / k else 0)) =
      ∑ p ∈ m.primesLE, Real.log p / p := by
  classical
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]

lemma Icc_zero_eq_range_succ (m : ℕ) :
    Finset.Icc 0 m = Finset.range (m + 1) := by
  ext k
  simp

example {N : ℕ} (hN : 4 ≤ N) : True := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k / k else 0
  let w : ℕ → ℝ := fun k => (Real.log k)⁻¹
  let A : ℕ → ℝ := fun m => ∑ k ∈ Finset.range (m + 1), c k
  have hparts0 := Finset.sum_range_by_parts' c w (N + 1)
  have hparts1 := hparts0
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts1
  have hparts :
      (∑ k ∈ Finset.range (N + 1), w k * c k) =
        A N * w N +
          ∑ i ∈ Finset.range N, A i * (w i - w (i + 1)) := by
    calc
      (∑ k ∈ Finset.range (N + 1), w k * c k) =
          ∑ k ∈ Finset.range (N + 1), c k * w k := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (∑ k ∈ Finset.range (N + 1), c k) * w N -
          ∑ i ∈ Finset.range N,
            (∑ k ∈ Finset.range (i + 1), c k) * (w (i + 1) - w i) := hparts1
      _ = A N * w N +
          ∑ i ∈ Finset.range N, A i * (w i - w (i + 1)) := by
            simp only [A, sub_eq_add_neg]
            congr 1
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  trivial

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem sum_prime_recip_le_loglog_add_five
    {N : ℕ} (hN : 4 ≤ N) :
    (∑ p ∈ N.primesLE, (1 : ℝ) / p)
      ≤ Real.log (Real.log (N : ℝ)) + 5 := by
  classical
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k / k else 0
  let w : ℕ → ℝ := fun k => (Real.log k)⁻¹
  let A : ℕ → ℝ := fun m => ∑ k ∈ Finset.range (m + 1), c k
  have hAeq (m : ℕ) :
      A m = ∑ p ∈ m.primesLE, Real.log p / p := by
    dsimp [A, c]
    rw [← Icc_zero_eq_range_succ m]
    exact prime_log_div_prefix_eq m
  have hSrange :
      (∑ p ∈ N.primesLE, (1 : ℝ) / p) =
        ∑ k ∈ Finset.range (N + 1), w k * c k := by
    rw [sum_prime_recip_eq_abel_sum N, Icc_zero_eq_range_succ]
  have hparts0 := Finset.sum_range_by_parts' c w (N + 1)
  have hparts1 := hparts0
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts1
  have hparts :
      (∑ k ∈ Finset.range (N + 1), w k * c k) =
        A N * w N +
          ∑ i ∈ Finset.range N, A i * (w i - w (i + 1)) := by
    calc
      (∑ k ∈ Finset.range (N + 1), w k * c k) =
          ∑ k ∈ Finset.range (N + 1), c k * w k := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (∑ k ∈ Finset.range (N + 1), c k) * w N -
          ∑ i ∈ Finset.range N,
            (∑ k ∈ Finset.range (i + 1), c k) * (w (i + 1) - w i) := hparts1
      _ = A N * w N +
          ∑ i ∈ Finset.range N, A i * (w i - w (i + 1)) := by
            simp only [A, sub_eq_add_neg]
            congr 1
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog4pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hboundary : A N * w N ≤ 2 := by
    have hAN := sum_prime_log_div_le (N := N) (by omega)
    rw [← hAeq N] at hAN
    have hlog4le : Real.log (4 : ℝ) ≤ Real.log (N : ℝ) :=
      (Real.log_le_log_iff (by norm_num) (by exact_mod_cast (show 0 < N by omega))).2
        (by exact_mod_cast hN)
    have hA2 : A N ≤ 2 * Real.log (N : ℝ) := by linarith
    dsimp [w]
    calc
      A N * (Real.log (N : ℝ))⁻¹ ≤
          (2 * Real.log (N : ℝ)) * (Real.log (N : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hA2 (le_of_lt (inv_pos.mpr hlogNpos))
      _ = 2 := by field_simp
  let G : ℕ → ℝ := fun i =>
    (Real.log (Real.log ((i + 1 : ℕ) : ℝ)) -
      Real.log (Real.log (i : ℝ))) +
      Real.log (4 : ℝ) * (w i - w (i + 1))
  have hpoint : ∀ i ∈ Finset.range N,
      A i * (w i - w (i + 1)) ≤ if 2 ≤ i then G i else 0 := by
    intro i hi
    by_cases hi2 : 2 ≤ i
    · rw [if_pos hi2]
      have hiPos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
      have hisPos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      have hlogi : 0 < Real.log (i : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < i by omega))
      have hlogis : 0 < Real.log ((i + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < i + 1 by omega))
      have hlogle : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
        (Real.log_le_log_iff hiPos hisPos).2 (by exact_mod_cast (Nat.le_succ i))
      have hdiff : 0 ≤ w i - w (i + 1) := by
        dsimp [w]
        rw [sub_nonneg]
        exact (inv_le_inv₀ hlogis hlogi).2 hlogle
      have hAi0 : 0 ≤ A i := by
        rw [hAeq i]
        apply Finset.sum_nonneg
        intro p hp
        have hpP := Nat.prime_of_mem_primesLE hp
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpP.one_le)) (by positivity)
      have hAi := sum_prime_log_div_le (N := i) (by omega)
      rw [← hAeq i] at hAi
      have hmul := mul_le_mul_of_nonneg_right hAi hdiff
      have hrpos : 0 < Real.log (i : ℝ) / Real.log ((i + 1 : ℕ) : ℝ) :=
        div_pos hlogi hlogis
      have hbasic := Real.log_le_sub_one_of_pos hrpos
      rw [Real.log_div hlogi.ne' hlogis.ne'] at hbasic
      have hfirst :
          1 - Real.log (i : ℝ) / Real.log ((i + 1 : ℕ) : ℝ) ≤
            Real.log (Real.log ((i + 1 : ℕ) : ℝ)) -
              Real.log (Real.log (i : ℝ)) := by
        linarith
      calc
        A i * (w i - w (i + 1)) ≤
            (Real.log (i : ℝ) + Real.log (4 : ℝ)) *
              (w i - w (i + 1)) := hmul
        _ = (1 - Real.log (i : ℝ) / Real.log ((i + 1 : ℕ) : ℝ)) +
            Real.log (4 : ℝ) * (w i - w (i + 1)) := by
              dsimp [w]
              field_simp [hlogi.ne', hlogis.ne']
        _ ≤ G i := by
              dsimp [G]
              simpa [add_comm] using
                (add_le_add_right hfirst (Real.log (4 : ℝ) * (w i - w (i + 1))))
    · rw [if_neg hi2]
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · norm_num [A, c, w]
      · have hA1 : A 1 = 0 := by
          rw [hAeq 1]
          norm_num
        simp [hA1, w]
  have htail0 :
      (∑ i ∈ Finset.range N, A i * (w i - w (i + 1))) ≤
        ∑ i ∈ Finset.range N, if 2 ≤ i then G i else 0 :=
    Finset.sum_le_sum hpoint
  have hfilter :
      (Finset.range N).filter (fun i => 2 ≤ i) = Finset.Ico 2 N := by
    ext i
    simp
    omega
  have htail1 :
      (∑ i ∈ Finset.range N, A i * (w i - w (i + 1))) ≤
        ∑ i ∈ Finset.Ico 2 N, G i := by
    calc
      (∑ i ∈ Finset.range N, A i * (w i - w (i + 1))) ≤
          ∑ i ∈ Finset.range N, if 2 ≤ i then G i else 0 := htail0
      _ = ∑ i ∈ (Finset.range N).filter (fun i => 2 ≤ i), G i := by
          rw [Finset.sum_filter]
      _ = ∑ i ∈ Finset.Ico 2 N, G i := by rw [hfilter]
  have hsumG :
      (∑ i ∈ Finset.Ico 2 N, G i) =
        (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ))) +
          Real.log (4 : ℝ) * (w 2 - w N) := by
    dsimp [G]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have htel1 := Finset.sum_Ico_sub
      (fun i : ℕ => Real.log (Real.log (i : ℝ))) (show 2 ≤ N by omega)
    have htel2 := Finset.sum_Ico_sub w (show 2 ≤ N by omega)
    rw [htel1]
    have hrev :
        (∑ i ∈ Finset.Ico 2 N, (w i - w (i + 1))) = w 2 - w N := by
      calc
        (∑ i ∈ Finset.Ico 2 N, (w i - w (i + 1))) =
            -(∑ i ∈ Finset.Ico 2 N, (w (i + 1) - w i)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = w 2 - w N := by rw [htel2]; ring
    rw [hrev]
    norm_num
  have htail :
      (∑ i ∈ Finset.range N, A i * (w i - w (i + 1))) ≤
        (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ))) +
          Real.log (4 : ℝ) * (w 2 - w N) := by
    rw [← hsumG]
    exact htail1
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hw2 : Real.log (4 : ℝ) * w 2 = 2 := by
    dsimp [w]
    rw [hlog4eq]
    field_simp [hlog2pos.ne']
  have hwNnon : 0 ≤ w N := by
    dsimp [w]
    exact le_of_lt (inv_pos.mpr hlogNpos)
  have hlog2half : (1 : ℝ) / 2 < Real.log (2 : ℝ) := by
    have h := eleven_sixteenths_lt_log_two
    norm_num at h ⊢
    linarith
  have hinvlog2 : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hlog2pos).2 (by nlinarith [hlog2half])
  have hnegloglog2 : -Real.log (Real.log (2 : ℝ)) ≤ 1 := by
    have hiPos : 0 < (Real.log (2 : ℝ))⁻¹ := inv_pos.mpr hlog2pos
    have h := Real.log_le_sub_one_of_pos hiPos
    rw [Real.log_inv] at h
    linarith
  rw [hSrange, hparts]
  calc
    A N * w N + ∑ i ∈ Finset.range N, A i * (w i - w (i + 1)) ≤
      2 + ((Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ))) +
        Real.log (4 : ℝ) * (w 2 - w N)) := add_le_add hboundary htail
    _ ≤ Real.log (Real.log (N : ℝ)) + 5 := by
      have hcorr : Real.log (4 : ℝ) * (w 2 - w N) ≤ 2 := by
        calc
          Real.log (4 : ℝ) * (w 2 - w N) ≤ Real.log (4 : ℝ) * w 2 := by
            nlinarith [hlog4pos.le, hwNnon]
          _ = 2 := hw2
      linarith

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma prime_euler_log_factor_le
    {p : ℕ} (hp : p.Prime) :
    Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      (1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hden : 0 < 1 - (p : ℝ)⁻¹ := by
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hpR
  have hfac : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := inv_pos.mpr hden
  have hlog := Real.log_le_sub_one_of_pos hfac
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  calc
    Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
        (1 - (p : ℝ)⁻¹)⁻¹ - 1 := hlog
    _ = (1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hp0, hp1]
      ring

lemma sum_prime_euler_correction_le_one
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  have hsub : N.primesLE ⊆ Finset.Icc 2 N := by
    intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    exact Finset.mem_Icc.mpr ⟨hpP.two_le, Nat.le_of_mem_primesLE hp⟩
  have hmajor :
      (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnnot
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnpos : 0 < (n : ℝ) := by linarith
    have hn1pos : 0 < (n : ℝ) - 1 := by linarith
    exact div_nonneg zero_le_one (mul_nonneg hnpos.le hn1pos.le)
  have htel :
      (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1))) =
        1 - 1 / (N : ℝ) := by
    rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by ext n; simp]
    let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 1)
    calc
      (∑ n ∈ Finset.Ico 2 (N + 1),
        1 / ((n : ℝ) * ((n : ℝ) - 1))) =
          ∑ n ∈ Finset.Ico 2 (N + 1), (f n - f (n + 1)) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn2 := (Finset.mem_Ico.mp hn).1
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
            have hn1 : (n : ℝ) - 1 ≠ 0 := by
              exact sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
            dsimp [f]
            push_cast
            field_simp [hn0, hn1]
            ring
      _ = -(∑ n ∈ Finset.Ico 2 (N + 1), (f (n + 1) - f n)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ = -(f (N + 1) - f 2) := by
            rw [Finset.sum_Ico_sub f (show 2 ≤ N + 1 by omega)]
      _ = 1 - 1 / (N : ℝ) := by
            dsimp [f]
            push_cast
            have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
            field_simp [hN0]
            ring
  calc
    (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := hmajor
    _ = 1 - 1 / (N : ℝ) := htel
    _ ≤ 1 := by
      have : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith

theorem primeEulerProduct_one_le
    {N : ℕ} (hN : 4 ≤ N) :
    (∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹)
      ≤ Real.exp 6 * (1 + Real.log N) := by
  have hlogsum :
      (∑ p ∈ N.primesLE, Real.log ((1 - (p : ℝ)⁻¹)⁻¹)) ≤
        Real.log (Real.log (N : ℝ)) + 6 := by
    calc
      (∑ p ∈ N.primesLE, Real.log ((1 - (p : ℝ)⁻¹)⁻¹)) ≤
          ∑ p ∈ N.primesLE,
            ((1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
              apply Finset.sum_le_sum
              intro p hp
              exact prime_euler_log_factor_le (Nat.prime_of_mem_primesLE hp)
      _ = (∑ p ∈ N.primesLE, (1 : ℝ) / p) +
          (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (Real.log (Real.log (N : ℝ)) + 5) + 1 := by
            exact add_le_add
              (sum_prime_recip_le_loglog_add_five hN)
              (sum_prime_euler_correction_le_one (by omega))
      _ = Real.log (Real.log (N : ℝ)) + 6 := by ring
  have hfacpos : ∀ p ∈ N.primesLE, 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpP.one_lt
    apply inv_pos.mpr
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hpR
  have hprodpos : 0 < ∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹ :=
    Finset.prod_pos hfacpos
  have hlogprod :
      Real.log (∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹) =
        ∑ p ∈ N.primesLE, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := by
    rw [Real.log_prod]
    intro p hp
    exact (hfacpos p hp).ne'
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    (∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹) =
        Real.exp (Real.log (∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹)) := by
          rw [Real.exp_log hprodpos]
    _ = Real.exp (∑ p ∈ N.primesLE, Real.log ((1 - (p : ℝ)⁻¹)⁻¹)) := by
          rw [hlogprod]
    _ ≤ Real.exp (Real.log (Real.log (N : ℝ)) + 6) :=
          Real.exp_le_exp.mpr hlogsum
    _ = Real.exp 6 * Real.log (N : ℝ) := by
          rw [Real.exp_add, Real.exp_log hlogNpos]
          ring
    _ ≤ Real.exp 6 * (1 + Real.log N) := by
          have hexp0 : 0 ≤ Real.exp 6 := (Real.exp_pos 6).le
          nlinarith

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

lemma prime_totient_factor_eq_euler
    {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / ((p : ℝ) - 1) = (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp [hp0, hp1]

lemma prime_totient_factor_eq_one_add
    {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp [hp1]
  ring

noncomputable def weakMertensC : ℝ := 64 + 2 * Real.exp 8

theorem totientRatio_le_weakMertens
    {h : ℕ} (hh : 16 ≤ h) :
    (h : ℝ) / (h.totient : ℝ) ≤
      weakMertensC * Real.log (Real.log (h : ℝ)) := by
  have hhpos : 0 < h := by omega
  have hL1 : (1 : ℝ) ≤ Real.log (Real.log (h : ℝ)) :=
    one_le_log_log_nat_of_sixteen_le hh
  by_cases h64 : 64 ≤ h
  · let N : ℕ := ⌊Real.log (h : ℝ)⌋₊
    have hloghpos : 0 < Real.log (h : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < h by omega))
    have hlog2 := eleven_sixteenths_lt_log_two
    have hlog64gt4 : (4 : ℝ) < Real.log (64 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num at hlog2 ⊢
      nlinarith
    have hlog64le : Real.log (64 : ℝ) ≤ Real.log (h : ℝ) :=
      (Real.log_le_log_iff (by norm_num) (by exact_mod_cast hhpos)).2
        (by exact_mod_cast h64)
    have hlogh4 : (4 : ℝ) < Real.log (h : ℝ) :=
      hlog64gt4.trans_le hlog64le
    have hN4 : 4 ≤ N := by
      apply Nat.le_floor
      exact hlogh4.le
    have hNpos : 0 < N := by omega
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hNle : (N : ℝ) ≤ Real.log (h : ℝ) := by
      dsimp [N]
      exact Nat.floor_le hloghpos.le
    have hLltN1 : Real.log (h : ℝ) < (N : ℝ) + 1 := by
      dsimp [N]
      simpa using (Nat.lt_floor_add_one (Real.log (h : ℝ)))
    have hN34 : (3 : ℝ) / 4 * Real.log (h : ℝ) < (N : ℝ) := by
      nlinarith
    have hratioLN : Real.log (h : ℝ) / (N : ℝ) ≤ (4 : ℝ) / 3 := by
      apply (div_le_iff₀ hNposR).2
      nlinarith
    have hlog4gt1 : (1 : ℝ) < Real.log (4 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num at hlog2 ⊢
      nlinarith
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogN1 : (1 : ℝ) < Real.log (N : ℝ) := by
      have hlog4le : Real.log (4 : ℝ) ≤ Real.log (N : ℝ) :=
        (Real.log_le_log_iff (by norm_num) hNposR).2 (by exact_mod_cast hN4)
      exact hlog4gt1.trans_le hlog4le
    have hlogNle :
        Real.log (N : ℝ) ≤ Real.log (Real.log (h : ℝ)) :=
      (Real.log_le_log_iff hNposR hloghpos).2 hNle
    let small := h.primeFactors.filter fun p => p ≤ N
    let large := h.primeFactors.filter fun p => N < p
    have hpart : h.primeFactors = small ∪ large := by
      ext p
      simp only [small, large, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        by_cases hpN : p ≤ N
        · exact Or.inl ⟨hp, hpN⟩
        · exact Or.inr ⟨hp, Nat.lt_of_not_ge hpN⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj : Disjoint small large := by
      refine Finset.disjoint_left.mpr ?_
      intro p hps hpl
      have hs := (Finset.mem_filter.mp hps).2
      have hl := (Finset.mem_filter.mp hpl).2
      omega
    have hsmallsub : small ⊆ N.primesLE := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpF.2, Nat.prime_of_mem_primeFactors hpF.1⟩
    have hsmall :
        (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ≤
          Real.exp 6 * (1 + Real.log (N : ℝ)) := by
      calc
        (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ≤
            ∏ p ∈ N.primesLE, (p : ℝ) / ((p : ℝ) - 1) := by
              apply Finset.prod_le_prod_of_subset_of_one_le₀ hsmallsub
              · intro p hp
                exact zero_le_one.trans
                  (prime_totient_factor_one_le
                    (Nat.prime_of_mem_primeFactors
                      (Finset.mem_filter.mp hp).1))
              · intro p hp hpnot
                exact prime_totient_factor_one_le (Nat.prime_of_mem_primesLE hp)
        _ = ∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹)⁻¹ := by
              apply Finset.prod_congr rfl
              intro p hp
              exact prime_totient_factor_eq_euler (Nat.prime_of_mem_primesLE hp)
        _ ≤ Real.exp 6 * (1 + Real.log N) := primeEulerProduct_one_le hN4
    have hsmall' :
        (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ≤
          2 * Real.exp 6 * Real.log (Real.log (h : ℝ)) := by
      have htwolog :
          1 + Real.log (N : ℝ) ≤
            2 * Real.log (Real.log (h : ℝ)) := by
        nlinarith
      calc
        (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ≤
            Real.exp 6 * (1 + Real.log (N : ℝ)) := hsmall
        _ ≤ Real.exp 6 * (2 * Real.log (Real.log (h : ℝ))) := by
              exact mul_le_mul_of_nonneg_left htwolog (Real.exp_nonneg _)
        _ = 2 * Real.exp 6 * Real.log (Real.log (h : ℝ)) := by ring
    have hsumPF :
        (∑ p ∈ h.primeFactors, Real.log (p : ℝ)) ≤ Real.log (h : ℝ) := by
      have hbase := sum_log_prime_divisors_le_log
        (n := h) (N := h) hhpos le_rfl
      have hfilter :
          h.primesLE.filter (fun p => p ∣ h) = h.primeFactors := by
        ext p
        simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
        constructor
        · rintro ⟨⟨hp_le, hpP⟩, hpd⟩
          exact ⟨hpP, hpd, Nat.ne_of_gt hhpos⟩
        · rintro ⟨hpP, hpd, hn0⟩
          exact ⟨⟨Nat.le_of_dvd hhpos hpd, hpP⟩, hpd⟩
      have heq :
          (∑ p ∈ h.primesLE, if p ∣ h then Real.log p else 0) =
            ∑ p ∈ h.primeFactors, Real.log p := by
        rw [← Finset.sum_filter, hfilter]
      simpa [heq] using hbase
    have hsumlarge_log :
        (∑ p ∈ large, Real.log (p : ℝ)) ≤ Real.log (h : ℝ) := by
      calc
        (∑ p ∈ large, Real.log (p : ℝ)) ≤
            ∑ p ∈ h.primeFactors, Real.log (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _)
              intro p hp hpnot
              exact Real.log_nonneg
                (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
        _ ≤ Real.log (h : ℝ) := hsumPF
    have hlarge_term :
        ∀ p ∈ large,
          1 / ((p : ℝ) - 1) ≤
            Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP := Nat.prime_of_mem_primeFactors hpF.1
      have hpgt : N < p := hpF.2
      have hpR : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast hpP.one_lt
      have hp1pos : 0 < (p : ℝ) - 1 := by linarith
      have hNlepm1R : (N : ℝ) ≤ (p : ℝ) - 1 := by
        have hs : N + 1 ≤ p := Nat.succ_le_of_lt hpgt
        have hsR : ((N + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hs
        push_cast at hsR
        linarith
      have hfirst : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / (N : ℝ) := by
        apply (div_le_div_iff₀ hp1pos hNposR).2
        nlinarith
      have hlogNp : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := by
        apply (Real.log_le_log_iff hNposR (by exact_mod_cast hpP.pos)).2
        exact_mod_cast (Nat.le_of_lt hpgt)
      have hdenpos : 0 < (N : ℝ) * Real.log (N : ℝ) :=
        mul_pos hNposR hlogNpos
      have hsecond :
          (1 : ℝ) / (N : ℝ) ≤
            Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
        calc
          (1 : ℝ) / (N : ℝ) =
              Real.log (N : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
                field_simp [hNposR.ne', hlogNpos.ne']
          _ ≤ Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
                exact (div_le_div_iff_of_pos_right hdenpos).2 hlogNp
      exact hfirst.trans hsecond
    have hsumlarge :
        (∑ p ∈ large, 1 / ((p : ℝ) - 1)) ≤ (4 : ℝ) / 3 := by
      calc
        (∑ p ∈ large, 1 / ((p : ℝ) - 1)) ≤
            ∑ p ∈ large,
              Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) :=
          Finset.sum_le_sum hlarge_term
        _ = (∑ p ∈ large, Real.log (p : ℝ)) /
              ((N : ℝ) * Real.log (N : ℝ)) := by
              rw [Finset.sum_div]
        _ ≤ Real.log (h : ℝ) /
              ((N : ℝ) * Real.log (N : ℝ)) := by
              exact (div_le_div_iff_of_pos_right
                (mul_pos hNposR hlogNpos)).2 hsumlarge_log
        _ = (Real.log (h : ℝ) / (N : ℝ)) /
              Real.log (N : ℝ) := by ring
        _ ≤ (4 : ℝ) / 3 := by
              apply (div_le_iff₀ hlogNpos).2
              have hlogNge1 : (1 : ℝ) ≤ Real.log (N : ℝ) := hlogN1.le
              nlinarith
    have hlarge :
        (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) ≤ Real.exp 2 := by
      calc
        (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) =
            ∏ p ∈ large, (1 + 1 / ((p : ℝ) - 1)) := by
              apply Finset.prod_congr rfl
              intro p hp
              exact prime_totient_factor_eq_one_add
                (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        _ ≤ Real.exp (∑ p ∈ large, 1 / ((p : ℝ) - 1)) := by
              have hexp := Real.prod_one_add_le_exp_sum large
                (f := fun p : ℕ =>
                  if p ∈ large then 1 / ((p : ℝ) - 1) else 0)
                (by
                  intro p
                  by_cases hp : p ∈ large
                  · simp only [hp, if_true]
                    have hpP := Nat.prime_of_mem_primeFactors
                      (Finset.mem_filter.mp hp).1
                    have hpR : (1 : ℝ) < (p : ℝ) := by
                      exact_mod_cast hpP.one_lt
                    exact div_nonneg zero_le_one (by linarith)
                  · simp [hp])
              have hprod :
                  (∏ p ∈ large,
                    (1 + if p ∈ large then 1 / ((p : ℝ) - 1) else 0)) =
                    ∏ p ∈ large, (1 + 1 / ((p : ℝ) - 1)) := by
                apply Finset.prod_congr rfl
                intro p hp
                simp [hp]
              have hsum :
                  (∑ p ∈ large,
                    if p ∈ large then 1 / ((p : ℝ) - 1) else 0) =
                    ∑ p ∈ large, 1 / ((p : ℝ) - 1) := by
                apply Finset.sum_congr rfl
                intro p hp
                simp [hp]
              rw [hprod, hsum] at hexp
              exact hexp
        _ ≤ Real.exp ((4 : ℝ) / 3) := Real.exp_le_exp.mpr hsumlarge
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    rw [← full_prime_factor_prod_eq_totient_ratio hhpos]
    rw [hpart, Finset.prod_union hdisj]
    calc
      (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) *
          (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) ≤
        (2 * Real.exp 6 * Real.log (Real.log (h : ℝ))) * Real.exp 2 := by
          exact mul_le_mul hsmall' hlarge
            (Finset.prod_nonneg fun p hp =>
              zero_le_one.trans (prime_totient_factor_one_le
                (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)))
            (by positivity)
      _ = 2 * (Real.exp 6 * Real.exp 2) *
          Real.log (Real.log (h : ℝ)) := by ring
      _ = 2 * Real.exp (6 + 2) * Real.log (Real.log (h : ℝ)) := by
          rw [← Real.exp_add]
      _ = 2 * Real.exp 8 * Real.log (Real.log (h : ℝ)) := by norm_num
      _ ≤ weakMertensC * Real.log (Real.log (h : ℝ)) := by
          unfold weakMertensC
          have hLnon : 0 ≤ Real.log (Real.log (h : ℝ)) := hL1.trans' zero_le_one
          nlinarith
  · have hh64 : h < 64 := lt_of_not_ge h64
    have hphiPos : 0 < (h.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hhpos
    have hphi1 : (1 : ℝ) ≤ (h.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hhpos
    have hratioh : (h : ℝ) / (h.totient : ℝ) ≤ (h : ℝ) := by
      apply (div_le_iff₀ hphiPos).2
      have hhR : 0 ≤ (h : ℝ) := by positivity
      nlinarith
    have hhR64 : (h : ℝ) ≤ 64 := by exact_mod_cast (Nat.le_of_lt_succ (by omega : h < 65))
    have hC64 : (64 : ℝ) ≤ weakMertensC := by
      unfold weakMertensC
      nlinarith [Real.exp_pos 8]
    have hCnon : 0 ≤ weakMertensC := le_trans (by norm_num) hC64
    calc
      (h : ℝ) / (h.totient : ℝ) ≤ (h : ℝ) := hratioh
      _ ≤ 64 := by exact_mod_cast (show h ≤ 64 by omega)
      _ ≤ weakMertensC := hC64
      _ ≤ weakMertensC * Real.log (Real.log (h : ℝ)) := by
            nlinarith

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def weakDecoratedMertensC : ℝ :=
  (4 / 3 : ℝ) * weakMertensC

theorem decoratedMertensProduct_lt_weakMertens
    {q h : ℕ} (hh : 16 ≤ h) :
    decoratedMertensProduct q h <
      weakDecoratedMertensC * Real.log (Real.log (h : ℝ)) := by
  have hbase :=
    decoratedMertensProduct_lt_four_thirds_mul_totient_ratio
      (q := q) (h := h) (by omega)
  have htot := totientRatio_le_weakMertens (h := h) hh
  have h43 : (0 : ℝ) < 4 / 3 := by norm_num
  calc
    decoratedMertensProduct q h <
        (4 : ℝ) / 3 * ((h : ℝ) / (h.totient : ℝ)) := hbase
    _ ≤ (4 : ℝ) / 3 *
        (weakMertensC * Real.log (Real.log (h : ℝ))) :=
      mul_le_mul_of_nonneg_left htot h43.le
    _ = weakDecoratedMertensC * Real.log (Real.log (h : ℝ)) := by
      unfold weakDecoratedMertensC
      ring

theorem sum_decorated_finiteVWeightReal_lt_weakMertens
    {q h : ℕ} (hh : 16 ≤ h) :
    (∑ s ∈ (decoratedHeightPrimeSet q h).powerset,
      finiteVWeightReal h s) <
      weakDecoratedMertensC * Real.log (Real.log (h : ℝ)) := by
  rw [sum_decorated_finiteVWeightReal]
  exact decoratedMertensProduct_lt_weakMertens hh

end RML.Fourier.Vaaler.Internal

