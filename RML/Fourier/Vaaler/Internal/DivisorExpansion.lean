module

public import RML.Fourier.Vaaler.Internal.PeriodicCount
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Data.Nat.Squarefree
import all Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Paper B fixed-q divisor expansion: finite active-prime kernel

Frozen Paper B source:
* `paper_b_frozen.tex`
* SHA-256: `9004c20d63218b529ea392d13914c17a347c485fd43814eb88bf8612a8512070`
* labels: `eq:c0c1`, `eq:omegaq`, `eq:vqh`, `eq:Cqstar`,
  `prop:divisor-expansion`, `eq:Tq-expansion`

This module begins the exact fixed-period reduction immediately after the paid
periodic-count theorem.  It proves the finite active-high-prime algebra behind
the manuscript's divisor expansion.  No convergence, asymptotic, or analytic
estimate is claimed here; the infinite Euler-product/divisor-family passage
remains a separate downstream obligation.
-/

open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal

def c0 (p : ℕ) : ℚ :=
  (p : ℚ) * ((p : ℚ) - 3) / (((p : ℚ) - 1) * ((p : ℚ) - 2))

def c1 (p : ℕ) : ℚ :=
  (p : ℚ) * ((p : ℚ) - 2) / (((p : ℚ) - 1) ^ 2)

theorem c0_selector {p : ℕ} (hp : 5 ≤ p) :
    c0 p * (1 + 1 / ((p : ℚ) - 3)) =
      (p : ℚ) / ((p : ℚ) - 1) := by
  have h1 : (p : ℚ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
  have h2 : (p : ℚ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 2 by omega))
  have h3 : (p : ℚ) - 3 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 3 by omega))
  unfold c0
  field_simp [h1, h2, h3]
  ring

theorem c1_selector {p : ℕ} (hp : 5 ≤ p) :
    c1 p * (1 + 1 / ((p : ℚ) - 2)) =
      (p : ℚ) / ((p : ℚ) - 1) := by
  have h1 : (p : ℚ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
  have h2 : (p : ℚ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 2 by omega))
  unfold c1
  field_simp [h1, h2]
  ring

def highPrimeLocalRatio (p h y : ℕ) : ℚ :=
  if p ∣ h then
    if p ∣ y then (p : ℚ) / ((p : ℚ) - 1) else c1 p
  else
    if p ∣ y then (p : ℚ) / ((p : ℚ) - 1)
    else if p ∣ h - y then (p : ℚ) / ((p : ℚ) - 1) else c0 p

def highPrimeSelectorFactor (p h y : ℕ) : ℚ :=
  if p ∣ h then
    1 + (if p ∣ y then 1 / ((p : ℚ) - 2) else 0)
  else
    1 + (if p ∣ y then 1 / ((p : ℚ) - 3) else 0) +
      (if p ∣ h - y then 1 / ((p : ℚ) - 3) else 0)

def highPrimeBaseline (p h : ℕ) : ℚ :=
  if p ∣ h then c1 p else c0 p

theorem highPrimeLocalRatio_eq_baseline_mul_selector
    {p h y : ℕ} (hp : 5 ≤ p) (hy : y ≤ h) :
    highPrimeLocalRatio p h y =
      highPrimeBaseline p h * highPrimeSelectorFactor p h y := by
  by_cases hph : p ∣ h
  · by_cases hpy : p ∣ y
    · simpa [highPrimeLocalRatio, highPrimeBaseline, highPrimeSelectorFactor,
        hph, hpy] using (c1_selector hp).symm
    · simp [highPrimeLocalRatio, highPrimeBaseline, highPrimeSelectorFactor,
        hph, hpy]
  · by_cases hpy : p ∣ y
    · have hpnot : ¬ p ∣ h - y := by
        intro hpdy
        apply hph
        have hadd : p ∣ (h - y) + y := Nat.dvd_add hpdy hpy
        simpa [Nat.sub_add_cancel hy] using hadd
      simpa [highPrimeLocalRatio, highPrimeBaseline, highPrimeSelectorFactor,
        hph, hpy, hpnot] using (c0_selector hp).symm
    · by_cases hpdy : p ∣ h - y
      · simpa [highPrimeLocalRatio, highPrimeBaseline, highPrimeSelectorFactor,
          hph, hpy, hpdy] using (c0_selector hp).symm
      · simp [highPrimeLocalRatio, highPrimeBaseline, highPrimeSelectorFactor,
          hph, hpy, hpdy]

theorem finiteHighPrimeProduct_factorization
    (P : Finset ℕ) (h y : ℕ) (hy : y ≤ h)
    (hHigh : ∀ p ∈ P, 5 ≤ p) :
    (∏ p ∈ P, highPrimeLocalRatio p h y) =
      (∏ p ∈ P, highPrimeBaseline p h) *
        (∏ p ∈ P, highPrimeSelectorFactor p h y) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact highPrimeLocalRatio_eq_baseline_mul_selector (hHigh p hp) hy

def highPrimeLeftSelector (p h y : ℕ) : ℚ :=
  if p ∣ y then
    if p ∣ h then 1 / ((p : ℚ) - 2) else 1 / ((p : ℚ) - 3)
  else 0

def highPrimeRightSelector (p h y : ℕ) : ℚ :=
  if p ∣ h then 0
  else if p ∣ h - y then 1 / ((p : ℚ) - 3) else 0

theorem highPrimeSelectorFactor_eq
    (p h y : ℕ) :
    highPrimeSelectorFactor p h y =
      1 + highPrimeLeftSelector p h y + highPrimeRightSelector p h y := by
  by_cases hph : p ∣ h <;>
    by_cases hpy : p ∣ y <;>
      by_cases hpdy : p ∣ h - y <;>
        simp [highPrimeSelectorFactor, highPrimeLeftSelector,
          highPrimeRightSelector, hph, hpy, hpdy]

theorem prod_one_add_add_expansion
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (left right : ι → ℚ) :
    (∏ p ∈ P, (1 + left p + right p)) =
      ∑ e ∈ P.powerset,
        ∑ e1 ∈ e.powerset,
          (∏ p ∈ e1, left p) * (∏ p ∈ e \ e1, right p) := by
  calc
    (∏ p ∈ P, (1 + left p + right p)) =
        ∏ p ∈ P, (1 + (left p + right p)) := by
          apply Finset.prod_congr rfl
          intro p hp
          ring
    _ = ∑ e ∈ P.powerset, ∏ p ∈ e, (left p + right p) := by
          exact Finset.prod_one_add P
    _ = ∑ e ∈ P.powerset,
          ∑ e1 ∈ e.powerset,
            (∏ p ∈ e1, left p) * (∏ p ∈ e \ e1, right p) := by
          apply Finset.sum_congr rfl
          intro e he
          exact Finset.prod_add left right e

theorem finiteHighPrimeProduct_divisorExpansion
    (P : Finset ℕ) (h y : ℕ) (hy : y ≤ h)
    (hHigh : ∀ p ∈ P, 5 ≤ p) :
    (∏ p ∈ P, highPrimeLocalRatio p h y) =
      (∏ p ∈ P, highPrimeBaseline p h) *
        ∑ e ∈ P.powerset,
          ∑ e1 ∈ e.powerset,
            (∏ p ∈ e1, highPrimeLeftSelector p h y) *
              (∏ p ∈ e \ e1, highPrimeRightSelector p h y) := by
  rw [finiteHighPrimeProduct_factorization P h y hy hHigh]
  congr 1
  calc
    (∏ p ∈ P, highPrimeSelectorFactor p h y) =
        ∏ p ∈ P,
          (1 + highPrimeLeftSelector p h y + highPrimeRightSelector p h y) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact highPrimeSelectorFactor_eq p h y
    _ = _ := prod_one_add_add_expansion P (fun p => highPrimeLeftSelector p h y) (fun p => highPrimeRightSelector p h y)


def primeSubsetProduct (s : Finset ℕ) : ℕ :=
  ∏ p ∈ s, p

theorem primeSubsetProduct_primeFactors
    (s : Finset ℕ) (hPrime : ∀ p ∈ s, Nat.Prime p) :
    (primeSubsetProduct s).primeFactors = s := by
  unfold primeSubsetProduct
  exact Nat.primeFactors_prod hPrime

theorem primeSubsetProduct_injective_on_powerset
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, Nat.Prime p) :
    Set.InjOn primeSubsetProduct (P.powerset : Set (Finset ℕ)) := by
  intro s hs t ht hst
  have hsSub : s ⊆ P := Finset.mem_powerset.mp hs
  have htSub : t ⊆ P := Finset.mem_powerset.mp ht
  have hsPrime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    exact hPrime p (hsSub hp)
  have htPrime : ∀ p ∈ t, Nat.Prime p := by
    intro p hp
    exact hPrime p (htSub hp)
  have hsPF := primeSubsetProduct_primeFactors s hsPrime
  have htPF := primeSubsetProduct_primeFactors t htPrime
  calc
    s = (primeSubsetProduct s).primeFactors := hsPF.symm
    _ = (primeSubsetProduct t).primeFactors := by rw [hst]
    _ = t := htPF


theorem primeSubsetProduct_dvd_iff
    (s : Finset ℕ) (hPrime : ∀ p ∈ s, Nat.Prime p)
    {n : ℕ} (hn : n ≠ 0) :
    primeSubsetProduct s ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  have hpf := primeSubsetProduct_primeFactors s hPrime
  rw [show primeSubsetProduct s =
      ∏ p ∈ (primeSubsetProduct s).primeFactors, p by
        rw [hpf]
        rfl]
  rw [Nat.prod_primeFactors_dvd_iff hn]
  rw [hpf]
  constructor
  · intro hs p hp
    exact Nat.dvd_of_mem_primeFactors (hs hp)
  · intro hs p hp
    rw [Nat.mem_primeFactors]
    exact ⟨hPrime p hp, hs p hp, hn⟩

theorem primeSubsetProduct_coprime_iff
    (s : Finset ℕ) (hPrime : ∀ p ∈ s, Nat.Prime p) (n : ℕ) :
    (primeSubsetProduct s).Coprime n ↔
      ∀ p ∈ s, ¬ p ∣ n := by
  unfold primeSubsetProduct
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro hs p hp
    exact (hPrime p hp).coprime_iff_not_dvd.mp (hs p hp)
  · intro hs p hp
    exact (hPrime p hp).coprime_iff_not_dvd.mpr (hs p hp)


def finiteVWeight (h : ℕ) (s : Finset ℕ) : ℚ :=
  ∏ p ∈ s,
    if p ∣ h then 1 / ((p : ℚ) - 2) else 1 / ((p : ℚ) - 3)

def finiteOmegaWeight (s : Finset ℕ) : ℚ :=
  ∏ p ∈ s, 1 / ((p : ℚ) - 3)

theorem prod_highPrimeLeftSelector_eq
    (s : Finset ℕ) (h y : ℕ)
    (hPrime : ∀ p ∈ s, Nat.Prime p) (hy : y ≠ 0) :
    (∏ p ∈ s, highPrimeLeftSelector p h y) =
      if primeSubsetProduct s ∣ y then finiteVWeight h s else 0 := by
  unfold highPrimeLeftSelector finiteVWeight
  rw [Finset.prod_ite_zero]
  by_cases hd : primeSubsetProduct s ∣ y
  · have hall : ∀ p ∈ s, p ∣ y :=
      (primeSubsetProduct_dvd_iff s hPrime hy).1 hd
    rw [if_pos hall, if_pos hd]
  · have hnotall : ¬ (∀ p ∈ s, p ∣ y) := by
      intro hall
      exact hd ((primeSubsetProduct_dvd_iff s hPrime hy).2 hall)
    rw [if_neg hnotall, if_neg hd]

theorem highPrimeRightSelector_eq_ite
    (p h y : ℕ) :
    highPrimeRightSelector p h y =
      if (¬ p ∣ h ∧ p ∣ h - y) then
        1 / ((p : ℚ) - 3)
      else 0 := by
  by_cases hph : p ∣ h <;>
    by_cases hpdy : p ∣ h - y <;>
      simp [highPrimeRightSelector, hph, hpdy]

theorem prod_highPrimeRightSelector_eq
    (s : Finset ℕ) (h y : ℕ)
    (hPrime : ∀ p ∈ s, Nat.Prime p) (hhy : h - y ≠ 0) :
    (∏ p ∈ s, highPrimeRightSelector p h y) =
      if (primeSubsetProduct s).Coprime h ∧
          primeSubsetProduct s ∣ h - y
      then finiteOmegaWeight s
      else 0 := by
  simp_rw [highPrimeRightSelector_eq_ite]
  rw [Finset.prod_ite_zero]
  have hcond :
      (∀ p ∈ s, ¬ p ∣ h ∧ p ∣ h - y) ↔
        (primeSubsetProduct s).Coprime h ∧
          primeSubsetProduct s ∣ h - y := by
    constructor
    · intro hs
      constructor
      · exact (primeSubsetProduct_coprime_iff s hPrime h).2
          (fun p hp => (hs p hp).1)
      · exact (primeSubsetProduct_dvd_iff s hPrime hhy).2
          (fun p hp => (hs p hp).2)
    · intro hs p hp
      exact ⟨
        (primeSubsetProduct_coprime_iff s hPrime h).1 hs.1 p hp,
        (primeSubsetProduct_dvd_iff s hPrime hhy).1 hs.2 p hp⟩
  by_cases hc :
      (primeSubsetProduct s).Coprime h ∧
        primeSubsetProduct s ∣ h - y
  · have hall : ∀ p ∈ s, ¬ p ∣ h ∧ p ∣ h - y := hcond.2 hc
    rw [if_pos hall, if_pos hc]
    rfl
  · have hnotall : ¬ (∀ p ∈ s, ¬ p ∣ h ∧ p ∣ h - y) := by
      intro hall
      exact hc (hcond.1 hall)
    rw [if_neg hnotall, if_neg hc]


theorem finiteHighPrimeProduct_divisorConditions
    (P : Finset ℕ) (h y : ℕ)
    (hy0 : 0 < y) (hyh : y < h)
    (hPrime : ∀ p ∈ P, Nat.Prime p)
    (hHigh : ∀ p ∈ P, 5 ≤ p) :
    (∏ p ∈ P, highPrimeLocalRatio p h y) =
      (∏ p ∈ P, highPrimeBaseline p h) *
        ∑ e ∈ P.powerset,
          ∑ e1 ∈ e.powerset,
            (if primeSubsetProduct e1 ∣ y
              then finiteVWeight h e1
              else 0) *
            (if (primeSubsetProduct (e \ e1)).Coprime h ∧
                primeSubsetProduct (e \ e1) ∣ h - y
              then finiteOmegaWeight (e \ e1)
              else 0) := by
  rw [finiteHighPrimeProduct_divisorExpansion P h y (Nat.le_of_lt hyh) hHigh]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have heSub : e ⊆ P := Finset.mem_powerset.mp he
  apply Finset.sum_congr rfl
  intro e1 he1
  have he1Sub : e1 ⊆ e := Finset.mem_powerset.mp he1
  have he2Sub : e \ e1 ⊆ e := Finset.sdiff_subset
  have hPrime1 : ∀ p ∈ e1, Nat.Prime p := by
    intro p hp
    exact hPrime p (heSub (he1Sub hp))
  have hPrime2 : ∀ p ∈ e \ e1, Nat.Prime p := by
    intro p hp
    exact hPrime p (heSub (he2Sub hp))
  have hyne : y ≠ 0 := Nat.ne_of_gt hy0
  have hhyne : h - y ≠ 0 := by omega
  rw [prod_highPrimeLeftSelector_eq e1 h y hPrime1 hyne]
  rw [prod_highPrimeRightSelector_eq (e \ e1) h y hPrime2 hhyne]


/-!
## Infinite baseline normalization

The finite selector algebra above leaves one infinite Euler normalization.
The correction is absolutely summable by a crude O(p^-2) majorant; Mathlib's
`tprod_one_add` then identifies the Euler product with the sum over finite
prime subsets.  Primewise the manuscript baseline is its exact inverse.
-/

noncomputable def normalizationCorrection (q h p : ℕ) : ℝ :=
  if p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q then
    if p ∣ h then
      1 / ((p : ℝ) * ((p : ℝ) - 2))
    else
      2 / ((p : ℝ) * ((p : ℝ) - 3))
  else 0

noncomputable def normalizationBaseline (q h p : ℕ) : ℝ :=
  if p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q then
    if p ∣ h then
      (p : ℝ) * ((p : ℝ) - 2) / (((p : ℝ) - 1) ^ 2)
    else
      (p : ℝ) * ((p : ℝ) - 3) /
        (((p : ℝ) - 1) * ((p : ℝ) - 2))
  else 1

theorem normalizationBaseline_mul_one_add_correction
    (q h p : ℕ) :
    normalizationBaseline q h p * (1 + normalizationCorrection q h p) = 1 := by
  by_cases ha : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q
  · have hp5 : 5 ≤ p := ha.2.1
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
    have hp2 : (p : ℝ) - 2 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 2 by omega))
    have hp3 : (p : ℝ) - 3 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 3 by omega))
    by_cases hph : p ∣ h
    · simp [normalizationBaseline, normalizationCorrection, ha, hph]
      field_simp [hp0, hp1, hp2]
      ring
    · simp [normalizationBaseline, normalizationCorrection, ha, hph]
      field_simp [hp0, hp1, hp2, hp3]
      ring
  · simp [normalizationBaseline, normalizationCorrection, ha]

theorem normalizationCorrection_nonneg
    (q h p : ℕ) :
    0 ≤ normalizationCorrection q h p := by
  by_cases ha : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q
  · have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ha.2.1
    have hpPos : 0 < (p : ℝ) := by linarith
    have hp2Pos : 0 < (p : ℝ) - 2 := by linarith
    have hp3Pos : 0 < (p : ℝ) - 3 := by linarith
    rw [normalizationCorrection, if_pos ha]
    by_cases hph : p ∣ h
    · rw [if_pos hph]
      exact div_nonneg (by norm_num) (mul_nonneg hpPos.le hp2Pos.le)
    · rw [if_neg hph]
      exact div_nonneg (by norm_num) (mul_nonneg hpPos.le hp3Pos.le)
  · rw [normalizationCorrection, if_neg ha]

theorem normalizationCorrection_le
    (q h p : ℕ) :
    normalizationCorrection q h p ≤ 10 / (p : ℝ) ^ 2 := by
  by_cases ha : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q
  · have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ha.2.1
    have hpPos : 0 < (p : ℝ) := by linarith
    have hp2Pos : 0 < (p : ℝ) - 2 := by linarith
    have hp3Pos : 0 < (p : ℝ) - 3 := by linarith
    have hpSq : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hpPos
    rw [normalizationCorrection, if_pos ha]
    by_cases hph : p ∣ h
    · rw [if_pos hph]
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) :=
        mul_pos hpPos hp2Pos
      rw [div_le_div_iff₀ hden hpSq]
      nlinarith
    · rw [if_neg hph]
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 3) :=
        mul_pos hpPos hp3Pos
      rw [div_le_div_iff₀ hden hpSq]
      nlinarith
  · rw [normalizationCorrection, if_neg ha]
    exact div_nonneg (by norm_num) (sq_nonneg _)

theorem norm_normalizationCorrection_le
    (q h p : ℕ) :
    ‖normalizationCorrection q h p‖ ≤ 10 / (p : ℝ) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (normalizationCorrection_nonneg q h p)]
  exact normalizationCorrection_le q h p

theorem summable_norm_normalizationCorrection (q h : ℕ) :
    Summable (fun p : ℕ => ‖normalizationCorrection q h p‖) := by
  have hs : Summable (fun p : ℕ => (10 : ℝ) * (1 / (p : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 10
  exact Summable.of_nonneg_of_le
    (fun p => norm_nonneg _)
    (fun p => by
      simpa [div_eq_mul_inv] using norm_normalizationCorrection_le q h p)
    hs

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

theorem normalizationBaseline_eq_inv_one_add_correction
    (q h p : ℕ) :
    normalizationBaseline q h p =
      (1 + normalizationCorrection q h p)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (normalizationBaseline_mul_one_add_correction q h p)

theorem multipliable_one_add_normalizationCorrection (q h : ℕ) :
    Multipliable (fun p : ℕ => 1 + normalizationCorrection q h p) :=
  multipliable_one_add_of_summable
    (summable_norm_normalizationCorrection q h)

theorem normalizationBaseline_fun_eq_inv
    (q h : ℕ) :
    (fun p : ℕ => normalizationBaseline q h p) =
      (fun p : ℕ => (1 + normalizationCorrection q h p)⁻¹) := by
  funext p
  exact normalizationBaseline_eq_inv_one_add_correction q h p

theorem one_add_normalizationCorrection_pos
    (q h p : ℕ) :
    0 < 1 + normalizationCorrection q h p := by
  have hnonneg := normalizationCorrection_nonneg q h p
  linarith

theorem tprod_one_add_normalizationCorrection_eq_tsum_finset
    (q h : ℕ) :
    (∏' p : ℕ, (1 + normalizationCorrection q h p)) =
      ∑' s : Finset ℕ, ∏ p ∈ s, normalizationCorrection q h p := by
  exact tprod_one_add
    (summable_finsetProd_of_summable_norm
      (summable_norm_normalizationCorrection q h))

theorem tprod_normalizationBaseline_eq_inv
    (q h : ℕ) :
    (∏' p : ℕ, normalizationBaseline q h p) =
      ∏' p : ℕ, (1 + normalizationCorrection q h p)⁻¹ := by
  exact congrArg
    (fun f : ℕ → ℝ => ∏' p : ℕ, f p)
    (normalizationBaseline_fun_eq_inv q h)

theorem correction_tprod_ne_zero
    (q h : ℕ) :
    (∏' p : ℕ, (1 + normalizationCorrection q h p)) ≠ 0 := by
  exact tprod_one_add_ne_zero_of_summable
    (fun p => ne_of_gt (one_add_normalizationCorrection_pos q h p))
    (summable_norm_normalizationCorrection q h)

theorem inv_correction_tprod_mul_correction_tprod
    (q h : ℕ) :
    (∏' p : ℕ, (1 + normalizationCorrection q h p)⁻¹) *
        (∏' p : ℕ, (1 + normalizationCorrection q h p)) = 1 := by
  have hinv :
      (∏' p : ℕ, (1 + normalizationCorrection q h p)⁻¹) =
        (∏' p : ℕ, (1 + normalizationCorrection q h p))⁻¹ := by
    exact
      (multipliable_one_add_normalizationCorrection q h).tprod_inv₀
        (correction_tprod_ne_zero q h)
  rw [hinv]
  exact inv_mul_cancel₀ (correction_tprod_ne_zero q h)

theorem normalizationBaseline_tprod_mul_correction_tprod
    (q h : ℕ) :
    (∏' p : ℕ, normalizationBaseline q h p) *
        (∏' p : ℕ, (1 + normalizationCorrection q h p)) = 1 := by
  rw [tprod_normalizationBaseline_eq_inv q h]
  exact inv_correction_tprod_mul_correction_tprod q h

theorem infiniteBaselineNormalization
    (q h : ℕ) :
    (∏' p : ℕ, normalizationBaseline q h p) *
      (∑' s : Finset ℕ, ∏ p ∈ s, normalizationCorrection q h p) = 1 := by
  rw [← tprod_one_add_normalizationCorrection_eq_tsum_finset q h]
  exact normalizationBaseline_tprod_mul_correction_tprod q h

noncomputable def normalizationLeft (q h p : ℕ) : ℝ :=
  if p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q then
    if p ∣ h then
      1 / ((p : ℝ) * ((p : ℝ) - 2))
    else
      1 / ((p : ℝ) * ((p : ℝ) - 3))
  else 0

noncomputable def normalizationRight (q h p : ℕ) : ℝ :=
  if p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q then
    if p ∣ h then 0
    else 1 / ((p : ℝ) * ((p : ℝ) - 3))
  else 0

theorem normalizationCorrection_eq_left_add_right
    (q h p : ℕ) :
    normalizationCorrection q h p =
      normalizationLeft q h p + normalizationRight q h p := by
  by_cases ha : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q
  · by_cases hph : p ∣ h
    · simp [normalizationCorrection, normalizationLeft, normalizationRight,
        ha, hph]
    · have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ha.2.1
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp3 : (p : ℝ) - 3 ≠ 0 := by linarith
      simp [normalizationCorrection, normalizationLeft, normalizationRight,
        ha, hph]
      field_simp [hp0, hp3]
      ring
  · simp [normalizationCorrection, normalizationLeft, normalizationRight, ha]

theorem prod_normalizationCorrection_partition
    (q h : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, normalizationCorrection q h p) =
      ∑ e1 ∈ s.powerset,
        (∏ p ∈ e1, normalizationLeft q h p) *
          (∏ p ∈ s \ e1, normalizationRight q h p) := by
  calc
    (∏ p ∈ s, normalizationCorrection q h p) =
        ∏ p ∈ s,
          (normalizationLeft q h p + normalizationRight q h p) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact normalizationCorrection_eq_left_add_right q h p
    _ = _ := Finset.prod_add
      (fun p => normalizationLeft q h p)
      (fun p => normalizationRight q h p)
      s

theorem infiniteBaselineNormalization_partitioned
    (q h : ℕ) :
    (∏' p : ℕ, normalizationBaseline q h p) *
      (∑' s : Finset ℕ,
        ∑ e1 ∈ s.powerset,
          (∏ p ∈ e1, normalizationLeft q h p) *
            (∏ p ∈ s \ e1, normalizationRight q h p)) = 1 := by
  simpa only [prod_normalizationCorrection_partition] using
    infiniteBaselineNormalization q h

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def activeHighPrime (q p : ℕ) : Prop :=
  p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q

instance activeHighPrimeDecidable (q p : ℕ) :
    Decidable (activeHighPrime q p) := by
  unfold activeHighPrime
  infer_instance

noncomputable def finiteVWeightReal (h : ℕ) (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, if p ∣ h then 1 / ((p : ℝ) - 2) else 1 / ((p : ℝ) - 3)

noncomputable def finiteOmegaWeightReal (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, 1 / ((p : ℝ) - 3)

theorem normalizationLeft_eq_weight_over_prime
    (q h p : ℕ) :
    normalizationLeft q h p =
      if activeHighPrime q p then
        (if p ∣ h then 1 / ((p : ℝ) - 2) else 1 / ((p : ℝ) - 3)) / (p : ℝ)
      else 0 := by
  by_cases ha : activeHighPrime q p
  · have ha' : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q := by
      simpa [activeHighPrime] using ha
    have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ha'.2.1
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    have hp3 : (p : ℝ) - 3 ≠ 0 := by linarith
    by_cases hph : p ∣ h
    · rw [if_pos ha, if_pos hph]
      simp [normalizationLeft, ha', hph]
      field_simp [hp0, hp2]
    · rw [if_pos ha, if_neg hph]
      simp [normalizationLeft, ha', hph]
      field_simp [hp0, hp3]
  · rw [if_neg ha]
    have ha' : ¬ (p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q) := by
      simpa [activeHighPrime] using ha
    simp [normalizationLeft, ha']

theorem normalizationRight_eq_weight_over_prime
    (q h p : ℕ) :
    normalizationRight q h p =
      if activeHighPrime q p ∧ ¬ p ∣ h then
        (1 / ((p : ℝ) - 3)) / (p : ℝ)
      else 0 := by
  classical
  by_cases ha : activeHighPrime q p
  · have ha' : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q := by
      simpa [activeHighPrime] using ha
    have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ha'.2.1
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp3 : (p : ℝ) - 3 ≠ 0 := by linarith
    by_cases hph : p ∣ h
    · have hcond : ¬ (activeHighPrime q p ∧ ¬ p ∣ h) := by
        intro hc
        exact hc.2 hph
      rw [if_neg hcond]
      simp [normalizationRight, ha', hph]
    · have hcond : activeHighPrime q p ∧ ¬ p ∣ h := ⟨ha, hph⟩
      rw [if_pos hcond]
      simp [normalizationRight, ha', hph]
      field_simp [hp0, hp3]
  · have hcond : ¬ (activeHighPrime q p ∧ ¬ p ∣ h) := by
      intro hc
      exact ha hc.1
    rw [if_neg hcond]
    have ha' : ¬ (p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q) := by
      simpa [activeHighPrime] using ha
    simp [normalizationRight, ha']

theorem prod_normalizationLeft_eq
    (q h : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, normalizationLeft q h p) =
      if (∀ p ∈ s, activeHighPrime q p) then
        finiteVWeightReal h s / (∏ p ∈ s, (p : ℝ))
      else 0 := by
  classical
  simp_rw [normalizationLeft_eq_weight_over_prime q h]
  rw [Finset.prod_ite_zero]
  by_cases hs : ∀ p ∈ s, activeHighPrime q p
  · rw [if_pos hs, if_pos hs]
    rw [Finset.prod_div_distrib]
    rfl
  · rw [if_neg hs, if_neg hs]

theorem prod_normalizationRight_eq
    (q h : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, normalizationRight q h p) =
      if (∀ p ∈ s, activeHighPrime q p ∧ ¬ p ∣ h) then
        finiteOmegaWeightReal s / (∏ p ∈ s, (p : ℝ))
      else 0 := by
  classical
  simp_rw [normalizationRight_eq_weight_over_prime q h]
  rw [Finset.prod_ite_zero]
  by_cases hs : ∀ p ∈ s, activeHighPrime q p ∧ ¬ p ∣ h
  · rw [if_pos hs, if_pos hs]
    rw [Finset.prod_div_distrib]
    rfl
  · rw [if_neg hs, if_neg hs]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def cStarReal (q h : ℕ) : ℝ :=
  ∏' p : ℕ, normalizationBaseline q h p

theorem infiniteBaselineNormalization_weights
    (q h : ℕ) :
    cStarReal q h *
      (∑' s : Finset ℕ,
        ∑ e1 ∈ s.powerset,
          (if (∀ p ∈ e1, activeHighPrime q p) then
              finiteVWeightReal h e1 / (∏ p ∈ e1, (p : ℝ))
            else 0) *
          (if (∀ p ∈ s \ e1, activeHighPrime q p ∧ ¬ p ∣ h) then
              finiteOmegaWeightReal (s \ e1) /
                (∏ p ∈ s \ e1, (p : ℝ))
            else 0)) = 1 := by
  simpa only [cStarReal, prod_normalizationLeft_eq,
      prod_normalizationRight_eq] using
    infiniteBaselineNormalization_partitioned q h

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def activeHighBaseline (q h p : ℕ) : ℝ :=
  if activeHighPrime q p then ((highPrimeBaseline p h : ℚ) : ℝ) else 1

noncomputable def activeHighLocalRatio (q h y p : ℕ) : ℝ :=
  if activeHighPrime q p then ((highPrimeLocalRatio p h y : ℚ) : ℝ) else 1

noncomputable def activeHighLeftSelector (q h y p : ℕ) : ℝ :=
  if activeHighPrime q p then ((highPrimeLeftSelector p h y : ℚ) : ℝ) else 0

noncomputable def activeHighRightSelector (q h y p : ℕ) : ℝ :=
  if activeHighPrime q p then ((highPrimeRightSelector p h y : ℚ) : ℝ) else 0

theorem activeHighBaseline_eq_normalizationBaseline
    (q h p : ℕ) :
    activeHighBaseline q h p = normalizationBaseline q h p := by
  by_cases ha : activeHighPrime q p
  · have ha' : p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q := by
      simpa [activeHighPrime] using ha
    by_cases hph : p ∣ h
    · simp [activeHighBaseline, highPrimeBaseline, normalizationBaseline,
        c1, ha, ha', hph]
    · simp [activeHighBaseline, highPrimeBaseline, normalizationBaseline,
        c0, ha, ha', hph]
  · have ha' : ¬ (p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ q) := by
      simpa [activeHighPrime] using ha
    simp [activeHighBaseline, normalizationBaseline, ha, ha']

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem cast_highPrimeSelectorFactor_eq
    (p h y : ℕ) :
    ((highPrimeSelectorFactor p h y : ℚ) : ℝ) =
      1 +
        ((highPrimeLeftSelector p h y : ℚ) : ℝ) +
        ((highPrimeRightSelector p h y : ℚ) : ℝ) := by
  exact_mod_cast highPrimeSelectorFactor_eq p h y

theorem activeHighSelectorFactor_eq
    (q h y p : ℕ) :
    (if activeHighPrime q p then
        ((highPrimeSelectorFactor p h y : ℚ) : ℝ)
      else 1) =
      1 + activeHighLeftSelector q h y p +
        activeHighRightSelector q h y p := by
  by_cases ha : activeHighPrime q p
  · simp [activeHighLeftSelector, activeHighRightSelector, ha,
      cast_highPrimeSelectorFactor_eq]
  · simp [activeHighLeftSelector, activeHighRightSelector, ha]

theorem cast_highPrimeLocalRatio_factorization
    {p h y : ℕ} (hp : 5 ≤ p) (hy : y ≤ h) :
    ((highPrimeLocalRatio p h y : ℚ) : ℝ) =
      ((highPrimeBaseline p h : ℚ) : ℝ) *
        ((highPrimeSelectorFactor p h y : ℚ) : ℝ) := by
  exact_mod_cast highPrimeLocalRatio_eq_baseline_mul_selector hp hy

theorem activeHighLocalRatio_factorization
    (q h y p : ℕ) (hy : y ≤ h) :
    activeHighLocalRatio q h y p =
      activeHighBaseline q h p *
        (1 + activeHighLeftSelector q h y p +
          activeHighRightSelector q h y p) := by
  by_cases ha : activeHighPrime q p
  · have hp : 5 ≤ p := ha.2.1
    rw [activeHighLocalRatio, if_pos ha]
    rw [activeHighBaseline, if_pos ha]
    rw [← activeHighSelectorFactor_eq q h y p]
    rw [if_pos ha]
    exact cast_highPrimeLocalRatio_factorization hp hy
  · simp [activeHighLocalRatio, activeHighBaseline,
      activeHighLeftSelector, activeHighRightSelector, ha]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

def selectorPrimeSet (h y : ℕ) : Finset ℕ :=
  y.primeFactors ∪ (h - y).primeFactors

theorem activeHighSelectors_zero_of_not_mem
    (q h y p : ℕ) (hy0 : 0 < y) (hyh : y < h)
    (hpnot : p ∉ selectorPrimeSet h y) :
    activeHighLeftSelector q h y p = 0 ∧
      activeHighRightSelector q h y p = 0 := by
  have hyne : y ≠ 0 := Nat.ne_of_gt hy0
  have hhyne : h - y ≠ 0 := by omega
  by_cases ha : activeHighPrime q p
  · have hpPrime : p.Prime := ha.1
    have hpy : ¬ p ∣ y := by
      intro hpdy
      have hmem : p ∈ y.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpPrime, hpdy, hyne⟩
      exact hpnot (by simp [selectorPrimeSet, hmem])
    have hphy : ¬ p ∣ h - y := by
      intro hpdy
      have hmem : p ∈ (h - y).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpPrime, hpdy, hhyne⟩
      exact hpnot (by simp [selectorPrimeSet, hmem])
    constructor
    · simp [activeHighLeftSelector, highPrimeLeftSelector, ha, hpy]
    · by_cases hph : p ∣ h
      · simp [activeHighRightSelector, highPrimeRightSelector, ha, hph]
      · simp [activeHighRightSelector, highPrimeRightSelector, ha, hph, hphy]
  · simp [activeHighLeftSelector, activeHighRightSelector, ha]

theorem activeHighSelectorFactor_eq_one_of_not_mem
    (q h y p : ℕ) (hy0 : 0 < y) (hyh : y < h)
    (hpnot : p ∉ selectorPrimeSet h y) :
    1 + activeHighLeftSelector q h y p +
        activeHighRightSelector q h y p = 1 := by
  obtain ⟨hl, hr⟩ :=
    activeHighSelectors_zero_of_not_mem q h y p hy0 hyh hpnot
  rw [hl, hr]
  ring

theorem multipliable_activeHighSelectorFactor
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    Multipliable
      (fun p : ℕ =>
        1 + activeHighLeftSelector q h y p +
          activeHighRightSelector q h y p) := by
  apply multipliable_of_hasFiniteMulSupport
  refine (selectorPrimeSet h y).finite_toSet.subset ?_
  intro p hp
  by_contra hpmem
  exact hp (activeHighSelectorFactor_eq_one_of_not_mem
    q h y p hy0 hyh hpmem)

theorem tprod_activeHighSelectorFactor_eq_prod
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    (∏' p : ℕ,
      (1 + activeHighLeftSelector q h y p +
        activeHighRightSelector q h y p)) =
      ∏ p ∈ selectorPrimeSet h y,
        (1 + activeHighLeftSelector q h y p +
          activeHighRightSelector q h y p) := by
  exact tprod_eq_prod
    (fun p hp => activeHighSelectorFactor_eq_one_of_not_mem
      q h y p hy0 hyh hp)

theorem norm_normalizationBaseline_sub_one_le
    (q h p : ℕ) :
    ‖normalizationBaseline q h p - 1‖ ≤
      ‖normalizationCorrection q h p‖ := by
  have hc : 0 ≤ normalizationCorrection q h p :=
    normalizationCorrection_nonneg q h p
  have hpos : 0 < 1 + normalizationCorrection q h p := by
    linarith
  rw [normalizationBaseline_eq_inv_one_add_correction q h p]
  have hid :
      (1 + normalizationCorrection q h p)⁻¹ - 1 =
        - normalizationCorrection q h p /
          (1 + normalizationCorrection q h p) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hid, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg hc, abs_of_pos hpos]
  rw [Real.norm_eq_abs, abs_of_nonneg hc]
  apply (div_le_iff₀ hpos).2
  nlinarith [sq_nonneg (normalizationCorrection q h p)]

theorem summable_norm_normalizationBaseline_sub_one
    (q h : ℕ) :
    Summable (fun p : ℕ => ‖normalizationBaseline q h p - 1‖) := by
  exact Summable.of_nonneg_of_le
    (fun p => norm_nonneg _)
    (fun p => norm_normalizationBaseline_sub_one_le q h p)
    (summable_norm_normalizationCorrection q h)

theorem multipliable_normalizationBaseline' (q h : ℕ) :
    Multipliable (fun p : ℕ => normalizationBaseline q h p) := by
  have hm :
      Multipliable
        (fun p : ℕ => 1 + (normalizationBaseline q h p - 1)) :=
    multipliable_one_add_of_summable
      (summable_norm_normalizationBaseline_sub_one q h)
  exact hm.congr (fun p => by ring)

theorem multipliable_activeHighBaseline (q h : ℕ) :
    Multipliable (fun p : ℕ => activeHighBaseline q h p) := by
  exact (multipliable_normalizationBaseline' q h).congr
    (fun p => (activeHighBaseline_eq_normalizationBaseline q h p).symm)

theorem tprod_activeHighLocalRatio_factorization
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    (∏' p : ℕ, activeHighLocalRatio q h y p) =
      cStarReal q h *
        ∏ p ∈ selectorPrimeSet h y,
          (1 + activeHighLeftSelector q h y p +
            activeHighRightSelector q h y p) := by
  have hb := multipliable_activeHighBaseline q h
  have hs := multipliable_activeHighSelectorFactor q h y hy0 hyh
  calc
    (∏' p : ℕ, activeHighLocalRatio q h y p) =
        ∏' p : ℕ,
          activeHighBaseline q h p *
            (1 + activeHighLeftSelector q h y p +
              activeHighRightSelector q h y p) := by
            apply tprod_congr
            intro p
            exact activeHighLocalRatio_factorization q h y p
              (Nat.le_of_lt hyh)
    _ = (∏' p : ℕ, activeHighBaseline q h p) *
          (∏' p : ℕ,
            (1 + activeHighLeftSelector q h y p +
              activeHighRightSelector q h y p)) := by
            exact hb.tprod_mul hs
    _ = cStarReal q h *
          ∏ p ∈ selectorPrimeSet h y,
            (1 + activeHighLeftSelector q h y p +
              activeHighRightSelector q h y p) := by
            rw [tprod_activeHighSelectorFactor_eq_prod q h y hy0 hyh]
            unfold cStarReal
            apply congrArg (fun z : ℝ => z *
              ∏ p ∈ selectorPrimeSet h y,
                (1 + activeHighLeftSelector q h y p +
                  activeHighRightSelector q h y p))
            apply tprod_congr
            intro p
            exact activeHighBaseline_eq_normalizationBaseline q h p

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem prod_one_add_add_expansion_real
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (left right : ι → ℝ) :
    (∏ p ∈ P, (1 + left p + right p)) =
      ∑ e ∈ P.powerset,
        ∑ e1 ∈ e.powerset,
          (∏ p ∈ e1, left p) *
            (∏ p ∈ e \ e1, right p) := by
  calc
    (∏ p ∈ P, (1 + left p + right p)) =
        ∏ p ∈ P, (1 + (left p + right p)) := by
          apply Finset.prod_congr rfl
          intro p hp
          ring
    _ = ∑ e ∈ P.powerset, ∏ p ∈ e, (left p + right p) := by
          exact Finset.prod_one_add P
    _ = ∑ e ∈ P.powerset,
          ∑ e1 ∈ e.powerset,
            (∏ p ∈ e1, left p) *
              (∏ p ∈ e \ e1, right p) := by
          apply Finset.sum_congr rfl
          intro e he
          exact Finset.prod_add left right e

theorem activeHighLeftSelector_eq_weight_ite
    (q h y p : ℕ) :
    activeHighLeftSelector q h y p =
      if activeHighPrime q p ∧ p ∣ y then
        if p ∣ h then 1 / ((p : ℝ) - 2)
        else 1 / ((p : ℝ) - 3)
      else 0 := by
  by_cases ha : activeHighPrime q p
  · by_cases hpy : p ∣ y
    · by_cases hph : p ∣ h
      · simp [activeHighLeftSelector, highPrimeLeftSelector, ha, hpy, hph]
      · simp [activeHighLeftSelector, highPrimeLeftSelector, ha, hpy, hph]
    · simp [activeHighLeftSelector, highPrimeLeftSelector, ha, hpy]
  · simp [activeHighLeftSelector, ha]

theorem activeHighRightSelector_eq_weight_ite
    (q h y p : ℕ) :
    activeHighRightSelector q h y p =
      if activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y then
        1 / ((p : ℝ) - 3)
      else 0 := by
  by_cases ha : activeHighPrime q p
  · by_cases hph : p ∣ h
    · simp [activeHighRightSelector, highPrimeRightSelector, ha, hph]
    · by_cases hphy : p ∣ h - y
      · simp [activeHighRightSelector, highPrimeRightSelector,
          ha, hph, hphy]
      · simp [activeHighRightSelector, highPrimeRightSelector,
          ha, hph, hphy]
  · simp [activeHighRightSelector, ha]

theorem prod_activeHighLeftSelector_eq
    (q h y : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, activeHighLeftSelector q h y p) =
      if (∀ p ∈ s, activeHighPrime q p ∧ p ∣ y) then
        finiteVWeightReal h s
      else 0 := by
  classical
  simp_rw [activeHighLeftSelector_eq_weight_ite q h y]
  rw [Finset.prod_ite_zero]
  by_cases hs : ∀ p ∈ s, activeHighPrime q p ∧ p ∣ y
  · rw [if_pos hs, if_pos hs]
    rfl
  · rw [if_neg hs, if_neg hs]

theorem prod_activeHighRightSelector_eq
    (q h y : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, activeHighRightSelector q h y p) =
      if (∀ p ∈ s,
          activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y) then
        finiteOmegaWeightReal s
      else 0 := by
  classical
  simp_rw [activeHighRightSelector_eq_weight_ite q h y]
  rw [Finset.prod_ite_zero]
  by_cases hs :
      ∀ p ∈ s, activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y
  · rw [if_pos hs, if_pos hs]
    rfl
  · rw [if_neg hs, if_neg hs]

theorem finiteActiveSelectorProduct_expansion
    (q h y : ℕ) :
    (∏ p ∈ selectorPrimeSet h y,
      (1 + activeHighLeftSelector q h y p +
        activeHighRightSelector q h y p)) =
      ∑ e ∈ (selectorPrimeSet h y).powerset,
        ∑ e1 ∈ e.powerset,
          (∏ p ∈ e1, activeHighLeftSelector q h y p) *
            (∏ p ∈ e \ e1, activeHighRightSelector q h y p) := by
  exact prod_one_add_add_expansion_real
    (selectorPrimeSet h y)
    (fun p => activeHighLeftSelector q h y p)
    (fun p => activeHighRightSelector q h y p)

theorem tprod_activeHighLocalRatio_divisorExpansion
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    (∏' p : ℕ, activeHighLocalRatio q h y p) =
      cStarReal q h *
        ∑ e ∈ (selectorPrimeSet h y).powerset,
          ∑ e1 ∈ e.powerset,
            (if (∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) then
                finiteVWeightReal h e1
              else 0) *
            (if (∀ p ∈ e \ e1,
                activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y) then
                finiteOmegaWeightReal (e \ e1)
              else 0) := by
  rw [tprod_activeHighLocalRatio_factorization q h y hy0 hyh]
  congr 1
  rw [finiteActiveSelectorProduct_expansion q h y]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro e1 he1
  rw [prod_activeHighLeftSelector_eq q h y e1]
  rw [prod_activeHighRightSelector_eq q h y (e \ e1)]

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

noncomputable def perYSelectorMass
    (q h y : ℕ) (e : Finset ℕ) : ℝ :=
  ∑ e1 ∈ e.powerset,
    (∏ p ∈ e1, activeHighLeftSelector q h y p) *
      (∏ p ∈ e \ e1, activeHighRightSelector q h y p)

noncomputable def perYWeightMass
    (q h y : ℕ) (e : Finset ℕ) : ℝ :=
  ∑ e1 ∈ e.powerset,
    (if (∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) then
        finiteVWeightReal h e1
      else 0) *
    (if (∀ p ∈ e \ e1,
        activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y) then
        finiteOmegaWeightReal (e \ e1)
      else 0)

theorem perYSelectorMass_eq_zero_of_not_mem
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h)
    {e : Finset ℕ}
    (he : e ∉ (selectorPrimeSet h y).powerset) :
    perYSelectorMass q h y e = 0 := by
  have hnotSub : ¬ e ⊆ selectorPrimeSet h y := by
    intro hsub
    exact he (Finset.mem_powerset.mpr hsub)
  obtain ⟨p, hpe, hpnot⟩ := Finset.not_subset.mp hnotSub
  obtain ⟨hl, hr⟩ :=
    activeHighSelectors_zero_of_not_mem q h y p hy0 hyh hpnot
  unfold perYSelectorMass
  apply Finset.sum_eq_zero
  intro e1 he1
  by_cases hpe1 : p ∈ e1
  · have hleft :
        (∏ x ∈ e1, activeHighLeftSelector q h y x) = 0 :=
      Finset.prod_eq_zero hpe1 hl
    rw [hleft, zero_mul]
  · have hrightMem : p ∈ e \ e1 := by
      simp [hpe, hpe1]
    have hright :
        (∏ x ∈ e \ e1, activeHighRightSelector q h y x) = 0 :=
      Finset.prod_eq_zero hrightMem hr
    rw [hright, mul_zero]

theorem summable_perYSelectorMass
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    Summable (perYSelectorMass q h y) := by
  apply summable_of_hasFiniteSupport
  refine (selectorPrimeSet h y).powerset.finite_toSet.subset ?_
  intro e he
  by_contra hemem
  exact he (perYSelectorMass_eq_zero_of_not_mem
    q h y hy0 hyh hemem)

theorem tsum_perYSelectorMass_eq_finite
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    (∑' e : Finset ℕ, perYSelectorMass q h y e) =
      ∑ e ∈ (selectorPrimeSet h y).powerset,
        perYSelectorMass q h y e := by
  exact tsum_eq_sum
    (fun e he => perYSelectorMass_eq_zero_of_not_mem
      q h y hy0 hyh he)

theorem perYSelectorMass_eq_weightMass
    (q h y : ℕ) (e : Finset ℕ) :
    perYSelectorMass q h y e =
      perYWeightMass q h y e := by
  unfold perYSelectorMass perYWeightMass
  apply Finset.sum_congr rfl
  intro e1 he1
  rw [prod_activeHighLeftSelector_eq q h y e1]
  rw [prod_activeHighRightSelector_eq q h y (e \ e1)]

theorem tprod_activeHighLocalRatio_globalDivisorExpansion
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    (∏' p : ℕ, activeHighLocalRatio q h y p) =
      cStarReal q h *
        (∑' e : Finset ℕ, perYWeightMass q h y e) := by
  rw [tprod_activeHighLocalRatio_factorization q h y hy0 hyh]
  rw [finiteActiveSelectorProduct_expansion q h y]
  change
    cStarReal q h *
        (∑ e ∈ (selectorPrimeSet h y).powerset,
          perYSelectorMass q h y e) =
      cStarReal q h *
        (∑' e : Finset ℕ, perYWeightMass q h y e)
  rw [← tsum_perYSelectorMass_eq_finite q h y hy0 hyh]
  apply congrArg (fun z : ℝ => cStarReal q h * z)
  apply tsum_congr
  intro e
  exact perYSelectorMass_eq_weightMass q h y e

end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

theorem summable_perYWeightMass
    (q h y : ℕ) (hy0 : 0 < y) (hyh : y < h) :
    Summable (perYWeightMass q h y) := by
  exact (summable_perYSelectorMass q h y hy0 hyh).congr
    (fun e => perYSelectorMass_eq_weightMass q h y e)

theorem interior_sum_tsum_perYWeightMass
    (q h : ℕ) (lambda : ℕ → ℝ) :
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∑' e : Finset ℕ, perYWeightMass q h y e)) =
      ∑' e : Finset ℕ,
        ∑ y ∈ Finset.Ioo 0 h,
          lambda y * perYWeightMass q h y e := by
  have hs :
      ∀ y ∈ Finset.Ioo 0 h,
        Summable (fun e : Finset ℕ =>
          lambda y * perYWeightMass q h y e) := by
    intro y hy
    have hy' := Finset.mem_Ioo.mp hy
    exact Summable.mul_left (lambda y)
      (summable_perYWeightMass q h y hy'.1 hy'.2)
  calc
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∑' e : Finset ℕ, perYWeightMass q h y e)) =
      ∑ y ∈ Finset.Ioo 0 h,
        (∑' e : Finset ℕ, lambda y * perYWeightMass q h y e) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact tsum_mul_left.symm
    _ = ∑' e : Finset ℕ,
        ∑ y ∈ Finset.Ioo 0 h,
          lambda y * perYWeightMass q h y e := by
          exact (Summable.tsum_finsetSum hs).symm

theorem weightedActiveRatioSum_expansion
    (q h : ℕ) (lambda : ℕ → ℝ) :
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∏' p : ℕ, activeHighLocalRatio q h y p)) =
      cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) := by
  calc
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∏' p : ℕ, activeHighLocalRatio q h y p)) =
      ∑ y ∈ Finset.Ioo 0 h,
        lambda y *
          (cStarReal q h *
            (∑' e : Finset ℕ, perYWeightMass q h y e)) := by
              apply Finset.sum_congr rfl
              intro y hy
              have hy' := Finset.mem_Ioo.mp hy
              rw [tprod_activeHighLocalRatio_globalDivisorExpansion
                q h y hy'.1 hy'.2]
    _ = cStarReal q h *
        (∑ y ∈ Finset.Ioo 0 h,
          lambda y *
            (∑' e : Finset ℕ, perYWeightMass q h y e)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
    _ = cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) := by
              rw [interior_sum_tsum_perYWeightMass q h lambda]

noncomputable def normalizationWeightMass
    (q h : ℕ) (e : Finset ℕ) : ℝ :=
  ∑ e1 ∈ e.powerset,
    (if (∀ p ∈ e1, activeHighPrime q p) then
        finiteVWeightReal h e1 / (∏ p ∈ e1, (p : ℝ))
      else 0) *
    (if (∀ p ∈ e \ e1, activeHighPrime q p ∧ ¬ p ∣ h) then
        finiteOmegaWeightReal (e \ e1) /
          (∏ p ∈ e \ e1, (p : ℝ))
      else 0)

theorem infiniteNormalizationWeightMass
    (q h : ℕ) :
    cStarReal q h *
      (∑' e : Finset ℕ, normalizationWeightMass q h e) = 1 := by
  simpa only [normalizationWeightMass] using
    infiniteBaselineNormalization_weights q h

theorem weightedActiveRatioSum_sub_exactCount
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ) :
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∏' p : ℕ, activeHighLocalRatio q h y p)) - N =
      cStarReal q h *
        ((∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) -
          N * (∑' e : Finset ℕ, normalizationWeightMass q h e)) := by
  rw [weightedActiveRatioSum_expansion q h lambda]
  have hnorm := infiniteNormalizationWeightMass q h
  calc
    cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) - N =
      cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) -
        N * (cStarReal q h *
          (∑' e : Finset ℕ, normalizationWeightMass q h e)) := by
            rw [hnorm]
            ring
    _ = cStarReal q h *
        ((∑' e : Finset ℕ,
          ∑ y ∈ Finset.Ioo 0 h,
            lambda y * perYWeightMass q h y e) -
          N * (∑' e : Finset ℕ, normalizationWeightMass q h e)) := by
            ring


theorem normalizationWeightMass_eq_prod_correction
    (q h : ℕ) (e : Finset ℕ) :
    normalizationWeightMass q h e =
      ∏ p ∈ e, normalizationCorrection q h p := by
  unfold normalizationWeightMass
  rw [prod_normalizationCorrection_partition q h e]
  apply Finset.sum_congr rfl
  intro e1 he1
  rw [prod_normalizationLeft_eq q h e1]
  rw [prod_normalizationRight_eq q h (e \ e1)]

theorem summable_normalizationWeightMass
    (q h : ℕ) :
    Summable (normalizationWeightMass q h) := by
  have hs :
      Summable (fun e : Finset ℕ =>
        ∏ p ∈ e, normalizationCorrection q h p) :=
    summable_finsetProd_of_summable_norm
      (summable_norm_normalizationCorrection q h)
  exact hs.congr (fun e =>
    (normalizationWeightMass_eq_prod_correction q h e).symm)

noncomputable def weightedPerEMass
    (q h : ℕ) (lambda : ℕ → ℝ) (e : Finset ℕ) : ℝ :=
  ∑ y ∈ Finset.Ioo 0 h,
    lambda y * perYWeightMass q h y e

theorem summable_weightedPerEMass
    (q h : ℕ) (lambda : ℕ → ℝ) :
    Summable (weightedPerEMass q h lambda) := by
  classical
  have aux :
      ∀ s : Finset ℕ, s ⊆ Finset.Ioo 0 h →
        Summable (fun e : Finset ℕ =>
          ∑ y ∈ s, lambda y * perYWeightMass q h y e) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert y s hy ih =>
        have hyI : y ∈ Finset.Ioo 0 h :=
          hs (Finset.mem_insert_self y s)
        have hsI : s ⊆ Finset.Ioo 0 h := by
          intro z hz
          exact hs (Finset.mem_insert_of_mem hz)
        have hyBounds := Finset.mem_Ioo.mp hyI
        have hySum :
            Summable (fun e : Finset ℕ =>
              lambda y * perYWeightMass q h y e) :=
          Summable.mul_left (lambda y)
            (summable_perYWeightMass q h y hyBounds.1 hyBounds.2)
        have hsSum := ih hsI
        simpa [Finset.sum_insert hy] using hySum.add hsSum
  unfold weightedPerEMass
  exact aux (Finset.Ioo 0 h) (by intro x hx; exact hx)

noncomputable def centeredWeightMass
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ)
    (e : Finset ℕ) : ℝ :=
  weightedPerEMass q h lambda e -
    N * normalizationWeightMass q h e

theorem summable_centeredWeightMass
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ) :
    Summable (centeredWeightMass q h lambda N) := by
  have ha := summable_weightedPerEMass q h lambda
  have hb :
      Summable (fun e : Finset ℕ =>
        N * normalizationWeightMass q h e) :=
    Summable.mul_left N (summable_normalizationWeightMass q h)
  exact (ha.add hb.neg).congr (fun e => by
    simp [centeredWeightMass]
    ring)

theorem tsum_centeredWeightMass_eq
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ) :
    (∑' e : Finset ℕ, centeredWeightMass q h lambda N e) =
      (∑' e : Finset ℕ, weightedPerEMass q h lambda e) -
        N * (∑' e : Finset ℕ, normalizationWeightMass q h e) := by
  have ha := summable_weightedPerEMass q h lambda
  have hb :
      Summable (fun e : Finset ℕ =>
        N * normalizationWeightMass q h e) :=
    Summable.mul_left N (summable_normalizationWeightMass q h)
  have hneg := hb.neg
  calc
    (∑' e : Finset ℕ, centeredWeightMass q h lambda N e) =
        ∑' e : Finset ℕ,
          (weightedPerEMass q h lambda e +
            -(N * normalizationWeightMass q h e)) := by
              apply tsum_congr
              intro e
              simp [centeredWeightMass]
              ring
    _ = (∑' e : Finset ℕ, weightedPerEMass q h lambda e) +
        (∑' e : Finset ℕ,
          -(N * normalizationWeightMass q h e)) := by
            exact ha.tsum_add hneg
    _ = (∑' e : Finset ℕ, weightedPerEMass q h lambda e) -
        N * (∑' e : Finset ℕ, normalizationWeightMass q h e) := by
            rw [tsum_neg, tsum_mul_left]
            ring

theorem weightedActiveRatioSum_centeredWeightMass
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ) :
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∏' p : ℕ, activeHighLocalRatio q h y p)) - N =
      cStarReal q h *
        (∑' e : Finset ℕ, centeredWeightMass q h lambda N e) := by
  rw [weightedActiveRatioSum_sub_exactCount q h lambda N]
  change
    cStarReal q h *
        ((∑' e : Finset ℕ, weightedPerEMass q h lambda e) -
          N * (∑' e : Finset ℕ, normalizationWeightMass q h e)) =
      cStarReal q h *
        (∑' e : Finset ℕ, centeredWeightMass q h lambda N e)
  rw [← tsum_centeredWeightMass_eq q h lambda N]


def leftActiveSupport (q : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, activeHighPrime q p

def rightActiveSupport (q h : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, activeHighPrime q p ∧ ¬ p ∣ h

def leftDivisibility (y : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, p ∣ y

def rightDivisibility (h y : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, p ∣ h - y

instance leftActiveSupportDecidable (q : ℕ) (s : Finset ℕ) :
    Decidable (leftActiveSupport q s) := by
  unfold leftActiveSupport
  infer_instance

instance rightActiveSupportDecidable (q h : ℕ) (s : Finset ℕ) :
    Decidable (rightActiveSupport q h s) := by
  unfold rightActiveSupport
  infer_instance

instance leftDivisibilityDecidable (y : ℕ) (s : Finset ℕ) :
    Decidable (leftDivisibility y s) := by
  unfold leftDivisibility
  infer_instance

instance rightDivisibilityDecidable (h y : ℕ) (s : Finset ℕ) :
    Decidable (rightDivisibility h y s) := by
  unfold rightDivisibility
  infer_instance

noncomputable def pairCoefficient
    (q h : ℕ) (e e1 : Finset ℕ) : ℝ :=
  (if (∀ p ∈ e1, activeHighPrime q p) then
      finiteVWeightReal h e1
    else 0) *
    (if (∀ p ∈ e \ e1, activeHighPrime q p ∧ ¬ p ∣ h) then
        finiteOmegaWeightReal (e \ e1)
      else 0)

noncomputable def pairDenominator
    (e e1 : Finset ℕ) : ℝ :=
  (∏ p ∈ e1, (p : ℝ)) * (∏ p ∈ e \ e1, (p : ℝ))

noncomputable def pairCount
    (q h : ℕ) (lambda : ℕ → ℝ) (e e1 : Finset ℕ) : ℝ :=
  ∑ y ∈ Finset.Ioo 0 h,
    if (∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) ∧
        (∀ p ∈ e \ e1,
          activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y)
    then lambda y
    else 0

noncomputable def pairDelta
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ)
    (e e1 : Finset ℕ) : ℝ :=
  pairCount q h lambda e e1 - N / pairDenominator e e1

theorem weightedPerEMass_eq_pairCountSum
    (q h : ℕ) (lambda : ℕ → ℝ) (e : Finset ℕ) :
    weightedPerEMass q h lambda e =
      ∑ e1 ∈ e.powerset,
        pairCoefficient q h e e1 *
          pairCount q h lambda e e1 := by
  classical
  unfold weightedPerEMass perYWeightMass pairCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e1 he1
  apply Finset.sum_congr rfl
  intro y hy
  unfold pairCoefficient
  by_cases hLY :
      ∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y
  · by_cases hRY :
        ∀ p ∈ e \ e1,
          activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y
    · have hLS : ∀ p ∈ e1, activeHighPrime q p := by
        intro p hp
        exact (hLY p hp).1
      have hRS :
          ∀ p ∈ e \ e1, activeHighPrime q p ∧ ¬ p ∣ h := by
        intro p hp
        exact ⟨(hRY p hp).1, (hRY p hp).2.1⟩
      have hBoth :
          (∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) ∧
            (∀ p ∈ e \ e1,
              activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y) :=
        ⟨hLY, hRY⟩
      simp only [if_pos hLY, if_pos hRY, if_pos hLS, if_pos hRS,
        if_pos hBoth]
      ring
    · have hNotBoth :
          ¬ ((∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) ∧
            (∀ p ∈ e \ e1,
              activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y)) := by
        intro hb
        exact hRY hb.2
      simp only [if_pos hLY, if_neg hRY, if_neg hNotBoth,
        mul_zero]
  · have hNotBoth :
        ¬ ((∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) ∧
          (∀ p ∈ e \ e1,
            activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y)) := by
      intro hb
      exact hLY hb.1
    simp only [if_neg hLY, if_neg hNotBoth, zero_mul, mul_zero]

theorem normalizationWeightMass_eq_pairBaselineSum
    (q h : ℕ) (e : Finset ℕ) :
    normalizationWeightMass q h e =
      ∑ e1 ∈ e.powerset,
        pairCoefficient q h e e1 / pairDenominator e e1 := by
  classical
  unfold normalizationWeightMass pairCoefficient pairDenominator
  apply Finset.sum_congr rfl
  intro e1 he1
  by_cases hL : ∀ p ∈ e1, activeHighPrime q p
  · by_cases hR :
        ∀ p ∈ e \ e1, activeHighPrime q p ∧ ¬ p ∣ h
    · simp only [if_pos hL, if_pos hR]
      rw [div_eq_mul_inv]
      ring
    · simp only [if_pos hL, if_neg hR, mul_zero, zero_div]
  · simp only [if_neg hL, zero_mul, zero_div]

theorem centeredWeightMass_eq_pairDeltaSum
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ)
    (e : Finset ℕ) :
    centeredWeightMass q h lambda N e =
      ∑ e1 ∈ e.powerset,
        pairCoefficient q h e e1 *
          pairDelta q h lambda N e e1 := by
  rw [centeredWeightMass]
  rw [weightedPerEMass_eq_pairCountSum q h lambda e]
  rw [normalizationWeightMass_eq_pairBaselineSum q h e]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e1 he1
  unfold pairDelta
  ring

theorem weightedActiveRatioSum_pairDelta
    (q h : ℕ) (lambda : ℕ → ℝ) (N : ℝ) :
    (∑ y ∈ Finset.Ioo 0 h,
        lambda y * (∏' p : ℕ, activeHighLocalRatio q h y p)) - N =
      cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ e1 ∈ e.powerset,
            pairCoefficient q h e e1 *
              pairDelta q h lambda N e e1) := by
  rw [weightedActiveRatioSum_centeredWeightMass q h lambda N]
  apply congrArg (fun z : ℝ => cStarReal q h * z)
  apply tsum_congr
  intro e
  exact centeredWeightMass_eq_pairDeltaSum q h lambda N e

def lowPrimeSet : Finset ℕ := {2, 3}

noncomputable def lowPrimeLocalRatio
    (p h y : ℕ) : ℝ :=
  ((highPrimeLocalRatio p h y : ℚ) : ℝ)

noncomputable def fixedQLowWeight
    (q a h y : ℕ) : ℝ :=
  (if q.Coprime (a + y) then 1 else 0) *
    ∏ p ∈ lowPrimeSet,
      if p ∣ q then 1 else lowPrimeLocalRatio p h y

noncomputable def fixedQLevelOneKernel
    (q a h : ℕ) : ℝ :=
  (∑ y ∈ Finset.Ioo 0 h,
      fixedQLowWeight q a h y *
        (∏' p : ℕ, activeHighLocalRatio q h y p)) -
    (admissibleInteriorCount q a h : ℝ)

/-- Frozen-paper prop:divisor-expansion / eq:Tq-expansion, with the
infinite divisor family represented canonically by disjoint finite sets of
active high primes. e1 represents the left divisor and e \\ e1 the right
divisor. The natural-number divisor reindex and the identification of
fixedQLowWeight * activeHighLocalRatio with the literal restricted
singular-series ratio are source-correspondence obligations downstream; the
Euler expansion and exact density centering are fully proved here. -/
theorem fixedQLevelOneKernel_divisorExpansion
    (q a h : ℕ) :
    fixedQLevelOneKernel q a h =
      cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ e1 ∈ e.powerset,
            pairCoefficient q h e e1 *
              pairDelta q h (fixedQLowWeight q a h)
                (admissibleInteriorCount q a h : ℝ) e e1) := by
  unfold fixedQLevelOneKernel
  exact weightedActiveRatioSum_pairDelta
    q h (fixedQLowWeight q a h)
      (admissibleInteriorCount q a h : ℝ)

def endpointResidueCount (p h : ℕ) : ℕ :=
  if p ∣ h then 1 else 2

def tripleResidueCount (p h y : ℕ) : ℕ :=
  if p ∣ h then
    if p ∣ y then 1 else 2
  else
    if p ∣ y then 2
    else if p ∣ h - y then 2 else 3

noncomputable def anchoredLocalFactorRatio (p h y : ℕ) : ℝ :=
  ((1 - (tripleResidueCount p h y : ℝ) / (p : ℝ)) /
      (1 - (endpointResidueCount p h : ℝ) / (p : ℝ))) /
    (1 - 1 / (p : ℝ))

theorem anchoredLocalFactorRatio_eq_highPrimeLocalRatio
    {p h y : ℕ} (hp : 5 ≤ p) :
    anchoredLocalFactorRatio p h y =
      ((highPrimeLocalRatio p h y : ℚ) : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
  have hp2 : (p : ℝ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 2 by omega))
  have hp3 : (p : ℝ) - 3 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 3 by omega))
  by_cases hph : p ∣ h
  · by_cases hpy : p ∣ y
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, hph, hpy]
      field_simp [hp0, hp1]
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, c1, hph, hpy]
      field_simp [hp0, hp1, hp2]
  · by_cases hpy : p ∣ y
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, hph, hpy]
      field_simp [hp0, hp1, hp2]
    · by_cases hphy : p ∣ h - y
      · simp [anchoredLocalFactorRatio, endpointResidueCount,
          tripleResidueCount, highPrimeLocalRatio, hph, hpy, hphy]
        field_simp [hp0, hp1, hp2]
      · simp [anchoredLocalFactorRatio, endpointResidueCount,
          tripleResidueCount, highPrimeLocalRatio, c0, hph, hpy, hphy]
        field_simp [hp0, hp1, hp2, hp3]

theorem card_pair_zero_of_ne_zero {a : ℕ} (ha : a ≠ 0) :
    ({0, a} : Finset ℕ).card = 2 := by
  exact Finset.card_pair ha.symm

theorem card_triple_zero_of_pairwise_ne
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ({0, a, b} : Finset ℕ).card = 3 := by
  have h0 : 0 ∉ ({a, b} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ha.symm, hb.symm⟩
  rw [Finset.card_insert_of_notMem h0]
  rw [Finset.card_pair hab]

def endpointOccupiedCount (p h : ℕ) : ℕ :=
  ({0 % p, h % p} : Finset ℕ).card

def tripleOccupiedCount (p h y : ℕ) : ℕ :=
  ({0 % p, y % p, h % p} : Finset ℕ).card

theorem endpointOccupiedCount_eq
    (p h : ℕ) :
    endpointOccupiedCount p h = endpointResidueCount p h := by
  unfold endpointOccupiedCount endpointResidueCount
  by_cases hph : p ∣ h
  · have hz : h % p = 0 := Nat.mod_eq_zero_of_dvd hph
    simp [hph, hz]
  · have hnz : h % p ≠ 0 := by
      exact (Nat.dvd_iff_mod_eq_zero.not.mp hph)
    rw [if_neg hph]
    simpa using card_pair_zero_of_ne_zero hnz

theorem tripleOccupiedCount_eq
    {p h y : ℕ} (hy : y ≤ h) :
    tripleOccupiedCount p h y = tripleResidueCount p h y := by
  unfold tripleOccupiedCount tripleResidueCount
  by_cases hph : p ∣ h
  · have hh0 : h % p = 0 := Nat.mod_eq_zero_of_dvd hph
    by_cases hpy : p ∣ y
    · have hy0 : y % p = 0 := Nat.mod_eq_zero_of_dvd hpy
      simp [hph, hpy, hh0, hy0]
    · have hynz : y % p ≠ 0 :=
        Nat.dvd_iff_mod_eq_zero.not.mp hpy
      simp [hph, hpy, hh0, hynz]
  · have hhnz : h % p ≠ 0 :=
      Nat.dvd_iff_mod_eq_zero.not.mp hph
    by_cases hpy : p ∣ y
    · have hy0 : y % p = 0 := Nat.mod_eq_zero_of_dvd hpy
      rw [if_neg hph, if_pos hpy]
      rw [hy0]
      simpa using card_pair_zero_of_ne_zero hhnz
    · have hynz : y % p ≠ 0 :=
        Nat.dvd_iff_mod_eq_zero.not.mp hpy
      by_cases hphy : p ∣ h - y
      · have hmod : y ≡ h [MOD p] :=
          (Nat.modEq_iff_dvd' hy).2 hphy
        change y % p = h % p at hmod
        rw [if_neg hph, if_neg hpy, if_pos hphy]
        rw [hmod]
        simpa using card_pair_zero_of_ne_zero hhnz
      · have hnotmod : ¬ y ≡ h [MOD p] := by
          exact (Nat.modEq_iff_dvd' hy).not.mpr hphy
        change y % p ≠ h % p at hnotmod
        rw [if_neg hph, if_neg hpy, if_neg hphy]
        simpa using
          card_triple_zero_of_pairwise_ne hynz hhnz hnotmod

noncomputable def occupiedAnchoredLocalFactorRatio
    (p h y : ℕ) : ℝ :=
  ((1 - (tripleOccupiedCount p h y : ℝ) / (p : ℝ)) /
      (1 - (endpointOccupiedCount p h : ℝ) / (p : ℝ))) /
    (1 - 1 / (p : ℝ))

theorem occupiedAnchoredLocalFactorRatio_eq_highPrimeLocalRatio
    {p h y : ℕ} (hp : 5 ≤ p) (hy : y ≤ h) :
    occupiedAnchoredLocalFactorRatio p h y =
      ((highPrimeLocalRatio p h y : ℚ) : ℝ) := by
  rw [occupiedAnchoredLocalFactorRatio, tripleOccupiedCount_eq hy,
    endpointOccupiedCount_eq]
  exact anchoredLocalFactorRatio_eq_highPrimeLocalRatio hp

theorem anchoredLocalFactorRatio_two
    {h y : ℕ} (h2 : 2 ∣ h) :
    anchoredLocalFactorRatio 2 h y =
      ((highPrimeLocalRatio 2 h y : ℚ) : ℝ) := by
  by_cases h2y : 2 ∣ y
  · simp [anchoredLocalFactorRatio, endpointResidueCount,
      tripleResidueCount, highPrimeLocalRatio, h2, h2y]
    norm_num
  · simp [anchoredLocalFactorRatio, endpointResidueCount,
      tripleResidueCount, highPrimeLocalRatio, c1, h2, h2y]

theorem anchoredLocalFactorRatio_three
    (h y : ℕ) :
    anchoredLocalFactorRatio 3 h y =
      ((highPrimeLocalRatio 3 h y : ℚ) : ℝ) := by
  by_cases h3 : 3 ∣ h
  · by_cases h3y : 3 ∣ y
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, h3, h3y]
      norm_num
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, c1, h3, h3y]
      norm_num
  · by_cases h3y : 3 ∣ y
    · simp [anchoredLocalFactorRatio, endpointResidueCount,
        tripleResidueCount, highPrimeLocalRatio, h3, h3y]
      norm_num
    · by_cases h3hy : 3 ∣ h - y
      · simp [anchoredLocalFactorRatio, endpointResidueCount,
          tripleResidueCount, highPrimeLocalRatio, h3, h3y, h3hy]
        norm_num
      · simp [anchoredLocalFactorRatio, endpointResidueCount,
          tripleResidueCount, highPrimeLocalRatio, c0, h3, h3y, h3hy]

theorem occupiedAnchoredLocalFactorRatio_two
    {h y : ℕ} (h2 : 2 ∣ h) (hy : y ≤ h) :
    occupiedAnchoredLocalFactorRatio 2 h y =
      ((highPrimeLocalRatio 2 h y : ℚ) : ℝ) := by
  rw [occupiedAnchoredLocalFactorRatio, tripleOccupiedCount_eq hy,
    endpointOccupiedCount_eq]
  exact anchoredLocalFactorRatio_two h2

theorem occupiedAnchoredLocalFactorRatio_three
    {h y : ℕ} (hy : y ≤ h) :
    occupiedAnchoredLocalFactorRatio 3 h y =
      ((highPrimeLocalRatio 3 h y : ℚ) : ℝ) := by
  rw [occupiedAnchoredLocalFactorRatio, tripleOccupiedCount_eq hy,
    endpointOccupiedCount_eq]
  exact anchoredLocalFactorRatio_three h y

noncomputable def occupiedFixedQLowWeight
    (q a h y : ℕ) : ℝ :=
  (if q.Coprime (a + y) then 1 else 0) *
    ∏ p ∈ lowPrimeSet,
      if p ∣ q then 1 else occupiedAnchoredLocalFactorRatio p h y

theorem fixedQLowWeight_eq_occupied
    {q a h y : ℕ} (hy : y ≤ h)
    (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    fixedQLowWeight q a h y =
      occupiedFixedQLowWeight q a h y := by
  unfold fixedQLowWeight occupiedFixedQLowWeight lowPrimeLocalRatio
  apply congrArg (fun z : ℝ =>
    (if q.Coprime (a + y) then 1 else 0) * z)
  unfold lowPrimeSet
  norm_num [Finset.prod_insert]
  by_cases h2q : 2 ∣ q
  · simp [h2q]
    by_cases h3q : 3 ∣ q
    · simp [h3q]
    · simp [h3q, occupiedAnchoredLocalFactorRatio_three hy]
  · have h2h : 2 ∣ h := h2admissible h2q
    simp [h2q, occupiedAnchoredLocalFactorRatio_two h2h hy]
    by_cases h3q : 3 ∣ q
    · simp [h3q]
    · simp [h3q, occupiedAnchoredLocalFactorRatio_three hy]

noncomputable def occupiedActiveHighLocalRatio
    (q h y p : ℕ) : ℝ :=
  if activeHighPrime q p then
    occupiedAnchoredLocalFactorRatio p h y
  else 1

theorem occupiedActiveHighLocalRatio_eq
    {q h y p : ℕ} (hy : y ≤ h) :
    occupiedActiveHighLocalRatio q h y p =
      activeHighLocalRatio q h y p := by
  unfold occupiedActiveHighLocalRatio activeHighLocalRatio
  by_cases ha : activeHighPrime q p
  · have hp5 : 5 ≤ p := ha.2.1
    rw [if_pos ha, if_pos ha]
    exact occupiedAnchoredLocalFactorRatio_eq_highPrimeLocalRatio hp5 hy
  · simp [ha]

theorem tprod_occupiedActiveHighLocalRatio_eq
    {q h y : ℕ} (hy : y ≤ h) :
    (∏' p : ℕ, occupiedActiveHighLocalRatio q h y p) =
      ∏' p : ℕ, activeHighLocalRatio q h y p := by
  apply tprod_congr
  intro p
  exact occupiedActiveHighLocalRatio_eq hy

noncomputable def occupiedFixedQLevelOneKernel
    (q a h : ℕ) : ℝ :=
  (∑ y ∈ Finset.Ioo 0 h,
      occupiedFixedQLowWeight q a h y *
        (∏' p : ℕ, occupiedActiveHighLocalRatio q h y p)) -
    (admissibleInteriorCount q a h : ℝ)

theorem fixedQLevelOneKernel_eq_occupied
    {q a h : ℕ} (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    fixedQLevelOneKernel q a h =
      occupiedFixedQLevelOneKernel q a h := by
  unfold fixedQLevelOneKernel occupiedFixedQLevelOneKernel
  apply congrArg (fun z : ℝ => z - (admissibleInteriorCount q a h : ℝ))
  apply Finset.sum_congr rfl
  intro y hy
  have hyI := Finset.mem_Ioo.mp hy
  rw [fixedQLowWeight_eq_occupied (Nat.le_of_lt hyI.2) h2admissible]
  rw [tprod_occupiedActiveHighLocalRatio_eq (Nat.le_of_lt hyI.2)]

theorem pairCount_fixedQLow_eq_occupied
    {q a h : ℕ} (h2admissible : ¬ 2 ∣ q → 2 ∣ h)
    (e e1 : Finset ℕ) :
    pairCount q h (fixedQLowWeight q a h) e e1 =
      pairCount q h (occupiedFixedQLowWeight q a h) e e1 := by
  unfold pairCount
  apply Finset.sum_congr rfl
  intro y hy
  have hyI := Finset.mem_Ioo.mp hy
  have hw := fixedQLowWeight_eq_occupied
    (q := q) (a := a) (h := h) (y := y)
    (Nat.le_of_lt hyI.2) h2admissible
  by_cases hc :
      (∀ p ∈ e1, activeHighPrime q p ∧ p ∣ y) ∧
        (∀ p ∈ e \ e1,
          activeHighPrime q p ∧ ¬ p ∣ h ∧ p ∣ h - y)
  · rw [if_pos hc, if_pos hc, hw]
  · rw [if_neg hc, if_neg hc]

theorem pairDelta_fixedQLow_eq_occupied
    {q a h : ℕ} (h2admissible : ¬ 2 ∣ q → 2 ∣ h)
    (e e1 : Finset ℕ) :
    pairDelta q h (fixedQLowWeight q a h)
        (admissibleInteriorCount q a h : ℝ) e e1 =
      pairDelta q h (occupiedFixedQLowWeight q a h)
        (admissibleInteriorCount q a h : ℝ) e e1 := by
  unfold pairDelta
  rw [pairCount_fixedQLow_eq_occupied h2admissible e e1]

theorem occupiedFixedQLevelOneKernel_divisorExpansion
    {q a h : ℕ} (h2admissible : ¬ 2 ∣ q → 2 ∣ h) :
    occupiedFixedQLevelOneKernel q a h =
      cStarReal q h *
        (∑' e : Finset ℕ,
          ∑ e1 ∈ e.powerset,
            pairCoefficient q h e e1 *
              pairDelta q h (occupiedFixedQLowWeight q a h)
                (admissibleInteriorCount q a h : ℝ) e e1) := by
  rw [← fixedQLevelOneKernel_eq_occupied h2admissible]
  rw [fixedQLevelOneKernel_divisorExpansion q a h]
  apply congrArg (fun z : ℝ => cStarReal q h * z)
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro e1 he1
  rw [pairDelta_fixedQLow_eq_occupied h2admissible e e1]

end RML.Fourier.Vaaler.Internal
