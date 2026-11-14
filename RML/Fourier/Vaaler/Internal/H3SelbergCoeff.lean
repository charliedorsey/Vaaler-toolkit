module

public import RML.Fourier.Vaaler.Internal.H3VaalerCoeff
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace RML.Fourier.Vaaler.Internal

/-- Fejer coefficient at degree J, specialized to the H3 endpoint correction. -/
noncomputable def h3FejerCoeff (J : ℕ) (n : ℤ) : ℝ :=
  if n.natAbs ≤ J then
    1 - (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
  else 0

lemma h3FejerCoeff_nonneg (J : ℕ) (n : ℤ) :
    0 ≤ h3FejerCoeff J n := by
  unfold h3FejerCoeff
  by_cases h : n.natAbs ≤ J
  · rw [if_pos h]
    have hden : (0 : ℝ) < (J + 1 : ℕ) := by positivity
    rw [sub_nonneg, div_le_one hden]
    exact_mod_cast Nat.le_succ_of_le h
  · simp [h]

lemma h3FejerCoeff_le_one (J : ℕ) (n : ℤ) :
    h3FejerCoeff J n ≤ 1 := by
  unfold h3FejerCoeff
  by_cases h : n.natAbs ≤ J
  · rw [if_pos h]
    have hnonneg : 0 ≤ (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ)) := by positivity
    linarith
  · simp [h]

lemma h3FejerCoeff_eq_zero_of_band_lt {J : ℕ} {n : ℤ}
    (h : J < n.natAbs) :
    h3FejerCoeff J n = 0 := by
  simp [h3FejerCoeff, not_le.mpr h]

noncomputable def h3EndpointPhase
    (N r : ℕ) [NeZero N] (n : ℤ) : ℂ :=
  ZMod.stdAddChar (-(n : ZMod N) * (r : ZMod N))

lemma norm_h3EndpointPhase
    (N r : ℕ) [NeZero N] (n : ℤ) :
    ‖h3EndpointPhase N r n‖ = 1 := by
  exact norm_stdAddChar_eq_one N _

noncomputable def h3IntervalUpperCoeff
    (N r J : ℕ) [NeZero N] (n : ℤ) : ℂ :=
  if n = 0 then
    (((r : ℝ) / (N : ℝ) + 1 / (((J + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
  else
    h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1) +
      (((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
        (h3EndpointPhase N r n + 1))

@[simp] lemma h3IntervalUpperCoeff_zero
    (N r J : ℕ) [NeZero N] :
    h3IntervalUpperCoeff N r J 0 =
      (((r : ℝ) / (N : ℝ) + 1 / (((J + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  simp [h3IntervalUpperCoeff]

lemma h3IntervalUpperCoeff_eq_zero_of_band_lt
    {N r J : ℕ} [NeZero N] {n : ℤ}
    (h : J < n.natAbs) :
    h3IntervalUpperCoeff N r J n = 0 := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at h
  simp [h3IntervalUpperCoeff, hn,
    h3VaalerSawCoeff_eq_zero_of_band_lt h,
    h3FejerCoeff_eq_zero_of_band_lt h]

lemma norm_h3IntervalUpperCoeff_le
    {N r J : ℕ} [NeZero N] {n : ℤ}
    (hn : n ≠ 0) (hband : n.natAbs ≤ J) :
    ‖h3IntervalUpperCoeff N r J n‖ ≤ 2 / (n.natAbs : ℝ) := by
  rw [h3IntervalUpperCoeff, if_neg hn]
  have hphase_sub :
      ‖h3EndpointPhase N r n - 1‖ ≤ 2 := by
    calc
      ‖h3EndpointPhase N r n - 1‖
          ≤ ‖h3EndpointPhase N r n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_h3EndpointPhase]; norm_num
  have hphase_add :
      ‖h3EndpointPhase N r n + 1‖ ≤ 2 := by
    calc
      ‖h3EndpointPhase N r n + 1‖
          ≤ ‖h3EndpointPhase N r n‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_h3EndpointPhase]; norm_num
  have hsaw := norm_h3VaalerSawCoeff_le J hn
  have hf0 := h3FejerCoeff_nonneg J n
  have hf1 := h3FejerCoeff_le_one J n
  have hdpos : 0 < (n.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hn
  have hdJ : (n.natAbs : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ_of_le hband
  have hinvJ : 1 / (((J + 1 : ℕ) : ℝ)) ≤ 1 / (n.natAbs : ℝ) := by
    exact one_div_le_one_div_of_le hdpos hdJ
  calc
    ‖h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1) +
        (((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
          (h3EndpointPhase N r n + 1))‖
      ≤ ‖h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1)‖ +
        ‖(((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
          (h3EndpointPhase N r n + 1))‖ := norm_add_le _ _
    _ ≤ (1 / (2 * Real.pi * (n.natAbs : ℝ))) * 2 +
        (1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n) * 2 := by
      rw [norm_mul, norm_mul]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) hf0)]
      gcongr
    _ ≤ (1 / (n.natAbs : ℝ)) + 1 / (((J + 1 : ℕ) : ℝ)) := by
      have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hdenle : (n.natAbs : ℝ) ≤ Real.pi * (n.natAbs : ℝ) := by
        nlinarith
      have hA0 :
          1 / (Real.pi * (n.natAbs : ℝ)) ≤ 1 / (n.natAbs : ℝ) :=
        one_div_le_one_div_of_le hdpos hdenle
      have hA :
          (1 / (2 * Real.pi * (n.natAbs : ℝ))) * 2 ≤
            1 / (n.natAbs : ℝ) := by
        convert hA0 using 1 <;> ring
      have hden : 0 ≤ 1 / (((J + 1 : ℕ) : ℝ)) := by positivity
      have hB0 :
          (1 / (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n ≤
            1 / (((J + 1 : ℕ) : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_left hf1 hden
      have hB :
          (1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n) * 2 ≤
            1 / (((J + 1 : ℕ) : ℝ)) := by
        convert hB0 using 1 <;> ring
      exact add_le_add hA hB
    _ ≤ 2 / (n.natAbs : ℝ) := by
      have h := add_le_add_left hinvJ (1 / (n.natAbs : ℝ))
      convert h using 1 <;> ring

#print axioms norm_h3IntervalUpperCoeff_le
end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

noncomputable def h3IntervalLowerCoeff
    (N r J : ℕ) [NeZero N] (n : ℤ) : ℂ :=
  if n = 0 then
    (((r : ℝ) / (N : ℝ) - 1 / (((J + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
  else
    h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1) -
      (((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
        (h3EndpointPhase N r n + 1))

@[simp] lemma h3IntervalLowerCoeff_zero
    (N r J : ℕ) [NeZero N] :
    h3IntervalLowerCoeff N r J 0 =
      (((r : ℝ) / (N : ℝ) - 1 / (((J + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  simp [h3IntervalLowerCoeff]

lemma h3IntervalLowerCoeff_eq_zero_of_band_lt
    {N r J : ℕ} [NeZero N] {n : ℤ}
    (h : J < n.natAbs) :
    h3IntervalLowerCoeff N r J n = 0 := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at h
  simp [h3IntervalLowerCoeff, hn,
    h3VaalerSawCoeff_eq_zero_of_band_lt h,
    h3FejerCoeff_eq_zero_of_band_lt h]

lemma norm_h3IntervalLowerCoeff_le
    {N r J : ℕ} [NeZero N] {n : ℤ}
    (hn : n ≠ 0) (hband : n.natAbs ≤ J) :
    ‖h3IntervalLowerCoeff N r J n‖ ≤ 2 / (n.natAbs : ℝ) := by
  rw [h3IntervalLowerCoeff, if_neg hn]
  have hphase_sub :
      ‖h3EndpointPhase N r n - 1‖ ≤ 2 := by
    calc
      ‖h3EndpointPhase N r n - 1‖
          ≤ ‖h3EndpointPhase N r n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_h3EndpointPhase]; norm_num
  have hphase_add :
      ‖h3EndpointPhase N r n + 1‖ ≤ 2 := by
    calc
      ‖h3EndpointPhase N r n + 1‖
          ≤ ‖h3EndpointPhase N r n‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_h3EndpointPhase]; norm_num
  have hsaw := norm_h3VaalerSawCoeff_le J hn
  have hf0 := h3FejerCoeff_nonneg J n
  have hf1 := h3FejerCoeff_le_one J n
  have hdpos : 0 < (n.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hn
  have hdJ : (n.natAbs : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ_of_le hband
  have hinvJ : 1 / (((J + 1 : ℕ) : ℝ)) ≤ 1 / (n.natAbs : ℝ) :=
    one_div_le_one_div_of_le hdpos hdJ
  have htermA :
      ‖h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1)‖ ≤
        (1 / (2 * Real.pi * (n.natAbs : ℝ))) * 2 := by
    rw [norm_mul]
    exact mul_le_mul hsaw hphase_sub (norm_nonneg _) (by positivity)
  have htermB :
      ‖(((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
        (h3EndpointPhase N r n + 1))‖ ≤
        (1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n) * 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) hf0)]
    exact mul_le_mul_of_nonneg_left hphase_add
      (mul_nonneg (by positivity) hf0)
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hdenle : (n.natAbs : ℝ) ≤ Real.pi * (n.natAbs : ℝ) := by
    nlinarith
  have hA0 :
      1 / (Real.pi * (n.natAbs : ℝ)) ≤ 1 / (n.natAbs : ℝ) :=
    one_div_le_one_div_of_le hdpos hdenle
  have hA :
      (1 / (2 * Real.pi * (n.natAbs : ℝ))) * 2 ≤
        1 / (n.natAbs : ℝ) := by
    convert hA0 using 1 <;> ring
  have hden : 0 ≤ 1 / (((J + 1 : ℕ) : ℝ)) := by positivity
  have hB0 :
      (1 / (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n ≤
        1 / (((J + 1 : ℕ) : ℝ)) := by
    simpa using mul_le_mul_of_nonneg_left hf1 hden
  have hB :
      (1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n) * 2 ≤
        1 / (((J + 1 : ℕ) : ℝ)) := by
    convert hB0 using 1 <;> ring
  calc
    ‖h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1) -
        (((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
          (h3EndpointPhase N r n + 1))‖
      ≤ ‖h3VaalerSawCoeff J n * (h3EndpointPhase N r n - 1)‖ +
        ‖(((1 / (2 * (((J + 1 : ℕ) : ℝ))) * h3FejerCoeff J n : ℝ) : ℂ) *
          (h3EndpointPhase N r n + 1))‖ := norm_sub_le _ _
    _ ≤ (1 / (n.natAbs : ℝ)) + 1 / (((J + 1 : ℕ) : ℝ)) :=
      add_le_add (htermA.trans hA) (htermB.trans hB)
    _ ≤ 2 / (n.natAbs : ℝ) := by
      have h := add_le_add_left hinvJ (1 / (n.natAbs : ℝ))
      convert h using 1 <;> ring

#print axioms norm_h3IntervalLowerCoeff_le
end RML.Fourier.Vaaler.Internal
