module

public import RML.Fourier.Vaaler.Internal.H3SelbergCoeff

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace RML.Fourier.Vaaler.Internal

noncomputable def h3CenteredSawtooth
    (N : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  if x = 0 then 0 else (x.val : ℝ) / (N : ℝ) - 1 / 2

@[simp] lemma h3CenteredSawtooth_zero
    (N : ℕ) [NeZero N] :
    h3CenteredSawtooth N 0 = 0 := by
  simp [h3CenteredSawtooth]

lemma h3CenteredSawtooth_of_ne_zero
    {N : ℕ} [NeZero N] {x : ZMod N} (hx : x ≠ 0) :
    h3CenteredSawtooth N x =
      (x.val : ℝ) / (N : ℝ) - 1 / 2 := by
  simp [h3CenteredSawtooth, hx]

lemma zmod_val_natCast_of_lt
    {N r : ℕ} [NeZero N] (hr : r < N) :
    (r : ZMod N).val = r := by
  exact ZMod.val_natCast_of_lt hr

lemma zmod_val_sub_natCast_of_le
    {N r : ℕ} [NeZero N] (hrN : r < N)
    {x : ZMod N} (hrx : r ≤ x.val) :
    (x - (r : ZMod N)).val = x.val - r := by
  have h := ZMod.val_sub (a := x) (b := (r : ZMod N)) (by
    simpa [ZMod.val_natCast_of_lt hrN] using hrx)
  rw [ZMod.val_natCast_of_lt hrN] at h
  exact h

lemma zmod_val_sub_natCast_of_lt
    {N r : ℕ} [NeZero N] (hr0 : 0 < r) (hrN : r < N)
    {x : ZMod N} (hxr : x.val < r) :
    (x - (r : ZMod N)).val = N + x.val - r := by
  have hrz : (r : ZMod N) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hrN] at hv
    simp at hv
    omega
  have hneg : (-(r : ZMod N)).val = N - r := by
    rw [ZMod.neg_val, if_neg hrz, ZMod.val_natCast_of_lt hrN]
  rw [sub_eq_add_neg, ZMod.val_add, hneg]
  have hsum_lt : x.val + (N - r) < N := by omega
  rw [Nat.mod_eq_of_lt hsum_lt]
  omega

noncomputable def h3HalfOpenIntervalCentered
    (N r : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (if x.val < r then 1 else 0) - (r : ℝ) / (N : ℝ)

noncomputable def h3EndpointCorrection
    (N r : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (if x = 0 then (1 / 2 : ℝ) else 0) -
    (if x = (r : ZMod N) then (1 / 2 : ℝ) else 0)

lemma h3HalfOpenIntervalCentered_eq_sawtooth_sub
    {N r : ℕ} [NeZero N] (hrN : r < N) (x : ZMod N) :
    h3HalfOpenIntervalCentered N r x =
      h3CenteredSawtooth N (x - (r : ZMod N)) -
        h3CenteredSawtooth N x +
        h3EndpointCorrection N r x := by
  have hNpos : 0 < N := NeZero.pos N
  by_cases hr0 : r = 0
  · subst r
    simp [h3HalfOpenIntervalCentered, h3EndpointCorrection]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  by_cases hx0 : x = 0
  · subst x
    have hrz : (r : ZMod N) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hrN] at hv
      simp at hv
      omega
    have hval : (0 - (r : ZMod N)).val = N - r := by
      rw [zero_sub, ZMod.neg_val, if_neg hrz, ZMod.val_natCast_of_lt hrN]
    have hzero_ne_r : (0 : ZMod N) ≠ (r : ZMod N) := Ne.symm hrz
    have hsubne : (0 : ZMod N) - (r : ZMod N) ≠ 0 :=
      sub_ne_zero.mpr hzero_ne_r
    have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrN)]
    rw [h3HalfOpenIntervalCentered, h3EndpointCorrection,
      h3CenteredSawtooth_of_ne_zero hsubne, h3CenteredSawtooth_zero, hval, hcast]
    simp [hrpos, hzero_ne_r]
    field_simp
  by_cases hxr : x.val < r
  · have hxsub0 : x - (r : ZMod N) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [zmod_val_sub_natCast_of_lt hrpos hrN hxr] at hv
      simp at hv
      omega
    have hxne_r : x ≠ (r : ZMod N) := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hrN] at hv
      omega
    have hcast : ((N + x.val - r : ℕ) : ℝ) =
        (N : ℝ) + (x.val : ℝ) - (r : ℝ) := by
      rw [Nat.cast_sub (by omega : r ≤ N + x.val)]
      push_cast
      ring
    rw [h3HalfOpenIntervalCentered, h3EndpointCorrection]
    simp [hxr, hx0, hxne_r,
      h3CenteredSawtooth_of_ne_zero hxsub0,
      h3CenteredSawtooth_of_ne_zero hx0,
      zmod_val_sub_natCast_of_lt hrpos hrN hxr, hcast]
    field_simp
    ring
  · have hrx : r ≤ x.val := Nat.le_of_not_gt hxr
    by_cases hxeq : x = (r : ZMod N)
    · subst x
      have hrz : (r : ZMod N) ≠ 0 := by
        intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hrN] at hv
        simp at hv
        omega
      rw [h3HalfOpenIntervalCentered, h3EndpointCorrection]
      simp [ZMod.val_natCast_of_lt hrN, hrN, hrz,
        h3CenteredSawtooth_of_ne_zero hrz]
      field_simp
      ring
    · have hxsub0 : x - (r : ZMod N) ≠ 0 := sub_ne_zero.mpr hxeq
      have hcast : ((x.val - r : ℕ) : ℝ) = (x.val : ℝ) - (r : ℝ) := by
        rw [Nat.cast_sub hrx]
      rw [h3HalfOpenIntervalCentered, h3EndpointCorrection]
      simp [hxr, hx0, hxeq,
        h3CenteredSawtooth_of_ne_zero hxsub0,
        h3CenteredSawtooth_of_ne_zero hx0,
        zmod_val_sub_natCast_of_le hrN hrx, hcast]
      field_simp
      ring

#print axioms h3HalfOpenIntervalCentered_eq_sawtooth_sub

/-- Real finite Vaaler sawtooth approximant, specialized to ZMod N. -/
noncomputable def h3VaalerApprox
    (N J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  - ∑ j ∈ Finset.Icc 1 J,
      (h3VaalerJHat J (j : ℤ) /
        (Real.pi * (j : ℝ))) *
        (ZMod.stdAddChar ((j : ZMod N) * x)).im

@[simp] lemma h3VaalerApprox_zero
    (N J : ℕ) [NeZero N] :
    h3VaalerApprox N J 0 = 0 := by
  unfold h3VaalerApprox
  simp

/-- Fejer kernel K_{J+1}, in the normalization used by Vaaler's error term. -/
noncomputable def h3FejerKernel
    (N J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (((J + 1 : ℕ) : ℝ))⁻¹ *
    ‖∑ k ∈ Finset.range (J + 1), (ZMod.stdAddChar x) ^ k‖ ^ 2

noncomputable def h3VaalerError
    (N J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (1 / (2 * (((J + 1 : ℕ) : ℝ)))) * h3FejerKernel N J x

lemma h3FejerKernel_nonneg
    (N J : ℕ) [NeZero N] (x : ZMod N) :
    0 ≤ h3FejerKernel N J x := by
  unfold h3FejerKernel
  positivity

lemma h3VaalerError_nonneg
    (N J : ℕ) [NeZero N] (x : ZMod N) :
    0 ≤ h3VaalerError N J x := by
  unfold h3VaalerError
  exact mul_nonneg (by positivity) (h3FejerKernel_nonneg N J x)

@[simp] lemma h3FejerKernel_zero
    (N J : ℕ) [NeZero N] :
    h3FejerKernel N J 0 = (J + 1 : ℕ) := by
  unfold h3FejerKernel
  have hsum :
      (∑ k ∈ Finset.range (J + 1),
        (ZMod.stdAddChar (0 : ZMod N)) ^ k) = ((J + 1 : ℕ) : ℂ) := by
    simp
  rw [hsum, Complex.norm_natCast]
  have hJ : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hJ]

@[simp] lemma h3VaalerError_zero
    (N J : ℕ) [NeZero N] :
    h3VaalerError N J 0 = 1 / 2 := by
  unfold h3VaalerError
  rw [h3FejerKernel_zero]
  have hJ : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hJ]

noncomputable def h3IntervalUpperCentered
    (N r J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  h3VaalerApprox N J (x - (r : ZMod N)) - h3VaalerApprox N J x +
    h3VaalerError N J (x - (r : ZMod N)) + h3VaalerError N J x

noncomputable def h3IntervalLowerCentered
    (N r J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  h3VaalerApprox N J (x - (r : ZMod N)) - h3VaalerApprox N J x -
    h3VaalerError N J (x - (r : ZMod N)) - h3VaalerError N J x

lemma h3SawDiff_le_approxDiff_add_errors
    {N J : ℕ} [NeZero N]
    (herr : ∀ y : ZMod N,
      |h3VaalerApprox N J y - h3CenteredSawtooth N y| ≤ h3VaalerError N J y)
    (y z : ZMod N) :
    h3CenteredSawtooth N y - h3CenteredSawtooth N z ≤
      h3VaalerApprox N J y - h3VaalerApprox N J z +
        h3VaalerError N J y + h3VaalerError N J z := by
  have hy := abs_le.mp (herr y)
  have hz := abs_le.mp (herr z)
  linarith

lemma h3ApproxDiff_sub_errors_le_sawDiff
    {N J : ℕ} [NeZero N]
    (herr : ∀ y : ZMod N,
      |h3VaalerApprox N J y - h3CenteredSawtooth N y| ≤ h3VaalerError N J y)
    (y z : ZMod N) :
    h3VaalerApprox N J y - h3VaalerApprox N J z -
        h3VaalerError N J y - h3VaalerError N J z ≤
      h3CenteredSawtooth N y - h3CenteredSawtooth N z := by
  have hy := abs_le.mp (herr y)
  have hz := abs_le.mp (herr z)
  linarith

lemma h3IntervalCentered_sandwich_of_error
    {N r J : ℕ} [NeZero N] (hrN : r < N)
    (herr : ∀ y : ZMod N,
      |h3VaalerApprox N J y - h3CenteredSawtooth N y| ≤ h3VaalerError N J y)
    (x : ZMod N) :
    h3IntervalLowerCentered N r J x ≤ h3HalfOpenIntervalCentered N r x ∧
      h3HalfOpenIntervalCentered N r x ≤ h3IntervalUpperCentered N r J x := by
  have hid := h3HalfOpenIntervalCentered_eq_sawtooth_sub hrN x
  have hlow := h3ApproxDiff_sub_errors_le_sawDiff herr
    (x - (r : ZMod N)) x
  have hupp := h3SawDiff_le_approxDiff_add_errors herr
    (x - (r : ZMod N)) x
  rw [hid]
  by_cases hr0 : r = 0
  · subst r
    simpa [h3IntervalLowerCentered, h3IntervalUpperCentered,
      h3EndpointCorrection] using And.intro hlow hupp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hrz : (r : ZMod N) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hrN] at hv
    simp at hv
    omega
  by_cases hx0 : x = 0
  · subst x
    have hzero_ne_r : (0 : ZMod N) ≠ (r : ZMod N) := Ne.symm hrz
    have hcorr : h3EndpointCorrection N r (0 : ZMod N) = 1 / 2 := by
      simp [h3EndpointCorrection, hzero_ne_r]
    constructor
    · rw [hcorr]
      exact hlow.trans (by linarith)
    · have hy := (abs_le.mp (herr ((0 : ZMod N) - (r : ZMod N)))).1
      rw [hcorr]
      have hA0 : h3VaalerApprox N J (0 : ZMod N) = 0 := h3VaalerApprox_zero N J
      have hS0 : h3CenteredSawtooth N (0 : ZMod N) = 0 := h3CenteredSawtooth_zero N
      have hE0 : h3VaalerError N J (0 : ZMod N) = 1 / 2 := h3VaalerError_zero N J
      unfold h3IntervalUpperCentered
      rw [hA0, hS0, hE0]
      linarith
  by_cases hxr : x = (r : ZMod N)
  · subst x
    constructor
    · have hy := (abs_le.mp (herr (r : ZMod N))).1
      simp [h3IntervalLowerCentered, h3EndpointCorrection, hrz] at hy ⊢
      linarith
    · have hcorr : h3EndpointCorrection N r (r : ZMod N) = -(1 / 2) := by
        simp [h3EndpointCorrection, hrz]
      rw [hcorr]
      have hupp' :
          h3CenteredSawtooth N ((r : ZMod N) - (r : ZMod N)) -
              h3CenteredSawtooth N (r : ZMod N) ≤
            h3IntervalUpperCentered N r J (r : ZMod N) := by
        simpa [h3IntervalUpperCentered] using hupp
      linarith
  · have hcorr : h3EndpointCorrection N r x = 0 := by
      simp [h3EndpointCorrection, hx0, hxr]
    rw [hcorr, add_zero]
    exact ⟨hlow, hupp⟩

#print axioms h3IntervalCentered_sandwich_of_error
end RML.Fourier.Vaaler.Internal


namespace RML.Fourier.Vaaler.Internal

/-- The one genuine analytic atom left in the specialized H3 Selberg court. -/
def H3VaalerGridErrorSpec (N J : ℕ) [NeZero N] : Prop :=
  ∀ y : ZMod N,
    |h3VaalerApprox N J y - h3CenteredSawtooth N y| ≤ h3VaalerError N J y

noncomputable def h3HalfOpenIntervalIndicator
    (r : ℕ) {N : ℕ} [NeZero N] (x : ZMod N) : ℝ :=
  if x.val < r then 1 else 0

noncomputable def h3IntervalUpperMajorant
    (N r J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (r : ℝ) / (N : ℝ) + h3IntervalUpperCentered N r J x

noncomputable def h3IntervalLowerMinorant
    (N r J : ℕ) [NeZero N] (x : ZMod N) : ℝ :=
  (r : ℝ) / (N : ℝ) + h3IntervalLowerCentered N r J x

lemma h3HalfOpenIntervalCentered_eq_indicator_sub
    (N r : ℕ) [NeZero N] (x : ZMod N) :
    h3HalfOpenIntervalCentered N r x =
      h3HalfOpenIntervalIndicator r x - (r : ℝ) / (N : ℝ) := by
  rfl

/-- Literal specialized Selberg sandwich, conditional only on the one Vaaler grid atom. -/
theorem fixedProductBooleanRootInterval_selberg_majorant_of_grid_error
    {N r J : ℕ} [NeZero N] (hrN : r < N)
    (hVaaler : H3VaalerGridErrorSpec N J)
    (x : ZMod N) :
    h3IntervalLowerMinorant N r J x ≤ h3HalfOpenIntervalIndicator r x ∧
      h3HalfOpenIntervalIndicator r x ≤ h3IntervalUpperMajorant N r J x := by
  have h := h3IntervalCentered_sandwich_of_error hrN hVaaler x
  rw [h3HalfOpenIntervalCentered_eq_indicator_sub] at h
  unfold h3IntervalLowerMinorant h3IntervalUpperMajorant
  constructor <;> linarith [h.1, h.2]

#print axioms fixedProductBooleanRootInterval_selberg_majorant_of_grid_error
end RML.Fourier.Vaaler.Internal
