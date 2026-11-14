module

public import RML.Fourier.Vaaler.Internal.H3VaalerPointwise
public import RML.Fourier.Vaaler.Internal.H3SelbergMajorant

@[expose] public section

open scoped BigOperators Topology
open Filter Function

namespace RML.Fourier.Vaaler.Internal

noncomputable def h3VaalerSign (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

noncomputable def h3ScaledVaalerError (J : ℕ) (x : ℝ) : ℝ :=
  (((J + 1 : ℕ) : ℝ)) *
    (h3VaalerSign ((((J + 1 : ℕ) : ℝ)) * x) -
      h3VaalerH ((((J + 1 : ℕ) : ℝ)) * x))

noncomputable def h3ScaledVaalerKernel (J : ℕ) (x : ℝ) : ℝ :=
  (((J + 1 : ℕ) : ℝ)) *
    h3VaalerK ((((J + 1 : ℕ) : ℝ)) * x)

lemma h3ScaledVaalerKernel_nonneg (J : ℕ) (x : ℝ) :
    0 ≤ h3ScaledVaalerKernel J x := by
  unfold h3ScaledVaalerKernel
  exact mul_nonneg (by positivity) (h3VaalerK_nonneg _)
theorem h3ScaledVaalerError_abs_le_kernel (J : ℕ) (x : ℝ) :
    |h3ScaledVaalerError J x| ≤ h3ScaledVaalerKernel J x := by
  unfold h3ScaledVaalerError h3ScaledVaalerKernel h3VaalerSign
  rw [abs_mul]
  have hscale : |(((J + 1 : ℕ) : ℝ))| = (((J + 1 : ℕ) : ℝ)) := by
    rw [abs_of_nonneg]
    positivity
  rw [hscale]
  gcongr
  exact h3Vaaler_sign_sub_abs_le_K ((((J + 1 : ℕ) : ℝ)) * x)



lemma h3_sin_scaled_sub_int_sq
    (J : ℕ) (x : ℝ) (n : ℤ) :
    Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * (x - (n : ℝ)))) ^ 2 =
      Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) ^ 2 := by
  let z : ℤ := (((J + 1 : ℕ) : ℤ) * n)
  have harg :
      Real.pi * (((J + 1 : ℕ) : ℝ) * (x - (n : ℝ))) =
        Real.pi * (((J + 1 : ℕ) : ℝ) * x) - (z : ℝ) * Real.pi := by
    dsimp [z]
    push_cast
    ring
  rw [harg, Real.sin_sub_int_mul_pi]
  rw [mul_pow]
  have hsignsq : ((-1 : ℝ) ^ z) ^ 2 = 1 := by
    rw [← sq_abs, abs_neg_one_zpow]
    norm_num
  rw [hsignsq, one_mul]

lemma h3ScaledVaalerKernel_sub_int_eq
    (J : ℕ) {x : ℝ} (n : ℤ)
    (hxn : x ≠ (n : ℝ)) :
    h3ScaledVaalerKernel J (x - (n : ℝ)) =
      ((Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi) ^ 2 /
          (((J + 1 : ℕ) : ℝ))) *
        (1 / (x - (n : ℝ)) ^ 2) := by
  let M : ℝ := (((J + 1 : ℕ) : ℝ))
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hsub : x - (n : ℝ) ≠ 0 := sub_ne_zero.mpr hxn
  have hMsub : M * (x - (n : ℝ)) ≠ 0 := mul_ne_zero hM.ne' hsub
  unfold h3ScaledVaalerKernel h3VaalerK
  rw [if_neg hMsub]
  have hsin := h3_sin_scaled_sub_int_sq J x n
  dsimp [M] at hM hMsub ⊢
  rw [show Real.pi * ((((J + 1 : ℕ) : ℝ)) * (x - (n : ℝ))) =
      Real.pi * (((J + 1 : ℕ) : ℝ) * (x - (n : ℝ))) by ring]
  rw [div_pow]
  rw [hsin]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hMN : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hsub' : x - (n : ℝ) ≠ 0 := hsub
  field_simp [hpi, hMN, hsub']
noncomputable def h3RealFejerClosed (J : ℕ) (x : ℝ) : ℝ :=
  (((J + 1 : ℕ) : ℝ))⁻¹ *
    (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) /
      Real.sin (Real.pi * x)) ^ 2

theorem h3ScaledVaalerKernel_summable_of_noninteger
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    Summable (fun n : ℤ => h3ScaledVaalerKernel J (x - (n : ℝ))) := by
  let C : ℝ :=
    (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi) ^ 2 /
      (((J + 1 : ℕ) : ℝ))
  have hs : Summable (fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2) :=
    one_div_sub_sq_summable x
  have hmul : Summable (fun n : ℤ => C * (1 / (x - (n : ℝ)) ^ 2)) :=
    Summable.mul_left C hs
  refine hmul.congr ?_
  intro n
  symm
  apply h3ScaledVaalerKernel_sub_int_eq
  intro h
  exact hx ⟨n, h⟩

theorem h3ScaledVaalerKernel_periodized_eq_closed
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    (∑' n : ℤ, h3ScaledVaalerKernel J (x - (n : ℝ))) =
      h3RealFejerClosed J x := by
  let C : ℝ :=
    (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi) ^ 2 /
      (((J + 1 : ℕ) : ℝ))
  calc
    (∑' n : ℤ, h3ScaledVaalerKernel J (x - (n : ℝ))) =
        ∑' n : ℤ, C * (1 / (x - (n : ℝ)) ^ 2) := by
      apply tsum_congr
      intro n
      apply h3ScaledVaalerKernel_sub_int_eq
      intro h
      exact hx ⟨n, h⟩
    _ = C * (∑' n : ℤ, 1 / (x - (n : ℝ)) ^ 2) := by
      rw [tsum_mul_left]
    _ = C * (Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2) := by
      rw [csc_sq_mittag_leffler hx]
    _ = h3RealFejerClosed J x := by
      unfold C h3RealFejerClosed
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hM : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hsin : Real.sin (Real.pi * x) ≠ 0 := by
        rw [Real.sin_ne_zero_iff]
        intro n hEq
        apply hx
        refine ⟨n, ?_⟩
        nlinarith [Real.pi_pos]
      field_simp [hpi, hM, hsin]
lemma h3_stdAddChar_eq_exp_val
    {N : ℕ} [NeZero N] (y : ZMod N) :
    ZMod.stdAddChar y =
      Complex.exp (Complex.I *
        ((2 * Real.pi * (y.val : ℝ) / (N : ℝ) : ℝ) : ℂ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  push_cast
  congr 1
  ring
lemma h3_norm_stdAddChar_pow_sub_one
    {N : ℕ} [NeZero N] (y : ZMod N) (L : ℕ) :
    ‖(ZMod.stdAddChar y) ^ L - 1‖ =
      |2 * Real.sin (Real.pi * (L : ℝ) * (y.val : ℝ) / (N : ℝ))| := by
  rw [h3_stdAddChar_eq_exp_val]
  rw [← Complex.exp_nat_mul]
  have harg :
      ((L : ℂ) *
          (Complex.I * ((2 * Real.pi * (y.val : ℝ) / (N : ℝ) : ℝ) : ℂ))) =
        Complex.I *
          ((2 * Real.pi * (L : ℝ) * (y.val : ℝ) / (N : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs]
  congr 2
  ring

lemma h3_norm_stdAddChar_sub_one
    {N : ℕ} [NeZero N] (y : ZMod N) :
    ‖ZMod.stdAddChar y - 1‖ =
      |2 * Real.sin (Real.pi * (y.val : ℝ) / (N : ℝ))| := by
  simpa using h3_norm_stdAddChar_pow_sub_one y 1

theorem h3FejerKernel_eq_closed_of_ne_zero
    (N J : ℕ) [NeZero N] {y : ZMod N} (hy : y ≠ 0) :
    h3FejerKernel N J y =
      h3RealFejerClosed J ((y.val : ℝ) / (N : ℝ)) := by
  let q : ℂ := ZMod.stdAddChar y
  have hq1 : q ≠ 1 := by
    intro h
    have hz : ZMod.stdAddChar y = ZMod.stdAddChar (0 : ZMod N) := by
      simpa [q] using h
    exact hy (ZMod.injective_stdAddChar hz)
  have hgeom :
      (∑ k ∈ Finset.range (J + 1), q ^ k) =
        (q ^ (J + 1) - 1) / (q - 1) := geom_sum_eq hq1 (J + 1)
  have hval0 : y.val ≠ 0 := by
    intro h0
    apply hy
    apply ZMod.val_injective
    simp [h0]
  have hval_pos : 0 < y.val := Nat.pos_of_ne_zero hval0
  have hval_lt : y.val < N := ZMod.val_lt y
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hratio_pos : 0 < (y.val : ℝ) / (N : ℝ) := by
    exact div_pos (by exact_mod_cast hval_pos) hNpos
  have hratio_lt : (y.val : ℝ) / (N : ℝ) < 1 := by
    rw [div_lt_one hNpos]
    exact_mod_cast hval_lt
  have hangle_pos :
      0 < Real.pi * ((y.val : ℝ) / (N : ℝ)) :=
    mul_pos Real.pi_pos hratio_pos
  have hangle_lt :
      Real.pi * ((y.val : ℝ) / (N : ℝ)) < Real.pi := by
    simpa using mul_lt_mul_of_pos_left hratio_lt Real.pi_pos
  have hsinpos :
      0 < Real.sin (Real.pi * ((y.val : ℝ) / (N : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt
  have hsin :
      Real.sin (Real.pi * (y.val : ℝ) / (N : ℝ)) ≠ 0 := by
    convert ne_of_gt hsinpos using 1 <;> ring
  unfold h3FejerKernel
  rw [show ZMod.stdAddChar y = q by rfl]
  rw [hgeom, norm_div]
  rw [h3_norm_stdAddChar_pow_sub_one y (J + 1),
    h3_norm_stdAddChar_sub_one y]
  unfold h3RealFejerClosed
  have hJ : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [div_pow, div_pow, sq_abs, sq_abs]
  field_simp [hsin, hJ]


theorem h3ScaledVaalerError_summable_of_noninteger
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    Summable (fun n : ℤ => h3ScaledVaalerError J (x - (n : ℝ))) := by
  have hk := h3ScaledVaalerKernel_summable_of_noninteger J hx
  apply Summable.of_norm_bounded hk
  intro n
  simpa [Real.norm_eq_abs] using
    h3ScaledVaalerError_abs_le_kernel J (x - (n : ℝ))

theorem h3ScaledVaalerError_periodized_abs_le_closed
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    |∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))| ≤
      h3RealFejerClosed J x := by
  have he := h3ScaledVaalerError_summable_of_noninteger J hx
  have hk := h3ScaledVaalerKernel_summable_of_noninteger J hx
  have henorm : Summable
      (fun n : ℤ => ‖h3ScaledVaalerError J (x - (n : ℝ))‖) :=
    he.norm
  have hpoint : ∀ n : ℤ,
      ‖h3ScaledVaalerError J (x - (n : ℝ))‖ ≤
        h3ScaledVaalerKernel J (x - (n : ℝ)) := by
    intro n
    simpa [Real.norm_eq_abs] using
      h3ScaledVaalerError_abs_le_kernel J (x - (n : ℝ))
  calc
    |∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))| =
        ‖∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℤ, ‖h3ScaledVaalerError J (x - (n : ℝ))‖ :=
      norm_tsum_le_tsum_norm henorm
    _ ≤ ∑' n : ℤ, h3ScaledVaalerKernel J (x - (n : ℝ)) :=
      Summable.tsum_le_tsum hpoint henorm hk
    _ = h3RealFejerClosed J x :=
      h3ScaledVaalerKernel_periodized_eq_closed J hx

lemma h3_grid_fraction_noninteger_of_ne_zero
    {N : ℕ} [NeZero N] {y : ZMod N} (hy : y ≠ 0) :
    ¬ ∃ m : ℤ, (y.val : ℝ) / (N : ℝ) = (m : ℝ) := by
  have hval0 : y.val ≠ 0 := by
    intro h0
    apply hy
    apply ZMod.val_injective
    simp [h0]
  have hval_pos : 0 < y.val := Nat.pos_of_ne_zero hval0
  have hval_lt : y.val < N := ZMod.val_lt y
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hpos : 0 < (y.val : ℝ) / (N : ℝ) :=
    div_pos (by exact_mod_cast hval_pos) hNpos
  have hlt : (y.val : ℝ) / (N : ℝ) < 1 := by
    rw [div_lt_one hNpos]
    exact_mod_cast hval_lt
  rintro ⟨m, hm⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by rwa [← hm]
  have hmlt : (m : ℝ) < 1 := by rwa [← hm]
  have hmge : (1 : ℤ) ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ (m : ℝ) by
    exact_mod_cast (Int.add_one_le_iff.mpr (show (0 : ℤ) < m by exact_mod_cast hmpos)))
  have hmgeR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge
  linarith

theorem h3ScaledVaalerError_grid_periodized_abs_le_fejer
    (N J : ℕ) [NeZero N] {y : ZMod N} (hy : y ≠ 0) :
    |∑' n : ℤ,
        h3ScaledVaalerError J
          ((y.val : ℝ) / (N : ℝ) - (n : ℝ))| ≤
      h3FejerKernel N J y := by
  have hx := h3_grid_fraction_noninteger_of_ne_zero hy
  have hbound :=
    h3ScaledVaalerError_periodized_abs_le_closed J hx
  rw [h3FejerKernel_eq_closed_of_ne_zero N J hy]
  exact hbound
def H3ScaledVaalerPeriodizationIdentity
    (N J : ℕ) [NeZero N] : Prop :=
  ∀ y : ZMod N, y ≠ 0 →
    (2 * (((J + 1 : ℕ) : ℝ))) *
        (h3VaalerApprox N J y - h3CenteredSawtooth N y) =
      ∑' n : ℤ,
        h3ScaledVaalerError J
          ((y.val : ℝ) / (N : ℝ) - (n : ℝ))

theorem h3Vaaler_periodic_error_of_scaled_periodization
    (N J : ℕ) [NeZero N]
    (hper : H3ScaledVaalerPeriodizationIdentity N J) :
    ∀ y : ZMod N,
      |h3VaalerApprox N J y - h3CenteredSawtooth N y| ≤
        h3VaalerError N J y := by
  intro y
  by_cases hy : y = 0
  · subst y
    rw [h3VaalerApprox_zero, h3CenteredSawtooth_zero]
    simpa using h3VaalerError_nonneg N J (0 : ZMod N)
  · have hbound :=
      h3ScaledVaalerError_grid_periodized_abs_le_fejer N J hy
    have hid := hper y hy
    let scale : ℝ := 2 * (((J + 1 : ℕ) : ℝ))
    let err : ℝ := h3VaalerApprox N J y - h3CenteredSawtooth N y
    have hscale_pos : 0 < scale := by
      dsimp [scale]
      positivity
    have hscaled : |scale * err| ≤ h3FejerKernel N J y := by
      dsimp [scale, err]
      rw [hid]
      exact hbound
    have habs : scale * |err| ≤ h3FejerKernel N J y := by
      rwa [abs_mul, abs_of_pos hscale_pos] at hscaled
    have hdiv : |err| ≤ h3FejerKernel N J y / scale := by
      exact (le_div_iff₀ hscale_pos).2 (by simpa [mul_comm] using habs)
    dsimp [err, scale] at hdiv ⊢
    unfold h3VaalerError
    convert hdiv using 1 <;> field_simp <;> ring

theorem h3VaalerGridErrorSpec_of_scaled_periodization
    (N J : ℕ) [NeZero N]
    (hper : H3ScaledVaalerPeriodizationIdentity N J) :
    H3VaalerGridErrorSpec N J :=
  h3Vaaler_periodic_error_of_scaled_periodization N J hper

end RML.Fourier.Vaaler.Internal
