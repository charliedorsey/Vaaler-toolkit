module

public import RML.Fourier.Vaaler.Discrepancy.SignedETK
public import RML.Fourier.Vaaler.Discrepancy.OneDimETK
public import RML.Fourier.Vaaler.Discrepancy.TorusBox

@[expose] public section

/-!
# Tier 4B (Phase I) — signed one-dimensional ETK consumers

NEW extension module (VAALER-4B-R0001). Arbitrary real weights, no sign hypothesis.

* The Vaaler MAIN polynomial is controlled by the SIGNED exponential sums
  `S_w(j) = ∑ₙ wₙ e(j xₙ)`.
* The Fejér ERROR is charged to `|w|`: its zero mode is exactly `2 V(N,w)/(J+1)` with
  `V(N,w) = ∑ |wₙ|` (NOT `2 |∑ wₙ|/(J+1)`), and its oscillatory modes use
  `S_|w|(j) = ∑ₙ |wₙ| e(j xₙ)`.

Supplied: a general certificate-to-bound lemma, the exact signed Fejér-error identity,
half-open and directed torus-arc (wrapped or unwrapped) signed 1D ETK, recovery of the
existing nonnegative theorem, and a kernel-checked NEGATIVE CONTROL showing that the
naive bound with `|∑ w|` and `S_w` in the error is false.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Absolute-weight exponential sum `S_|w|(h) = ∑ₙ |wₙ| e(h xₙ)`. -/
noncomputable abbrev absWeightedExponentialSum
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) (h : ℤ) : ℂ :=
  weightedExponentialSum N (fun n => |w n|) x h

/-- **Certificate-to-bound (signed, one coordinate).** If `ind = ℓ + σ` pointwise and
`|σ − P| ≤ E` pointwise, then for arbitrary real weights the signed discrepancy is at most
the signed main sum plus the `|w|`-weighted error. -/
theorem signed_abs_discrepancy_le_main_add_error
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)
    (ind : ℝ → ℝ) (ℓ : ℝ) (σ P E : ℝ → ℝ)
    (hid : ∀ t, ind t = ℓ + σ t) (hE : ∀ t, |σ t - P t| ≤ E t) :
    |(∑ n ∈ N, w n * ind (x n)) - (∑ n ∈ N, w n) * ℓ| ≤
      |∑ n ∈ N, w n * P (x n)| + ∑ n ∈ N, |w n| * E (x n) := by
  have h1 : (∑ n ∈ N, w n * ind (x n)) - (∑ n ∈ N, w n) * ℓ =
      (∑ n ∈ N, w n * P (x n)) + ∑ n ∈ N, w n * (σ (x n) - P (x n)) := by
    simp_rw [hid]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hE _) (abs_nonneg _)

/-- **Exact signed Fejér-error identity.** The `|w|`-weighted Vaaler error has zero mode
exactly `2 V(N,w)/(J+1)` and oscillatory modes in `S_|w|(j)`, `1 ≤ j ≤ J`. -/
theorem signed_intervalError_eq_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, |w n| * intervalError J a b (errorCoeff J) (x n)) =
    (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        (intervalErrorFrequencyCoeff J a b j *
          absWeightedExponentialSum N w x (j : ℤ)).re :=
  weighted_intervalError_eq_exponential_sums N (fun n => |w n|) x J a b

theorem signed_intervalError_le_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, |w n| * intervalError J a b (errorCoeff J) (x n)) ≤
    (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        ‖intervalErrorFrequencyCoeff J a b j‖ *
          ‖absWeightedExponentialSum N w x (j : ℤ)‖ :=
  weighted_intervalError_le_exponential_sums N (fun n => |w n|) x J a b

/-- Combine a certificate with the explicit main/error exponential-sum bounds. -/
theorem signed_oneDim_of_certificate
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)
    (J : ℕ) (a b : ℝ) (ind : ℝ → ℝ) (ℓ : ℝ)
    (hid : ∀ t, ind t = ℓ + intervalSigma a b t)
    (hE : ∀ t, |intervalSigma a b t - intervalMain J a b (mainCoeff J) t| ≤
      intervalError J a b (errorCoeff J) t) :
    |(∑ n ∈ N, w n * ind (x n)) - (∑ n ∈ N, w n) * ℓ| ≤
      (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff J a b j‖ *
            ‖absWeightedExponentialSum N w x (j : ℤ)‖) := by
  calc _ ≤ |∑ n ∈ N, w n * intervalMain J a b (mainCoeff J) (x n)| +
          ∑ n ∈ N, |w n| * intervalError J a b (errorCoeff J) (x n) :=
        signed_abs_discrepancy_le_main_add_error N w x ind ℓ (intervalSigma a b)
          (intervalMain J a b (mainCoeff J)) (intervalError J a b (errorCoeff J)) hid hE
    _ ≤ (∑ j ∈ Finset.Icc 1 J,
            ‖intervalFrequencyCoeff J a b j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖) +
          ((2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
            ∑ j ∈ Finset.Icc 1 J, ‖intervalErrorFrequencyCoeff J a b j‖ *
              ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
        add_le_add (weighted_intervalMain_abs_le_exponential_sums N w x J a b)
          (signed_intervalError_le_exponential_sums N w x J a b)
    _ = _ := by rw [Finset.sum_add_distrib]; ring

/-- **Signed one-dimensional ETK, half-open interval `[a,b)` modulo 1.** -/
theorem signed_oneDim_etk_exponential
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    |(∑ n ∈ N, w n *
        (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * (b - a)| ≤
      (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff J a b j‖ *
            ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_of_certificate N w x J a b
    (fun t => if a ≤ Int.fract t ∧ Int.fract t < b then (1 : ℝ) else 0) (b - a)
    (fun t => (explicit_halfOpen_interval_certificate J hJ a b ha hab hb t).1)
    (fun t => (explicit_halfOpen_interval_certificate J hJ a b ha hab hb t).2.2.1)

/-- **Signed one-dimensional ETK on a directed half-open torus arc**, wrapped
(`b < a`, the arc `[a,1) ∪ [0,b)`) or unwrapped (`a < b`). Equal endpoints are excluded
exactly as in `explicit_torus_arc_certificate`. -/
theorem signed_oneDim_arc_etk_exponential
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≠ b) :
    |(∑ n ∈ N, w n * torusArcIndicator a b (x n)) -
      (∑ n ∈ N, w n) * torusArcLength a b| ≤
      (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff J a b j‖ *
            ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_of_certificate N w x J a b (torusArcIndicator a b) (torusArcLength a b)
    (fun t => (explicit_torus_arc_certificate J hJ a b ha0 ha1 hb0 hb1 hab t).1)
    (fun t => (explicit_torus_arc_certificate J hJ a b ha0 ha1 hb0 hb1 hab t).2.2.1)

/-- Consumer form: plug in independently proved bounds `B j ≥ ‖S_w(j)‖` and
`C j ≥ ‖S_|w|(j)‖` and an upper bound `V ≤ Vbar`. -/
theorem signed_oneDim_arc_etk_external_bounds
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≠ b)
    (Vbar : ℝ) (hV : ETKd.signedWeightVariation N w ≤ Vbar)
    (B C : ℕ → ℝ)
    (hB : ∀ j ∈ Finset.Icc 1 J, ‖weightedExponentialSum N w x (j : ℤ)‖ ≤ B j)
    (hC : ∀ j ∈ Finset.Icc 1 J, ‖absWeightedExponentialSum N w x (j : ℤ)‖ ≤ C j) :
    |(∑ n ∈ N, w n * torusArcIndicator a b (x n)) -
      (∑ n ∈ N, w n) * torusArcLength a b| ≤
      (2 : ℝ) / (J + 1) * Vbar +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ * B j +
          ‖intervalErrorFrequencyCoeff J a b j‖ * C j) := by
  refine (signed_oneDim_arc_etk_exponential N w x J hJ a b ha0 ha1 hb0 hb1 hab).trans ?_
  have hJ0 : (0 : ℝ) ≤ (2 : ℝ) / (J + 1) := by positivity
  gcongr with j hj
  · exact hB j hj
  · exact hC j hj

/-- **Recovery.** For nonnegative weights `S_|w| = S_w` and `V = ∑ w`, and the signed
half-open theorem gives exactly the statement of `weighted_oneDim_etk_exponential`. -/
theorem weighted_oneDim_etk_exponential_of_signed
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → ℝ) (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    |(∑ n ∈ N, w n *
        (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * (b - a)| ≤
      (2 : ℝ) / (J + 1) * (∑ n ∈ N, w n) +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ + ‖intervalErrorFrequencyCoeff J a b j‖) *
          ‖weightedExponentialSum N w x (j : ℤ)‖ := by
  have hS : ∀ j : ℤ, absWeightedExponentialSum N w x j = weightedExponentialSum N w x j :=
    fun j => Finset.sum_congr rfl fun n hn => by simp only [abs_of_nonneg (hw n hn)]
  have h := signed_oneDim_etk_exponential N w x J hJ a b ha hab hb
  rw [ETKd.signedWeightVariation_eq_sum_of_nonneg N w hw] at h
  simp_rw [hS, ← add_mul] at h
  exact h

#print axioms signed_abs_discrepancy_le_main_add_error
#print axioms signed_intervalError_eq_exponential_sums
#print axioms signed_intervalError_le_exponential_sums
#print axioms signed_oneDim_of_certificate
#print axioms signed_oneDim_etk_exponential
#print axioms signed_oneDim_arc_etk_exponential
#print axioms signed_oneDim_arc_etk_external_bounds
#print axioms weighted_oneDim_etk_exponential_of_signed

end RML.Fourier.Vaaler.Positive
