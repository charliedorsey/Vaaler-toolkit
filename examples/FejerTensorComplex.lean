module

public import RML.Fourier.Vaaler.Discrepancy.FejerTensorComplex

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-- Independent cutoffs in two dimensions; exact zero-mode accounting. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → Fin 2 → ℝ) (a b : Fin 2 → ℝ) :
    ((∑ n ∈ N, w n *
      ((∏ i : Fin 2,
        (1 + intervalError (if i = 0 then 3 else 7)
          (a i) (b i)
          (errorCoeff (if i = 0 then 3 else 7)) (x n i))) - 1) : ℝ) : ℂ) =
    (∑ p ∈ Fintype.piFinset
      (fun i : Fin 2 => signedErrorOneSupport (if i = 0 then 3 else 7)),
      (∏ i : Fin 2,
        signedErrorOneCoeff (if i = 0 then 3 else 7)
          (a i) (b i) (p i)) *
        weightedTensorExponentialSum N w x
          (fun i : Fin 2 => signedErrorOneFreq (p i))) -
      ((∑ n ∈ N, w n : ℝ) : ℂ) := by
  exact weighted_fejer_tensor_error_eq_signed_box N w x
    (fun i : Fin 2 => if i = 0 then 3 else 7) a b

/-- The zero-dimensional error product subtracts exactly its unit. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → Fin 0 → ℝ) (J : Fin 0 → ℕ)
    (a b : Fin 0 → ℝ) :
    ((∑ n ∈ N, w n *
      ((∏ i : Fin 0,
        (1 + intervalError (J i) (a i) (b i)
          (errorCoeff (J i)) (x n i))) - 1) : ℝ) : ℂ) = 0 := by
  simp
