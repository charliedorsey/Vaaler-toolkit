module

public import Mathlib

@[expose] public section

/-!
# Hunt 09 — d-dimensional weighted Erdős–Turán–Koksma: the algebraic core

Coordinates form any finite type `κ` (e.g. `Fin d`). Each coordinate `i` carries a
*local approximation package*: the centred box indicator `σ i t = 1_{[αᵢ,βᵢ)}(t) − ℓᵢ`, a
trigonometric approximant `P i`, and a majorant `E i ≥ |σ i − P i|`, with `|σ i| ≤ 1`.
(The Vaaler toolkit supplies these with `P = ψ*_J(·−β) − ψ*_J(·−α)` and `E = Fejér_J/(2J+2)` shifts.)

* `abs_prod_sub_prod_le` — **tensor product rule** `|∏σᵢ − ∏Pᵢ| ≤ ∏(1+Eᵢ) − 1`
  (for `d = 2` this is the `E₁ + E₂ + E₁E₂` rule of `ErdosTuran.Torus2`).
* `prod_add_expand` — box indicator expansion `∏ (ℓᵢ + σᵢ) = ∑_{A ⊆ κ} (∏_{i∉A} ℓᵢ)(∏_{i∈A} σᵢ)`.
* **`etk_abstract`** — weighted d-dimensional ETK, explicit in `d` (one term per nonempty
  `A ⊆ κ`, i.e. `2^d − 1` terms) and in the packages:

    `|∑ₙ wₙ ∏ᵢ 1_{Iᵢ}(xₙᵢ) − (∑ w) ∏ᵢ ℓᵢ| ≤
       ∑_{A ≠ ∅} ( |∑ₙ wₙ ∏_{i∈A} Pᵢ(xₙᵢ)| + ∑ₙ wₙ (∏_{i∈A} (1 + Eᵢ(xₙᵢ)) − 1) )`

  for weights `w ≥ 0` and lengths `0 ≤ ℓᵢ ≤ 1`. Substituting the Fourier expansions of `Pᵢ, Eᵢ`
  turns each bracket into d-dimensional exponential sums `S(h) = ∑ wₙ e(h·xₙ)` with
  `h ∈ ∏_{i∈A} [−J_i, J_i]` (unequal truncations allowed: each package has its own `Jᵢ`).
-/

open Finset

namespace ETKd

variable {κ : Type*} [DecidableEq κ]

/-- **Tensor product rule.** -/
theorem abs_prod_sub_prod_le (s : Finset κ) (σ P E : κ → ℝ)
    (hσ : ∀ i ∈ s, |σ i| ≤ 1) (hE : ∀ i ∈ s, |σ i - P i| ≤ E i) :
    |∏ i ∈ s, σ i - ∏ i ∈ s, P i| ≤ ∏ i ∈ s, (1 + E i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hσ' : ∀ i ∈ s, |σ i| ≤ 1 := fun i hi => hσ i (mem_insert_of_mem hi)
    have hE' : ∀ i ∈ s, |σ i - P i| ≤ E i := fun i hi => hE i (mem_insert_of_mem hi)
    have ih := ih hσ' hE'
    have hEa : |σ a - P a| ≤ E a := hE a (mem_insert_self a s)
    have hσa : |σ a| ≤ 1 := hσ a (mem_insert_self a s)
    have hS : |∏ i ∈ s, σ i| ≤ 1 := by
      rw [abs_prod]; exact prod_le_one₀ (fun i _ => abs_nonneg _) hσ'
    have hT : |∏ i ∈ s, P i| ≤ ∏ i ∈ s, (1 + E i) := by
      have := abs_sub_abs_le_abs_sub (∏ i ∈ s, P i) (∏ i ∈ s, σ i)
      rw [abs_sub_comm (∏ i ∈ s, P i)] at this
      linarith
    rw [prod_insert ha, prod_insert ha, prod_insert ha]
    have key : σ a * ∏ i ∈ s, σ i - P a * ∏ i ∈ s, P i =
        σ a * (∏ i ∈ s, σ i - ∏ i ∈ s, P i) + (σ a - P a) * ∏ i ∈ s, P i := by ring
    rw [key]
    calc |σ a * (∏ i ∈ s, σ i - ∏ i ∈ s, P i) + (σ a - P a) * ∏ i ∈ s, P i|
        ≤ |σ a| * |∏ i ∈ s, σ i - ∏ i ∈ s, P i| + |σ a - P a| * |∏ i ∈ s, P i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (∏ i ∈ s, (1 + E i) - 1) + E a * ∏ i ∈ s, (1 + E i) := by
          gcongr
          exact (abs_nonneg _).trans hEa
      _ = (1 + E a) * ∏ i ∈ s, (1 + E i) - 1 := by ring

/-- Box-indicator expansion over subsets of coordinates. -/
theorem prod_add_expand [Fintype κ] (ℓ σ : κ → ℝ) :
    ∏ i, (ℓ i + σ i) = ∑ A ∈ (univ : Finset κ).powerset, (∏ i ∈ A, σ i) * ∏ i ∈ univ \ A, ℓ i := by
  rw [show (fun i => ℓ i + σ i) = (fun i => σ i + ℓ i) from funext fun i => add_comm _ _]
  exact prod_add σ ℓ univ

variable [Fintype κ] {ι : Type*}

/-- **Abstract weighted d-dimensional ETK.** -/
theorem etk_abstract (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n) (x : ι → κ → ℝ)
    (ℓ : κ → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (σ P E : κ → ℝ → ℝ) (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
  -- expand each product over subsets, then isolate the `A = ∅` term (the main term)
  have hexp : ∀ n, ∏ i, (ℓ i + σ i (x n i)) =
      ∑ A ∈ (univ : Finset κ).powerset, (∏ i ∈ A, σ i (x n i)) * ∏ i ∈ univ \ A, ℓ i :=
    fun n => prod_add_expand ℓ (fun i => σ i (x n i))
  simp_rw [hexp, mul_sum]
  rw [sum_comm, ← add_sum_erase _ _ (empty_mem_powerset _)]
  simp only [prod_empty, one_mul, sdiff_empty]
  rw [← sum_mul, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A hA => ?_)
  -- each nonempty `A`
  have hℓA : 0 ≤ ∏ i ∈ univ \ A, ℓ i ∧ ∏ i ∈ univ \ A, ℓ i ≤ 1 :=
    ⟨prod_nonneg fun i _ => hℓ0 i, prod_le_one₀ (fun i _ => hℓ0 i) fun i _ => hℓ1 i⟩
  have hsplit : ∑ n ∈ N, w n * ((∏ i ∈ A, σ i (x n i)) * ∏ i ∈ univ \ A, ℓ i) =
      (∏ i ∈ univ \ A, ℓ i) * (∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i) +
        ∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))) := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit, abs_mul, abs_of_nonneg hℓA.1]
  have hrem : |∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))| ≤
      ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    rw [abs_mul, abs_of_nonneg (hw n hn)]
    exact mul_le_mul_of_nonneg_left
      (abs_prod_sub_prod_le A (fun i => σ i (x n i)) (fun i => P i (x n i))
        (fun i => E i (x n i)) (fun i _ => hσ i _) (fun i _ => hE i _)) (hw n hn)
  have hbr : 0 ≤ |∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
      ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1) :=
    add_nonneg (abs_nonneg _) ((abs_nonneg _).trans hrem)
  calc (∏ i ∈ univ \ A, ℓ i) * |∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i) +
        ∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))|
      ≤ 1 * (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
        apply mul_le_mul hℓA.2 _ (abs_nonneg _) zero_le_one
        exact (abs_add_le _ _).trans (add_le_add_right hrem _)
    _ = _ := one_mul _

end ETKd
