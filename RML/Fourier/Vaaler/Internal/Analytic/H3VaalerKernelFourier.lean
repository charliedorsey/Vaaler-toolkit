module

public import RML.Fourier.Vaaler.Internal.H3VaalerPointwise
public import RML.Fourier.Vaaler.Internal.Analytic.SincSquare

@[expose] public section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.FejerTriangle
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare

theorem h3VaalerK_eq_sincSqPi (x : ℝ) :
    h3VaalerK x = sincSqPi x := by
  unfold h3VaalerK sincSqPi Real.sinc
  by_cases hx : x = 0
  · subst x
    simp
  · have hπx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
    rw [if_neg hx, if_neg hπx]

theorem h3VaalerK_eq_sincSqPi_fun :
    h3VaalerK = sincSqPi :=
  funext h3VaalerK_eq_sincSqPi

theorem h3VaalerK_integrable :
    Integrable h3VaalerK := by
  rw [h3VaalerK_eq_sincSqPi_fun]
  exact sincSqPi_integrable

theorem fourier_h3VaalerK_eq_fejerTriangle :
    𝓕 (fun x : ℝ => (h3VaalerK x : ℂ)) =
      fun t : ℝ => (fejerTriangle t : ℂ) := by
  have hfun :
      (fun x : ℝ => (h3VaalerK x : ℂ)) =
        fun x : ℝ => (sincSqPi x : ℂ) := by
    funext x
    rw [h3VaalerK_eq_sincSqPi]
  rw [hfun]
  exact fourier_sincSqPi_eq_fejerTriangle

#print axioms h3VaalerK_eq_sincSqPi
#print axioms fourier_h3VaalerK_eq_fejerTriangle

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
