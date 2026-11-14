module

public import RML.Fourier.Vaaler.Pointwise
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier

@[expose] public section

namespace RML.Fourier.Vaaler
open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier

/-- The error kernel is the normalized sinc square. -/
theorem K_eq_sincSqPi (x : ℝ) :
    K x = RML.Fourier.Vaaler.Internal.Analytic.SincSquare.sincSqPi x :=
  h3VaalerK_eq_sincSqPi x

open scoped FourierTransform

/-- Exact normalized Fourier transform of the nonnegative sinc-square kernel. -/
theorem kernel_fourier_fejer :
    𝓕 (fun x : ℝ => (K x : ℂ)) =
       (fun t : ℝ =>
         (RML.Fourier.Vaaler.Internal.Analytic.FejerTriangle.fejerTriangle t : ℂ)) :=
  fourier_h3VaalerK_eq_fejerTriangle

#print axioms kernel_fourier_fejer
#print axioms K_eq_sincSqPi
#print axioms fourier_h3VaalerK_eq_fejerTriangle
end RML.Fourier.Vaaler
