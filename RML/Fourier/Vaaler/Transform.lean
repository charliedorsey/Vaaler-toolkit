module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed

@[expose] public section

namespace RML.Fourier.Vaaler
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed

/-- Source-normalized nonzero-frequency Fourier transform (Corollary 7). -/
theorem error_fourier_transform_nonzero :
    RML.Fourier.Vaaler.Internal.H3VaalerCor7TransformSpec :=
  h3VaalerCor7TransformSpec_holds

#print axioms error_fourier_transform_nonzero
end RML.Fourier.Vaaler
