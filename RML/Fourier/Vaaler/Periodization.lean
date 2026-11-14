module

public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodizationCloseout

@[expose] public section

namespace RML.Fourier.Vaaler
open RML.Fourier.Vaaler.Internal

/-- Exact source-normalized scaled periodization statement. -/
theorem periodized_identity (N J : ℕ) [NeZero N] :
    RML.Fourier.Vaaler.Internal.H3ScaledVaalerPeriodizationIdentity N J :=
  h3ScaledVaalerPeriodizationIdentity_holds N J

#print axioms periodized_identity
#print axioms h3ScaledVaalerPeriodizationIdentity_holds
#print axioms h3VaalerGridErrorSpec_holds
end RML.Fourier.Vaaler
