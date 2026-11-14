module

public import RML.Fourier.Vaaler.Positive.Internal.VaalerFullPointwise

@[expose] public section

namespace RML.Fourier.Vaaler.Positive
/-- Positive Vaaler polynomial bound with the literal -1/2 integer saw jump. -/
theorem positive_pointwise : RealPositiveVaalerPointwise :=
  yevorin_realPositiveVaalerPointwise

#print axioms positive_pointwise
#print axioms saw_zero
end RML.Fourier.Vaaler.Positive
