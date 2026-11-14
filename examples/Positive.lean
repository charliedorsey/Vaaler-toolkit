module

public import RML.Fourier.Vaaler.Positive

@[expose] public section

open RML.Fourier.Vaaler.Positive

example : saw 0 = -(1 / 2 : ℝ) := saw_zero
example : RealPositiveVaalerPointwise := positive_pointwise

#print axioms RML.Fourier.Vaaler.Positive.positive_pointwise
