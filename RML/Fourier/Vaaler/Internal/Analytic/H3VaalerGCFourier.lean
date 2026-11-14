module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCFourier

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable

/-- Exact live Paper B analogue of the certified GCFTeqJhat. -/
theorem GCFTeqJhat :
    ∀ t : ℝ, 𝓕 h3GC t = h3VaalerJHatContC t := by
  intro t
  have hfun :
      𝓕 h3GC = h3VaalerJHatContC :=
    h3GCFourier_eq_JHat_of_fourierLimit
      memLp_gCes
      fourierSideL2Limit
      h3GC_integrable
  exact congrFun hfun t

theorem GCFTeqJhat_fun :
    𝓕 h3GC = h3VaalerJHatContC :=
  funext GCFTeqJhat

#print axioms GCFTeqJhat
#print axioms GCFTeqJhat_fun

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCFourier
