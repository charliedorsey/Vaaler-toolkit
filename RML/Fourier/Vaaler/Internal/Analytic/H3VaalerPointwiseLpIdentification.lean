module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
public import RML.Fourier.Vaaler.Internal.Analytic.FourierPlancherelBridge

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.FourierPlancherelBridge

abbrev FourierL2 :
    Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
      Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

theorem gCesLp_tendsto_inverseJ
    (hMemCes : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hFourier : Tendsto
      (fun M : ℕ => FourierL2 ((hMemCes M).toLp (gCes M)))
      atTop
      (𝓝 (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC))) :
    Tendsto
      (fun M : ℕ => (hMemCes M).toLp (gCes M))
      atTop
      (𝓝 (FourierL2.symm
        (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC))) := by
  have h := (FourierL2.symm.continuous.tendsto
    (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)).comp hFourier
  refine h.congr' ?_
  filter_upwards with M
  exact FourierL2.symm_apply_apply ((hMemCes M).toLp (gCes M))

theorem inverseJ_ae_eq_h3GC
    (hMemCes : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hFourier : Tendsto
      (fun M : ℕ => FourierL2 ((hMemCes M).toLp (gCes M)))
      atTop
      (𝓝 (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC))) :
    (⇑(FourierL2.symm
      (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)) : ℝ → ℂ)
      =ᵐ[volume] h3GC := by
  let L : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
    FourierL2.symm (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)
  have hLp : Tendsto (fun M : ℕ => (hMemCes M).toLp (gCes M))
      atTop (𝓝 L) := by
    simpa [L] using gCesLp_tendsto_inverseJ hMemCes hFourier
  have hLp0 : Tendsto
      (fun M : ℕ => eLpNorm
        (⇑((hMemCes M).toLp (gCes M)) - ⇑L) 2 (volume : Measure ℝ))
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun M : ℕ => (hMemCes M).toLp (gCes M)) L).mp hLp
  have hTIM : TendstoInMeasure (volume : Measure ℝ)
      (fun M : ℕ => (⇑((hMemCes M).toLp (gCes M)) : ℝ → ℂ))
      atTop (⇑L : ℝ → ℂ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hLp0
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae'
  have hcoe : ∀ M : ℕ,
      (⇑((hMemCes M).toLp (gCes M)) : ℝ → ℂ) =ᵐ[volume] gCes M :=
    fun M => (hMemCes M).coeFn_toLp
  have hcoe_all : ∀ᵐ x : ℝ, ∀ i : ℕ,
      (⇑((hMemCes (ns i)).toLp (gCes (ns i))) : ℝ → ℂ) x =
        gCes (ns i) x := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i => hcoe (ns i)
  filter_upwards [hae, hcoe_all, gCes_tendsto_h3GC_ae] with x hxL hxcoe hxpt
  have hxL' : Tendsto (fun i : ℕ => gCes (ns i) x) atTop
      (𝓝 ((L : ℝ → ℂ) x)) := by
    refine (Filter.tendsto_congr ?_).mp hxL
    intro i
    rw [hxcoe i]
  have hxpt' : Tendsto (fun i : ℕ => gCes (ns i) x) atTop
      (𝓝 (h3GC x)) :=
    hxpt.comp (by simpa using hns)
  exact tendsto_nhds_unique hxL' hxpt'

theorem h3GC_memLp_two_of_fourierLimit
    (hMemCes : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hFourier : Tendsto
      (fun M : ℕ => FourierL2 ((hMemCes M).toLp (gCes M)))
      atTop
      (𝓝 (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC))) :
    MemLp h3GC 2 (volume : Measure ℝ) := by
  let L : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
    FourierL2.symm (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)
  have hae : (⇑L : ℝ → ℂ) =ᵐ[volume] h3GC := by
    simpa [L] using inverseJ_ae_eq_h3GC hMemCes hFourier
  exact (memLp_congr_ae hae).mp (Lp.memLp L)

theorem fourierTransformLp_h3GC_eq_JHat
    (hMemCes : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hFourier : Tendsto
      (fun M : ℕ => FourierL2 ((hMemCes M).toLp (gCes M)))
      atTop
      (𝓝 (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC))) :
    FourierL2 ((h3GC_memLp_two_of_fourierLimit hMemCes hFourier).toLp h3GC) =
      h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC := by
  let L : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
    FourierL2.symm (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)
  have hLeq :
      L = (h3GC_memLp_two_of_fourierLimit hMemCes hFourier).toLp h3GC := by
    apply Lp.ext
    have hae : (⇑L : ℝ → ℂ) =ᵐ[volume] h3GC := by
      simpa [L] using inverseJ_ae_eq_h3GC hMemCes hFourier
    exact hae.trans
      ((h3GC_memLp_two_of_fourierLimit hMemCes hFourier).coeFn_toLp).symm
  have hFL : FourierL2 L =
      h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC := by
    simp [L, FourierL2]
  rw [← hLeq]
  exact hFL

theorem h3GCFourier_eq_JHat_of_fourierLimit
    (hMemCes : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hFourier : Tendsto
      (fun M : ℕ => FourierL2 ((hMemCes M).toLp (gCes M)))
      atTop
      (𝓝 (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)))
    (hGint : Integrable h3GC) :
    𝓕 h3GC = h3VaalerJHatContC := by
  let hMemGC := h3GC_memLp_two_of_fourierLimit hMemCes hFourier
  exact fourierIntegral_eq_of_plancherel
    hGint hMemGC h3VaalerJHatContC_memLp_two
    h3VaalerJHatContC_continuous
    (by simpa [hMemGC] using
      fourierTransformLp_h3GC_eq_JHat hMemCes hFourier)

#print axioms inverseJ_ae_eq_h3GC
#print axioms h3GC_memLp_two_of_fourierLimit
#print axioms fourierTransformLp_h3GC_eq_JHat
#print axioms h3GCFourier_eq_JHat_of_fourierLimit

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
