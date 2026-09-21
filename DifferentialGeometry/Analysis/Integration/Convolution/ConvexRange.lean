import DifferentialGeometry.Analysis.Integration.Measure.BoundedDensity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2

section

noncomputable section

open Filter MeasureTheory Set ContinuousLinearMap
open scoped Convolution ENNReal

namespace Convex

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem integral_smul_mem_of_nonneg_of_integral_eq_one
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    {k : X → ℝ} (hk : AEMeasurable k μ) (hk0 : 0 ≤ᵐ[μ] k)
    (hk1 : ∫ x, k x ∂μ = 1) {f : X → F}
    (hfK : ∀ᵐ x ∂μ, f x ∈ K) (hfi : Integrable (fun x => k x • f x) μ) :
    (∫ x, k x • f x ∂μ) ∈ K := by
  let ν : Measure X := μ.withDensity (fun x => ENNReal.ofReal (k x))
  let : IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_ofReal hk0 hk1
  have hfν : ∀ᵐ x ∂ν, f x ∈ K := (withDensity_absolutelyContinuous μ _).ae_le hfK
  have hiν : Integrable f ν := by
    apply (integrable_withDensity_iff_integrable_smul₀' hk.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    apply hfi.congr
    filter_upwards [hk0] with x hx
    rw [ENNReal.toReal_ofReal hx]
  have hm := hK.integral_mem hKclosed hfν hiν
  have heq : (∫ x, f x ∂ν) = ∫ x, k x • f x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hk0] with x hx
    rw [ENNReal.toReal_ofReal hx]
  rwa [heq] at hm

end Convex

namespace ContDiffBump

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "V" => EuclideanSpace ℝ (Fin d)

theorem normed_convolution_mem_of_ae_mem_closed_convex
    (φ : ContDiffBump (0 : V)) {f : V → F} (hf : LocallyIntegrable f volume)
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hfK : ∀ᵐ x ∂volume, f x ∈ K) (x : V) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x ∈ K := by
  rw [convolution_def]
  apply hK.integral_smul_mem_of_nonneg_of_integral_eq_one hKclosed
    φ.continuous_normed.measurable.aemeasurable
    (Eventually.of_forall φ.nonneg_normed) φ.integral_normed
  · exact (Measure.measurePreserving_sub_left (volume : Measure V) x).quasiMeasurePreserving.ae hfK
  · exact φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hf x

theorem normed_convolution_indicator_mem_of_ae_mem_closed_convex
    (φ : ContDiffBump (0 : V)) {Ω : Set V} (hΩ : MeasurableSet Ω) {f : V → F}
    (hf : LocallyIntegrable (Ω.indicator f) volume)
    {K : Set F} (hK : Convex ℝ K) (hKclosed : IsClosed K) (h0 : (0 : F) ∈ K)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K) (x : V) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x ∈ K := by
  apply φ.normed_convolution_mem_of_ae_mem_closed_convex hf hK hKclosed
  filter_upwards [(ae_restrict_iff' hΩ).mp hfK] with y hy
  by_cases hyΩ : y ∈ Ω
  · rw [indicator_of_mem hyΩ]
    exact hy hyΩ
  · rw [indicator_of_notMem hyΩ]
    exact h0

end ContDiffBump

end

end
