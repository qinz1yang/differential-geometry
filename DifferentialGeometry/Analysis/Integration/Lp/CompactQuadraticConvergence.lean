import DifferentialGeometry.Analysis.Integration.Lp.QuadraticConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.Bounded


noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal Topology

variable {P X : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [T2Space P]
  {μ : Measure P} [NormedAddCommGroup X] [NormedSpace ℝ X]

private local instance dualNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance dualNormedSpace : NormedSpace ℝ (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance bilinearNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance bilinearNormedSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem tendsto_setIntegral_quadratic_of_tendstoUniformlyOn_of_isCompact
    {K : Set P} (hK : IsCompact K)
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, ContinuousOn (B n) K) (hB₀ : ContinuousOn B₀ K)
    (hconv : TendstoUniformlyOn B B₀ atTop K)
    (u : ℕ → P → X) (u₀ : P → X)
    (hu : ∀ n, MemLp (u n) 2 (μ.restrict K)) (hu₀ : MemLp u₀ 2 (μ.restrict K))
    (htendsto : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu₀.toLp u₀))) :
    Tendsto (fun n => ∫ z in K, B n z (u n z) (u n z) ∂μ) atTop
      (𝓝 (∫ z in K, B₀ z (u₀ z) (u₀ z) ∂μ)) := by
  classical
  choose C hC using fun n => hK.exists_bound_of_continuousOn (hB n)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hB₀
  have hmeas (n : ℕ) (x y : X) :
      AEStronglyMeasurable (fun z => B n z x y) (μ.restrict K) :=
    (((hB n).clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hmeas₀ (x y : X) :
      AEStronglyMeasurable (fun z => B₀ z x y) (μ.restrict K) :=
    ((hB₀.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hbound (n : ℕ) : ∀ᵐ z ∂μ.restrict K, ‖B n z‖ ≤ C n := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hC n z hz
  have hbound₀ : ∀ᵐ z ∂μ.restrict K, ‖B₀ z‖ ≤ C₀ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hC₀ z hz
  have hconv' : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂μ.restrict K, ‖B n z - B₀ z‖ ≤ δ := by
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn z hz)
  have h := tendsto_integral_quadratic_of_tendsto B B₀ hmeas hmeas₀ C C₀
    hbound hbound₀ hconv' (fun n => (hu n).toLp (u n)) (hu₀.toLp u₀) htendsto
  have heq (n : ℕ) :
      (∫ z in K, B n z ((hu n).toLp (u n) z) ((hu n).toLp (u n) z) ∂μ) =
        ∫ z in K, B n z (u n z) (u n z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp] with z hz
    rw [hz]
  have heq₀ :
      (∫ z in K, B₀ z (hu₀.toLp u₀ z) (hu₀.toLp u₀ z) ∂μ) =
        ∫ z in K, B₀ z (u₀ z) (u₀ z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu₀.coeFn_toLp] with z hz
    rw [hz]
  simpa only [heq, heq₀] using h

end MeasureTheory
