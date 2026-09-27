import DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal Topology

variable {P X : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [T2Space P]
  {μ : Measure P} [NormedAddCommGroup X] [NormedSpace ℝ X]

private local instance domainDualNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance domainDualNormedSpace : NormedSpace ℝ (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance scalarBilinearNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance scalarBilinearNormedSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section General

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private local instance codomainMapNormedAddCommGroup : NormedAddCommGroup (Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance codomainMapNormedSpace : NormedSpace ℝ (Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedSpace

private local instance bilinearMapNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance bilinearMapNormedSpace : NormedSpace ℝ (X →L[ℝ] Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedSpace

theorem integrableOn_bilinear_of_continuousOn_of_isCompact
    [SecondCountableTopologyEither P Z]
    {K : Set P} (hK : IsCompact K)
    (B : P → X →L[ℝ] Y →L[ℝ] Z) (hB : ContinuousOn B K)
    {u : P → X} {v : P → Y}
    (hu : MemLp u 2 (μ.restrict K)) (hv : MemLp v 2 (μ.restrict K)) :
    IntegrableOn (fun z => B z (u z) (v z)) K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hB
  apply integrable_bilinear_of_apply_aestronglyMeasurable B
    (fun x y =>
      ((hB.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
        hK.measurableSet) (C := C) _ hu hv
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC z hz

end General

theorem tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact
    {K : Set P} (hK : IsCompact K)
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, ContinuousOn (B n) K) (hB₀ : ContinuousOn B₀ K)
    (hconv : TendstoUniformlyOn B B₀ atTop K)
    (u : ℕ → P → X) (u₀ v : P → X)
    (hu : ∀ n, MemLp (u n) 2 (μ.restrict K))
    (hu₀ : MemLp u₀ 2 (μ.restrict K)) (hv : MemLp v 2 (μ.restrict K))
    (htendsto : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu₀.toLp u₀))) :
    Tendsto (fun n => ∫ z in K, B n z (u n z) (v z) ∂μ) atTop
      (𝓝 (∫ z in K, B₀ z (u₀ z) (v z) ∂μ)) := by
  classical
  choose C hC using fun n => hK.exists_bound_of_continuousOn (hB n)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hB₀
  have hmeas (n : ℕ) (x y : X) :
      AEStronglyMeasurable (fun z => (B n z).flip x y) (μ.restrict K) :=
    (((hB n).clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hmeas₀ (x y : X) :
      AEStronglyMeasurable (fun z => (B₀ z).flip x y) (μ.restrict K) :=
    ((hB₀.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hbound (n : ℕ) : ∀ᵐ z ∂μ.restrict K, ‖(B n z).flip‖ ≤ C n := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    simpa only [ContinuousLinearMap.opNorm_flip] using hC n z hz
  have hbound₀ : ∀ᵐ z ∂μ.restrict K, ‖(B₀ z).flip‖ ≤ C₀ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    simpa only [ContinuousLinearMap.opNorm_flip] using hC₀ z hz
  have hconv' : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂μ.restrict K, ‖(B n z).flip - (B₀ z).flip‖ ≤ δ := by
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have heq : (B n z).flip - (B₀ z).flip = (B n z - B₀ z).flip := rfl
    rw [heq, ContinuousLinearMap.opNorm_flip]
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn z hz)
  have h := tendsto_integral_bilinear_of_weak
    (fun n z => (B n z).flip) (fun z => (B₀ z).flip)
    hmeas hmeas₀ C C₀ hbound hbound₀ hconv'
    (fun n => (hu n).toLp (u n)) (hu₀.toLp u₀) (hv.toLp v)
    (fun L => L.continuous.continuousAt.tendsto.comp htendsto)
  have heq (n : ℕ) :
      (∫ z in K, (B n z).flip (hv.toLp v z) ((hu n).toLp (u n) z) ∂μ) =
        ∫ z in K, B n z (u n z) (v z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp, hv.coeFn_toLp] with z huz hvz
    rw [huz, hvz, ContinuousLinearMap.flip_apply]
  have heq₀ :
      (∫ z in K, (B₀ z).flip (hv.toLp v z) (hu₀.toLp u₀ z) ∂μ) =
        ∫ z in K, B₀ z (u₀ z) (v z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu₀.coeFn_toLp, hv.coeFn_toLp] with z huz hvz
    rw [huz, hvz, ContinuousLinearMap.flip_apply]
  simpa only [heq, heq₀] using h

end MeasureTheory
