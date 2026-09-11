import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Manifold Topology Interval

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem ae_mdifferentiableAt_of_extChartAt
    {a b : ℝ} {gamma : ℝ → M} (p : M)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) a b)
    (hsrc : MapsTo gamma (uIcc a b) (chartAt H p).source) :
    ∀ᵐ r ∂volume.restrict (uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
  have hmaps : MapsTo ((extChartAt I p) ∘ gamma) (uIcc a b)
      (extChartAt I p).target := by
    intro r hr
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrc hr)
  have hcont : ContinuousOn gamma (uIcc a b) := by
    have h := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    refine h.congr ?_
    intro r hr
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hsrc hr)).symm
  have hmem : ∀ᵐ r ∂volume.restrict (uIcc a b), r ∈ Ioo (min a b) (max a b) := by
    rw [uIcc, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdiff : ∀ᵐ r ∂volume.restrict (uIcc a b),
      r ∈ uIcc a b → DifferentiableAt ℝ ((extChartAt I p) ∘ gamma) r :=
    ae_mono Measure.restrict_le_self
      hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff, hmem] with r hr hri
  have hcc : r ∈ uIcc a b := ⟨hri.1.le, hri.2.le⟩
  apply (mdifferentiableAt_iff_target_of_mem_source (hsrc hcc)).mpr
  refine ⟨(hcont r hcc).continuousAt (Icc_mem_nhds hri.1 hri.2), ?_⟩
  exact mdifferentiableAt_iff_differentiableAt.mpr (hr hcc)

end AbsolutelyContinuousOnInterval
