import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem IsLocalMin.mvfderiv_eq_zero {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x) (hx : I.IsInteriorPoint x) : mvfderiv I f x = 0 := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  swap
  · simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
      ContinuousLinearMap.comp_zero]
  have hmin_chart : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hmin' : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by
      simpa only [mfld_simps] using hmin
    exact hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  rw [hf.mvfderiv, fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)]
  have heq : writtenInExtChartAt I 𝓘(ℝ, ℝ) x f = f ∘ (extChartAt I x).symm := by
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
    rfl
  rw [heq]
  exact hmin_chart.fderiv_eq_zero

theorem IsLocalMax.mvfderiv_eq_zero {f : M → ℝ} {x : M}
    (hmax : IsLocalMax f x) (hx : I.IsInteriorPoint x) : mvfderiv I f x = 0 := by
  have h := hmax.neg.mvfderiv_eq_zero hx
  change mvfderiv I (-f) x = 0 at h
  simpa only [mvfderiv_neg, neg_eq_zero] using h
