import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [I.Boundaryless] [J.Boundaryless]

private theorem mdifferentiableAt_inverse_chart (p : M) {y : E}
    (hy : y ∈ (extChartAt I p).target) :
    MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm y := by
  simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
    (mdifferentiableWithinAt_extChartAt_symm (I := I) hy)

omit [J.Boundaryless] in
private theorem fderiv_fixed_chart_of_mdifferentiableAt
    (f : M → N) (p : M) (q : N) (x : M)
    (hx : x ∈ (extChartAt I p).source) (hfx : f x ∈ (extChartAt J q).source)
    (hf : MDifferentiableAt I J f x) :
    fderiv ℝ ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p x) =
      ((trivializationAt F (TangentSpace J) q).continuousLinearMapAt ℝ (f x)).comp
        ((mfderiv I J f x).comp ((trivializationAt E (TangentSpace I) p).symmL ℝ x)) := by
  have hxs : x ∈ (chartAt H p).source := by simpa only [extChartAt_source] using hx
  have hfqs : f x ∈ (chartAt H' q).source := by simpa only [extChartAt_source] using hfx
  have hφ := mdifferentiableAt_inverse_chart p ((extChartAt I p).map_source hx)
  have hψ := mdifferentiableAt_extChartAt (I := J) hfqs
  have hleft := (extChartAt I p).left_inv hx
  have hf' : MDifferentiableAt I J f ((extChartAt I p).symm (extChartAt I p x)) := by
    simpa only [hleft] using hf
  have hψ' : MDifferentiableAt J 𝓘(ℝ, F) (extChartAt J q)
      (f ((extChartAt I p).symm (extChartAt I p x))) := by simpa only [hleft] using hψ
  have hinner : MDifferentiableAt 𝓘(ℝ, E) J (f ∘ (extChartAt I p).symm)
      (extChartAt I p x) := hf'.comp _ hφ
  have hd := mfderiv_comp (extChartAt I p x) hψ' hinner
  have hdi := mfderiv_comp (extChartAt I p x) hf' hφ
  rw [hdi] at hd
  have hd' : fderiv ℝ ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p x) =
      (mfderiv J 𝓘(ℝ, F) (extChartAt J q) (f ((extChartAt I p).symm (extChartAt I p x)))).comp
        ((mfderiv I J f ((extChartAt I p).symm (extChartAt I p x))).comp
          (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (extChartAt I p x))) := by
    simpa only [mfderiv_eq_fderiv, Function.comp_apply] using! hd
  rw [hd']
  rw [hleft, ← TangentBundle.continuousLinearMapAt_trivializationAt hfqs]
  have hinv := TangentBundle.symmL_trivializationAt (I := I) hxs
  rw [I.range_eq_univ, mfderivWithin_univ] at hinv
  rw [← hinv]
  rfl

theorem mdifferentiableAt_iff_differentiableAt_fixed_chart
    (f : M → N) (p : M) (q : N) (x : M)
    (hx : x ∈ (extChartAt I p).source) (hfx : f x ∈ (extChartAt J q).source)
    (hc : ContinuousAt f x) :
    MDifferentiableAt I J f x ↔
      DifferentiableAt ℝ ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p x) := by
  have hxs : x ∈ (chartAt H p).source := by simpa only [extChartAt_source] using hx
  have hfqs : f x ∈ (chartAt H' q).source := by simpa only [extChartAt_source] using hfx
  have hφ := mdifferentiableAt_extChartAt (I := I) hxs
  have hφinv := mdifferentiableAt_inverse_chart p ((extChartAt I p).map_source hx)
  have hψ := mdifferentiableAt_extChartAt (I := J) hfqs
  have hψinv := mdifferentiableAt_inverse_chart q ((extChartAt J q).map_source hfx)
  have hleft := (extChartAt I p).left_inv hx
  constructor
  · intro hf
    have hf' : MDifferentiableAt I J f ((extChartAt I p).symm (extChartAt I p x)) := by
      simpa only [hleft] using hf
    have hψ' : MDifferentiableAt J 𝓘(ℝ, F) (extChartAt J q)
        (f ((extChartAt I p).symm (extChartAt I p x))) := by simpa only [hleft] using hψ
    have hinner : MDifferentiableAt 𝓘(ℝ, E) J (f ∘ (extChartAt I p).symm)
        (extChartAt I p x) := hf'.comp _ hφinv
    exact (hψ'.comp (extChartAt I p x) hinner).differentiableAt
  · intro hF
    have hFc := hF.mdifferentiableAt.comp x hφ
    have hψinv' : MDifferentiableAt 𝓘(ℝ, F) J (extChartAt J q).symm
        (((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p x)) := by
      simpa only [Function.comp_apply, hleft] using hψinv
    have hcomp := hψinv'.comp x hFc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hx,
      hc ((isOpen_extChartAt_source (I := J) q).mem_nhds hfx)] with y hy hyf
    simp only [Function.comp_apply, (extChartAt I p).left_inv hy,
      (extChartAt J q).left_inv hyf]

theorem fderiv_fixed_chart_eq_trivialization_comp_mfderiv
    (f : M → N) (p : M) (q : N) (x : M)
    (hx : x ∈ (extChartAt I p).source) (hfx : f x ∈ (extChartAt J q).source)
    (hc : ContinuousAt f x) :
    fderiv ℝ ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p x) =
      ((trivializationAt F (TangentSpace J) q).continuousLinearMapAt ℝ (f x)).comp
        ((mfderiv I J f x).comp ((trivializationAt E (TangentSpace I) p).symmL ℝ x)) := by
  by_cases hf : MDifferentiableAt I J f x
  · exact fderiv_fixed_chart_of_mdifferentiableAt f p q x hx hfx hf
  · have hF := mt (mdifferentiableAt_iff_differentiableAt_fixed_chart f p q x hx hfx hc).mpr hf
    rw [fderiv_zero_of_not_differentiableAt hF, mfderiv_zero_of_not_mdifferentiableAt hf]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

end DifferentialGeometry.Topology.Manifold
