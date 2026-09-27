import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem mfderiv_add_const_real {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => f y + b) x) =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (f + (fun _ : M => b)) x) = _
  erw [mfderiv_add hf mdifferentiableAt_const,mfderiv_const,add_zero]


theorem isCriticalPointAt_iff_of_eventuallyEq_add_const {f g : M → ℝ} {x : M} {b : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    IsCriticalPointAt I g x ↔ IsCriticalPointAt I f x := by
  exact Iff.of_eq (congrArg (fun L : E →L[ℝ] ℝ => L = 0)
    (h.mfderiv_eq.trans (mfderiv_add_const_real hf b)))

variable [IsManifold I ∞ M]


theorem chartHessianAt_eq_of_eventuallyEq_add_const {f g : M → ℝ} {x : M} {b : ℝ}
    (hx : I.IsInteriorPoint x) (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    chartHessianAt (fun z => g ((extChartAt I x).symm z)) (extChartAt I x x) =
      chartHessianAt (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x) := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hc : ContinuousAt c.symm (c x) :=
    c.symm.toOpenPartialHomeomorph.continuousOn.continuousAt
      (c.open_target.mem_nhds (c.map_source hxc))
  have hct : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    have hh : Tendsto c.symm (𝓝 (c x)) (𝓝 (c.symm (c x))) := hc
    exact (congrArg (fun y : M => Tendsto c.symm (𝓝 (c x)) (𝓝 y)) (c.left_inv hxc)).mp hh
  have hgerm : (fun z => g (c.symm z)) =ᶠ[𝓝 (c x)] (fun z => f (c.symm z) + b) :=
    h.comp_tendsto hct
  have hD := (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hconst : fderiv ℝ (fun z => f (c.symm z) + b) = fderiv ℝ (fun z => f (c.symm z)) :=
    funext fun z => fderiv_add_const b
  rw [hconst] at hD
  unfold chartHessianAt chartHessianBilinAt
  congr 1
  ext v w
  exact congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) hD


theorem isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
    {f g : M → ℝ} {x : M} {b : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hx : I.IsInteriorPoint x)
    (h : g =ᶠ[𝓝 x] (fun y => f y + b)) :
    IsNondegenerateCriticalPointAt I g x ↔ IsNondegenerateCriticalPointAt I f x := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_iff_of_eventuallyEq_add_const hf h,
    chartHessianAt_eq_of_eventuallyEq_add_const hx h]

end DifferentialGeometry.Morse
