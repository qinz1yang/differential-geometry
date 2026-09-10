import DifferentialGeometry.Geometry.Boundary.ModelCoordinates
import DifferentialGeometry.Geometry.Boundary.Metric.Induced
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem modelBoundaryParam_extChartAt_boundary (x y : BoundaryManifold I M)
    (hy : y.1 ∈ (chartAt H x.1).source) :
    modelBoundaryParam I (extChartAt hI.boundaryI x y) = extChartAt I x.1 y.1 := by
  let : Nonempty hI.boundaryH := ⟨hI.boundaryI.symm 0⟩
  have hchart : chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
  change I (hI.inclH (hI.boundaryI.symm (hI.boundaryI (chartAt hI.boundaryH x y)))) =
    I (chartAt H x.1 y.1)
  rw [hI.boundaryI.left_inv, hchart]
  exact congrArg I (BoundaryManifold.inclH_boundaryChartFun_apply (I := I) hy)

set_option backward.isDefEq.respectTransparency false in
theorem boundaryInclusionMfderiv_model (x : BoundaryManifold I M)
    (w : TangentSpace hI.boundaryI x) :
    tangentSpaceModelContinuousLinearEquiv (I := I) x.1 (boundaryInclusionMfderiv x w) =
      fderiv ℝ (modelBoundaryParam I) (extChartAt hI.boundaryI x x)
        (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x w) := by
  have hinc : MDifferentiableAt hI.boundaryI I (boundaryInclusion I M) x :=
    (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x.1) x.1 :=
    mdifferentiableAt_extChartAt (mem_chart_source H x.1)
  have hbc : MDifferentiableAt hI.boundaryI 𝓘(ℝ, hI.boundaryE)
      (extChartAt hI.boundaryI x) x := mdifferentiableAt_extChartAt (mem_chart_source _ x)
  have hparam : MDifferentiableAt 𝓘(ℝ, hI.boundaryE) 𝓘(ℝ, E)
      (modelBoundaryParam I) (extChartAt hI.boundaryI x x) :=
    (hI.I_inclH_boundaryI_symm_contDiff.differentiable (by simp) _).mdifferentiableAt
  have heq : (extChartAt I x.1 ∘ boundaryInclusion I M) =ᶠ[𝓝 x]
      (modelBoundaryParam I ∘ extChartAt hI.boundaryI x) := by
    filter_upwards [(boundaryInclusion_contMDiff (I := I) (M := M)).continuous.continuousAt.preimage_mem_nhds
      ((chartAt H x.1).open_source.mem_nhds (mem_chart_source H x.1))] with y hy
    exact (modelBoundaryParam_extChartAt_boundary x y hy).symm
  have hd := heq.mfderiv_eq (I := hI.boundaryI) (I' := 𝓘(ℝ, E))
  dsimp only [boundaryInclusion] at hd hinc
  rw [mfderiv_comp x hc hinc, mfderiv_comp x hparam hbc,
    mfderiv_extChartAt_self, mfderiv_extChartAt_self, mfderiv_eq_fderiv,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] at hd
  exact congrArg (fun L : TangentSpace hI.boundaryI x →L[ℝ] E ↦ L w) hd

end DifferentialGeometry.Geometry.Boundary
