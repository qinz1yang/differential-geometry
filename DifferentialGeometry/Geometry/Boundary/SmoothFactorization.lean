import DifferentialGeometry.Geometry.Boundary.ChartTangent
import DifferentialGeometry.Geometry.Boundary.LevelComponents

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem boundary_extChartAt_eq_projE (x y : BoundaryManifold I M)
    (hy : y.1 ∈ (chartAt H x.1).source) :
    extChartAt hI.boundaryI x y = hI.projE (extChartAt I x.1 y.1) := by
  rw [← modelBoundaryParam_extChartAt_boundary x y hy]
  change _ = hI.projE (I (hI.inclH (hI.boundaryI.symm (extChartAt hI.boundaryI x y))))
  rw [hI.proj_inclH_compat]
  exact (hI.boundaryI.toHomeomorph.right_inv _).symm

variable {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {J : ModelWithCorners ℝ F G}

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_boundaryInclusion_comp_iff
    {f : N → BoundaryManifold I M} {s : Set N} {x : N} :
    ContMDiffWithinAt J I ∞ (boundaryInclusion I M ∘ f) s x ↔
      ContMDiffWithinAt J hI.boundaryI ∞ f s x := by
  constructor
  · intro hf
    have hc : ContinuousWithinAt f s x := tendsto_subtype_rng.mpr hf.continuousWithinAt
    have hd := (contMDiffWithinAt_iff_target.mp hf).2
    have hp : ContMDiffWithinAt J 𝓘(ℝ, hI.boundaryE) ∞
        (hI.projE ∘ (extChartAt I (f x).1 ∘ (boundaryInclusion I M ∘ f))) s x :=
      hI.projE_contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hd
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨hc, hp.congr_of_eventuallyEq ?_ ?_⟩
    · filter_upwards [hf.continuousWithinAt.preimage_mem_nhdsWithin
        ((chartAt H (f x).1).open_source.mem_nhds (mem_chart_source H (f x).1))] with y hy
      exact boundary_extChartAt_eq_projE (f x) (f y) hy
    · exact boundary_extChartAt_eq_projE (f x) (f x) (mem_chart_source H (f x).1)
  · intro hf
    exact boundaryInclusion_contMDiff.contMDiffAt.comp_contMDiffWithinAt x hf

theorem contMDiff_boundaryInclusion_comp_iff {f : N → BoundaryManifold I M} :
    ContMDiff J I ∞ (boundaryInclusion I M ∘ f) ↔ ContMDiff J hI.boundaryI ∞ f := by
  simp only [ContMDiff, ContMDiffAt, contMDiffWithinAt_boundaryInclusion_comp_iff]

theorem contMDiffWithinAt_boundaryLevelInclusion_comp_iff
    (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    {f : N → boundaryLevel u a b hab hu hboundary} {s : Set N} {x : N} :
    ContMDiffWithinAt J I ∞ (fun y ↦ (f y).1.1) s x ↔
      ContMDiffWithinAt J hI.boundaryI ∞ f s x := by
  change ContMDiffWithinAt J I ∞ (boundaryInclusion I M ∘ (Subtype.val ∘ f)) s x ↔ _
  rw [contMDiffWithinAt_boundaryInclusion_comp_iff, ContMDiffWithinAt.subtypeVal_comp_iff]

theorem contMDiff_boundaryLevelInclusion_comp_iff
    (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    {f : N → boundaryLevel u a b hab hu hboundary} :
    ContMDiff J I ∞ (fun y ↦ (f y).1.1) ↔ ContMDiff J hI.boundaryI ∞ f := by
  simp only [ContMDiff, ContMDiffAt, contMDiffWithinAt_boundaryLevelInclusion_comp_iff]

end DifferentialGeometry.Geometry.Boundary
