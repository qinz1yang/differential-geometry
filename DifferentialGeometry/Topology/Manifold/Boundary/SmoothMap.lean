import DifferentialGeometry.Geometry.Boundary.Metric.Induced

open Set Function Filter Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Boundary

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem extChartAt_boundary_eq_proj (p q : BoundaryManifold I M)
    (hq : (q : M) ∈ (chartAt H (p : M)).source) :
    extChartAt hI.boundaryI p q = hI.projE (extChartAt I (p : M) (q : M)) := by
  let : Nonempty hI.boundaryH := ⟨chartAt hI.boundaryH p p⟩
  have hc : chartAt hI.boundaryH p = BoundaryManifold.boundaryChart (I := I) p :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart p
  change hI.boundaryI (chartAt hI.boundaryH p q) = hI.projE (I (chartAt H (p : M) (q : M)))
  rw [hc, ← BoundaryManifold.inclH_boundaryChart_apply p q hq]
  exact (hI.proj_inclH_compat _).symm

variable {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace G X]
  {J : ModelWithCorners ℝ F G}

theorem contMDiffWithinAt_boundary_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M} {s : Set X} {x : X} :
    ContMDiffWithinAt J hI.boundaryI k f s x ↔
      ContMDiffWithinAt J I k (fun y => (f y : M)) s x := by
  constructor
  · intro h
    exact ((boundaryInclusion_contMDiff (I := I) (M := M)).of_le hk).contMDiffAt.comp_contMDiffWithinAt x h
  · intro h
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨IsInducing.subtypeVal.continuousWithinAt_iff.mpr h.continuousWithinAt, ?_⟩
    have hcoord := (contMDiffWithinAt_iff_target.mp h).2
    have hproj := (hI.projE_contDiff.contMDiff.of_le hk).contMDiffAt.comp_contMDiffWithinAt x hcoord
    apply hproj.congr_of_eventuallyEq
    · have hevent : ∀ᶠ y in 𝓝[s] x, (f y : M) ∈ (chartAt H (f x : M)).source :=
        h.continuousWithinAt ((chartAt H (f x : M)).open_source.mem_nhds (mem_chart_source _ _))
      filter_upwards [hevent] with y hy
      exact extChartAt_boundary_eq_proj (f x) (f y) hy
    · exact extChartAt_boundary_eq_proj (f x) (f x) (mem_chart_source _ _)


theorem contMDiffAt_boundary_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M} {x : X} :
    ContMDiffAt J hI.boundaryI k f x ↔ ContMDiffAt J I k (fun y => (f y : M)) x :=
  contMDiffWithinAt_boundary_iff hk


theorem contMDiffOn_boundary_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M} {s : Set X} :
    ContMDiffOn J hI.boundaryI k f s ↔ ContMDiffOn J I k (fun y => (f y : M)) s := by
  exact forall₂_congr fun _ _ => contMDiffWithinAt_boundary_iff hk


theorem contMDiff_boundary_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M} :
    ContMDiff J hI.boundaryI k f ↔ ContMDiff J I k (fun y => (f y : M)) := by
  exact forall_congr' fun _ => contMDiffAt_boundary_iff hk

end Poincare.Manifold.Boundary
