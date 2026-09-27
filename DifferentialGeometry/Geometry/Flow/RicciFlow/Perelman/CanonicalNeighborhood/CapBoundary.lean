import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CylinderBoundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.exists_boundary_diffeomorph_of_core_ball_chart
    (cap : LocalCap S eps x t U)
    (A : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hA : Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (hcore : A '' Metric.closedBall (0 : ThreeSpace) 1 = cap.core.carrier) :
    ∃ e : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
      (∀ q, A (e q) = cap.tube_map (q, 0)) ∧
      (∀ q, cap.tube_map (e.symm q, 0) = A q) := by
  let _ : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
  apply DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_sphere_chart_and_cylinder_boundary
    A cap.tube_map (Metric.sphere_subset_closedBall.trans hA)
    (fun q => cap.tube_domain ⟨mem_univ q, le_rfl, zero_le_one⟩)
  have hclosed : IsClosed (A '' Metric.closedBall (0 : ThreeSpace) 1) :=
    hcore.symm ▸ cap.core.compact.isClosed
  have hfront := A.toOpenPartialHomeomorph.image_frontier_of_subset_source hA
    Metric.isClosed_closedBall hclosed
  rw [frontier_closedBall _ one_ne_zero] at hfront
  change A '' Metric.sphere (0 : ThreeSpace) 1 =
    frontier (A '' Metric.closedBall (0 : ThreeSpace) 1) at hfront
  rw [hcore] at hfront
  rw [hfront, ← cap.inner_boundary]
  ext y
  constructor
  · rintro ⟨⟨q, a⟩, ha, rfl⟩
    have ha0 : a = 0 := ha.2
    exact ⟨q, by rw [ha0]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨mem_univ q, rfl⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
