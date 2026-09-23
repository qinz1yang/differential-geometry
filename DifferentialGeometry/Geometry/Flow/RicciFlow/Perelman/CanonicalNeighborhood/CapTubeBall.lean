import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CapCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapBoundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarDepth

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.exists_ball_chart_eqOn_tube_neighborhood_of_core_ball_chart
    (cap : LocalCap S eps x t U)
    (A : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hA : Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (hcore : A '' Metric.closedBall (0 : ThreeSpace) 1 = cap.core.carrier) :
    ∃ B : PartialDiffeomorph I3 I3 ThreeSpace M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source ∧
      B '' Metric.closedBall (0 : ThreeSpace) 1 = U ∧
      ∃ F : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
        F '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
        (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1, B ((1 / 2 : ℝ) • z) = A (F z)) ∧
        (∀ q : Sphere 2, ∀ a ∈ Icc (0 : ℝ) 1,
          B (((a + 1) / 2) • (q : ThreeSpace)) = cap.tube_map (q, a)) ∧
        ∃ V : Set (Sphere 2 × ℝ), IsOpen V ∧ univ ×ˢ Icc (0 : ℝ) 1 ⊆ V ∧
          EqOn (fun q => B (((q.2 + 1) / 2) • (q.1 : ThreeSpace))) cap.tube_map V := by
  have hboundary : A '' Metric.sphere (0 : ThreeSpace) 1 =
      range (fun q : Sphere 2 => cap.tube_map (q, 0)) := by
    obtain ⟨η, hη, hηi⟩ := cap.exists_boundary_diffeomorph_of_core_ball_chart A hA hcore
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨η.symm ⟨z, hz⟩, hηi ⟨z, hz⟩⟩
    · rintro ⟨q, rfl⟩
      exact ⟨η q, (η q).property, hη q⟩
  obtain ⟨B, hBs, hBU, F, hF, hcoreMap, htubeMap, hneighborhood⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods A cap.tube_map
      hA cap.tube_domain hboundary (fun q a ha hm =>
        (cap.tube_map_mem_core_iff ha).mp (hcore ▸ hm))
  refine ⟨B, hBs, ?_, F, hF, hcoreMap, htubeMap, hneighborhood⟩
  rw [hBU, hcore, cap.tube_eq, ← cap.union_eq]

theorem LocalCap.exists_ball_chart_of_core_ball_chart
    (cap : LocalCap S eps x t U)
    (A : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hA : Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (hcore : A '' Metric.closedBall (0 : ThreeSpace) 1 = cap.core.carrier) :
    ∃ B : PartialDiffeomorph I3 I3 ThreeSpace M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source ∧
      B '' Metric.closedBall (0 : ThreeSpace) 1 = U ∧
      ∃ F : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
        F '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
        (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1, B ((1 / 2 : ℝ) • z) = A (F z)) ∧
        ∀ q : Sphere 2, ∀ a ∈ Icc (0 : ℝ) 1,
          B (((a + 1) / 2) • (q : ThreeSpace)) = cap.tube_map (q, a) := by
  obtain ⟨B, hBs, hBU, F, hF, hcoreMap, htubeMap, _⟩ :=
    cap.exists_ball_chart_eqOn_tube_neighborhood_of_core_ball_chart A hA hcore
  exact ⟨B, hBs, hBU, F, hF, hcoreMap, htubeMap⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
