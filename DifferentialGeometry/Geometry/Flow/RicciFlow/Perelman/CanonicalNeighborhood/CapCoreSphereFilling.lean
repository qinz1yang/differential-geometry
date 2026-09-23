import DifferentialGeometry.Topology.ThreeManifold.SphereInsideBall
import DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapSphereFilling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem CapCore.exists_compact_side_of_sphere_embedding
    {U : Set M} (cap : CapCore U)
    (e : Sphere 2 → M) (he : IsSmoothEmbedding I2 I3 ∞ e)
    (hinside : range e ⊆ interior U) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
      frontier K = range e ∧ K ⊆ interior U := by
  cases cap with
  | ball C hC hcore =>
    have hCint : C '' Metric.ball (0 : ThreeSpace) 1 = interior U := by
      have h := C.toOpenPartialHomeomorph.image_interior_of_subset_source hC
      change C '' interior (closedBall (0 : ThreeSpace) 1) =
        interior (C '' closedBall (0 : ThreeSpace) 1) at h
      rw [interior_closedBall _ one_ne_zero, hcore] at h
      exact h
    obtain ⟨B, hB, hBs, hBin⟩ :=
      DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_inside_ball_of_sphere_embedding
        C hC e he (hCint.symm ▸ hinside)
    have hcompact : IsCompact (B '' closedBall (0 : ThreeSpace) 1) :=
      (isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)
    refine ⟨B '' closedBall (0 : ThreeSpace) 1, hcompact, ?_, ?_, hCint ▸ hBin⟩
    · apply B.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hB _ hcompact.isClosed
      rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]
    · rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB,
        frontier_closedBall _ one_ne_zero, hBs]
  | projective Z pr C hC F hF hcore =>
    have hp : IsLocalDiffeomorph (𝓡 3) I3 ∞ pr.quotient :=
      DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
        pr.quotient pr.smooth (fun x => (pr.local_diffeo x).injective) rfl
    obtain ⟨K, B, _, _, _, hcompact, hreg, hfront, hsubset⟩ :=
      DifferentialGeometry.Topology.ThreeManifold.exists_compact_side_inside_projective_cap_of_sphere_embedding
        pr.quotient hp pr.onto pr.fibers C F
        ((closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hC)
        hF e he (hcore.symm ▸ hinside)
    exact ⟨K, hcompact, hreg, hfront, hcore ▸ hsubset⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
