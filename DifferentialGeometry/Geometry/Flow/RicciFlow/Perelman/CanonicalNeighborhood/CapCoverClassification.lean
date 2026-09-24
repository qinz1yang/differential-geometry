import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCover
import DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapGluing

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem nonempty_positiveComponent_of_ball_cap_cover
    {K : Set M} (B : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hB : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (cap : CapCore K)
    (hcover : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K = univ) :
    Nonempty (PositiveComponent (univ : Set M)) := by
  have hBK : IsConnected (B '' Metric.closedBall (0 : ThreeSpace) 1) :=
    capCore_isConnected_image_closedBall B hB
  have hK := cap.isConnected_carrier
  have hclosedK : IsClosed K := cap.isCompact_carrier.isClosed
  have hmeet : (B '' Metric.closedBall (0 : ThreeSpace) 1 ∩ K).Nonempty := by
    by_contra hn
    have hdisj : Disjoint (B '' Metric.closedBall (0 : ThreeSpace) 1) K :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)
    have heq : (B '' Metric.closedBall (0 : ThreeSpace) 1)ᶜ = K := by
      ext x
      constructor
      · intro hx
        have hh : x ∈ B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K := hcover.symm ▸ Set.mem_univ x
        exact hh.resolve_left hx
      · intro hx hxb
        exact Set.disjoint_left.mp hdisj hxb hx
    have hopen : IsOpen (B '' Metric.closedBall (0 : ThreeSpace) 1) := by
      rw [← isClosed_compl_iff, heq]
      exact hclosedK
    have hclosed : IsClosed (B '' Metric.closedBall (0 : ThreeSpace) 1) :=
      ((isCompact_closedBall (0 : ThreeSpace) 1).image_of_continuousOn
        (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
    have hfront : frontier (B '' Metric.closedBall (0 : ThreeSpace) 1) = ∅ :=
      IsClopen.frontier_eq ⟨hclosed, hopen⟩
    have he := B.image_frontier_of_isCompact (isCompact_closedBall (0 : ThreeSpace) 1) hB
    rw [frontier_closedBall _ one_ne_zero, hfront] at he
    have hz : (EuclideanSpace.single 0 1 : ThreeSpace) ∈ Metric.sphere 0 1 := by simp
    have hmem := Set.mem_image_of_mem B hz
    rw [he] at hmem
    exact hmem
  let _ : PreconnectedSpace M := ⟨hcover ▸ (hBK.union hmeet hK).isPreconnected⟩
  cases cap with
  | ball A hA hK =>
    obtain ⟨e, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover
        A B hA hB (hK.symm ▸ hcover)
    exact ⟨positiveComponentOfDiffeomorphSphereThree e.symm⟩
  | projective Z pr b hb F hF hK =>
    have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    rcases DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover
      pr.quotient pr.isLocalDiffeomorph pr.onto pr.fibers b F B hb1 hF hB
      (hK.symm ▸ hcover) with ⟨e, _⟩ | ⟨e, _⟩
    · exact ⟨positiveComponentOfDiffeomorphSphereThree e.symm⟩
    · exact ⟨positiveComponentOfDiffeomorphProjective Z pr e.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
