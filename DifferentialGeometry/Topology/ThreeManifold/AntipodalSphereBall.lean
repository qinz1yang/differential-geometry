import DifferentialGeometry.Topology.ThreeManifold.SphereBallAvoidingPoint
import DifferentialGeometry.Topology.Connected.InvolutionSeparation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem exists_ball_chart_disjoint_antipodal_of_sphere_embedding
    (e : S2 → S3) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hdisj : Disjoint (range e) (range (fun x => -(e x)))) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧ B '' sphere (0 : E3) 1 = range e ∧
      Disjoint (B '' closedBall (0 : E3) 1)
        ((Neg.neg : S3 → S3) '' (B '' closedBall (0 : E3) 1)) := by
  let z : S2 := DifferentialGeometry.Topology.sphereTwoNorth
  let p : S3 := -(e z)
  have hp : p ∉ range e := fun hx => hdisj.le_bot ⟨hx, z, rfl⟩
  obtain ⟨B, hB, hBs, hpB⟩ := exists_ball_chart_of_sphere_embedding_avoiding_point e he p hp
  let K := B '' closedBall (0 : E3) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hfront : frontier K = range e := by
    have hh := B.image_frontier_of_isCompact (isCompact_closedBall (0 : E3) 1) hB
    rw [frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm.trans hBs
  let h := (DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph
    (E := E4) (n := 3)).toHomeomorph
  have hother : IsPreconnected (range (fun x => -(e x))) := by
    let : PreconnectedSpace S2 := Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) 0 1)
    exact (isPreconnected_range (h.continuous.comp he.contMDiff.continuous))
  have hcover : range (fun x => -(e x)) ⊆ interior K ∪ Kᶜ := by
    intro y hy
    have hf : y ∈ (frontier K)ᶜ := by
      rw [hfront]
      exact fun hx => hdisj.le_bot ⟨hx, hy⟩
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hf
  have hout : range (fun x => -(e x)) ⊆ Kᶜ := by
    rcases hother.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with hi | ho
    · exact False.elim (hpB (interior_subset (hi (mem_range_self z))))
    · exact ho
  have havoid : Disjoint K (h '' frontier K) := by
    rw [hfront]
    apply disjoint_left.mpr
    rintro y hy ⟨v, ⟨x, rfl⟩, rfl⟩
    exact hout (mem_range_self x) hy
  have hconn : IsPreconnected K := (convex_closedBall (0 : E3) 1).isPreconnected.image
    B (B.contMDiffOn_toFun.continuousOn.mono hB)
  refine ⟨B, hB, hBs, ?_⟩
  exact DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier
    h (fun x => neg_neg x) hK.isClosed hconn (hfront.symm ▸ range_nonempty e) havoid

end DifferentialGeometry.Topology.ThreeManifold
