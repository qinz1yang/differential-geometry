import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.RetainedBall

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e : OrientedBallChart N.toClosedOrientedManifold)
  (a : BoundaryAttachment)

theorem exists_orientedBallChart_pair_inr
    (c d : OrientedBallChart N.toClosedOrientedManifold)
    (hc : Disjoint (c.chart '' Metric.closedBall 0 2) (e.chart '' Metric.closedBall 0 1))
    (hd : Disjoint (d.chart '' Metric.closedBall 0 2) (e.chart '' Metric.closedBall 0 1))
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
        c'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩) ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
        d'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩) ∧
      Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2) := by
  obtain ⟨c', hc'⟩ := exists_orientedBallChart_inr m e a c (fun x hx => Set.disjoint_left.mp hc ⟨x, hx, rfl⟩)
  obtain ⟨d', hd'⟩ := exists_orientedBallChart_inr m e a d (fun x hx => Set.disjoint_left.mp hd ⟨x, hx, rfl⟩)
  refine ⟨c', d', hc', hd', Set.disjoint_left.mpr ?_⟩
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
  obtain ⟨hx', hcx⟩ := hc' x hx
  obtain ⟨hz', hdz⟩ := hd' z hz
  rw [hcx, hdz] at hzx
  have heq := congrArg (fun q : e.Punctured => q.val) (inr_injective m.toBallChart e.toBallChart a.val.toHomeomorph hzx)
  exact Set.disjoint_left.mp hcd ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩

variable (c : OrientedBallChart N.toClosedOrientedManifold)
  (c' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)

include hc' in
theorem chart_image_ball_eq_inr_image :
    c'.chart '' Metric.ball 0 1 =
      inr m.toBallChart e.toBallChart a.val.toHomeomorph ''
        {x : e.Punctured | x.val ∈ c.chart '' Metric.ball 0 1} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx', hmap⟩ := hc' x (Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hx))
    exact ⟨⟨c.chart x, hx'⟩, ⟨x, hx, rfl⟩, hmap.symm⟩
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    obtain ⟨hz', hmap⟩ := hc' z (Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hz))
    exact ⟨z, hz, hmap.trans (congrArg (inr m.toBallChart e.toBallChart a.val.toHomeomorph) (Subtype.ext hzx))⟩

end DifferentialGeometry.Topology.ConnectedSumQuotient
