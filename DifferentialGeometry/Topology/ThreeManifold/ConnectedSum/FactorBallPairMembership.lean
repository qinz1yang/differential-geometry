import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FactorBallPair
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e c d : OrientedBallChart N.toClosedOrientedManifold)
  (a : BoundaryAttachment)
  (c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)
  (hd' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    d'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩)

include hc' in
theorem inr_mem_chart_closedBall_iff (x : e.Punctured) :
    inr m.toBallChart e.toBallChart a.val.toHomeomorph x ∈ c'.chart '' Metric.closedBall 0 1 ↔
      x.val ∈ c.chart '' Metric.closedBall 0 1 := by
  constructor
  · rintro ⟨z, hz, heq⟩
    obtain ⟨hz', hmap⟩ := hc' z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    rw [hmap] at heq
    exact ⟨z, hz, congrArg (fun x : e.Punctured => x.val)
      (inr_injective m.toBallChart e.toBallChart a.val.toHomeomorph heq)⟩
  · rintro ⟨z, hz, heq⟩
    obtain ⟨hz', hmap⟩ := hc' z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    exact ⟨z, hz, hmap.trans (congrArg (inr m.toBallChart e.toBallChart a.val.toHomeomorph) (Subtype.ext heq))⟩

include hc' in
theorem inl_not_mem_chart_closedBall
    (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
    (x : m.Punctured) : inl m.toBallChart e.toBallChart a.val.toHomeomorph x ∉ c'.chart '' Metric.closedBall 0 1 := by
  rintro ⟨z, hz, heq⟩
  obtain ⟨hz', hmap⟩ := hc' z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
  rw [hmap] at heq
  obtain ⟨w, _, heq'⟩ := (inl_eq_inr_iff m.toBallChart e.toBallChart a.val.toHomeomorph x ⟨c.chart z, hz'⟩).mp heq.symm
  have hv := congrArg (fun x : e.Punctured => x.val) heq'
  exact Set.disjoint_left.mp hec
    ⟨a.val w, Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall (a.val w).property), hv⟩
    ⟨z, Metric.closedBall_subset_closedBall (by norm_num) hz, rfl⟩

include hc' hd' in
theorem interiorRight_mem_pairCore_iff (x : e.interior) :
    interiorRight m.toBallChart e.toBallChart a.val x ∈ SelfAttachment.coreInterior c'.toBallChart d'.toBallChart ↔
      x.val ∈ SelfAttachment.coreInterior c.toBallChart d.toBallChart := by
  change ¬ (_ ∈ c'.chart '' Metric.closedBall 0 1 ∨ _ ∈ d'.chart '' Metric.closedBall 0 1) ↔
    ¬ (x.val ∈ c.chart '' Metric.closedBall 0 1 ∨ x.val ∈ d.chart '' Metric.closedBall 0 1)
  exact not_congr (or_congr
    (inr_mem_chart_closedBall_iff m e c a c' hc' (e.interiorToPunctured x))
    (inr_mem_chart_closedBall_iff m e d a d' hd' (e.interiorToPunctured x)))

end DifferentialGeometry.Topology.ConnectedSumQuotient
