import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Transport

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))
  [ChartedSpace E3 (Quotient c d hcd a)]
  (e : BallChart 3 (𝓡 3) M) (e' : BallChart 3 (𝓡 3) (Quotient c d hcd a))
  (he : ∀ x ∈ Metric.closedBall (0 : E3) 2,
    ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
      e'.chart x = coreInclusion c d hcd a ⟨e.chart x, hx⟩)

private theorem ball_subset_closedBall_two {x : E3} (hx : x ∈ Metric.ball (0 : E3) 1) :
    x ∈ Metric.closedBall (0 : E3) 2 :=
  Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hx)

include he in
theorem preimage_coreInclusion_retained_ball :
    coreInclusion c d hcd a ⁻¹' (e'.chart '' Metric.ball 0 1) =
      {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.ball 0 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    rw [hmap] at hzx
    have hh := coreInclusion_injective c d hcd a hzx
    exact ⟨z, hz, congrArg (fun y : c.DoublePunctured d => y.val) hh⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩

include he in
theorem preimage_bandInclusion_retained_ball
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    bandInclusion c d hcd a ⁻¹' (e'.chart '' Metric.ball 0 1) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p
  rintro ⟨z, hz, hzp⟩
  obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
  rw [hmap] at hzp
  obtain ⟨⟨b, w⟩, _, hbw⟩ := (bandInclusion_eq_coreInclusion_iff c d hcd a p ⟨e.chart z, hz'⟩).mp hzp.symm
  have hbw' := congrArg (fun y : c.DoublePunctured d => y.val) hbw
  cases b
  · exact havoid z (ball_subset_closedBall_two hz) (Or.inl
      ⟨w, Metric.sphere_subset_closedBall w.property, hbw'⟩)
  · exact havoid z (ball_subset_closedBall_two hz) (Or.inr
      ⟨a w, Metric.sphere_subset_closedBall (a w).property, hbw'⟩)

include he in
theorem retained_ball_eq_coreInclusion_image :
    e'.chart '' Metric.ball 0 1 =
      coreInclusion c d hcd a '' {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.ball 0 1} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨⟨e.chart z, hz'⟩, ⟨z, hz, rfl⟩, hmap.symm⟩
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩


include he in
theorem preimage_coreInclusion_retained_closedBall :
    coreInclusion c d hcd a ⁻¹' (e'.chart '' Metric.closedBall 0 1) =
      {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.closedBall 0 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    rw [hmap] at hzx
    have hh := coreInclusion_injective c d hcd a hzx
    exact ⟨z, hz, congrArg (fun y : c.DoublePunctured d => y.val) hh⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩

include he in
theorem preimage_bandInclusion_retained_closedBall
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    bandInclusion c d hcd a ⁻¹' (e'.chart '' Metric.closedBall 0 1) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p
  rintro ⟨z, hz, hzp⟩
  obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
  rw [hmap] at hzp
  obtain ⟨⟨b, w⟩, _, hbw⟩ := (bandInclusion_eq_coreInclusion_iff c d hcd a p ⟨e.chart z, hz'⟩).mp hzp.symm
  have hbw' := congrArg (fun y : c.DoublePunctured d => y.val) hbw
  cases b
  · exact havoid z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz) (Or.inl
      ⟨w, Metric.sphere_subset_closedBall w.property, hbw'⟩)
  · exact havoid z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz) (Or.inr
      ⟨a w, Metric.sphere_subset_closedBall (a w).property, hbw'⟩)

end DifferentialGeometry.Topology.SelfAttachment
