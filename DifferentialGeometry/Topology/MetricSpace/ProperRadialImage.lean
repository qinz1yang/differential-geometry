import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

open Set Metric Filter

namespace ProperSpace

theorem of_surjective_dist_basepoint_eq {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [ProperSpace X] (f : X → Y) (hf : Continuous f)
    (hsurj : Function.Surjective f) (p : X)
    (hradial : ∀ x, dist (f x) (f p) = dist x p) : ProperSpace Y := by
  apply ProperSpace.of_seq_closedBall (x := f p) (r := fun R : ℝ => R) tendsto_id
  apply Eventually.of_forall
  intro R
  have heq : f '' closedBall p R = closedBall (f p) R := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_closedBall, hradial] using hx
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, by simpa only [mem_closedBall, hradial] using hy, rfl⟩
  rw [← heq]
  exact (isCompact_closedBall p R).image hf

end ProperSpace
