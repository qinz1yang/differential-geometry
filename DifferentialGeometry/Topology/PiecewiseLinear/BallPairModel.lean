import DifferentialGeometry.Topology.PiecewiseLinear.BallPair
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coneSet_eq_iUnion_segment {p : E} {X : Set E} (hX : X.Nonempty) :
    coneSet p X = ⋃ z ∈ X, segment ℝ p z := by
  ext x
  constructor
  · intro hx
    rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · obtain ⟨z, hz⟩ := hX
      exact mem_iUnion₂.mpr ⟨z, hz, left_mem_segment ℝ x z⟩
    · refine mem_iUnion₂.mpr ⟨z, hz, ?_⟩
      rw [segment_eq_image]
      exact ⟨s, ⟨hs.le, hs'⟩, (add_smul_sub_eq_combo p z s).symm⟩
  · intro hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
    rw [segment_eq_image] at hxz
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hxz
    rcases eq_or_lt_of_le hs0 with rfl | hs
    · simpa only [sub_zero, one_smul, zero_smul, add_zero] using apex_mem_coneSet p X
    · exact Or.inr ⟨z, hz, s, hs, hs1, (add_smul_sub_eq_combo p z s).symm⟩

theorem coneSet_pair_eq_union_segment (p a b : E) :
    coneSet p ({a, b} : Set E) = segment ℝ p a ∪ segment ℝ p b := by
  rw [coneSet_eq_iUnion_segment ⟨a, mem_insert a {b}⟩, biUnion_pair]

theorem isPLBallPair_coneSet_arc [FiniteDimensional ℝ E] {m : ℕ} {p : E}
    {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hJL : J.faces ⊆ L.faces) (hsph : IsPLSphere m L.space) {a b : E} (hab : a ≠ b)
    (hJ : J.space = {a, b}) :
    IsPLBallPair m 1 (coneSet p L.space) (segment ℝ p a ∪ segment ℝ p b) := by
  have h0 : IsPLSphere 0 J.space := isPLSphere_zero_iff.mpr ⟨a, b, hab, hJ⟩
  have hpair := isPLBallPair_coneSet_of_isPLSphere hL hJL hsph h0
  rwa [hJ, coneSet_pair_eq_union_segment] at hpair

end DifferentialGeometry.Topology.PiecewiseLinear
