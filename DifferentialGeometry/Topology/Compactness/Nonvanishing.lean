import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Continuity

set_option autoImplicit false
open Set
namespace Poincare.Topology
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]

theorem exists_pos_lt_norm_of_isCompact {f : X → E} {K : Set X} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hn : ∀ x ∈ K, f x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ < ‖f x‖ := by
  by_cases he : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn he hf.norm
    have hp : 0 < ‖f x‖ := norm_pos_iff.mpr (hn x hx)
    exact ⟨‖f x‖ / 2, half_pos hp, fun y hy => (half_lt_self hp).trans_le (hmin hy)⟩
  · exact ⟨1,zero_lt_one,fun x hx => (he ⟨x,hx⟩).elim⟩

end Poincare.Topology
