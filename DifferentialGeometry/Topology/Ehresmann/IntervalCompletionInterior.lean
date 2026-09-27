import DifferentialGeometry.Topology.Ehresmann.IntervalCompletionSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {M : Type*} [TopologicalSpace M]

def intervalCompletionInterior {u : M → ℝ} (hu : Continuous u) (a b : ℝ) :
    OpenPartialHomeomorph M (IntervalCompletionSpace u a b) where
  toFun := intervalCompletionInclusion u a b
  invFun := fun q ↦ q.1.1
  source := u ⁻¹' Ioo a b
  target := intervalCompletionHeight u a b ⁻¹' Ioo a b
  map_source' := fun _ hx ↦ hx
  map_target' := by
    intro q hq
    rcases q.2 with h | ⟨_, ht⟩ | ⟨_, ht⟩
    · change u q.1.1 ∈ Ioo a b
      exact h ▸ (show q.1.2 ∈ Ioo a b from hq)
    · exact (not_lt_of_ge ht hq.1).elim
    · exact (not_lt_of_ge ht hq.2).elim
  left_inv' := fun _ _ ↦ rfl
  right_inv' := by
    intro q hq
    have heq : q.1.2 = u q.1.1 := by
      rcases q.2 with h | ⟨_, ht⟩ | ⟨_, ht⟩
      · exact h
      · exact (not_lt_of_ge ht hq.1).elim
      · exact (not_lt_of_ge ht hq.2).elim
    exact Subtype.ext (Prod.ext rfl heq.symm)
  open_source := isOpen_Ioo.preimage hu
  open_target := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
  continuousOn_toFun := ((continuous_id.prodMk hu).subtype_mk _).continuousOn
  continuousOn_invFun := (continuous_fst.comp continuous_subtype_val).continuousOn

end DifferentialGeometry.Topology.Ehresmann
