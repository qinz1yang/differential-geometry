import DifferentialGeometry.Geometry.Metric.Isometry.Topology
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Covering.Basic

namespace IsometryEquiv

variable {X B : Type*} [PseudoEMetricSpace X] [TopologicalSpace B] [PreconnectedSpace X]

theorem discreteTopology_subgroup_of_isCoveringMap
    {p : X → B} (hp : IsCoveringMap p) (Γ : Subgroup (X ≃ᵢ X))
    (hΓ : ∀ g : Γ, ∀ x, p ((g : X ≃ᵢ X) x) = p x) : DiscreteTopology Γ := by
  classical
  by_cases hX : Nonempty X
  · let o : X := Classical.choice hX
    obtain ⟨e, ho, hpe⟩ := hp.isLocalHomeomorph o
    have hpre : (fun g : Γ => (g : X ≃ᵢ X) o) ⁻¹' e.source = {1} := by
      ext g
      constructor
      · intro hg
        have hfix : (g : X ≃ᵢ X) o = o := e.injOn hg ho (by rw [← hpe]; exact hΓ g o)
        have heq : ((g : X ≃ᵢ X) : X → X) = id :=
          hp.eq_of_comp_eq (g : X ≃ᵢ X).continuous continuous_id (funext (hΓ g)) o hfix
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        apply IsometryEquiv.ext
        exact congrFun heq
      · rintro rfl
        exact ho
    apply discreteTopology_of_isOpen_singleton_one
    rw [← hpre]
    exact e.open_source.preimage ((continuous_eval_const o).comp continuous_subtype_val)
  · let : Subsingleton Γ :=
      ⟨fun g h => Subtype.ext (IsometryEquiv.ext fun x => (hX ⟨x⟩).elim)⟩
    infer_instance

end IsometryEquiv
