import DifferentialGeometry.Topology.Homotopy.LoopTopology



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {D E X : Type*} [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace X]


abbrev basedMappingSpace (d : D) (x : X) := {f : C(D, X) // f d = x}


def basedMappingSpaceDomainHomeomorph (e : D ≃ₜ E) (d : D) (b : E) (he : e d = b) (x : X) :
    basedMappingSpace b x ≃ₜ basedMappingSpace d x := by
  subst b
  refine {
    toFun := fun f => ⟨f.val.comp ⟨e, e.continuous⟩, f.property⟩
    invFun := fun f => ⟨f.val.comp ⟨e.symm, e.symm.continuous⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · change f.val (e.symm (e d)) = x
    rw [e.symm_apply_apply, f.property]
  · intro f
    apply Subtype.ext
    ext t
    exact congrArg f.val (e.apply_symm_apply t)
  · intro f
    apply Subtype.ext
    ext t
    exact congrArg f.val (e.symm_apply_apply t)
  · exact ((continuous_precomp (⟨e, e.continuous⟩ : C(D, E))).comp
      continuous_subtype_val).subtype_mk _
  · exact ((continuous_precomp (⟨e.symm, e.symm.continuous⟩ : C(E, D))).comp
      continuous_subtype_val).subtype_mk _


theorem basedMappingSpaceDomainHomeomorph_apply (e : D ≃ₜ E) (d : D) (b : E)
    (he : e d = b) (x : X) (f : basedMappingSpace b x) (t : D) :
    (basedMappingSpaceDomainHomeomorph e d b he x f).val t = f.val (e t) := by
  subst b
  rfl



theorem basedMappingSpace_joined_iff [LocallyCompactSpace D] (d : D) (x : X)
    (f g : basedMappingSpace d x) : Joined f g ↔ f.val.HomotopicRel g.val {d} := by
  constructor
  · rintro ⟨P⟩
    let F : C(unitInterval, C(D, X)) :=
      ⟨fun t => (P t).val, continuous_subtype_val.comp P.continuous⟩
    refine ⟨⟨⟨F.uncurry, ?_, ?_⟩, ?_⟩⟩
    · intro y
      change (P 0).val y = f.val y
      rw [P.source]
    · intro y
      change (P 1).val y = g.val y
      rw [P.target]
    · intro t y hy
      obtain rfl := mem_singleton_iff.mp hy
      exact (P t).property.trans f.property.symm
  · rintro ⟨H⟩
    let F : C(unitInterval, basedMappingSpace d x) :=
      ⟨fun t => ⟨H.toHomotopy.curry t,
        (H.eq_fst t (mem_singleton d)).trans f.property⟩,
        H.toHomotopy.curry.continuous.subtype_mk _⟩
    refine ⟨⟨F, ?_, ?_⟩⟩
    · apply Subtype.ext
      ext y
      exact H.apply_zero y
    · apply Subtype.ext
      ext y
      exact H.apply_one y

end DifferentialGeometry.Topology
