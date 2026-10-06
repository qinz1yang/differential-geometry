/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Maps.ProperCollisionProjection

noncomputable section

open Set

namespace DifferentialGeometry.Topology

/-- A closed same-value relation with a unique partner over every source point
defines a unique continuous map when its second-coordinate map is proper. -/
theorem exists_continuousMap_of_unique_closed_proper_relation
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (g : Y → Z) (hf : Continuous f) (hg : IsProperMap g)
    (S : Set (X × Y)) (hS : IsClosed S)
    (hvalue : ∀ p ∈ S, f p.1 = g p.2)
    (hunique : ∀ x, ∃! y, (x, y) ∈ S) :
    ∃ τ : C(X, Y), (∀ x, (x, τ x) ∈ S) ∧ (∀ x, f x = g (τ x)) ∧
      ∀ σ : C(X, Y), (∀ x, (x, σ x) ∈ S) → σ = τ := by
  classical
  let τ : X → Y := fun x => Classical.choose (hunique x)
  have hτ (x : X) : (x, τ x) ∈ S := (Classical.choose_spec (hunique x)).1
  have hτunique (x : X) (y : Y) (hy : (x, y) ∈ S) : y = τ x :=
    (Classical.choose_spec (hunique x)).2 y hy
  have hτcontinuous : Continuous τ := by
    apply continuous_iff_isClosed.mpr
    intro F hF
    have heq : τ ⁻¹' F = Prod.fst '' (S ∩ Prod.snd ⁻¹' F) := by
      ext x
      constructor
      · intro hx
        exact ⟨(x, τ x), ⟨hτ x, hx⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        change τ a ∈ F
        rw [← hτunique a b hab.1]
        exact hab.2
    rw [heq]
    exact isClosed_fst_image_of_isProperMap hf hg
      (hS.inter (hF.preimage continuous_snd)) (fun p hp => hvalue p hp.1)
  refine ⟨⟨τ, hτcontinuous⟩, hτ, fun x => hvalue (x, τ x) (hτ x), ?_⟩
  intro σ hσ
  apply ContinuousMap.ext
  intro x
  exact hτunique x (σ x) (hσ x)

end DifferentialGeometry.Topology
