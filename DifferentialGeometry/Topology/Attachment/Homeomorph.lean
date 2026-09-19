/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! Homeomorphisms of adjunction spaces induced by commuting attaching maps. -/

namespace DifferentialGeometry.Topology

variable {A A' B B' X X' : Type*}

private def adjunctionMapOfCommute (i : A → B) (φ : A → X) (j : A' → B') (ψ : A' → X')
    (a : A → A') (b : B → B') (f : X → X')
    (hi : ∀ u, b (i u) = j (a u)) (hφ : ∀ u, f (φ u) = ψ (a u)) :
    AdjunctionSpace i φ → AdjunctionSpace j ψ :=
  Quot.lift (Sum.elim (fun z => adjunctionCell j ψ (b z))
    (fun z => adjunctionLower ψ (f z))) fun _ _ h => by
    rcases h with ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · change adjunctionCell j ψ (b (i u)) = adjunctionLower ψ (f (φ u))
      rw [hi, hφ, adjunction_coherence]
    · change adjunctionLower ψ (f (φ u)) = adjunctionCell j ψ (b (i u))
      rw [hi, hφ, adjunction_coherence]

variable [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace X] [TopologicalSpace X']

private theorem continuous_adjunctionMapOfCommute
    (i : A → B) (φ : A → X) (j : A' → B') (ψ : A' → X')
    (a : A → A') (b : B → B') (f : X → X')
    (hi : ∀ u, b (i u) = j (a u)) (hφ : ∀ u, f (φ u) = ψ (a u))
    (hb : Continuous b) (hf : Continuous f) :
    Continuous (adjunctionMapOfCommute i φ j ψ a b f hi hφ) :=
  continuous_quot_lift _
    (((continuous_adjunctionCell j ψ).comp hb).sumElim
      ((continuous_adjunctionLower j ψ).comp hf))

def adjunctionHomeomorph (i : A → B) (φ : A → X) (j : A' → B') (ψ : A' → X')
    (a : A ≃ A') (b : B ≃ₜ B') (f : X ≃ₜ X')
    (hi : ∀ u, b (i u) = j (a u)) (hφ : ∀ u, f (φ u) = ψ (a u)) :
    AdjunctionSpace i φ ≃ₜ AdjunctionSpace j ψ := by
  have hi' (u : A') : b.symm (j u) = i (a.symm u) := by
    apply b.injective
    rw [b.apply_symm_apply, hi, a.apply_symm_apply]
  have hφ' (u : A') : f.symm (ψ u) = φ (a.symm u) := by
    apply f.injective
    rw [f.apply_symm_apply, hφ, a.apply_symm_apply]
  exact {
    toFun := adjunctionMapOfCommute i φ j ψ a b f hi hφ
    invFun := adjunctionMapOfCommute j ψ i φ a.symm b.symm f.symm hi' hφ'
    left_inv := by
      intro z
      induction z using Quot.ind with
      | mk z =>
        cases z with
        | inl z =>
          change adjunctionCell i φ (b.symm (b z)) = adjunctionCell i φ z
          rw [b.symm_apply_apply]
        | inr z =>
          change adjunctionLower φ (f.symm (f z)) = adjunctionLower φ z
          rw [f.symm_apply_apply]
    right_inv := by
      intro z
      induction z using Quot.ind with
      | mk z =>
        cases z with
        | inl z =>
          change adjunctionCell j ψ (b (b.symm z)) = adjunctionCell j ψ z
          rw [b.apply_symm_apply]
        | inr z =>
          change adjunctionLower ψ (f (f.symm z)) = adjunctionLower ψ z
          rw [f.apply_symm_apply]
    continuous_toFun := continuous_adjunctionMapOfCommute i φ j ψ a b f hi hφ
      b.continuous f.continuous
    continuous_invFun := continuous_adjunctionMapOfCommute j ψ i φ a.symm b.symm f.symm
      hi' hφ' b.symm.continuous f.symm.continuous }

@[simp]
theorem adjunctionHomeomorph_lower
    (i : A → B) (φ : A → X) (j : A' → B') (ψ : A' → X')
    (a : A ≃ A') (b : B ≃ₜ B') (f : X ≃ₜ X')
    (hi : ∀ u, b (i u) = j (a u)) (hφ : ∀ u, f (φ u) = ψ (a u)) (x : X) :
    adjunctionHomeomorph i φ j ψ a b f hi hφ (adjunctionLower φ x) =
      adjunctionLower ψ (f x) := rfl

@[simp]
theorem adjunctionHomeomorph_cell
    (i : A → B) (φ : A → X) (j : A' → B') (ψ : A' → X')
    (a : A ≃ A') (b : B ≃ₜ B') (f : X ≃ₜ X')
    (hi : ∀ u, b (i u) = j (a u)) (hφ : ∀ u, f (φ u) = ψ (a u)) (z : B) :
    adjunctionHomeomorph i φ j ψ a b f hi hφ (adjunctionCell i φ z) =
      adjunctionCell j ψ (b z) := rfl

end DifferentialGeometry.Topology
