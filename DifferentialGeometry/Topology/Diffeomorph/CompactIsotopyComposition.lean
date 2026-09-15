import Mathlib.Geometry.Manifold.Diffeomorph

section

open Set
open scoped ContDiff Manifold

namespace Diffeomorph

private theorem compact_isotopy_trans
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E ≃ₘ[ℝ] E) {C₀ C₁ : Set E}
    (hF : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ ∞ (fun z : ℝ × E => (F z.1).symm z.2))
    (hF₀ : F 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞) (hC₀ : IsCompact C₀)
    (hfixF : ∀ t, EqOn (F t) id C₀ᶜ ∧ EqOn (F t).symm id C₀ᶜ)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    (hG₀ : G 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞) (hC₁ : IsCompact C₁)
    (hfixG : ∀ t, EqOn (G t) id C₁ᶜ ∧ EqOn (G t).symm id C₁ᶜ) :
    let H := fun t => (F t).trans (G t)
    ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧ IsCompact (C₀ ∪ C₁) ∧
      ∀ t, EqOn (H t) id (C₀ ∪ C₁)ᶜ ∧ EqOn (H t).symm id (C₀ ∪ C₁)ᶜ := by
  refine ⟨hG.comp (contDiff_fst.prodMk hF), hFi.comp (contDiff_fst.prodMk hGi),
    ?_, hC₀.union hC₁, ?_⟩
  · dsimp only
    rw [hF₀, hG₀, Diffeomorph.refl_trans]
  · intro t
    constructor
    · intro p hp
      have hp₀ : p ∉ C₀ := fun h => hp (Or.inl h)
      have hp₁ : p ∉ C₁ := fun h => hp (Or.inr h)
      change G t (F t p) = p
      rw [(hfixF t).1 hp₀, id_eq]
      exact (hfixG t).1 hp₁
    · intro p hp
      have hp₀ : p ∉ C₀ := fun h => hp (Or.inl h)
      have hp₁ : p ∉ C₁ := fun h => hp (Or.inr h)
      change (F t).symm ((G t).symm p) = p
      rw [(hfixG t).2 hp₁, id_eq]
      exact (hfixF t).2 hp₀

end Diffeomorph

end

section

open Set
open scoped ContDiff Manifold

namespace Diffeomorph

theorem exists_compact_isotopy_image_trans
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E ≃ₘ[ℝ] E) {C₀ C₁ A B D : Set E}
    (hF : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ ∞ (fun z : ℝ × E => (F z.1).symm z.2))
    (hF₀ : F 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞) (hC₀ : IsCompact C₀)
    (hfixF : ∀ t, EqOn (F t) id C₀ᶜ ∧ EqOn (F t).symm id C₀ᶜ)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    (hG₀ : G 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞) (hC₁ : IsCompact C₁)
    (hfixG : ∀ t, EqOn (G t) id C₁ᶜ ∧ EqOn (G t).symm id C₁ᶜ)
    (himageF : F 1 '' A = B) (himageG : G 1 '' B = D) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E, (∀ t, H t = (F t).trans (G t)) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧ IsCompact (C₀ ∪ C₁) ∧
      (∀ t, EqOn (H t) id (C₀ ∪ C₁)ᶜ ∧ EqOn (H t).symm id (C₀ ∪ C₁)ᶜ) ∧
      H 1 '' A = D ∧ H 1 '' interior A = interior D ∧ H 1 '' frontier A = frontier D := by
  let H : ℝ → E ≃ₘ[ℝ] E := fun t => (F t).trans (G t)
  obtain ⟨hH, hi, hz, hC, hfix⟩ := compact_isotopy_trans F G
    hF hFi hF₀ hC₀ hfixF hG hGi hG₀ hC₁ hfixG
  have himage : H 1 '' A = D := by
    calc
      H 1 '' A = G 1 '' (F 1 '' A) := by
        rw [image_image]
        rfl
      _ = D := by rw [himageF, himageG]
  exact ⟨H, fun _ => rfl, hH, hi, hz, hC, hfix, himage,
    ((H 1).toHomeomorph.image_interior A).trans (congrArg interior himage),
    ((H 1).toHomeomorph.image_frontier A).trans (congrArg frontier himage)⟩

end Diffeomorph

end
