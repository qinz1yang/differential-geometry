import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false
open CategoryTheory ComposableArrows Abelian
open _root_.HomologicalComplex _root_.HomologicalComplex.HomologySequence
noncomputable section
namespace Poincare.HomologicalComplex
variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (_root_.HomologicalComplex C c)}
  (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

theorem mono_homologyMap_middle (i : ι)
    (h₁ : Mono (homologyMap φ.τ₁ i)) (h₃ : Mono (homologyMap φ.τ₃ i))
    (hprev : ∀ j, c.Rel j i → Epi (homologyMap φ.τ₃ j)) :
    Mono (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel j i
  · obtain ⟨j, hji⟩ := hi
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ j i hji))
    · exact (composableArrows₅_exact hS₁ j i hji).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ j i hji).δ₀.δ₀
    · exact hprev j hji
    · exact h₁
    · exact h₃
  · apply mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₁ i) _ h₁ h₃
    have := hS₂.mono_f
    apply mono_homologyMap_of_mono_of_not_rel
    simpa using hi

theorem epi_homologyMap_middle (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i)) (h₃ : Epi (homologyMap φ.τ₃ i))
    (hnext : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₃
    · exact hnext j hij
  · apply epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i) _ h₁ h₃
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi

theorem isIso_homologyMap_middle (i : ι)
    (h₁ : IsIso (homologyMap φ.τ₁ i)) (h₃ : IsIso (homologyMap φ.τ₃ i))
    (hprev : ∀ j, c.Rel j i → Epi (homologyMap φ.τ₃ j))
    (hnext : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    IsIso (homologyMap φ.τ₂ i) := by
  have := mono_homologyMap_middle φ hS₁ hS₂ i inferInstance inferInstance hprev
  have := epi_homologyMap_middle φ hS₁ hS₂ i inferInstance inferInstance hnext
  exact isIso_of_mono_of_epi _

theorem quasiIso_middle (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_middle φ hS₁ hS₂ i
  all_goals infer_instance

end Poincare.HomologicalComplex
