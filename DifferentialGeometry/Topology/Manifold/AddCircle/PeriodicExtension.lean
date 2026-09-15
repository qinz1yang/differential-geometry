import DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import DifferentialGeometry.Topology.Manifold.IntervalExtension

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace AddCircle

theorem exists_contMDiff_extension_of_periodic
    {a b : ℝ} {β : ℝ → ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2)
      (Icc a b ×ˢ (univ : Set ℝ)))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (β t) 1) :
    ∃ γ : ℝ × AddCircle (1 : ℝ) → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ γ ∧
        ∀ t ∈ Icc a b, ∀ x : ℝ, γ (t, (x : AddCircle (1 : ℝ))) = β t x := by
  classical
  let β₀ : ℝ → ℝ → ℝ := fun t x => if t ∈ Icc a b then β t x else 0
  have hp₀ : ∀ t, Function.Periodic (β₀ t) 1 := by
    intro t x
    dsimp only [β₀]
    by_cases ht : t ∈ Icc a b
    · simp only [if_pos ht]
      exact hper t ht x
    · simp only [if_neg ht]
  let f : ℝ × AddCircle (1 : ℝ) → ℝ := fun p => (hp₀ p.1).lift p.2
  have hcoe (t x : ℝ) : f (t, (x : AddCircle (1 : ℝ))) = β₀ t x := rfl
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f
      (Icc a b ×ˢ (univ : Set (AddCircle (1 : ℝ)))) := by
    apply contMDiffOn_of_comp_coe
    have heq : EqOn (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ))))
        (fun p => β p.1 p.2) (Icc a b ×ˢ (univ : Set ℝ)) := by
      intro p hp
      change f (p.1, (p.2 : AddCircle (1 : ℝ))) = β p.1 p.2
      rw [hcoe]
      exact if_pos hp.1
    have hh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ))))
        (Icc a b ×ˢ (univ : Set ℝ)) := hβ.congr heq
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod] at hh
    exact hh
  obtain ⟨γ, hγ, hγf⟩ := Manifold.exists_contMDiff_extension_Icc hf
  refine ⟨γ, hγ, ?_⟩
  intro t ht x
  rw [hγf ⟨ht, mem_univ _⟩, hcoe]
  exact if_pos ht

end AddCircle
