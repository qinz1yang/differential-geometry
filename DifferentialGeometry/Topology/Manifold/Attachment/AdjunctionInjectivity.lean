import DifferentialGeometry.Topology.Attachment.Defs

set_option autoImplicit false
noncomputable section
open Set Function DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
variable {A B X : Type*}

private def representative (i : A → B) (φ : A → X) : B ⊕ X → B ⊕ X := by
  classical
  exact fun p => match p with
    | Sum.inl b => if h : ∃ a, i a = b then Sum.inr (φ (Classical.choose h)) else Sum.inl b
    | Sum.inr x => Sum.inr x
private theorem representative_boundary (i : A → B) (φ : A → X) (hi : Injective i) (a : A) :
    representative i φ (Sum.inl (i a)) = Sum.inr (φ a) := by
  have h : ∃ b, i b = i a := ⟨a, rfl⟩
  simp only [representative, dif_pos h]
  exact congrArg (fun b => Sum.inr (φ b)) (hi (Classical.choose_spec h))
private theorem representative_rel (i : A → B) (φ : A → X) (hi : Injective i)
    (x y : B ⊕ X) (h : adjunctionRel i φ x y) : representative i φ x = representative i φ y := by
  obtain ⟨a, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    exact representative_boundary i φ hi a
  · rcases h with ⟨rfl, rfl⟩
    exact (representative_boundary i φ hi a).symm
private def quotientRepresentative (i : A → B) (φ : A → X) (hi : Injective i) :
    AdjunctionSpace i φ → B ⊕ X := Quot.lift (representative i φ) (representative_rel i φ hi)

theorem adjunctionLower_injective (i : A → B) (φ : A → X) (hi : Injective i) :
    Injective (adjunctionLower (i := i) φ) := by
  intro x y he
  have hh := congrArg (quotientRepresentative i φ hi) he
  exact Sum.inr_injective hh

theorem adjunctionCell_eq_lower_iff (i : A → B) (φ : A → X) (hi : Injective i) (b : B) (x : X) :
    adjunctionCell i φ b = adjunctionLower φ x ↔ ∃ a : A, i a = b ∧ φ a = x := by
  classical
  constructor
  · intro he
    have hh := congrArg (quotientRepresentative i φ hi) he
    change representative i φ (Sum.inl b) = Sum.inr x at hh
    by_cases hb : ∃ a, i a = b
    · rw [representative, dif_pos hb] at hh
      exact ⟨Classical.choose hb, Classical.choose_spec hb, Sum.inr_injective hh⟩
    · rw [representative, dif_neg hb] at hh
      cases hh
  · rintro ⟨a, rfl, rfl⟩
    exact adjunction_coherence i φ a

theorem adjunctionCell_injective (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ) :
    Injective (adjunctionCell i φ) := by
  classical
  intro b c he
  have hh := congrArg (quotientRepresentative i φ hi) he
  change representative i φ (Sum.inl b) = representative i φ (Sum.inl c) at hh
  by_cases hb : ∃ a, i a = b
  · by_cases hc : ∃ a, i a = c
    · rw [representative, dif_pos hb, representative, dif_pos hc] at hh
      have ha := hφ (Sum.inr_injective hh)
      exact (Classical.choose_spec hb).symm.trans ((congrArg i ha).trans (Classical.choose_spec hc))
    · rw [representative, dif_pos hb, representative, dif_neg hc] at hh
      cases hh
  · by_cases hc : ∃ a, i a = c
    · rw [representative, dif_neg hb, representative, dif_pos hc] at hh
      cases hh
    · rw [representative, dif_neg hb, representative, dif_neg hc] at hh
      exact Sum.inl_injective hh

theorem adjunction_inclusions_cover (i : A → B) (φ : A → X) :
    range (adjunctionCell i φ) ∪ range (adjunctionLower (i := i) φ) = univ := by
  apply eq_univ_of_forall
  intro q
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl b => exact Or.inl ⟨b, rfl⟩
    | inr x => exact Or.inr ⟨x, rfl⟩

theorem adjunction_inclusions_inter (i : A → B) (φ : A → X) (hi : Injective i) :
    range (adjunctionCell i φ) ∩ range (adjunctionLower (i := i) φ) =
      range (adjunctionCell i φ ∘ i) := by
  ext q
  constructor
  · rintro ⟨⟨b, rfl⟩, ⟨x, hx⟩⟩
    obtain ⟨a, ha, _⟩ := (adjunctionCell_eq_lower_iff i φ hi b x).mp hx.symm
    exact ⟨a, congrArg (adjunctionCell i φ) ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨i a, rfl⟩, ⟨φ a, (adjunction_coherence i φ a).symm⟩⟩
end DifferentialGeometry.Topology.Manifold.Attachment
