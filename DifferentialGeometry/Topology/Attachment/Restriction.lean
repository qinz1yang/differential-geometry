import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation

set_option autoImplicit false
noncomputable section
open Set Function

namespace DifferentialGeometry.Topology

universe uA uB uX

variable {A : Type uA} {B : Type uB} {X : Type uX}

private def adjunctionRestrictionMap (i : A → B) (φ : A → X)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) → AdjunctionSpace i φ :=
  Quot.lift (Sum.elim (adjunctionCell i φ) (fun x : T => adjunctionLower (i := i) φ x.val)) (by
    rintro _ _ ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact adjunction_coherence i φ a
    · exact (adjunction_coherence i φ a).symm)

private theorem adjunctionRestrictionMap_not_mem
    (i : A → B) (φ : A → X) (hi : Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T)
    (q : AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T))) :
    adjunctionRestrictionMap i φ T hφT q ∉ adjunctionLower (i := i) φ '' Tᶜ := by
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl b =>
      rintro ⟨x, hx, he⟩
      obtain ⟨a, _, ha⟩ :=
        (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x).mp he.symm
      exact hx (ha ▸ hφT a)
    | inr x =>
      rintro ⟨y, hy, he⟩
      have hyx := Manifold.Attachment.adjunctionLower_injective i φ hi he
      exact hy (hyx.symm ▸ x.property)

private theorem adjunctionRestrictionMap_injective
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Injective (adjunctionRestrictionMap i φ T hφT) := by
  intro q r
  induction q using Quot.inductionOn with
  | h p =>
    induction r using Quot.inductionOn with
    | h s =>
      cases p with
      | inl b =>
        cases s with
        | inl b' =>
          intro h
          exact congrArg (adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)))
            (Manifold.Attachment.adjunctionCell_injective i φ hi hφ h)
        | inr x =>
          intro h
          obtain ⟨a, ha, hx⟩ :=
            (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x.val).mp h
          have he : (⟨φ a, hφT a⟩ : T) = x := Subtype.ext hx
          rw [← ha, ← he]
          exact adjunction_coherence i (fun a => (⟨φ a, hφT a⟩ : T)) a
      | inr x =>
        cases s with
        | inl b =>
          intro h
          obtain ⟨a, ha, hx⟩ :=
            (Manifold.Attachment.adjunctionCell_eq_lower_iff i φ hi b x.val).mp h.symm
          have he : (⟨φ a, hφT a⟩ : T) = x := Subtype.ext hx
          rw [← ha, ← he]
          exact (adjunction_coherence i (fun a => (⟨φ a, hφT a⟩ : T)) a).symm
        | inr y =>
          intro h
          exact congrArg (adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)))
            (Subtype.ext (Manifold.Attachment.adjunctionLower_injective i φ hi h))

private def adjunctionRestrictionToSubtype
    (i : A → B) (φ : A → X) (hi : Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) →
      {q : AdjunctionSpace i φ // q ∉ adjunctionLower (i := i) φ '' Tᶜ} :=
  fun q => ⟨adjunctionRestrictionMap i φ T hφT q,
    adjunctionRestrictionMap_not_mem i φ hi T hφT q⟩

private theorem adjunctionRestrictionToSubtype_surjective
    (i : A → B) (φ : A → X) (hi : Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Surjective (adjunctionRestrictionToSubtype i φ hi T hφT) := by
  intro q
  obtain ⟨p, hp⟩ := Quot.exists_rep q.val
  cases p with
  | inl b =>
    refine ⟨adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b, ?_⟩
    exact Subtype.ext hp
  | inr x =>
    have hx : x ∈ T := by
      by_contra h
      exact q.property ⟨x, h, hp⟩
    refine ⟨adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) ⟨x, hx⟩, ?_⟩
    exact Subtype.ext hp

variable [TopologicalSpace B] [TopologicalSpace X]

private theorem continuous_adjunctionRestrictionToSubtype
    (i : A → B) (φ : A → X) (hi : Injective i)
    (T : Set X) (hφT : ∀ a, φ a ∈ T) :
    Continuous (adjunctionRestrictionToSubtype i φ hi T hφT) := by
  apply Continuous.subtype_mk
  exact continuous_adjunction_lift i (fun a => (⟨φ a, hφT a⟩ : T)) _
    (Continuous.sumElim (continuous_adjunctionCell i φ)
      ((continuous_adjunctionLower i φ).comp continuous_subtype_val))

variable [TopologicalSpace A] [CompactSpace A] [CompactSpace B] [CompactSpace X]
  [T2Space B] [T2Space X]

def adjunctionClosedRestrictionHomeomorph
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) :
    AdjunctionSpace i (fun a => (⟨φ a, hφT a⟩ : T)) ≃ₜ
      {q : AdjunctionSpace i φ // q ∉ adjunctionLower (i := i) φ '' Tᶜ} := by
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
  let _ : T2Space (AdjunctionSpace i φ) :=
    Manifold.Attachment.adjunction_t2Space i φ hi hφ hci hcφ
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (adjunctionRestrictionToSubtype i φ hi T hφT)
      ⟨fun q r h => adjunctionRestrictionMap_injective i φ hi hφ T hφT
        (congrArg Subtype.val h), adjunctionRestrictionToSubtype_surjective i φ hi T hφT⟩)
    (continuous_adjunctionRestrictionToSubtype i φ hi T hφT)

@[simp] theorem adjunctionClosedRestrictionHomeomorph_cell
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (b : B) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT
      (adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b)).val = adjunctionCell i φ b := rfl

@[simp] theorem adjunctionClosedRestrictionHomeomorph_lower
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (x : T) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT
      (adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) x)).val =
      adjunctionLower (i := i) φ x.val := rfl

@[simp] theorem adjunctionClosedRestrictionHomeomorph_symm_cell
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (b : B)
    (hb : adjunctionCell i φ b ∉ adjunctionLower (i := i) φ '' Tᶜ) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).symm
        ⟨adjunctionCell i φ b, hb⟩ =
      adjunctionCell i (fun a => (⟨φ a, hφT a⟩ : T)) b := by
  apply (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

@[simp] theorem adjunctionClosedRestrictionHomeomorph_symm_lower
    (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (hci : Continuous i) (hcφ : Continuous φ)
    (T : Set X) (hT : IsClosed T) (hφT : ∀ a, φ a ∈ T) (x : T)
    (hx : adjunctionLower (i := i) φ x.val ∉ adjunctionLower (i := i) φ '' Tᶜ) :
    (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).symm
        ⟨adjunctionLower (i := i) φ x.val, hx⟩ =
      adjunctionLower (i := i) (fun a => (⟨φ a, hφT a⟩ : T)) x := by
  apply (adjunctionClosedRestrictionHomeomorph i φ hi hφ hci hcφ T hT hφT).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

end DifferentialGeometry.Topology
