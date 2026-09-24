import DifferentialGeometry.Topology.Attachment.Basic

set_option autoImplicit false
noncomputable section
open Function

namespace DifferentialGeometry.Topology

universe uA uB uC uD uX uY

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {X : Type uX}

private def adjunctionDesc {Y : Type uY} (i : A → B) (φ : A → X)
    (f : B → Y) (g : X → Y) (h : ∀ a, f (i a) = g (φ a)) :
    AdjunctionSpace i φ → Y :=
  Quot.lift (Sum.elim f g) (by
    rintro _ _ ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h a
    · exact (h a).symm)

private theorem continuous_adjunctionDesc {Y : Type uY}
    [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    (i : A → B) (φ : A → X) (f : B → Y) (g : X → Y)
    (h : ∀ a, f (i a) = g (φ a)) (hf : Continuous f) (hg : Continuous g) :
    Continuous (adjunctionDesc i φ f g h) :=
  continuous_adjunction_lift i φ _ (Continuous.sumElim hf hg)

private def adjunctionInnerSwap (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    AdjunctionSpace i φ → AdjunctionSpace i (adjunctionLower (i := j) ψ ∘ φ) :=
  adjunctionDesc i φ
    (adjunctionCell i (adjunctionLower (i := j) ψ ∘ φ))
    (adjunctionLower (i := i) (adjunctionLower (i := j) ψ ∘ φ) ∘
      adjunctionLower (i := j) ψ)
    (fun a => adjunction_coherence i (adjunctionLower (i := j) ψ ∘ φ) a)

private def adjunctionSwap (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    AdjunctionSpace j (adjunctionLower (i := i) φ ∘ ψ) →
      AdjunctionSpace i (adjunctionLower (i := j) ψ ∘ φ) :=
  adjunctionDesc j (adjunctionLower (i := i) φ ∘ ψ)
    (adjunctionLower (i := i) (adjunctionLower (i := j) ψ ∘ φ) ∘ adjunctionCell j ψ)
    (adjunctionInnerSwap i φ j ψ)
    (fun a => congrArg (adjunctionLower (i := i) (adjunctionLower (i := j) ψ ∘ φ))
      (adjunction_coherence j ψ a))

private theorem adjunctionSwap_leftInverse
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    LeftInverse (adjunctionSwap j ψ i φ) (adjunctionSwap i φ j ψ) := by
  intro q
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl d => rfl
    | inr z =>
      induction z using Quot.inductionOn with
      | h p => cases p <;> rfl

variable [TopologicalSpace B] [TopologicalSpace D] [TopologicalSpace X]

private theorem continuous_adjunctionInnerSwap
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    Continuous (adjunctionInnerSwap i φ j ψ) :=
  continuous_adjunctionDesc _ _ _ _ _ (continuous_adjunctionCell _ _)
    ((continuous_adjunctionLower _ _).comp (continuous_adjunctionLower _ _))

private theorem continuous_adjunctionSwap
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    Continuous (adjunctionSwap i φ j ψ) :=
  continuous_adjunctionDesc _ _ _ _ _
    ((continuous_adjunctionLower _ _).comp (continuous_adjunctionCell _ _))
    (continuous_adjunctionInnerSwap i φ j ψ)

def adjunctionAttachmentsHomeomorphComm
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    AdjunctionSpace j (adjunctionLower (i := i) φ ∘ ψ) ≃ₜ
      AdjunctionSpace i (adjunctionLower (i := j) ψ ∘ φ) where
  toFun := adjunctionSwap i φ j ψ
  invFun := adjunctionSwap j ψ i φ
  left_inv := adjunctionSwap_leftInverse i φ j ψ
  right_inv := adjunctionSwap_leftInverse j ψ i φ
  continuous_toFun := continuous_adjunctionSwap i φ j ψ
  continuous_invFun := continuous_adjunctionSwap j ψ i φ

@[simp] theorem adjunctionAttachmentsHomeomorphComm_cell
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) (d : D) :
    adjunctionAttachmentsHomeomorphComm i φ j ψ
        (adjunctionCell j (adjunctionLower (i := i) φ ∘ ψ) d) =
      adjunctionLower (i := i) (adjunctionLower (i := j) ψ ∘ φ) (adjunctionCell j ψ d) := rfl

@[simp] theorem adjunctionAttachmentsHomeomorphComm_lower_cell
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) (b : B) :
    adjunctionAttachmentsHomeomorphComm i φ j ψ
        (adjunctionLower (i := j) (adjunctionLower (i := i) φ ∘ ψ) (adjunctionCell i φ b)) =
      adjunctionCell i (adjunctionLower (i := j) ψ ∘ φ) b := rfl

@[simp] theorem adjunctionAttachmentsHomeomorphComm_lower_lower
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) (x : X) :
    adjunctionAttachmentsHomeomorphComm i φ j ψ
        (adjunctionLower (i := j) (adjunctionLower (i := i) φ ∘ ψ)
          (adjunctionLower (i := i) φ x)) =
      adjunctionLower (i := i) (adjunctionLower (i := j) ψ ∘ φ)
        (adjunctionLower (i := j) ψ x) := rfl

@[simp] theorem adjunctionAttachmentsHomeomorphComm_symm
    (i : A → B) (φ : A → X) (j : C → D) (ψ : C → X) :
    (adjunctionAttachmentsHomeomorphComm i φ j ψ).symm =
      adjunctionAttachmentsHomeomorphComm j ψ i φ := rfl

end DifferentialGeometry.Topology
