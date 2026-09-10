import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]


abbrev Double (B : Set X) :=
  DifferentialGeometry.Topology.AdjunctionSpace (Subtype.val : B → X) (Subtype.val : B → X)


def doublePositive (B : Set X) : C(X, Double B) :=
  ⟨DifferentialGeometry.Topology.adjunctionCell _ _,
    DifferentialGeometry.Topology.continuous_adjunctionCell _ _⟩


def doubleNegative (B : Set X) : C(X, Double B) :=
  ⟨DifferentialGeometry.Topology.adjunctionLower _,
    DifferentialGeometry.Topology.continuous_adjunctionLower _ _⟩


theorem double_seam (B : Set X) (b : B) :
    doublePositive B b.val = doubleNegative B b.val :=
  DifferentialGeometry.Topology.adjunction_coherence _ _ b


def doubleDesc {Y : Type*} [TopologicalSpace Y] (B : Set X)
    (f g : C(X, Y)) (h : ∀ b : B, f b.val = g b.val) : C(Double B, Y) := by
  let r : X ⊕ X → Y := Sum.elim f g
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (Subtype.val : B → X) (Subtype.val : B → X) a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact h p
    · exact (h p).symm
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim f.continuous g.continuous)⟩

@[simp] theorem doubleDesc_positive {Y : Type*} [TopologicalSpace Y] (B : Set X)
    (f g : C(X, Y)) (h : ∀ b : B, f b.val = g b.val) (x : X) :
    doubleDesc B f g h (doublePositive B x) = f x := rfl

@[simp] theorem doubleDesc_negative {Y : Type*} [TopologicalSpace Y] (B : Set X)
    (f g : C(X, Y)) (h : ∀ b : B, f b.val = g b.val) (x : X) :
    doubleDesc B f g h (doubleNegative B x) = g x := rfl


def doubleFold (B : Set X) : C(Double B, X) :=
  doubleDesc B (ContinuousMap.id X) (ContinuousMap.id X) (fun _ => rfl)

@[simp] theorem doubleFold_positive (B : Set X) (x : X) :
    doubleFold B (doublePositive B x) = x := rfl

@[simp] theorem doubleFold_negative (B : Set X) (x : X) :
    doubleFold B (doubleNegative B x) = x := rfl


theorem isEmbedding_doublePositive (B : Set X) : IsEmbedding (doublePositive B) :=
  (show LeftInverse (doubleFold B) (doublePositive B) from doubleFold_positive B).isEmbedding
    (doubleFold B).continuous (doublePositive B).continuous


theorem isEmbedding_doubleNegative (B : Set X) : IsEmbedding (doubleNegative B) :=
  (show LeftInverse (doubleFold B) (doubleNegative B) from doubleFold_negative B).isEmbedding
    (doubleFold B).continuous (doubleNegative B).continuous


def doubleHeight (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0) : C(Double B, ℝ) :=
  doubleDesc B r ⟨fun x => -r x, r.continuous.neg⟩ (fun b => by simp [hr b])

@[simp] theorem doubleHeight_positive (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (x : X) :
    doubleHeight B r hr (doublePositive B x) = r x := rfl

@[simp] theorem doubleHeight_negative (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (x : X) :
    doubleHeight B r hr (doubleNegative B x) = -r x := rfl


def doubleRealization (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0) :
    C(Double B, X × ℝ) := (doubleFold B).prodMk (doubleHeight B r hr)

theorem injective_doubleRealization (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B) :
    Injective (doubleRealization B r hr) := by
  intro a b
  refine Quot.inductionOn a ?_
  intro p
  refine Quot.inductionOn b ?_
  intro q hpq
  have hf := congrArg Prod.fst hpq
  have hh := congrArg Prod.snd hpq
  cases p with
  | inl x =>
    cases q with
    | inl y =>
      change x = y at hf
      exact congrArg (doublePositive B) hf
    | inr y =>
      change x = y at hf
      subst y
      have hx : r x = 0 := by change r x = -r x at hh; linarith
      exact double_seam B ⟨x, hz x hx⟩
  | inr x =>
    cases q with
    | inl y =>
      change x = y at hf
      subst y
      have hx : r x = 0 := by change -r x = r x at hh; linarith
      exact (double_seam B ⟨x, hz x hx⟩).symm
    | inr y =>
      change x = y at hf
      exact congrArg (doubleNegative B) hf


theorem isClosedEmbedding_doubleRealization [CompactSpace X] [T2Space X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) : IsClosedEmbedding (doubleRealization B r hr) :=
  (doubleRealization B r hr).continuous.isClosedEmbedding (injective_doubleRealization B r hr hz)


theorem t2Space_double [CompactSpace X] [T2Space X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) : T2Space (Double B) :=
  (isClosedEmbedding_doubleRealization B r hr hz).isEmbedding.t2Space

end Poincare.Topology
