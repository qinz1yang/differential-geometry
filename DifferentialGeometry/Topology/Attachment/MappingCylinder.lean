import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.UnitInterval

open Set Function Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]


abbrev MappingCylinder (f : C(A, X)) :=
  DifferentialGeometry.Topology.AdjunctionSpace
    (fun a : A => (a, (0 : Icc (0 : ℝ) 1))) f


def mappingCylinderOriginal (f : C(A, X)) : C(X, MappingCylinder f) :=
  ⟨DifferentialGeometry.Topology.adjunctionLower f,
    DifferentialGeometry.Topology.continuous_adjunctionLower _ _⟩


def mappingCylinderProduct (f : C(A, X)) : C(A × Icc (0 : ℝ) 1, MappingCylinder f) :=
  ⟨DifferentialGeometry.Topology.adjunctionCell _ f,
    DifferentialGeometry.Topology.continuous_adjunctionCell _ _⟩


theorem mappingCylinder_seam (f : C(A, X)) (a : A) :
    mappingCylinderProduct f (a, 0) = mappingCylinderOriginal f (f a) :=
  DifferentialGeometry.Topology.adjunction_coherence _ _ a


def mappingCylinderRetract (f : C(A, X)) : C(MappingCylinder f, X) := by
  let r : (A × Icc (0 : ℝ) 1) ⊕ X → X := Sum.elim (fun p => f p.1) id
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> rfl
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim (f.continuous.comp continuous_fst) continuous_id)⟩

def mappingCylinderHeight (f : C(A, X)) : C(MappingCylinder f, Icc (0 : ℝ) 1) := by
  let r : (A × Icc (0 : ℝ) 1) ⊕ X → Icc (0 : ℝ) 1 := Sum.elim Prod.snd (fun _ => 0)
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> rfl
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim continuous_snd continuous_const)⟩

@[simp] theorem mappingCylinderRetract_original (f : C(A, X)) (x : X) :
    mappingCylinderRetract f (mappingCylinderOriginal f x) = x := rfl

@[simp] theorem mappingCylinderRetract_product (f : C(A, X)) (p : A × Icc (0 : ℝ) 1) :
    mappingCylinderRetract f (mappingCylinderProduct f p) = f p.1 := rfl

@[simp] theorem mappingCylinderHeight_original (f : C(A, X)) (x : X) :
    mappingCylinderHeight f (mappingCylinderOriginal f x) = 0 := rfl

@[simp] theorem mappingCylinderHeight_product (f : C(A, X)) (p : A × Icc (0 : ℝ) 1) :
    mappingCylinderHeight f (mappingCylinderProduct f p) = p.2 := rfl


theorem isEmbedding_mappingCylinderOriginal (f : C(A, X)) :
    IsEmbedding (mappingCylinderOriginal f) :=
  (show LeftInverse (mappingCylinderRetract f) (mappingCylinderOriginal f) from
    mappingCylinderRetract_original f).isEmbedding
      (mappingCylinderRetract f).continuous (mappingCylinderOriginal f).continuous

theorem mappingCylinder_product_eq_original_iff (f : C(A, X))
    (p : A × Icc (0 : ℝ) 1) (x : X) :
    mappingCylinderProduct f p = mappingCylinderOriginal f x ↔ p.2 = 0 ∧ f p.1 = x := by
  constructor
  · intro h
    exact ⟨congrArg (mappingCylinderHeight f) h, congrArg (mappingCylinderRetract f) h⟩
  · rintro ⟨ht, rfl⟩
    rcases p with ⟨a, t⟩
    dsimp at ht
    subst t
    exact mappingCylinder_seam f a


theorem range_mappingCylinderOriginal (f : C(A, X)) :
    range (mappingCylinderOriginal f) = (mappingCylinderHeight f) ⁻¹' {0} := by
  ext z
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl p =>
      change (∃ x, mappingCylinderOriginal f x = mappingCylinderProduct f p) ↔ p.2 = 0
      constructor
      · rintro ⟨x, hx⟩
        exact ((mappingCylinder_product_eq_original_iff f p x).mp hx.symm).1
      · intro ht
        exact ⟨f p.1, ((mappingCylinder_product_eq_original_iff f p (f p.1)).mpr ⟨ht, rfl⟩).symm⟩
  | inr x =>
      exact iff_of_true ⟨x, rfl⟩ (mem_singleton 0)


theorem isClosedEmbedding_mappingCylinderOriginal (f : C(A, X)) :
    IsClosedEmbedding (mappingCylinderOriginal f) :=
  ⟨isEmbedding_mappingCylinderOriginal f, by
    rw [range_mappingCylinderOriginal]
    exact isClosed_singleton.preimage (mappingCylinderHeight f).continuous⟩


theorem isEmbedding_mappingCylinderProduct (f : C(A, X)) (hf : IsEmbedding f) :
    IsEmbedding (mappingCylinderProduct f) := by
  apply IsEmbedding.of_comp (mappingCylinderProduct f).continuous
    ((mappingCylinderRetract f).continuous.prodMk (mappingCylinderHeight f).continuous)
  exact hf.prodMap IsEmbedding.id

theorem range_mappingCylinderProduct (f : C(A, X)) :
    range (mappingCylinderProduct f) = (mappingCylinderRetract f) ⁻¹' range f := by
  ext z
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl p => exact iff_of_true ⟨p, rfl⟩ ⟨p.1, rfl⟩
  | inr x =>
      change (∃ p, mappingCylinderProduct f p = mappingCylinderOriginal f x) ↔ ∃ a, f a = x
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨p.1, ((mappingCylinder_product_eq_original_iff f p x).mp hp).2⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(a, 0), mappingCylinder_seam f a⟩


theorem isClosedEmbedding_mappingCylinderProduct (f : C(A, X)) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mappingCylinderProduct f) :=
  ⟨isEmbedding_mappingCylinderProduct f hf.isEmbedding, by
    rw [range_mappingCylinderProduct]
    exact hf.isClosed_range.preimage (mappingCylinderRetract f).continuous⟩

end DifferentialGeometry.Topology
