import DifferentialGeometry.Topology.Attachment.MappingCylinder

open Set Function Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]


def mappingCylinderDesc (f : C(A, X)) (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y))
    (hseam : ∀ a, g (a, 0) = j (f a)) : C(MappingCylinder f, Y) := by
  let r : (A × Icc (0 : ℝ) 1) ⊕ X → Y := Sum.elim g j
  have hr : ∀ a b, DifferentialGeometry.Topology.adjunctionRel
      (fun a : A => (a, (0 : Icc (0 : ℝ) 1))) f a b → r a = r b := by
    rintro a b ⟨p, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hseam p
    · exact (hseam p).symm
  exact ⟨Quot.lift r hr, DifferentialGeometry.Topology.continuous_adjunction_lift _ _ hr
    (Continuous.sumElim g.continuous j.continuous)⟩

@[simp] theorem mappingCylinderDesc_original (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a)) (x : X) :
    mappingCylinderDesc f g j hseam (mappingCylinderOriginal f x) = j x := rfl

@[simp] theorem mappingCylinderDesc_product (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (p : A × Icc (0 : ℝ) 1) :
    mappingCylinderDesc f g j hseam (mappingCylinderProduct f p) = g p := rfl

theorem isClosedMap_mappingCylinderDesc (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : IsClosedMap g) (hj : IsClosedMap j) :
    IsClosedMap (mappingCylinderDesc f g j hseam) := by
  intro S hS
  have heq : mappingCylinderDesc f g j hseam '' S =
      g '' ((mappingCylinderProduct f) ⁻¹' S) ∪ j '' ((mappingCylinderOriginal f) ⁻¹' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨q, rfl⟩ := Quot.exists_rep z
      cases q with
      | inl p => exact Or.inl ⟨p, hz, rfl⟩
      | inr x => exact Or.inr ⟨x, hz, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨mappingCylinderProduct f p, hp, rfl⟩
      · exact ⟨mappingCylinderOriginal f x, hx, rfl⟩
  rw [heq]
  exact (hg _ (hS.preimage (mappingCylinderProduct f).continuous)).union
    (hj _ (hS.preimage (mappingCylinderOriginal f).continuous))

def mappingCylinderHomeomorphOfClosedCover (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : IsClosedEmbedding g) (hj : IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : range g ∪ range j = univ) : MappingCylinder f ≃ₜ Y := by
  let d := mappingCylinderDesc f g j hseam
  have hdinj : Injective d := by
    intro z z' h
    obtain ⟨q, rfl⟩ := Quot.exists_rep z
    obtain ⟨q', rfl⟩ := Quot.exists_rep z'
    cases q with
    | inl p =>
      cases q' with
      | inl p' => exact congrArg (mappingCylinderProduct f) (hg.injective h)
      | inr x => exact (mappingCylinder_product_eq_original_iff f p x).mpr (hcross p x h)
    | inr x =>
      cases q' with
      | inl p => exact ((mappingCylinder_product_eq_original_iff f p x).mpr (hcross p x h.symm)).symm
      | inr x' => exact congrArg (mappingCylinderOriginal f) (hj.injective h)
  have hdsurj : Surjective d := by
    intro y
    have hy : y ∈ range g ∪ range j := hcover ▸ mem_univ y
    rcases hy with ⟨p, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨mappingCylinderProduct f p, rfl⟩
    · exact ⟨mappingCylinderOriginal f x, rfl⟩
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨d.continuous, isClosedMap_mappingCylinderDesc f g j hseam hg.isClosedMap hj.isClosedMap,
      hdinj, hdsurj⟩).homeomorph

@[simp] theorem mappingCylinderHomeomorphOfClosedCover_original (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : IsClosedEmbedding g) (hj : IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : range g ∪ range j = univ) (x : X) :
    mappingCylinderHomeomorphOfClosedCover f g j hseam hg hj hcross hcover
      (mappingCylinderOriginal f x) = j x := rfl

@[simp] theorem mappingCylinderHomeomorphOfClosedCover_product (f : C(A, X))
    (g : C(A × Icc (0 : ℝ) 1, Y)) (j : C(X, Y)) (hseam : ∀ a, g (a, 0) = j (f a))
    (hg : IsClosedEmbedding g) (hj : IsClosedEmbedding j)
    (hcross : ∀ p x, g p = j x → p.2 = 0 ∧ f p.1 = x)
    (hcover : range g ∪ range j = univ) (p : A × Icc (0 : ℝ) 1) :
    mappingCylinderHomeomorphOfClosedCover f g j hseam hg hj hcross hcover
      (mappingCylinderProduct f p) = g p := rfl

end DifferentialGeometry.Topology
