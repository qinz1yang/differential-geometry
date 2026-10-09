import DifferentialGeometry.Topology.SimplicialComplex.Expansion.ExpansionTransport

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [DecidableEq E] in
theorem range_subtype_comp (V : Finset E) (f : E → F) :
    range (fun i : V => f i.1) = f '' (V : Set E) := by
  classical
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem simplexFacet_subtype_eq_image {V : Finset E} (f : E → F)
    (A : E →ᵃ[ℝ] F) (hA : EqOn f A (convexHull ℝ (V : Set E))) (i : V) :
    simplexFacet (fun j : V => f j.1) i =
      f '' convexHull ℝ (V.erase i.1 : Set E) := by
  rw [image_convexHull_eq_of_eqOn_affineMap f A
    (hA.mono (convexHull_mono (Finset.erase_subset _ _)))]
  unfold simplexFacet
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.1, Finset.mem_erase.mpr ⟨?_, j.2⟩, rfl⟩
    exact fun he => hj (Subtype.ext he)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxi, hxV⟩ := Finset.mem_erase.mp hx
    exact ⟨⟨x, hxV⟩, fun he => hxi (congrArg Subtype.val he), rfl⟩

theorem ProperSimplexRoof.split_lowerRoof_eq_image {V B : Finset E}
    (h : ProperSimplexRoof V B) (f : E → F) (A : E →ᵃ[ℝ] F)
    (hA : EqOn f A (convexHull ℝ (V : Set E))) :
    h.split.lowerRoof (fun i : V => f i.1) = f '' simplexRoof V B := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
    rw [simplexFacet_subtype_eq_image f A hA i] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, mem_iUnion₂.mpr ⟨i.1, (h.mem_split_right i).mp hi, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    let j : V := ⟨i, h.subset hi⟩
    refine mem_iUnion₂.mpr ⟨j, (h.mem_split_right j).mpr hi, ?_⟩
    rw [simplexFacet_subtype_eq_image f A hA j]
    exact mem_image_of_mem f hx

structure SimplexAttachmentModel (C : Set E) (V B : Finset E) (f : E → F) where
  split : SimplexSplit V
  independent : AffineIndependent ℝ (fun i : V => f i.1)
  simplex_eq : convexHull ℝ (range (fun i : V => f i.1)) =
    f '' convexHull ℝ (V : Set E)
  lowerRoof_eq : split.lowerRoof (fun i : V => f i.1) = f '' simplexRoof V B
  roof_subset : split.lowerRoof (fun i : V => f i.1) ⊆ f '' C

def SimplexAttachment.affineModel {C : Set E} {V B : Finset E}
    (h : SimplexAttachment C V B) (f : E → F) (A : E →ᵃ[ℝ] F)
    (hA : EqOn f A (convexHull ℝ (V : Set E)))
    (hf : InjOn f (convexHull ℝ (V : Set E))) : SimplexAttachmentModel C V B f where
  split := h.properRoof.split
  independent := by
    have hAi : InjOn A (convexHull ℝ (V : Set E)) := by
      intro x hx y hy he
      exact hf hx hy ((hA hx).trans (he.trans (hA hy).symm))
    convert affineIndependent_of_injOn_convexHull h.independent A hAi using 1
    funext i
    exact hA (subset_convexHull ℝ _ i.2)
  simplex_eq := by
    rw [range_subtype_comp, image_convexHull_eq_of_eqOn_affineMap f A hA]
  lowerRoof_eq := h.properRoof.split_lowerRoof_eq_image f A hA
  roof_subset := by
    rw [h.properRoof.split_lowerRoof_eq_image f A hA]
    exact image_mono h.roof_subset

namespace SimplexAttachmentModel

variable {C : Set E} {V B : Finset E} {f : E → F}

theorem nonempty_index (m : SimplexAttachmentModel C V B f) : Nonempty V :=
  ⟨m.split.left_nonempty.choose⟩

theorem facet_subset_image (m : SimplexAttachmentModel C V B f)
    (i : V) (hi : i ∈ m.split.right) :
    simplexFacet (fun j : V => f j.1) i ⊆ f '' C := by
  intro y hy
  exact m.roof_subset (mem_iUnion₂.mpr ⟨i, hi, hy⟩)

theorem card_index (_m : SimplexAttachmentModel C V B f) : Fintype.card V = V.card :=
  Fintype.card_coe V

theorem moving_eq_image (m : SimplexAttachmentModel C V B f)
    (hf : InjOn f (convexHull ℝ (V : Set E))) :
    convexHull ℝ (range (fun i : V => f i.1)) \ m.split.lowerRoof (fun i : V => f i.1) =
      f '' (convexHull ℝ (V : Set E) \ simplexRoof V B) := by
  rw [m.simplex_eq, m.lowerRoof_eq]
  symm
  exact hf.image_sdiff_subset (simplexRoof_subset V B)

end SimplexAttachmentModel

theorem SimplexAttachment.affineModel_exists_inverse {C : Set E} {V B : Finset E}
    (h : SimplexAttachment C V B) (f : E → F) (A : E →ᵃ[ℝ] F)
    (hA : EqOn f A (convexHull ℝ (V : Set E)))
    (hf : InjOn f (convexHull ℝ (V : Set E))) :
    ∃ I : F →ᵃ[ℝ] E,
      (∀ x ∈ convexHull ℝ (V : Set E), I (f x) = x) ∧
      (∀ y ∈ convexHull ℝ (range (fun i : V => f i.1)),
        I y ∈ convexHull ℝ (V : Set E) ∧ f (I y) = y) := by
  let m := h.affineModel f A hA hf
  have hAi : AffineIndependent ℝ (fun i : V => A i.1) := by
    convert m.independent using 1
    funext i
    exact (hA (subset_convexHull ℝ _ i.2)).symm
  obtain ⟨I, hIA, _⟩ := exists_affine_inverse_on_affineSpan
    (h.properRoof.nonempty.mono h.properRoof.subset) A hAi
  have hleft : ∀ x ∈ convexHull ℝ (V : Set E), I (f x) = x := by
    intro x hx
    rw [hA hx]
    exact hIA x (convexHull_subset_affineSpan _ hx)
  refine ⟨I, hleft, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := m.simplex_eq.subset hy
  rw [hleft x hx]
  exact ⟨hx, rfl⟩

end

end DifferentialGeometry.Topology.Engulfing
