import DifferentialGeometry.Topology.SimplicialComplex.Expansion.ElementaryCollapse
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementSupport

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem finset_image_erase_of_injOn {V : Finset E} {f : E → F}
    (hf : InjOn f (V : Set E)) {i : E} (hi : i ∈ V) :
    (V.erase i).image f = (V.image f).erase (f i) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun he => hxi (hf hx hi he), x, hx, rfl⟩
  · rintro ⟨hyi, x, hx, rfl⟩
    exact ⟨x, ⟨fun he => hyi (congrArg f he), hx⟩, rfl⟩

theorem ProperSimplexRoof.image {V B : Finset E} (h : ProperSimplexRoof V B)
    {f : E → F} (hf : InjOn f (V : Set E)) :
    ProperSimplexRoof (V.image f) (B.image f) := by
  refine ⟨Finset.image_subset_image h.subset, h.nonempty.image f, ?_⟩
  obtain ⟨x, hx⟩ := h.complement_nonempty
  obtain ⟨hxV, hxB⟩ := Finset.mem_sdiff.mp hx
  refine ⟨f x, Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x, hxV, rfl⟩, ?_⟩⟩
  rintro hy
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hy
  exact hxB ((hf (h.subset hy) hxV he) ▸ hy)

theorem image_simplexRoof_of_affine {V B : Finset E} {f : E → F}
    (hB : B ⊆ V) (A : E →ᵃ[ℝ] F)
    (hA : EqOn f A (convexHull ℝ (V : Set E)))
    (hf : InjOn f (V : Set E)) :
    f '' simplexRoof V B = simplexRoof (V.image f) (B.image f) := by
  have hfacet (i : E) (hi : i ∈ B) :
      f '' convexHull ℝ (V.erase i : Set E) =
        convexHull ℝ ((V.image f).erase (f i) : Set F) := by
    rw [image_convexHull_eq_of_eqOn_affineMap f A
      (hA.mono (convexHull_mono (Finset.erase_subset i V))),
      ← Finset.coe_image, finset_image_erase_of_injOn hf (hB hi)]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨f i, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      (hfacet i hi).subset (mem_image_of_mem f hx)⟩
  · intro hy
    obtain ⟨j, hj, hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨x, hx, rfl⟩ := (hfacet i hi).symm.subset hy
    exact ⟨x, mem_iUnion₂.mpr ⟨i, hi, hx⟩, rfl⟩

theorem SimplexAttachment.image {K : SimplicialComplex ℝ E}
    {Q : SimplicialComplex ℝ F} {C : Set E} {V B : Finset E}
    (h : SimplexAttachment C V B) (hC : C ⊆ K.space) (hV : V ∈ K.faces)
    {f : E → F} (hf : InjOn f K.space)
    (A : E →ᵃ[ℝ] F) (hA : EqOn f A (convexHull ℝ (V : Set E)))
    (hQ : V.image f ∈ Q.faces) :
    SimplexAttachment (f '' C) (V.image f) (B.image f) := by
  have hfV : InjOn f (V : Set E) := hf.mono (K.subset_space hV)
  refine ⟨Q.indep hQ, h.properRoof.image hfV, ?_⟩
  rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap f A hA,
    ← hf.image_inter hC (K.convexHull_subset_space hV), h.intersection,
    image_simplexRoof_of_affine h.properRoof.subset A hA hfV]

theorem FiniteSimplexExpansionIn.image {K : SimplicialComplex ℝ E}
    {Q : SimplicialComplex ℝ F} {A C : Set E}
    (h : FiniteSimplexExpansionIn K A C) (hC : C ⊆ K.space)
    (f : E → F) (hf : InjOn f K.space)
    (ha : ∀ V ∈ K.faces, ∃ a : E →ᵃ[ℝ] F, EqOn f a (convexHull ℝ (V : Set E)))
    (hQ : ∀ V ∈ K.faces, V.image f ∈ Q.faces) :
    FiniteSimplexExpansionIn Q (f '' A) (f '' C) := by
  induction h with
  | refl => exact .refl _
  | @snoc C V B he hV hattach ih =>
    have hCK : C ⊆ K.space := subset_union_left.trans hC
    obtain ⟨a, ha⟩ := ha V hV
    have hnew := (ih hCK).snoc (hQ V hV) (hattach.image hCK hV hf a ha (hQ V hV))
    rw [image_union, image_convexHull_eq_of_eqOn_affineMap f a ha, ← Finset.coe_image]
    exact hnew

theorem FiniteSimplexExpansionIn.mono {K P : SimplicialComplex ℝ E} {A C : Set E}
    (h : FiniteSimplexExpansionIn K A C) (hKP : K.faces ⊆ P.faces) :
    FiniteSimplexExpansionIn P A C := by
  induction h with
  | refl => exact .refl _
  | snoc _ hV ha ih => exact ih.snoc (hKP hV) ha

theorem FiniteSimplexExpansionIn.restrict {K D : SimplicialComplex ℝ E} {A C : Set E}
    (h : FiniteSimplexExpansionIn K A C) (hDK : D.faces ⊆ K.faces)
    (hC : C ⊆ D.space) : FiniteSimplexExpansionIn D A C := by
  induction h with
  | refl => exact .refl _
  | @snoc C V B he hV ha ih =>
    have hVD : V ∈ D.faces := by
      have hcent : V.centroid ℝ id ∈ D.space := hC (Or.inr
        (V.centroid_mem_convexHull (K.nonempty_of_mem_faces hV)))
      obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hcent
      exact D.down_closed ht (face_subset_of_centroid_mem K hV (hDK ht) hct)
        (K.nonempty_of_mem_faces hV)
    exact (ih (subset_union_left.trans hC)).snoc hVD ha

end

end DifferentialGeometry.Topology.Engulfing
