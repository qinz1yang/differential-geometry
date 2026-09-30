import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.PiecewiseApproximation
import Mathlib.Topology.Homeomorph.Lemmas

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def disjointComplexUnion (K L : SimplicialComplex ℝ E) (hdisj : Disjoint K.space L.space) :
    SimplicialComplex ℝ E where
  faces := K.faces ∪ L.faces
  isRelLowerSet_faces := by
    rintro s (hs | hs)
    · exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht => Or.inl (K.down_closed hs hts ht)⟩
    · exact ⟨L.nonempty_of_mem_faces hs, fun t hts ht => Or.inr (L.down_closed hs hts ht)⟩
  indep := fun hs => hs.elim K.indep L.indep
  inter_subset_convexHull := by
    rintro s t (hs | hs) (ht | ht)
    · exact K.inter_subset_convexHull hs ht
    · rintro x ⟨hx, hy⟩
      exact False.elim (Set.disjoint_left.mp hdisj (K.convexHull_subset_space hs hx)
        (L.convexHull_subset_space ht hy))
    · rintro x ⟨hx, hy⟩
      exact False.elim (Set.disjoint_left.mp hdisj (K.convexHull_subset_space ht hy)
        (L.convexHull_subset_space hs hx))
    · exact L.inter_subset_convexHull hs ht

omit [DecidableEq E] in
@[simp] theorem disjointComplexUnion_space (K L : SimplicialComplex ℝ E)
    (hdisj : Disjoint K.space L.space) :
    (disjointComplexUnion K L hdisj).space = K.space ∪ L.space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs | hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    · exact Or.inl (K.convexHull_subset_space hs hxs)
    · exact Or.inr (L.convexHull_subset_space hs hxs)
  · rintro (hx | hx)
    · obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (disjointComplexUnion K L hdisj).convexHull_subset_space (Or.inl hs) hxs
    · obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (disjointComplexUnion K L hdisj).convexHull_subset_space (Or.inr hs) hxs

def geometricUnionLeft : E →ᵃ[ℝ] E × F × ℝ :=
  (AffineMap.id ℝ E).prod (AffineMap.const ℝ E (0, 0))

def geometricUnionRight : F →ᵃ[ℝ] E × F × ℝ :=
  (AffineMap.const ℝ F 0).prod ((AffineMap.id ℝ F).prod (AffineMap.const ℝ F 1))

omit [DecidableEq E] [DecidableEq F] in
@[simp] theorem geometricUnionLeft_apply (x : E) :
    (geometricUnionLeft (F := F)) x = (x, 0, 0) := rfl

omit [DecidableEq E] [DecidableEq F] in
@[simp] theorem geometricUnionRight_apply (y : F) :
    (geometricUnionRight (E := E)) y = (0, y, 1) := rfl

omit [DecidableEq E] [DecidableEq F] in
theorem geometricUnionLeft_injective : Function.Injective (geometricUnionLeft (E := E) (F := F)) :=
  fun _ _ h => congrArg Prod.fst h

omit [DecidableEq E] [DecidableEq F] in
theorem geometricUnionRight_injective : Function.Injective (geometricUnionRight (E := E) (F := F)) :=
  fun _ _ h => congrArg (fun z => z.2.1) h

def geometricUnionLeftComplex (K : SimplicialComplex ℝ E) : SimplicialComplex ℝ (E × F × ℝ) :=
  injectiveImageComplex K geometricUnionLeft
    (fun _ _ => ⟨geometricUnionLeft, fun _ _ => rfl⟩) geometricUnionLeft_injective.injOn

def geometricUnionRightComplex (T : SimplicialComplex ℝ F) : SimplicialComplex ℝ (E × F × ℝ) :=
  injectiveImageComplex T geometricUnionRight
    (fun _ _ => ⟨geometricUnionRight, fun _ _ => rfl⟩) geometricUnionRight_injective.injOn

@[simp] theorem geometricUnionLeftComplex_space (K : SimplicialComplex ℝ E) :
    (geometricUnionLeftComplex (F := F) K).space = geometricUnionLeft '' K.space :=
  injectiveImageComplex_space K _ _ _

@[simp] theorem geometricUnionRightComplex_space (T : SimplicialComplex ℝ F) :
    (geometricUnionRightComplex (E := E) T).space = geometricUnionRight '' T.space :=
  injectiveImageComplex_space T _ _ _

theorem geometricUnion_complexes_disjoint (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F) :
    Disjoint (geometricUnionLeftComplex (F := F) K).space
      (geometricUnionRightComplex (E := E) T).space := by
  rw [geometricUnionLeftComplex_space, geometricUnionRightComplex_space]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have h : (1 : ℝ) = 0 := congrArg (fun z => z.2.2) he
  norm_num at h

def geometricDisjointUnion (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F) :
    SimplicialComplex ℝ (E × F × ℝ) :=
  disjointComplexUnion (geometricUnionLeftComplex K) (geometricUnionRightComplex T)
    (geometricUnion_complexes_disjoint K T)

@[simp] theorem geometricDisjointUnion_space (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F) :
    (geometricDisjointUnion K T).space =
      geometricUnionLeft '' K.space ∪ geometricUnionRight '' T.space := by
  simp [geometricDisjointUnion]

theorem geometricDisjointUnion_finite_faces (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (hK : K.faces.Finite) (hT : T.faces.Finite) :
    (geometricDisjointUnion K T).faces.Finite :=
  (injectiveImageComplex_finite_faces K hK _ _ _).union
    (injectiveImageComplex_finite_faces T hT _ _ _)

theorem geometricDisjointUnion_face_card_le (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) {d : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ d) (hT : ∀ s ∈ T.faces, s.card ≤ d) :
    ∀ s ∈ (geometricDisjointUnion K T).faces, s.card ≤ d := by
  rintro s (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
  · exact Finset.card_image_le.trans (hK u hu)
  · exact Finset.card_image_le.trans (hT u hu)

theorem geometricUnionLeftComplex_mono {K J : SimplicialComplex ℝ E} (h : J.faces ⊆ K.faces) :
    (geometricUnionLeftComplex (F := F) J).faces ⊆ (geometricUnionLeftComplex (F := F) K).faces := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, h hs, rfl⟩

theorem geometricUnionRightComplex_mono {T J : SimplicialComplex ℝ F} (h : J.faces ⊆ T.faces) :
    (geometricUnionRightComplex (E := E) J).faces ⊆ (geometricUnionRightComplex (E := E) T).faces := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, h hs, rfl⟩

theorem geometricDisjointUnion_mono {K J : SimplicialComplex ℝ E}
    {T S : SimplicialComplex ℝ F} (hJK : J.faces ⊆ K.faces) (hST : S.faces ⊆ T.faces) :
    (geometricDisjointUnion J S).faces ⊆ (geometricDisjointUnion K T).faces :=
  union_subset_union (geometricUnionLeftComplex_mono hJK) (geometricUnionRightComplex_mono hST)

def geometricUnionLeftProjection : (E × F × ℝ) →ᵃ[ℝ] E :=
  (LinearMap.fst ℝ E (F × ℝ)).toAffineMap

def geometricUnionRightProjection : (E × F × ℝ) →ᵃ[ℝ] F :=
  ((LinearMap.fst ℝ F ℝ).comp (LinearMap.snd ℝ E (F × ℝ))).toAffineMap

omit [DecidableEq E] [DecidableEq F] in
@[simp] theorem geometricUnionLeftProjection_left (x : E) :
    geometricUnionLeftProjection (geometricUnionLeft (F := F) x) = x := rfl

omit [DecidableEq E] [DecidableEq F] in
@[simp] theorem geometricUnionRightProjection_right (x : F) :
    geometricUnionRightProjection (geometricUnionRight (E := E) x) = x := rfl

theorem geometricUnionLeft_face_sections (K : SimplicialComplex ℝ E)
    {t : Finset (E × F × ℝ)} (ht : t ∈ (geometricUnionLeftComplex (F := F) K).faces) :
    ∃ s ∈ K.faces, ∀ y ∈ convexHull ℝ (t : Set (E × F × ℝ)),
      geometricUnionLeftProjection y ∈ convexHull ℝ (s : Set E) ∧
        geometricUnionLeft (geometricUnionLeftProjection y) = y := by
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s, hs, ?_⟩
  rw [Finset.coe_image, ← geometricUnionLeft.image_convexHull]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hx, rfl⟩

theorem geometricUnionRight_face_sections (T : SimplicialComplex ℝ F)
    {t : Finset (E × F × ℝ)} (ht : t ∈ (geometricUnionRightComplex (E := E) T).faces) :
    ∃ s ∈ T.faces, ∀ y ∈ convexHull ℝ (t : Set (E × F × ℝ)),
      geometricUnionRightProjection y ∈ convexHull ℝ (s : Set F) ∧
        geometricUnionRight (geometricUnionRightProjection y) = y := by
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s, hs, ?_⟩
  rw [Finset.coe_image, ← geometricUnionRight.image_convexHull]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hx, rfl⟩

def geometricDisjointUnionInl (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F) :
    C(K.space, (geometricDisjointUnion K T).space) := by
  refine ⟨fun x => ⟨geometricUnionLeft x.1, ?_⟩, ?_⟩
  · rw [geometricDisjointUnion_space]
    exact Or.inl (mem_image_of_mem _ x.2)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk (continuous_const.prodMk continuous_const)

def geometricDisjointUnionInr (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F) :
    C(T.space, (geometricDisjointUnion K T).space) := by
  refine ⟨fun x => ⟨geometricUnionRight x.1, ?_⟩, ?_⟩
  · rw [geometricDisjointUnion_space]
    exact Or.inr (mem_image_of_mem _ x.2)
  · apply Continuous.subtype_mk
    exact continuous_const.prodMk (continuous_subtype_val.prodMk continuous_const)

@[simp] theorem geometricDisjointUnionInl_val (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (x : K.space) :
    (geometricDisjointUnionInl K T x).val = geometricUnionLeft x.val := rfl

@[simp] theorem geometricDisjointUnionInr_val (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (x : T.space) :
    (geometricDisjointUnionInr K T x).val = geometricUnionRight x.val := rfl

theorem geometricDisjointUnionInl_injective (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) : Function.Injective (geometricDisjointUnionInl K T) := by
  intro x y h
  exact Subtype.ext (geometricUnionLeft_injective (congrArg Subtype.val h))

theorem geometricDisjointUnionInr_injective (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) : Function.Injective (geometricDisjointUnionInr K T) := by
  intro x y h
  exact Subtype.ext (geometricUnionRight_injective (congrArg Subtype.val h))

theorem geometricDisjointUnion_sum_bijective (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) :
    Function.Bijective (Sum.elim (geometricDisjointUnionInl K T) (geometricDisjointUnionInr K T)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (geometricDisjointUnionInl_injective K T h)
      | inr y =>
        have hh : (0 : ℝ) = 1 := congrArg (fun z => z.val.2.2) h
        norm_num at hh
    | inr x =>
      cases y with
      | inl y =>
        have hh : (1 : ℝ) = 0 := congrArg (fun z => z.val.2.2) h
        norm_num at hh
      | inr y => exact congrArg Sum.inr (geometricDisjointUnionInr_injective K T h)
  · intro z
    have hz := (geometricDisjointUnion_space K T).subset z.2
    rcases hz with ⟨x, hx, h⟩ | ⟨y, hy, h⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, Subtype.ext h⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, Subtype.ext h⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def geometricDisjointUnionHomeomorph (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hT : T.faces.Finite) :
    (K.space ⊕ T.space) ≃ₜ (geometricDisjointUnion K T).space := by
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  letI : CompactSpace T.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces T hT)
  let e := Equiv.ofBijective _ (geometricDisjointUnion_sum_bijective K T)
  exact (show Continuous e from (geometricDisjointUnionInl K T).continuous.sumElim
    (geometricDisjointUnionInr K T).continuous).homeoOfEquivCompactToT2

@[simp] theorem geometricDisjointUnionHomeomorph_inl (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (hK : K.faces.Finite) (hT : T.faces.Finite) (x : K.space) :
    geometricDisjointUnionHomeomorph K T hK hT (Sum.inl x) = geometricDisjointUnionInl K T x := rfl

@[simp] theorem geometricDisjointUnionHomeomorph_inr (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (hK : K.faces.Finite) (hT : T.faces.Finite) (x : T.space) :
    geometricDisjointUnionHomeomorph K T hK hT (Sum.inr x) = geometricDisjointUnionInr K T x := rfl

theorem geometricDisjointUnionInl_isClosedEmbedding (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (hK : K.faces.Finite) :
    IsClosedEmbedding (geometricDisjointUnionInl K T) := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  exact (geometricDisjointUnionInl K T).continuous.isClosedEmbedding
    (geometricDisjointUnionInl_injective K T)

theorem geometricDisjointUnionInr_isClosedEmbedding (K : SimplicialComplex ℝ E)
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) :
    IsClosedEmbedding (geometricDisjointUnionInr K T) := by
  let : CompactSpace T.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces T hT)
  exact (geometricDisjointUnionInr K T).continuous.isClosedEmbedding
    (geometricDisjointUnionInr_injective K T)

theorem exists_continuousMap_geometricDisjointUnion {M : Type*} [TopologicalSpace M]
    (K : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hT : T.faces.Finite) (f : C(K.space, M)) (g : C(T.space, M)) :
    ∃ F₀ : C((geometricDisjointUnion K T).space, M),
      (∀ x, F₀ (geometricDisjointUnionInl K T x) = f x) ∧
      (∀ y, F₀ (geometricDisjointUnionInr K T y) = g y) := by
  let h := geometricDisjointUnionHomeomorph K T hK hT
  let F₀ : C((geometricDisjointUnion K T).space, M) :=
    ⟨Sum.elim f g ∘ h.symm, (f.continuous.sumElim g.continuous).comp h.symm.continuous⟩
  refine ⟨F₀, ?_, ?_⟩
  · intro x
    change Sum.elim f g (h.symm (h (Sum.inl x))) = f x
    rw [h.symm_apply_apply]
    rfl
  · intro y
    change Sum.elim f g (h.symm (h (Sum.inr y))) = g y
    rw [h.symm_apply_apply]
    rfl

end

end DifferentialGeometry.Topology.Engulfing
