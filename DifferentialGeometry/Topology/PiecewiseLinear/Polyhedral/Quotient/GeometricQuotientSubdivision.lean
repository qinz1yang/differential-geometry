import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.RealizedPolyhedralQuotient
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem standardFaceCentroid_mem_face {s : Finset ι} (hs : s.Nonempty) :
    standardFaceCentroid s ∈ convexHull ℝ
      (s.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ)) := by
  rw [standardFaceCentroid_eq_centroid hs, Finset.centroid_eq_centerMass _ hs]
  apply s.centerMass_mem_convexHull
  · intro i hi
    simp only [Finset.centroidWeights_apply, inv_nonneg, Nat.cast_nonneg]
  · rw [s.sum_centroidWeights_eq_one_of_nonempty ℝ hs]
    norm_num
  · intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem barycentricEvaluation_face_parent
    (P : PreAbstractSimplicialComplex ι) {C : Finset (Finset ι)}
    (hC : C ∈ (abstractBarycentric P).faces) :
    ∃ s ∈ P.faces, vertexEvaluation standardFaceCentroid '' convexHull ℝ
      (C.image (fun i => Pi.single i (1 : ℝ)) : Set (Finset ι → ℝ)) ⊆
        convexHull ℝ (s.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ)) := by
  obtain ⟨s, hs, hmax⟩ := hC.2.1.exists_largest hC.1
  refine ⟨s, hC.2.2 s hs, ?_⟩
  rw [vertexEvaluation_image_face]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image (hmax t ht)))
    (standardFaceCentroid_mem_face (hC.2.1.1 t ht))

theorem doubleBarycentricEvaluation_face_parent
    (P : PreAbstractSimplicialComplex ι) {C : Finset (Finset (Finset ι))}
    (hC : C ∈ (abstractBarycentric (abstractBarycentric P)).faces) :
    ∃ s ∈ P.faces, doubleBarycentricEvaluation '' convexHull ℝ
      (C.image (fun i => Pi.single i (1 : ℝ)) : Set (Finset (Finset ι) → ℝ)) ⊆
        convexHull ℝ (s.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ)) := by
  obtain ⟨t, ht, hCt⟩ := barycentricEvaluation_face_parent (abstractBarycentric P) hC
  obtain ⟨s, hs, hts⟩ := barycentricEvaluation_face_parent P ht
  refine ⟨s, hs, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hts (mem_image_of_mem _ (hCt (mem_image_of_mem _ hx)))

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem quotientLabel_injOn_doubleFace [Finite ι] [Finite κ]
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ D.faces, (s : Set ι).InjOn q)
    {C : Finset (Finset (Finset ι))}
    (hC : C ∈ (abstractBarycentric (abstractBarycentric P)).faces) :
    (C : Set (Finset (Finset ι))).InjOn
      (quotientFaceLabel D.faces (fun s : Finset ι => s.image q)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  exact quotientFaceLabel_injOn_chain (abstractBarycentric P) D.faces _
    (faceImage_injOn_barycentric_subcomplex P D q hq) hC

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def hasNondegeneratePLSubdivision (K : SimplicialComplex ℝ E) (q : K.space → F) : Prop :=
  ∃ R : SimplicialComplex ℝ E,
    R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
    (∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F,
      (∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → q x = A x.val) ∧
      InjOn A (convexHull ℝ (s : Set E)))

omit [DecidableEq E] [DecidableEq F] in
theorem hasNondegeneratePLSubdivision.exists_total_map
    {K : SimplicialComplex ℝ E} {q : K.space → F} (hq : hasNondegeneratePLSubdivision K q) :
    ∃ R : SimplicialComplex ℝ E, ∃ f : E → F,
      R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
      (∀ x : K.space, f x.val = q x) ∧
      (∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) ∧
      (∀ s ∈ R.faces, InjOn f (convexHull ℝ (s : Set E))) := by
  classical
  obtain ⟨R, hR, hspace, href, haff⟩ := hq
  let f : E → F := fun x => if hx : x ∈ K.space then q ⟨x, hx⟩ else 0
  have heq : ∀ x : K.space, f x.val = q x := by intro x; simp [f, x.property]
  have hface : ∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F,
      EqOn f A (convexHull ℝ (s : Set E)) ∧ InjOn A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, hA, hi⟩ := haff s hs
    refine ⟨A, ?_, hi⟩
    intro x hx
    have hxK : x ∈ K.space := hspace.subset (R.convexHull_subset_space hs hx)
    exact (heq ⟨x, hxK⟩).trans (hA ⟨x, hxK⟩ hx)
  refine ⟨R, f, hR, hspace, href, heq, ?_, ?_⟩
  · intro s hs
    obtain ⟨A, hA, _⟩ := hface s hs
    exact ⟨A, hA⟩
  · intro s hs
    obtain ⟨A, hA, hi⟩ := hface s hs
    intro x hx y hy he
    exact hi hx hy ((hA hx).symm.trans (he.trans (hA hy)))

omit [DecidableEq F] in
theorem exists_geometric_double_subdivision
    (P : PreAbstractSimplicialComplex ι) (v : ι → E) (hv : Function.Injective v)
    (K : SimplicialComplex ℝ E) (hfaces : K.faces = (P.map v).faces)
    (W : (Finset (Finset ι) → ℝ) →ₗ[ℝ] F)
    (hW : ∀ C ∈ (abstractBarycentric (abstractBarycentric P)).faces,
      InjOn W (convexHull ℝ
        (C.image (fun i => Pi.single i (1 : ℝ)) : Set (Finset (Finset ι) → ℝ))))
    (q : K.space → F)
    (hq : ∀ x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space,
      q (geometricRealizationHomeomorph P v hv K hfaces
        (doubleBarycentricRealizationHomeomorph P x)) = W x.val) :
    ∃ R : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
      (∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F,
        (∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → q x = A x.val) ∧
        InjOn A (convexHull ℝ (s : Set E))) := by
  classical
  let P₂ := abstractBarycentric (abstractBarycentric P)
  let S := standardRealization P₂
  let V : (Finset (Finset ι) → ℝ) →ₗ[ℝ] E :=
    (vertexEvaluation v).comp doubleBarycentricEvaluation
  let H : S.space ≃ₜ K.space := (doubleBarycentricRealizationHomeomorph P).trans
    (geometricRealizationHomeomorph P v hv K hfaces)
  have hH : ∀ x : S.space, (H x).val = V x.val := fun _ => rfl
  have hV : InjOn V S.space := by
    intro x hx y hy he
    have he' : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext he
    exact congrArg Subtype.val (H.injective he')
  let hVa : ∀ s ∈ S.faces, ∃ A : (Finset (Finset ι) → ℝ) →ᵃ[ℝ] E,
      EqOn V A (convexHull ℝ (s : Set (Finset (Finset ι) → ℝ))) :=
    fun _ _ => ⟨V.toAffineMap, fun _ _ => rfl⟩
  let R := injectiveImageComplex S V hVa hV
  have hRspace : R.space = K.space := by
    rw [injectiveImageComplex_space]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (H ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x.val, x.property, congrArg Subtype.val hx⟩
  have href : simplicialRefines R K := by
    rintro s ⟨t, ⟨C, hC, rfl⟩, rfl⟩
    obtain ⟨u, hu, hCu⟩ := doubleBarycentricEvaluation_face_parent P hC
    refine ⟨u.image v, hfaces.symm ▸ ⟨u, hu, rfl⟩, ?_⟩
    rw [Finset.coe_image, ← V.image_convexHull]
    rintro _ ⟨x, hx, rfl⟩
    exact (vertexEvaluation_image_face v u).subset
      (mem_image_of_mem _ (hCu (mem_image_of_mem _ hx)))
  let inv : E → (Finset (Finset ι) → ℝ) := fun y =>
    if hy : y ∈ K.space then (H.symm ⟨y, hy⟩).val else 0
  have hinv : ∀ x ∈ S.space, inv (V x) = x := by
    intro x hx
    have hmem : V x ∈ K.space := (H ⟨x, hx⟩).property
    simp only [inv, dite_eq_left hmem]
    have he : (⟨V x, hmem⟩ : K.space) = H ⟨x, hx⟩ := rfl
    rw [he, H.symm_apply_apply]
  refine ⟨R, injectiveImageComplex_finite_faces S (standardRealization_finite_faces P₂)
    V hVa hV, hRspace, href, ?_⟩
  intro s hs
  obtain ⟨A, hA⟩ := inverse_affine_on_injectiveImageComplex S V hVa hV inv hinv s hs
  refine ⟨W.toAffineMap.comp A, ?_, ?_⟩
  · intro x hx
    have hix : inv x.val = (H.symm x).val := by simp [inv, x.property]
    change q x = W (A x.val)
    rw [← hA hx, hix]
    have he := hq (H.symm x)
    change q (H (H.symm x)) = W (H.symm x).val at he
    simpa only [H.apply_symm_apply] using he
  · obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨C, hC, rfl⟩ := ht
    intro x hx y hy he
    rw [Finset.coe_image, ← V.image_convexHull] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hxS : x' ∈ S.space := S.convexHull_subset_space ⟨C, hC, rfl⟩ hx'
    have hyS : y' ∈ S.space := S.convexHull_subset_space ⟨C, hC, rfl⟩ hy'
    have hxR := mem_image_of_mem V hx'
    have hyR := mem_image_of_mem V hy'
    rw [V.image_convexHull, ← Finset.coe_image] at hxR hyR
    change W (A (V x')) = W (A (V y')) at he
    have hax : A (V x') = x' := (hA hxR).symm.trans (hinv x' hxS)
    have hay : A (V y') = y' := (hA hyR).symm.trans (hinv y' hyS)
    rw [hax, hay] at he
    exact congrArg V (hW C hC hx' hy' he)

end

end DifferentialGeometry.Topology.Engulfing
