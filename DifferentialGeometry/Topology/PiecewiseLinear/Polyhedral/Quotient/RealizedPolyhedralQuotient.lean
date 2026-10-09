import DifferentialGeometry.Topology.SimplicialComplex.Realization.BarycentricRealization

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def realizedPolyhedralQuotientMap
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    (standardRealization P).space → (subcomplexQuotientComplex P D q).space :=
  subcomplexQuotientMap P D q ∘ (doubleBarycentricRealizationHomeomorph P).symm

theorem continuous_realizedPolyhedralQuotientMap
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Continuous (realizedPolyhedralQuotientMap P D q) :=
  (continuous_standardVertexMap _ _).comp (doubleBarycentricRealizationHomeomorph P).symm.continuous

theorem surjective_realizedPolyhedralQuotientMap
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Function.Surjective (realizedPolyhedralQuotientMap P D q) :=
  (surjective_standardVertexMap _ _).comp (doubleBarycentricRealizationHomeomorph P).symm.surjective

theorem isQuotientMap_realizedPolyhedralQuotientMap
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    IsQuotientMap (realizedPolyhedralQuotientMap P D q) :=
  IsQuotientMap.of_surjective_continuous (surjective_realizedPolyhedralQuotientMap P D q)
    (continuous_realizedPolyhedralQuotientMap P D q)

@[simp] theorem realizedPolyhedralQuotientMap_subdivision
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    realizedPolyhedralQuotientMap P D q (doubleBarycentricRealizationHomeomorph P x) =
      subcomplexQuotientMap P D q x := by
  simp [realizedPolyhedralQuotientMap]

theorem realizedPolyhedralQuotientMap_fiber_iff
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P) (q : ι → κ)
    (hq : ∀ s ∈ D.faces, (s : Set ι).InjOn q)
    (x y : (standardRealization P).space) :
    realizedPolyhedralQuotientMap P D q x = realizedPolyhedralQuotientMap P D q y ↔
      x = y ∨
        (x.val ∈ (standardRealization D).space ∧ y.val ∈ (standardRealization D).space ∧
          vertexPushforward q x.val = vertexPushforward q y.val) := by
  let e := doubleBarycentricRealizationHomeomorph P
  have hxe : doubleBarycentricEvaluation (e.symm x).val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hye : doubleBarycentricEvaluation (e.symm y).val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hxD : x.val ∈ (standardRealization D).space ↔
      (e.symm x).val ∈ (standardRealization (abstractBarycentric (abstractBarycentric D))).space := by
    have h := doubleBarycentricRealizationHomeomorph_mem_subcomplex_iff P D hDP (e.symm x)
    simpa only [show doubleBarycentricRealizationHomeomorph P = e from rfl,
      e.apply_symm_apply] using h
  have hyD : y.val ∈ (standardRealization D).space ↔
      (e.symm y).val ∈ (standardRealization (abstractBarycentric (abstractBarycentric D))).space := by
    have h := doubleBarycentricRealizationHomeomorph_mem_subcomplex_iff P D hDP (e.symm y)
    simpa only [show doubleBarycentricRealizationHomeomorph P = e from rfl,
      e.apply_symm_apply] using h
  change subcomplexQuotientMap P D q (e.symm x) = subcomplexQuotientMap P D q (e.symm y) ↔ _
  rw [subcomplexQuotientMap_fiber_iff P D hDP q hq]
  constructor
  · rintro (hxy | ⟨hxA, hyA, hxy⟩)
    · exact Or.inl (e.symm.injective hxy)
    · refine Or.inr ⟨hxD.mpr hxA, hyD.mpr hyA, ?_⟩
      have he := (doubleFaceImage_eq_iff D q hq hxA hyA).mp hxy
      rwa [hxe, hye] at he
  · rintro (rfl | ⟨hxA, hyA, hxy⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨hxD.mp hxA, hyD.mp hyA, ?_⟩
      apply (doubleFaceImage_eq_iff D q hq (hxD.mp hxA) (hyD.mp hyA)).mpr
      rwa [hxe, hye]

def realizedPolyhedralQuotientHomeomorph
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Quotient (Setoid.ker (realizedPolyhedralQuotientMap P D q)) ≃ₜ
      (subcomplexQuotientComplex P D q).space :=
  (isQuotientMap_realizedPolyhedralQuotientMap P D q).homeomorph
    (f := ⟨realizedPolyhedralQuotientMap P D q, continuous_realizedPolyhedralQuotientMap P D q⟩)

def realizedQuotientImageComplex (D J : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    SimplicialComplex ℝ ((Finset (Finset κ) ⊕ Finset (Finset ι)) → ℝ) :=
  standardRealization ((abstractBarycentric (abstractBarycentric J)).map
    (quotientFaceLabel D.faces (fun s : Finset ι => s.image q)))

theorem realizedQuotientImageComplex_faces_subset
    (P D J : PreAbstractSimplicialComplex ι) (hJP : J ≤ P) (q : ι → κ) :
    (realizedQuotientImageComplex D J q).faces ⊆ (subcomplexQuotientComplex P D q).faces := by
  rintro _ ⟨s, ⟨t, ht, rfl⟩, rfl⟩
  exact ⟨_, ⟨t, abstractBarycentric_mono (abstractBarycentric_mono hJP) ht, rfl⟩, rfl⟩

theorem realizedQuotientImageComplex_face_card_le
    (D J : PreAbstractSimplicialComplex ι) (q : ι → κ) {r : ℕ}
    (hr : ∀ s ∈ J.faces, s.card ≤ r) :
    ∀ s ∈ (realizedQuotientImageComplex D J q).faces, s.card ≤ r := by
  apply standardRealization_face_card_le
  rintro _ ⟨s, hs, rfl⟩
  exact (Finset.card_image_le).trans
    (abstractBarycentric_face_card_le _ (abstractBarycentric_face_card_le J hr) s hs)

theorem realizedQuotientImageComplex_space
    (P D J : PreAbstractSimplicialComplex ι) (hJP : J ≤ P) (q : ι → κ) :
    (realizedQuotientImageComplex D J q).space =
      (fun x : (standardRealization P).space => (realizedPolyhedralQuotientMap P D q x).val) ''
        {x | x.val ∈ (standardRealization J).space} := by
  rw [show (realizedQuotientImageComplex D J q).space =
    vertexPushforward (quotientFaceLabel D.faces (fun s : Finset ι => s.image q)) ''
      (standardRealization (abstractBarycentric (abstractBarycentric J))).space from
        (vertexPushforward_image_space _ _).symm]
  let e := doubleBarycentricRealizationHomeomorph P
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxP := standardRealization_mono
      (abstractBarycentric_mono (abstractBarycentric_mono hJP)) hx
    let x' : (standardRealization (abstractBarycentric (abstractBarycentric P))).space := ⟨x, hxP⟩
    refine ⟨e x', (doubleBarycentricRealizationHomeomorph_mem_subcomplex_iff P J hJP x').mpr hx, ?_⟩
    exact congrArg Subtype.val (realizedPolyhedralQuotientMap_subdivision P D q x')
  · rintro ⟨x, hx, rfl⟩
    change x.val ∈ (standardRealization J).space at hx
    refine ⟨(e.symm x).val, ?_, rfl⟩
    apply (doubleBarycentricRealizationHomeomorph_mem_subcomplex_iff P J hJP (e.symm x)).mp
    simpa only [show doubleBarycentricRealizationHomeomorph P = e from rfl,
      e.apply_symm_apply] using hx

theorem exists_descended_map_realizedPolyhedralQuotient
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P) (q : ι → κ)
    (hq : ∀ s ∈ D.faces, (s : Set ι).InjOn q)
    (F : C((standardRealization P).space, Y))
    (hF : ∀ x y : (standardRealization P).space,
      x.val ∈ (standardRealization D).space → y.val ∈ (standardRealization D).space →
      (F x = F y ↔ vertexPushforward q x.val = vertexPushforward q y.val)) :
    ∃ G : C((subcomplexQuotientComplex P D q).space, Y),
      (∀ x, G (realizedPolyhedralQuotientMap P D q x) = F x) ∧
      IsClosedEmbedding (fun z : realizedPolyhedralQuotientMap P D q ''
        {x | x.val ∈ (standardRealization D).space} => G z.val) := by
  let Q := realizedPolyhedralQuotientMap P D q
  have hQs : Function.Surjective Q := surjective_realizedPolyhedralQuotientMap P D q
  let G : (subcomplexQuotientComplex P D q).space → Y := fun z => F (Function.surjInv hQs z)
  have hfactor : ∀ x, G (Q x) = F x := by
    intro x
    have he := Function.surjInv_eq hQs (Q x)
    rcases (realizedPolyhedralQuotientMap_fiber_iff P D hDP q hq _ _).mp he with
      heq | ⟨hxA, hyA, heq⟩
    · exact congrArg F heq
    · exact (hF _ _ hxA hyA).mpr heq
  have hGc : Continuous G := by
    apply (isQuotientMap_realizedPolyhedralQuotientMap P D q).continuous_iff.mpr
    have he : G ∘ Q = F := funext hfactor
    rw [show G ∘ realizedPolyhedralQuotientMap P D q = F from he]
    exact F.continuous
  let S : Set (standardRealization P).space := {x | x.val ∈ (standardRealization D).space}
  have hSc : IsCompact S :=
    ((isCompact_standardRealization_space D).isClosed.preimage continuous_subtype_val).isCompact
  have hQSc : IsCompact (Q '' S) := hSc.image (continuous_realizedPolyhedralQuotientMap P D q)
  let : CompactSpace (Q '' S) := isCompact_iff_compactSpace.mp hQSc
  refine ⟨⟨G, hGc⟩, hfactor, Continuous.isClosedEmbedding
    (hGc.comp continuous_subtype_val) ?_⟩
  intro z w hzw
  obtain ⟨x, hx, hxz⟩ := z.property
  obtain ⟨y, hy, hyw⟩ := w.property
  change Q x = z.val at hxz
  change Q y = w.val at hyw
  have hxy : F x = F y := by
    rw [← hfactor x, ← hfactor y, hxz, hyw]
    exact hzw
  apply Subtype.ext
  rw [← hxz, ← hyw]
  exact (realizedPolyhedralQuotientMap_fiber_iff P D hDP q hq x y).mpr
    (Or.inr ⟨hx, hy, (hF x y hx hy).mp hxy⟩)

end

end DifferentialGeometry.Topology.Engulfing
