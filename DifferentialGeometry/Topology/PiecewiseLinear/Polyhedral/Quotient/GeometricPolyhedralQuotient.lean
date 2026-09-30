import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.SimplicialVertexMap
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.RealizedPolyhedralQuotient
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.GeometricQuotientSubdivision

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def hasFacewiseAffineSections (K J : SimplicialComplex ℝ E)
    (Q R : SimplicialComplex ℝ F) (q : K.space → Q.space) : Prop :=
  ∀ t ∈ R.faces, ∃ s ∈ J.faces, ∃ B : F →ᵃ[ℝ] E,
    ∀ y ∈ convexHull ℝ (t : Set F), ∃ x : K.space,
      x.val = B y ∧ x.val ∈ convexHull ℝ (s : Set E) ∧ (q x).val = y

def ambientVertexSubcomplex (K D : SimplicialComplex ℝ E) :
    PreAbstractSimplicialComplex K.vertices where
  faces := {s | s.image Subtype.val ∈ D.faces}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.image_nonempty.mp (D.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact D.down_closed hs (Finset.image_subset_image hts) (Finset.image_nonempty.mpr ht)

theorem ambientVertexSubcomplex_le (K D : SimplicialComplex ℝ E)
    (hDK : D.faces ⊆ K.faces) : ambientVertexSubcomplex K D ≤ abstractVertexComplex K :=
  fun _ hs => hDK hs

theorem ambientVertexSubcomplex_map (K D : SimplicialComplex ℝ E)
    (hDK : D.faces ⊆ K.faces) :
    ((ambientVertexSubcomplex K D).map Subtype.val).faces = D.faces := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    let j : s → K.vertices := fun x => ⟨x.val, K.down_closed (hDK hs)
      (Finset.singleton_subset_iff.mpr x.property) (Finset.singleton_nonempty _)⟩
    let t : Finset K.vertices := s.attach.image j
    have ht : t.image Subtype.val = s := by
      change (s.attach.image j).image Subtype.val = s
      rw [Finset.image_image]
      exact Finset.attach_image_val
    refine ⟨t, ?_, ht⟩
    change t.image Subtype.val ∈ D.faces
    rwa [ht]

theorem vertexEvaluation_mem_ambientVertexSubcomplex_iff
    (K D : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hDK : D.faces ⊆ K.faces) {x : K.vertices → ℝ}
    (hx : x ∈ (standardRealization (abstractVertexComplex K)).space) :
    vertexEvaluation Subtype.val x ∈ D.space ↔
      x ∈ (standardRealization (ambientVertexSubcomplex K D)).space := by
  have himage := vertexEvaluation_image_space (ambientVertexSubcomplex K D)
    Subtype.val D (ambientVertexSubcomplex_map K D hDK).symm
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := himage.symm.subset h
    have hyK := standardRealization_mono (ambientVertexSubcomplex_le K D hDK) hy
    have hyx := vertexEvaluation_injOn_space (abstractVertexComplex K) Subtype.val
      Subtype.val_injective K (abstractVertexComplex_map K).symm hyK hx he
    exact hyx ▸ hy
  · intro h
    exact himage.subset (mem_image_of_mem _ h)

omit [DecidableEq E] in
theorem isCompact_geometric_realization_of_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space := by
  classical
  letI : Fintype K.vertices := (finite_vertices_of_finite_faces K hK).fintype
  rw [← vertexEvaluation_image_space (abstractVertexComplex K) Subtype.val K
    (abstractVertexComplex_map K).symm]
  exact (isCompact_standardRealization_space _).image
    (vertexEvaluation (Subtype.val : K.vertices → E)).continuous_of_finiteDimensional

theorem exists_euclidean_complex_model {ι : Type*} [Finite ι]
    (K : SimplicialComplex ℝ (ι → ℝ)) (hK : K.faces.Finite) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ Nonempty (K.space ≃ₜ Q.space) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e₀ : (ι → ℝ) ≃L[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (Fintype.card ι) => ℝ) (Fintype.equivFin ι)
  let e := e₀.trans (EuclideanSpace.equiv (Fin (Fintype.card ι)) ℝ).symm
  let ha : ∀ s ∈ K.faces, ∃ A : (ι → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)),
      EqOn e.toHomeomorph A (convexHull ℝ (s : Set (ι → ℝ))) :=
    fun _ _ => ⟨e.toLinearEquiv.toAffineEquiv.toAffineMap, fun _ _ => rfl⟩
  let Q := homeomorphImageComplex K e.toHomeomorph ha
  have hspace : Q.space = e.toHomeomorph '' K.space := homeomorphImageComplex_space K _ ha
  refine ⟨Fintype.card ι, Q, homeomorphImageComplex_finite_faces K hK _ ha,
    homeomorphImageComplex_face_card_le K _ ha hd, ?_⟩
  exact ⟨(e.toHomeomorph.image K.space).trans (Homeomorph.setCongr hspace.symm)⟩

omit [DecidableEq E] [DecidableEq F] in
theorem exists_geometric_polyhedral_quotient_full
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) ∧
      (∀ J : SimplicialComplex ℝ E, J.faces ⊆ K.faces →
        ∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
          R.faces ⊆ Q.faces ∧ R.space = (fun x : K.space => (q x).val) '' {x | x.val ∈ J.space} ∧
          (∀ r : ℕ, (∀ s ∈ J.faces, s.card ≤ r) → ∀ s ∈ R.faces, s.card ≤ r) ∧
          hasFacewiseAffineSections K J Q R q) ∧
      hasNondegeneratePLSubdivision K (fun x => (q x).val) := by
  classical
  obtain ⟨T, hTf, hTspace, hTdim, hTcompat, hTparent⟩ :=
    exists_compatible_image_triangulation K hK f hf hinj hd
  obtain ⟨B⟩ := exists_facewiseAffineInverse K f hf hinj
  let hT := fun s : K.faces => hTcompat s.val s.property
  let L := B.pullbackComplex T hT
  let J := complexRestriction L D
  have hL : L.faces.Finite := B.pullbackComplex_finite_faces hK T hTf hT
  have hLspace : L.space = K.space := B.pullbackComplex_space T hT
  have hJspace : J.space = D.space := B.pullbackComplex_subcomplex_space T hT D hDK
  have hJL : J.faces ⊆ L.faces := complexRestriction_faces_subset L D
  have href : simplicialRefines L K := B.pullbackComplex_refines T hT
  have hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces :=
    fun _ hs => B.pullbackComplex_face_image_mem T hT hs
  have hfL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    obtain ⟨A, hA⟩ := hf t ht
    exact ⟨A, hA.mono hst⟩
  have hinjL : ∀ s ∈ L.faces, InjOn f (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    exact (hinj t ht).mono hst
  letI : Fintype L.vertices := (finite_vertices_of_finite_faces L hL).fintype
  letI : Fintype T.vertices := (finite_vertices_of_finite_faces T hTf).fintype
  let P := abstractVertexComplex L
  let A := ambientVertexSubcomplex L J
  let v := geometricSimplicialVertexMap L T f hmap
  have hAP : A ≤ P := ambientVertexSubcomplex_le L J hJL
  have hv : ∀ s ∈ A.faces, (s : Set L.vertices).InjOn v :=
    fun s hs => geometricSimplicialVertexMap_injOn_face L T f hmap hinjL s (hAP hs)
  let H : (standardRealization P).space ≃ₜ K.space :=
    (geometricRealizationHomeomorph P Subtype.val Subtype.val_injective L
      (abstractVertexComplex_map L).symm).trans (Homeomorph.setCongr hLspace)
  have hHeval : ∀ x : (standardRealization P).space,
      (H x).val = vertexEvaluation Subtype.val x.val := fun _ => rfl
  have hHinv : ∀ x : K.space,
      vertexEvaluation Subtype.val (H.symm x).val = x.val := by
    intro x
    exact congrArg Subtype.val (H.apply_symm_apply x)
  have hAmem : ∀ x : K.space,
      (H.symm x).val ∈ (standardRealization A).space ↔ x.val ∈ D.space := by
    intro x
    rw [← vertexEvaluation_mem_ambientVertexSubcomplex_iff L J hJL (H.symm x).property,
      hHinv, hJspace]
  have hveq : ∀ x y : K.space,
      vertexPushforward v (H.symm x).val = vertexPushforward v (H.symm y).val ↔
        f x.val = f y.val := by
    intro x y
    rw [← geometricSimplicialVertexMap_fiber_iff L T f hmap hfL
      (H.symm x).property (H.symm y).property, hHinv, hHinv]
  let Q₀ := subcomplexQuotientComplex P A v
  have hQ₀ : Q₀.faces.Finite := subcomplexQuotientComplex_finite_faces P A v
  have hdim₀ : ∀ s ∈ Q₀.faces, s.card ≤ d + 1 :=
    subcomplexQuotientComplex_face_card_le P A v
      (abstractVertexComplex_face_card_le L (B.pullbackComplex_face_card_le T hT hd))
  let I := Finset (Finset T.vertices) ⊕ Finset (Finset L.vertices)
  let n := Fintype.card I
  let e₀ : (I → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℝ) (Fintype.equivFin I)
  let e := e₀.trans (EuclideanSpace.equiv (Fin n) ℝ).symm
  let ha : ∀ s ∈ Q₀.faces, ∃ B : (I → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn e.toHomeomorph B (convexHull ℝ (s : Set (I → ℝ))) :=
    fun _ _ => ⟨e.toLinearEquiv.toAffineEquiv.toAffineMap, fun _ _ => rfl⟩
  let Q := homeomorphImageComplex Q₀ e.toHomeomorph ha
  have hQ := homeomorphImageComplex_finite_faces Q₀ hQ₀ e.toHomeomorph ha
  have hdim := homeomorphImageComplex_face_card_le Q₀ e.toHomeomorph ha hdim₀
  let HQ : Q₀.space ≃ₜ Q.space := (e.toHomeomorph.image Q₀.space).trans
    (Homeomorph.setCongr (homeomorphImageComplex_space Q₀ e.toHomeomorph ha).symm)
  let q₀ := realizedPolyhedralQuotientMap P A v
  let q : C(K.space, Q.space) := ⟨HQ ∘ q₀ ∘ H.symm,
    HQ.continuous.comp ((continuous_realizedPolyhedralQuotientMap P A v).comp H.symm.continuous)⟩
  have hqs : Function.Surjective q :=
    HQ.surjective.comp ((surjective_realizedPolyhedralQuotientMap P A v).comp H.symm.surjective)
  let tag := quotientFaceLabel A.faces (fun s : Finset L.vertices => s.image v)
  let W := e.toLinearMap.comp (vertexPushforward tag)
  have hW : ∀ C ∈ (abstractBarycentric (abstractBarycentric P)).faces,
      InjOn W (convexHull ℝ (C.image (fun i => Pi.single i (1 : ℝ)) :
        Set (Finset (Finset L.vertices) → ℝ))) := by
    intro C hC x hx y hy he
    apply vertexPushforward_injective_of_supported tag
      (quotientLabel_injOn_doubleFace P A v hv hC)
      ((mem_standardFace_iff C x).mp hx).2 ((mem_standardFace_iff C y).mp hy).2
    exact e.injective he
  have hWq : ∀ x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space,
      (q (H (doubleBarycentricRealizationHomeomorph P x))).val = W x.val := by
    intro x
    change e ((q₀ (H.symm (H (doubleBarycentricRealizationHomeomorph P x)))).val) =
      e (vertexPushforward tag x.val)
    rw [H.symm_apply_apply]
    exact congrArg (fun z => e z.val) (realizedPolyhedralQuotientMap_subdivision P A v x)
  have hcompact : IsCompact K.space := isCompact_geometric_realization_of_finite K hK
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  refine ⟨n, Q, q, hQ, hdim, IsQuotientMap.of_surjective_continuous hqs q.continuous, ?_, ?_, ?_⟩
  · intro x y
    change HQ (q₀ (H.symm x)) = HQ (q₀ (H.symm y)) ↔ _
    rw [HQ.injective.eq_iff, realizedPolyhedralQuotientMap_fiber_iff P A hAP v hv,
      H.symm.injective.eq_iff, hAmem, hAmem, hveq]
  · intro N hNK
    let R := complexRestriction L N
    have hRL : R.faces ⊆ L.faces := complexRestriction_faces_subset L N
    have hRspace : R.space = N.space := B.pullbackComplex_subcomplex_space T hT N hNK
    let AR := ambientVertexSubcomplex L R
    have hARP : AR ≤ P := ambientVertexSubcomplex_le L R hRL
    let R₀ := realizedQuotientImageComplex A AR v
    have hR₀Q : R₀.faces ⊆ Q₀.faces := realizedQuotientImageComplex_faces_subset P A AR hARP v
    let haR := fun s hs => ha s (hR₀Q hs)
    let RQ := homeomorphImageComplex R₀ e.toHomeomorph haR
    refine ⟨RQ, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨s, hR₀Q hs, rfl⟩
    · rw [homeomorphImageComplex_space, realizedQuotientImageComplex_space P A AR hARP v,
        image_image]
      have hmem : ∀ x : (standardRealization P).space,
          x.val ∈ (standardRealization AR).space ↔ (H x).val ∈ N.space := by
        intro x
        rw [← vertexEvaluation_mem_ambientVertexSubcomplex_iff L R hRL x.property,
          ← hHeval, hRspace]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨H x, (hmem x).mp hx, ?_⟩
        change e ((q₀ (H.symm (H x))).val) = e ((q₀ x).val)
        rw [H.symm_apply_apply]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨H.symm x, ?_, rfl⟩
        change x.val ∈ N.space at hx
        exact (hmem (H.symm x)).mpr (by simpa only [H.apply_symm_apply] using hx)
    · intro r hr t ht
      obtain ⟨s, hs, rfl⟩ := ht
      rw [Finset.card_image_of_injective _ e.toHomeomorph.injective]
      apply realizedQuotientImageComplex_face_card_le A AR v ?_ s hs
      intro u hu
      have hu' : u.image Subtype.val ∈ R.faces := hu
      obtain ⟨w, hw, huw⟩ := complexRestriction_refines_right L N _ hu'
      have hc := ((R.indep hu').card_le_card_of_subset_affineSpan
        (fun x hx => convexHull_subset_affineSpan _
          (huw (subset_convexHull ℝ _ hx)))).trans (hr w hw)
      rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    · rintro t ⟨t₀, ⟨t₁, ⟨C, hC, rfl⟩, rfl⟩, rfl⟩
      have hCP := abstractBarycentric_mono (abstractBarycentric_mono hARP) hC
      let S := standardRealization (abstractBarycentric (abstractBarycentric P))
      have hstd : C.image (fun i => Pi.single i (1 : ℝ)) ∈ S.faces := ⟨C, hCP, rfl⟩
      obtain ⟨u, hu, hCu⟩ := doubleBarycentricEvaluation_face_parent AR hC
      have huR : u.image Subtype.val ∈ R.faces := hu
      obtain ⟨s, hs, hus⟩ := complexRestriction_refines_right L N _ huR
      obtain ⟨B₀, hB₀, _⟩ := exists_affine_inverse_on_affineSpan
        (S.nonempty_of_mem_faces hstd) W.toAffineMap
        (affineIndependent_of_injOn_convexHull (S.indep hstd) W.toAffineMap (hW C hCP))
      let V : (Finset (Finset L.vertices) → ℝ) →ₗ[ℝ] E :=
        (vertexEvaluation Subtype.val).comp doubleBarycentricEvaluation
      refine ⟨s, hs, V.toAffineMap.comp B₀, ?_⟩
      have himage : (C.image (fun i => Pi.single i (1 : ℝ))).image W =
          ((C.image tag).image (fun i => Pi.single i (1 : ℝ))).image e.toHomeomorph := by
        simp only [Finset.image_image]
        apply Finset.image_congr
        intro i hi
        change e (vertexPushforward tag (Pi.single i 1)) = e (Pi.single (tag i) 1)
        rw [vertexPushforward_single]
      intro y hy
      change y ∈ convexHull ℝ
        ((((C.image tag).image (fun i => Pi.single i (1 : ℝ))).image e.toHomeomorph) :
          Set (EuclideanSpace ℝ (Fin n))) at hy
      rw [← himage, Finset.coe_image, ← W.image_convexHull] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      let z' : S.space := ⟨z, S.convexHull_subset_space hstd hz⟩
      refine ⟨H (doubleBarycentricRealizationHomeomorph P z'), ?_, ?_, hWq z'⟩
      · change V z = V (B₀ (W z))
        exact congrArg V (hB₀ z (convexHull_subset_affineSpan _ hz)).symm
      · apply hus
        exact (vertexEvaluation_image_face (Subtype.val : L.vertices → E) u).subset
          (mem_image_of_mem _ (hCu (mem_image_of_mem _ hz)))
  · let qL : L.space → EuclideanSpace ℝ (Fin n) :=
      fun x => (q (Homeomorph.setCongr hLspace x)).val
    have hcomm : ∀ x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space,
        qL (geometricRealizationHomeomorph P Subtype.val Subtype.val_injective L
          (abstractVertexComplex_map L).symm (doubleBarycentricRealizationHomeomorph P x)) =
            W x.val := by
      intro x
      change e ((q₀ (H.symm (H (doubleBarycentricRealizationHomeomorph P x)))).val) =
        e (vertexPushforward tag x.val)
      rw [H.symm_apply_apply]
      exact congrArg (fun z => e z.val) (realizedPolyhedralQuotientMap_subdivision P A v x)
    obtain ⟨R, hR, hRLspace, hRLref, hRaff⟩ := exists_geometric_double_subdivision
      P Subtype.val Subtype.val_injective L (abstractVertexComplex_map L).symm W hW qL hcomm
    refine ⟨R, hR, hRLspace.trans hLspace, ?_, ?_⟩
    · intro s hs
      obtain ⟨t, ht, hst⟩ := hRLref s hs
      obtain ⟨u, hu, htu⟩ := href t ht
      exact ⟨u, hu, hst.trans htu⟩
    · intro s hs
      obtain ⟨B, hB, hBi⟩ := hRaff s hs
      refine ⟨B, ?_, hBi⟩
      intro x hx
      exact hB ((Homeomorph.setCongr hLspace).symm x) hx

omit [DecidableEq E] [DecidableEq F] in
theorem exists_geometric_polyhedral_quotient_with_subcomplex_images
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) ∧
      (∀ J : SimplicialComplex ℝ E, J.faces ⊆ K.faces →
        ∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
          R.faces ⊆ Q.faces ∧ R.space = (fun x : K.space => (q x).val) '' {x | x.val ∈ J.space} ∧
          ∀ r : ℕ, (∀ s ∈ J.faces, s.card ≤ r) → ∀ s ∈ R.faces, s.card ≤ r) := by
  classical
  obtain ⟨n, Q, q, hQ, hdQ, hq, hrel, himages, _⟩ :=
    exists_geometric_polyhedral_quotient_full K D hK hDK f hf hinj hd
  refine ⟨n, Q, q, hQ, hdQ, hq, hrel, ?_⟩
  intro J hJK
  obtain ⟨R, hR, hspace, hdim, _⟩ := himages J hJK
  exact ⟨R, hR, hspace, hdim⟩

omit [DecidableEq E] [DecidableEq F] in
theorem exists_geometric_polyhedral_quotient
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) := by
  classical
  obtain ⟨n, Q, q, hQ, hdQ, hq, hrel, _⟩ :=
    exists_geometric_polyhedral_quotient_with_subcomplex_images K D hK hDK f hf hinj hd
  exact ⟨n, Q, q, hQ, hdQ, hq, hrel⟩

theorem exists_descended_map_of_subspace_fibers
    {X Y Z M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace M] [T2Space M]
    (q : C(X, Y)) (hq : IsQuotientMap q) (S : Set X) (hS : IsCompact S)
    (f : X → Z)
    (hrel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ S ∧ y ∈ S ∧ f x = f y))
    (F : C(X, M)) (hF : ∀ x ∈ S, ∀ y ∈ S, F x = F y ↔ f x = f y) :
    ∃ G : C(Y, M), (∀ x, G (q x) = F x) ∧
      IsClosedEmbedding (fun z : q '' S => G z.val) := by
  let G : Y → M := fun z => F (Function.surjInv hq.surjective z)
  have hfactor : ∀ x, G (q x) = F x := by
    intro x
    have he := Function.surjInv_eq hq.surjective (q x)
    rcases (hrel _ _).mp he with heq | ⟨hx, hy, heq⟩
    · exact congrArg F heq
    · exact (hF _ hx _ hy).mpr heq
  have hGc : Continuous G := by
    apply hq.continuous_iff.mpr
    rw [show G ∘ q = F from funext hfactor]
    exact F.continuous
  have hQS : IsCompact (q '' S) := hS.image q.continuous
  letI : CompactSpace (q '' S) := isCompact_iff_compactSpace.mp hQS
  refine ⟨⟨G, hGc⟩, hfactor, Continuous.isClosedEmbedding
    (hGc.comp continuous_subtype_val) ?_⟩
  intro z w hzw
  obtain ⟨x, hx, hxz⟩ := z.property
  obtain ⟨y, hy, hyw⟩ := w.property
  have hxy : F x = F y := by
    rw [← hfactor x, ← hfactor y, hxz, hyw]
    exact hzw
  apply Subtype.ext
  rw [← hxz, ← hyw]
  exact (hrel x y).mpr (Or.inr ⟨hx, hy, (hF x hx y hy).mp hxy⟩)

theorem injOn_of_subspace_fibers {X Y Z : Type*} (q : X → Y) (S : Set X) (f : X → Z)
    (hrel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ S ∧ y ∈ S ∧ f x = f y))
    {A : Set X} (hA : InjOn f (A ∩ S)) : InjOn q A := by
  intro x hx y hy he
  rcases (hrel x y).mp he with heq | ⟨hxS, hyS, hxy⟩
  · exact heq
  · exact hA ⟨hx, hxS⟩ ⟨hy, hyS⟩ hxy

theorem preimage_image_eq_of_subspace_fibers {X Y Z : Type*}
    (q : X → Y) (S : Set X) (f : X → Z)
    (hrel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ S ∧ y ∈ S ∧ f x = f y))
    {A : Set X} (hA : ∀ x ∈ A ∩ S, ∀ y ∈ S, f y = f x → y ∈ A) :
    q ⁻¹' (q '' A) = A := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, hxy⟩
    rcases (hrel x y).mp hxy with rfl | ⟨hxS, hyS, he⟩
    · exact hx
    · exact hA x ⟨hx, hxS⟩ y hyS he.symm
  · exact subset_preimage_image _ _

omit [DecidableEq E] [DecidableEq F] in
theorem exists_geometric_polyhedral_quotient_with_descent
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (F₀ : C(K.space, M))
    (hF : ∀ x y : K.space, x.val ∈ D.space → y.val ∈ D.space →
      (F₀ x = F₀ y ↔ f x.val = f y.val)) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space), ∃ G : C(Q.space, M),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) ∧
      (∀ x, G (q x) = F₀ x) ∧
      IsClosedEmbedding (fun z : q '' {x | x.val ∈ D.space} => G z.val) := by
  classical
  obtain ⟨n, Q, q, hQ, hdim, hq, hrel⟩ :=
    exists_geometric_polyhedral_quotient K D hK hDK f hf hinj hd
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_geometric_realization_of_finite K hK)
  have hS : IsCompact {x : K.space | x.val ∈ D.space} :=
    ((isCompact_geometric_realization_of_finite D (hK.subset hDK)).isClosed.preimage
      continuous_subtype_val).isCompact
  obtain ⟨G, hfactor, hemb⟩ := exists_descended_map_of_subspace_fibers q hq
    {x | x.val ∈ D.space} hS (fun x => f x.val) hrel F₀
    (fun x hx y hy => hF x y hx hy)
  exact ⟨n, Q, q, G, hQ, hdim, hq, hrel, hfactor, hemb⟩

omit [DecidableEq E] [DecidableEq F] in
theorem exists_geometric_polyhedral_quotient_full_with_descent
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (F₀ : C(K.space, M))
    (hF : ∀ x y : K.space, x.val ∈ D.space → y.val ∈ D.space →
      (F₀ x = F₀ y ↔ f x.val = f y.val)) :
    ∃ n : ℕ, ∃ Q : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      ∃ q : C(K.space, Q.space), ∃ G : C(Q.space, M),
      Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧ IsQuotientMap q ∧
      (∀ x y : K.space, q x = q y ↔
        x = y ∨ (x.val ∈ D.space ∧ y.val ∈ D.space ∧ f x.val = f y.val)) ∧
      (∀ x, G (q x) = F₀ x) ∧
      IsClosedEmbedding (fun z : q '' {x | x.val ∈ D.space} => G z.val) ∧
      (∀ J : SimplicialComplex ℝ E, J.faces ⊆ K.faces →
        ∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
          R.faces ⊆ Q.faces ∧ R.space = (fun x : K.space => (q x).val) '' {x | x.val ∈ J.space} ∧
          (∀ r : ℕ, (∀ s ∈ J.faces, s.card ≤ r) → ∀ s ∈ R.faces, s.card ≤ r) ∧
          hasFacewiseAffineSections K J Q R q) ∧
      hasNondegeneratePLSubdivision K (fun x => (q x).val) := by
  classical
  obtain ⟨n, Q, q, hQ, hdim, hq, hrel, himages, hPL⟩ :=
    exists_geometric_polyhedral_quotient_full K D hK hDK f hf hinj hd
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_geometric_realization_of_finite K hK)
  have hS : IsCompact {x : K.space | x.val ∈ D.space} :=
    ((isCompact_geometric_realization_of_finite D (hK.subset hDK)).isClosed.preimage
      continuous_subtype_val).isCompact
  obtain ⟨G, hfactor, hemb⟩ := exists_descended_map_of_subspace_fibers q hq
    {x | x.val ∈ D.space} hS (fun x => f x.val) hrel F₀
    (fun x hx y hy => hF x y hx hy)
  exact ⟨n, Q, q, G, hQ, hdim, hq, hrel, hfactor, hemb, himages, hPL⟩

end

end DifferentialGeometry.Topology.Engulfing
