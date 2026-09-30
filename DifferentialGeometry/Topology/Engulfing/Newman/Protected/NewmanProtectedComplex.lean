import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanInduction
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.FinitePolyhedra

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped ContinuousMap

variable {E F : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [DecidableEq E] in
theorem exists_image_complex_of_facewise_affine
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    {p : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ p) :
    ∃ T : SimplicialComplex ℝ F, T.faces.Finite ∧ T.space = f '' K.space ∧
      (∀ t ∈ T.faces, t.card ≤ p) ∧
      ∀ t ∈ T.faces, ∃ s ∈ K.faces,
        convexHull ℝ (t : Set F) ⊆ f '' convexHull ℝ (s : Set E) := by
  classical
  let := hK.fintype
  obtain ⟨T, hT, hspace, href⟩ :=
    exists_complex_finite_convexHulls (fun s : K.faces => s.1.image f)
  have himage (s : K.faces) : convexHull ℝ (s.1.image f : Set F) =
      f '' convexHull ℝ (s.1 : Set E) := by
    obtain ⟨A, hA⟩ := hf s.1 s.2
    rw [Finset.coe_image, image_convexHull_eq_of_eqOn_affineMap f A hA]
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · rw [hspace]
    ext y
    constructor
    · intro hy
      obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      rw [himage s] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact mem_image_of_mem f (K.convexHull_subset_space s.2 hx)
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      apply mem_iUnion.mpr
      refine ⟨⟨s, hs⟩, ?_⟩
      rw [himage]
      exact mem_image_of_mem f hxs
  · intro t ht
    obtain ⟨s, hts⟩ := href t ht
    exact ((T.indep ht).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan _ (hts (subset_convexHull ℝ _ hx)))).trans
      ((Finset.card_image_le).trans (hd s.1 s.2))
  · intro t ht
    obtain ⟨s, hts⟩ := href t ht
    exact ⟨s.1, s.2, himage s ▸ hts⟩

omit [DecidableEq E] in
theorem exists_subdivision_preimage_complexes {ι : Type*} [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    (T : ι → SimplicialComplex ℝ F) (hT : ∀ i, (T i).faces.Finite)
    (a : ι → ℕ) (ha : ∀ i, ∀ t ∈ (T i).faces, t.card ≤ a i)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ (G : SimplicialComplex ℝ E) (P : ι → SimplicialComplex ℝ E),
      G.faces.Finite ∧ G.space = K.space ∧ simplicialRefines G K ∧
      (∀ s ∈ G.faces, s.card ≤ d + 1) ∧
      ∀ i, (P i).faces.Finite ∧ (P i).faces ⊆ G.faces ∧
        (P i).space = K.space ∩ f ⁻¹' (T i).space ∧
        ∀ s ∈ (P i).faces, s.card ≤ a i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Fintype (T i).faces := fun i => (hT i).fintype
  obtain ⟨G, hG, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_pullback_simplices_with_card_bound K hK f hf hinj
      (fun t : Σ i, (T i).faces => t.2.1) (fun t => (T t.1).indep t.2.2) hd
  let J (i : ι) (t : (T i).faces) : SimplicialComplex ℝ E :=
    vertexRestriction G (f ⁻¹' convexHull ℝ (t.1 : Set F))
  have hJG (i : ι) (t : (T i).faces) : (J i t).faces ⊆ G.faces := fun _ hs => hs.1
  let P (i : ι) := subcomplexUnion G (J i) (hJG i)
  refine ⟨G, P, hG, hspace, href, hdim, fun i => ?_⟩
  refine ⟨hG.subset (subcomplexUnion_faces_subset G (J i) (hJG i)),
    subcomplexUnion_faces_subset G (J i) (hJG i), ?_, ?_⟩
  · change (subcomplexUnion G (J i) (hJG i)).space = _
    rw [subcomplexUnion_space]
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      change x ∈ (vertexRestriction G (f ⁻¹' convexHull ℝ (t.1 : Set F))).space at ht
      rw [(hrestr ⟨i, t⟩).1] at ht
      exact ⟨ht.1, (T i).convexHull_subset_space t.2 ht.2⟩
    · rintro ⟨hx, hfx⟩
      obtain ⟨t, ht, hft⟩ := SimplicialComplex.mem_space_iff.mp hfx
      apply mem_iUnion.mpr
      refine ⟨⟨t, ht⟩, ?_⟩
      change x ∈ (vertexRestriction G (f ⁻¹' convexHull ℝ (t : Set F))).space
      rw [(hrestr ⟨i, ⟨t, ht⟩⟩).1]
      exact ⟨hx, hft⟩
  · apply subcomplexUnion_face_card_le
    intro t s hs
    exact ((hrestr ⟨i, t⟩).2 s hs).trans (ha i t.1 t.2)

omit [DecidableEq E] in
theorem exists_saturated_protected_complex
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    (T C : SimplicialComplex ℝ F) (hT : T.faces.Finite) (hC : C.faces.Finite)
    {d p q : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hTd : ∀ t ∈ T.faces, t.card ≤ p + 1) (hCd : ∀ t ∈ C.faces, t.card ≤ q)
    (hqp : q ≤ p + 1) :
    ∃ G D R P : SimplicialComplex ℝ E,
      G.faces.Finite ∧ G.space = K.space ∧ simplicialRefines G K ∧
      (∀ s ∈ G.faces, s.card ≤ d + 1) ∧
      D.faces.Finite ∧ D.faces ⊆ G.faces ∧
      D.space = K.space ∩ f ⁻¹' (T.space ∪ C.space) ∧
      (∀ s ∈ D.faces, s.card ≤ p + 1) ∧
      R.faces ⊆ D.faces ∧ P.faces ⊆ D.faces ∧ D.faces = R.faces ∪ P.faces ∧
      R.space = K.space ∩ f ⁻¹' T.space ∧
      P.space = K.space ∩ f ⁻¹' C.space ∧ (∀ s ∈ P.faces, s.card ≤ q) ∧
      (∀ x ∈ D.space, ∀ y ∈ K.space, f y = f x → y ∈ D.space) := by
  classical
  let target : Bool → SimplicialComplex ℝ F := fun b => if b then C else T
  let a : Bool → ℕ := fun b => if b then q else p + 1
  have ht (b : Bool) : (target b).faces.Finite := by cases b <;> assumption
  have ha (b : Bool) : ∀ t ∈ (target b).faces, t.card ≤ a b := by
    cases b <;> assumption
  obtain ⟨G, J, hG, hspace, href, hdim, hJ⟩ :=
    exists_subdivision_preimage_complexes K hK f hf hinj target ht a ha hd
  let D := subcomplexUnion G J (fun b => (hJ b).2.1)
  have hDfaces : D.faces = (J false).faces ∪ (J true).faces := by
    ext s
    simp only [D, subcomplexUnion, mem_iUnion, Bool.exists_bool, mem_union]
  have hDspace : D.space = K.space ∩ f ⁻¹' (T.space ∪ C.space) := by
    rw [show D.space = ⋃ b, (J b).space from subcomplexUnion_space _ _ _]
    ext x
    simp only [mem_iUnion, Bool.exists_bool]
    rw [(hJ false).2.2.1, (hJ true).2.2.1]
    dsimp [target]
    simp only [mem_union, mem_inter_iff, mem_preimage]
    tauto
  refine ⟨G, D, J false, J true, hG, hspace, href, hdim,
    hG.subset (subcomplexUnion_faces_subset G J _),
    subcomplexUnion_faces_subset G J _, hDspace, ?_, ?_, ?_, hDfaces,
    (hJ false).2.2.1, (hJ true).2.2.1, (hJ true).2.2.2, ?_⟩
  · apply subcomplexUnion_face_card_le
    intro b s hs
    cases b
    · exact (hJ false).2.2.2 s hs
    · exact ((hJ true).2.2.2 s hs).trans hqp
  · rw [hDfaces]
    exact subset_union_left
  · rw [hDfaces]
    exact subset_union_right
  · intro x hx y hy heq
    rw [hDspace] at hx ⊢
    refine ⟨hy, ?_⟩
    change f y ∈ T.space ∪ C.space
    rw [heq]
    exact hx.2

omit [DecidableEq E] in
theorem exists_saturated_protected_complex_of_subcomplex
    (K H : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hHK : H.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    (C : SimplicialComplex ℝ F) (hC : C.faces.Finite)
    {d p q : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1) (hCd : ∀ t ∈ C.faces, t.card ≤ q)
    (hqp : q ≤ p + 1) :
    ∃ G D R P : SimplicialComplex ℝ E,
      G.faces.Finite ∧ G.space = K.space ∧ simplicialRefines G K ∧
      (∀ s ∈ G.faces, s.card ≤ d + 1) ∧ D.faces.Finite ∧ D.faces ⊆ G.faces ∧
      D.space = K.space ∩ f ⁻¹' (f '' H.space ∪ C.space) ∧
      (∀ s ∈ D.faces, s.card ≤ p + 1) ∧
      R.faces ⊆ D.faces ∧ P.faces ⊆ D.faces ∧ D.faces = R.faces ∪ P.faces ∧
      R.space = K.space ∩ f ⁻¹' (f '' H.space) ∧
      P.space = K.space ∩ f ⁻¹' C.space ∧ (∀ s ∈ P.faces, s.card ≤ q) ∧
      H.space ⊆ D.space ∧
      (∀ x ∈ D.space, ∀ y ∈ K.space, f y = f x → y ∈ D.space) := by
  classical
  obtain ⟨T, hT, hTspace, hTdim, -⟩ := exists_image_complex_of_facewise_affine H
    (hK.subset hHK) f (fun s hs => hf s (hHK hs)) hHd
  obtain ⟨G, D, R, P, hG, hspace, href, hdim, hD, hDG, hDspace, hDdim,
    hRD, hPD, hfaces, hRspace, hPspace, hPdim, hsat⟩ :=
    exists_saturated_protected_complex K hK f hf hinj T C hT hC hd hTdim hCd hqp
  rw [hTspace] at hDspace hRspace
  refine ⟨G, D, R, P, hG, hspace, href, hdim, hD, hDG, hDspace, hDdim,
    hRD, hPD, hfaces, hRspace, hPspace, hPdim, ?_, hsat⟩
  intro x hx
  rw [hDspace]
  refine ⟨?_, Or.inl (mem_image_of_mem f hx)⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact K.convexHull_subset_space (hHK hs) hxs

omit [DecidableEq E] [FiniteDimensional ℝ F] in
theorem engulfingDecomposition_of_saturated_split {M : Type*} [MetricSpace M]
    (G D R P : SimplicialComplex ℝ E) (g : C(G.space, M)) (f : E → F)
    (T : SimplicialComplex ℝ F) {V : Set M} {q : ℕ}
    (hRD : R.faces ⊆ D.faces) (hPD : P.faces ⊆ D.faces)
    (hfaces : D.faces = R.faces ∪ P.faces)
    (hRspace : R.space ⊆ f ⁻¹' T.space)
    (hPdim : ∀ s ∈ P.faces, s.card ≤ q)
    (hcovered : ∀ x : G.space, f x.1 ∈ T.space → g x ∈ V) :
    engulfingDecomposition G D g V q :=
  ⟨R, P, hRD, hPD, hfaces, hPdim, fun x hx => hcovered x (hRspace hx)⟩

theorem injOn_descended_protected_union {Z Y M : Type*}
    (q : Z → Y) (f : Z → M) (g : Y → M) (hfactor : ∀ x, g (q x) = f x)
    {L D : Set Z} (hinj : InjOn f L)
    (hsat : ∀ x ∈ D, ∀ y ∈ L, f y = f x → y ∈ D)
    (hmerge : ∀ x ∈ D, ∀ y ∈ D, f x = f y → q x = q y) :
    InjOn g (q '' (L ∪ D)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  have heq : f x = f y := (hfactor x).symm.trans (hxy.trans (hfactor y))
  rcases hx with hxL | hxD
  · rcases hy with hyL | hyD
    · exact congrArg q (hinj hxL hyL heq)
    · exact hmerge x (hsat y hyD x hxL heq) y hyD heq
  · rcases hy with hyL | hyD
    · exact hmerge x hxD y (hsat x hxD y hyL heq.symm) heq
    · exact hmerge x hxD y hyD heq

theorem isClosedEmbedding_descended_protected_union {Z Y M : Type*}
    [TopologicalSpace Z] [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (q : C(Z, Y)) (f : C(Z, M)) (g : C(Y, M)) (hfactor : ∀ x, g (q x) = f x)
    {L D : Set Z} (hL : IsCompact L) (hD : IsCompact D) (hinj : InjOn f L)
    (hsat : ∀ x ∈ D, ∀ y ∈ L, f y = f x → y ∈ D)
    (hmerge : ∀ x ∈ D, ∀ y ∈ D, f x = f y → q x = q y) :
    _root_.Topology.IsClosedEmbedding (fun z : q '' (L ∪ D) => g z.1) := by
  let : CompactSpace (q '' (L ∪ D)) :=
    isCompact_iff_compactSpace.mp ((hL.union hD).image q.continuous)
  apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
  exact (injOn_descended_protected_union q f g hfactor hinj hsat hmerge).injective

end DifferentialGeometry.Topology.Engulfing
