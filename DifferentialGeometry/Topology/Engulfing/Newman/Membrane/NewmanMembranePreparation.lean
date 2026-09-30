import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanProblem
import DifferentialGeometry.Topology.Engulfing.Simplex.ConeAttachment
import DifferentialGeometry.Topology.SimplicialComplex.Expansion.PrincipalFaces

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [DecidableEq E] [DecidableEq (ConeSpace E)]

theorem exists_old_point_of_cone_subcomplex {m : ℕ} (K L : SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) (v : Fin m → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces)
    (x : (coneAttachmentComplex K v hv hf).space)
    (hx : x.1 ∈ (coneBaseComplex L).space) :
    ∃ y : K.space, y.1 ∈ L.space ∧ coneAttachmentSourceMap K v hv hf y = x := by
  rw [coneBaseComplex_space] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hyK : y ∈ K.space := by
    obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
    exact K.convexHull_subset_space (hLK hs) hys
  exact ⟨⟨y, hyK⟩, hy, Subtype.ext hxy⟩

theorem cone_membrane_fixed_injective {m : ℕ} (K L : SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) (v : Fin m → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces) (f : C(K.space, M))
    (hinj : InjOn f (Subtype.val ⁻¹' L.space))
    (F : C((coneAttachmentComplex K v hv hf).space, M))
    (hF : ∀ y, F (coneAttachmentSourceMap K v hv hf y) = f y) :
    InjOn F (Subtype.val ⁻¹' (coneBaseComplex L).space) := by
  intro x hx z hz hxz
  obtain ⟨y, hy, rfl⟩ := exists_old_point_of_cone_subcomplex K L hLK v hv hf x hx
  obtain ⟨w, hw, rfl⟩ := exists_old_point_of_cone_subcomplex K L hLK v hv hf z hz
  rw [hF, hF] at hxz
  exact congrArg (coneAttachmentSourceMap K v hv hf) (hinj hy hw hxz)

theorem hasAdaptedPiecewiseLinearCharts.cone_membrane {m n p : ℕ} (K L : SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) (v : Fin m → E) (hv : AffineIndependent ℝ v)
    (hf : Finset.univ.image v ∈ K.faces) (f : C(K.space, M)) {X : Set M}
    (hlocal : hasAdaptedPiecewiseLinearCharts K L f X n p)
    (F : C((coneAttachmentComplex K v hv hf).space, M))
    (hF : ∀ y, F (coneAttachmentSourceMap K v hv hf y) = f y) :
    hasAdaptedPiecewiseLinearCharts (coneAttachmentComplex K v hv hf) (coneBaseComplex L) F X n p := by
  intro y
  obtain ⟨b, hyb⟩ := hlocal y
  refine ⟨{
    toBufferedChart := b.toBufferedChart
    fixed_affine := ?_
    fixed_injective := ?_
    obstacle := b.obstacle
    obstacle_finite := b.obstacle_finite
    obstacle_dimension := b.obstacle_dimension
    obstacle_contains := b.obstacle_contains }, hyb⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨A, hA⟩ := b.fixed_affine s hs
    refine ⟨A.comp coneProjection.toAffineMap, ?_⟩
    intro x hx hxcore
    rw [Finset.coe_image, ← coneInclusion.image_convexHull] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    let z₀ : K.space := ⟨z, K.convexHull_subset_space (hLK hs) hz⟩
    have hxeq : coneAttachmentSourceMap K v hv hf z₀ = x := Subtype.ext hzx
    have hvalue : F x = f z₀ := hxeq ▸ hF z₀
    rw [hvalue]
    change b.chart (f z₀) = A (coneProjection x.1)
    rw [← hzx, coneProjection_inclusion]
    exact hA z₀ hz (hvalue ▸ hxcore)
  · intro x hx z hz hxz
    obtain ⟨y, hy, rfl⟩ := exists_old_point_of_cone_subcomplex K L hLK v hv hf x hx.1
    obtain ⟨w, hw, rfl⟩ := exists_old_point_of_cone_subcomplex K L hLK v hv hf z hz.1
    simp only [hF] at hxz
    have hycore : f y ∈ b.core := by rw [← hF]; exact hx.2
    have hwcore : f w ∈ b.core := by rw [← hF]; exact hz.2
    exact congrArg (coneAttachmentSourceMap K v hv hf)
      (b.fixed_injective ⟨hy, hycore⟩ ⟨hw, hwcore⟩ hxz)

omit [DecidableEq (ConeSpace E)] in
theorem exists_face_vertices {n p q : ℕ} (P : NewmanProblem E M n p (q + 1))
    (s : Finset E) (hs : s ∈ P.target.faces) (hcard : s.card = q + 1) :
    ∃ v : Fin (q + 1) → E, AffineIndependent ℝ v ∧ Finset.univ.image v = s := by
  classical
  let e : Fin (q + 1) ≃ s := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let v : Fin (q + 1) → E := fun i => e i
  have hv : AffineIndependent ℝ v := (P.target.indep hs).comp_embedding e.toEmbedding
  refine ⟨v, hv, ?_⟩
  ext x
  constructor
  · rintro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (e i).2
  · intro hx
    exact Finset.mem_image.mpr ⟨e.symm ⟨x, hx⟩, Finset.mem_univ _,
      congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩

omit [DecidableEq (ConeSpace E)] in
theorem single_face_boundary_covered {n p q : ℕ} (P : NewmanProblem E M n p (q + 1))
    (s : Finset E) (hs : s ∈ P.target.faces)
    (hother : ∀ t ∈ P.target.faces, t ≠ s →
      ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet)
    (v : Fin (q + 1) → E) (hv : AffineIndependent ℝ v) (hvs : Finset.univ.image v = s) :
    ∀ x : P.source.space, x.1 ∈ simplexBoundary v → P.map x ∈ P.openSet := by
  classical
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [← convexHull_erase_vertex_image v hv i, hvs] at hi
  have hne : (s.erase (v i)).Nonempty := by
    apply Finset.coe_nonempty.mp
    exact convexHull_nonempty_iff.mp ⟨x.1, hi⟩
  apply hother (s.erase (v i)) (P.target.down_closed hs (Finset.erase_subset _ _) hne) ?_ x hi
  intro heq
  have hvi : v i ∈ s := hvs ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact Finset.notMem_erase (v i) s (heq.symm ▸ hvi)

omit [DecidableEq (ConeSpace E)] in
theorem FiniteSimplexExpansionIn.union_fixed
    {K : SimplicialComplex ℝ E} {A C : Set E} (h : FiniteSimplexExpansionIn K A C)
    (W : Set E) (hWC : W ∩ C ⊆ A) : FiniteSimplexExpansionIn K (W ∪ A) (W ∪ C) := by
  classical
  induction h generalizing W with
  | refl => exact .refl _
  | @snoc C V B h hV ha ih =>
    have hWC₀ : W ∩ C ⊆ A := fun x hx => hWC ⟨hx.1, Or.inl hx.2⟩
    have hattach : SimplexAttachment (W ∪ C) V B := by
      refine ⟨ha.independent, ha.properRoof, ?_⟩
      apply Subset.antisymm
      · rintro x ⟨hxW | hxC, hxV⟩
        · exact ha.intersection ▸ ⟨h.subset (hWC ⟨hxW, Or.inr hxV⟩), hxV⟩
        · exact ha.intersection ▸ ⟨hxC, hxV⟩
      · intro x hx
        have hi := ha.intersection.symm ▸ hx
        exact ⟨Or.inr hi.1, hi.2⟩
    simpa only [union_assoc] using (ih W hWC₀).snoc hV hattach

structure NewmanPreparedMembrane {n p q : ℕ} (P : NewmanProblem E M n p (q + 1))
    (s : Finset E) where
  vertices : Fin (q + 1) → E
  independent : AffineIndependent ℝ vertices
  vertices_eq : Finset.univ.image vertices = s
  source_face : Finset.univ.image vertices ∈ P.source.faces
  principal : isPrincipalSimplex P.target s
  map : C((coneAttachmentComplex P.source vertices independent source_face).space, M)
  old_exact : ∀ x : P.source.space,
    map (coneAttachmentSourceMap P.source vertices independent source_face x) = P.map x
  roof_mem : ∀ x : (coneAttachmentComplex P.source vertices independent source_face).space,
    x.1 ∈ (coneSplit (Fin.last (q + 1))).lowerRoof (coneVertices vertices) → map x ∈ P.openSet
  old_covered : ∀ x : P.source.space,
    x.1 ∈ (erasePrincipalSimplex P.target s principal).space → P.map x ∈ P.openSet

namespace NewmanPreparedMembrane

variable {n p q : ℕ} {P : NewmanProblem E M n p (q + 1)} {s : Finset E}

abbrev source (D : NewmanPreparedMembrane P s) : SimplicialComplex ℝ (ConeSpace E) :=
  coneAttachmentComplex P.source D.vertices D.independent D.source_face

abbrev oldSourceMap (D : NewmanPreparedMembrane P s) : C(P.source.space, D.source.space) :=
  coneAttachmentSourceMap P.source D.vertices D.independent D.source_face

abbrev remaining (D : NewmanPreparedMembrane P s) : SimplicialComplex ℝ E :=
  erasePrincipalSimplex P.target s D.principal

abbrev roof (D : NewmanPreparedMembrane P s) : Set (ConeSpace E) :=
  (coneSplit (Fin.last (q + 1))).lowerRoof (coneVertices D.vertices)

abbrev simplex (D : NewmanPreparedMembrane P s) : Set (ConeSpace E) :=
  convexHull ℝ (range (coneVertices D.vertices))

def covered (D : NewmanPreparedMembrane P s) : Set (ConeSpace E) :=
  coneInclusion '' D.remaining.space ∪ D.roof

def membrane (D : NewmanPreparedMembrane P s) : Set (ConeSpace E) :=
  coneInclusion '' D.remaining.space ∪ D.simplex

theorem source_finite (D : NewmanPreparedMembrane P s) : D.source.faces.Finite :=
  coneAttachmentComplex_finite_faces P.source P.source_finite D.vertices D.independent D.source_face

theorem source_dimension (D : NewmanPreparedMembrane P s) :
    ∀ t ∈ D.source.faces, t.card ≤ p + 2 := by
  have hvcard : s.card = q + 1 := by
    rw [← D.vertices_eq, Finset.card_image_of_injective _ D.independent.injective]
    simp
  have hqp : q + 1 ≤ p + 1 := hvcard ▸ P.target_dimension s D.principal.1
  have h := coneAttachmentComplex_face_card_le P.source (d := p + 1)
    P.source_dimension D.vertices D.independent D.source_face
  simpa only [max_eq_left hqp] using h

theorem fixed_subcomplex (D : NewmanPreparedMembrane P s) :
    (coneBaseComplex P.fixed).faces ⊆ D.source.faces := by
  rintro _ ⟨t, ht, rfl⟩
  exact coneAttachmentComplex_old_faces P.source D.vertices D.independent D.source_face
    ⟨t, P.fixed_subcomplex ht, rfl⟩

theorem fixed_injective (D : NewmanPreparedMembrane P s) :
    InjOn D.map (Subtype.val ⁻¹' (coneBaseComplex P.fixed).space) :=
  cone_membrane_fixed_injective P.source P.fixed P.fixed_subcomplex D.vertices D.independent
    D.source_face P.map P.fixed_injective D.map D.old_exact

theorem hasAdaptedPiecewiseLinearCharts_map (D : NewmanPreparedMembrane P s) :
    hasAdaptedPiecewiseLinearCharts D.source (coneBaseComplex P.fixed) D.map P.obstacle n p :=
  P.localData.cone_membrane P.source P.fixed P.fixed_subcomplex D.vertices D.independent
    D.source_face P.map D.map D.old_exact

theorem remaining_subcomplex (D : NewmanPreparedMembrane P s) : D.remaining.faces ⊆ P.source.faces :=
  fun _ ht => P.target_subcomplex ht.1

theorem remaining_space_subset (D : NewmanPreparedMembrane P s) : D.remaining.space ⊆ P.source.space := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact P.source.convexHull_subset_space (D.remaining_subcomplex ht) hxt

theorem simplex_subset_source (D : NewmanPreparedMembrane P s) : D.simplex ⊆ D.source.space := by
  rw [coneAttachmentComplex_space]
  exact subset_union_right

theorem membrane_subset_source (D : NewmanPreparedMembrane P s) : D.membrane ⊆ D.source.space := by
  rw [coneAttachmentComplex_space]
  exact union_subset_union (image_mono D.remaining_space_subset) subset_rfl

theorem covered_subset_membrane (D : NewmanPreparedMembrane P s) : D.covered ⊆ D.membrane :=
  union_subset_union subset_rfl ((coneSplit _).lowerRoof_subset_simplex _)

theorem map_covered (D : NewmanPreparedMembrane P s) :
    ∀ x : D.source.space, x.1 ∈ D.covered → D.map x ∈ P.openSet := by
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩ | hx
  · let z : P.source.space := ⟨y, D.remaining_space_subset hy⟩
    have hzx : D.oldSourceMap z = x := Subtype.ext hxy
    rw [← hzx, D.old_exact]
    exact D.old_covered z hy
  · exact D.roof_mem x hx

theorem original_target_subset (D : NewmanPreparedMembrane P s) :
    coneInclusion '' P.target.space ⊆ D.membrane := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← erasePrincipalSimplex_space_union P.target s D.principal] at hx
  rcases hx with hx | hx
  · exact Or.inl (mem_image_of_mem _ hx)
  · apply Or.inr
    have hbase : coneInclusion x ∈ simplexFacet (coneVertices D.vertices) (Fin.last (q + 1)) := by
      rw [simplexFacet_coneVertices_last]
      refine mem_image_of_mem _ ?_
      have heq : (s : Set E) = range D.vertices := by
        simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
          congrArg (fun t : Finset E => (t : Set E)) D.vertices_eq.symm
      rwa [← heq]
    exact simplexFacet_subset_convexHull _ _ hbase

theorem boundary_eq (D : NewmanPreparedMembrane P s) :
    simplexBoundary D.vertices = finiteSimplexBoundary s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hvi : D.vertices i ∈ s := by
      have hmem : D.vertices i ∈ Finset.univ.image D.vertices :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simpa only [D.vertices_eq] using hmem
    refine mem_iUnion₂.mpr ⟨D.vertices i, hvi, ?_⟩
    have hh : x ∈ convexHull ℝ (((Finset.univ.image D.vertices).erase (D.vertices i) : Finset E) : Set E) :=
      (convexHull_erase_vertex_image D.vertices D.independent i).symm ▸ hi
    simpa only [D.vertices_eq] using hh
  · intro hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    have ha' : a ∈ Finset.univ.image D.vertices := D.vertices_eq.symm ▸ ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha'
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [← convexHull_erase_vertex_image D.vertices D.independent i]
    simpa only [D.vertices_eq] using hxa

theorem remaining_inter_simplex_subset_roof (D : NewmanPreparedMembrane P s) :
    (coneInclusion '' D.remaining.space) ∩ D.simplex ⊆ D.roof := by
  rintro x ⟨⟨y, hy, hxy⟩, hx⟩
  have hbase : convexHull ℝ (range D.vertices) ⊆ P.source.space := by
    simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
      P.source.convexHull_subset_space D.source_face
  have hf : x ∈ simplexFacet (coneVertices D.vertices) (Fin.last (q + 1)) :=
    (cone_inter_inclusion D.vertices D.independent P.source.space hbase) ▸
      ⟨⟨y, D.remaining_space_subset hy, hxy⟩, hx⟩
  rw [simplexFacet_coneVertices_last] at hf
  obtain ⟨z, hz, hzx⟩ := hf
  have hyz : y = z := coneInclusion_injective (hxy.trans hzx.symm)
  have hys : y ∈ convexHull ℝ (s : Set E) := by
    have hzeq : range D.vertices = (s : Set E) := by
      simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
        congrArg (fun t : Finset E => (t : Set E)) D.vertices_eq
    simpa only [hyz, ← hzeq] using hz
  have hbdy : y ∈ simplexBoundary D.vertices := by
    rw [D.boundary_eq, ← erasePrincipalSimplex_inter_simplex P.target s D.principal]
    exact ⟨hy, hys⟩
  have hxbdy : x ∈ simplexBoundary
      (facetVertices (coneVertices D.vertices) (Fin.last (q + 1))) := by
    rw [simplexBoundary_cone_base]
    exact ⟨y, hbdy, hxy⟩
  exact ((facet_boundary_eq_inter_roof (coneVertices D.vertices)
    (coneVertices_independent D.vertices D.independent) (Fin.last (q + 1))) ▸ hxbdy).2

theorem expansion (D : NewmanPreparedMembrane P s) :
    FiniteSimplexExpansionIn D.source D.covered D.membrane :=
  (coneAttachmentComplex_expansion P.source D.vertices D.independent D.source_face
    (coneSplit (Fin.last (q + 1)))).union_fixed _ D.remaining_inter_simplex_subset_roof

theorem covered_compact (D : NewmanPreparedMembrane P s) : IsCompact D.covered := by
  have hR : D.remaining.faces.Finite := P.source_finite.subset D.remaining_subcomplex
  exact ((hR.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).image
    coneInclusion.continuous_of_finiteDimensional).union ((coneSplit _).isCompact_lowerRoof _)

theorem membrane_compact (D : NewmanPreparedMembrane P s) : IsCompact D.membrane := by
  have hR : D.remaining.faces.Finite := P.source_finite.subset D.remaining_subcomplex
  exact ((hR.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).image
    coneInclusion.continuous_of_finiteDimensional).union
      ((finite_range (coneVertices D.vertices)).isCompact_convexHull ℝ)

theorem image_old (D : NewmanPreparedMembrane P s) (A : Set P.source.space) :
    D.map '' (D.oldSourceMap '' A) = P.map '' A := by
  rw [image_image]
  congr 1
  funext x
  exact D.old_exact x

theorem attaching_disjoint (D : NewmanPreparedMembrane P s)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle) :
    Disjoint (D.map '' (D.oldSourceMap '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E)))) P.obstacle := by
  rwa [D.image_old]

def conclusion (D : NewmanPreparedMembrane P s) (ε : ℝ) : Prop :=
  ∃ (g : C(D.source.space, M)) (h : M ≃ₜ M),
    (∀ x : D.source.space, x.1 ∈ (coneBaseComplex P.fixed).space → g x = D.map x) ∧
    (∀ x, dist (g x) (D.map x) < ε) ∧
    P.obstacle ∪ g '' (Subtype.val ⁻¹' D.membrane) ⊆ h '' P.openSet ∧
    IsCompact (closure {x | h x ≠ x})

theorem conclusion_of_membrane (D : NewmanPreparedMembrane P s) {ε : ℝ}
    (g : C(D.source.space, M)) (h : M ≃ₜ M)
    (hfix : ∀ x : D.source.space, x.1 ∈ (coneBaseComplex P.fixed).space → g x = D.map x)
    (hnear : ∀ x, dist (g x) (D.map x) < ε)
    (hcover : P.obstacle ∪ g '' (Subtype.val ⁻¹' D.membrane) ⊆ h '' P.openSet)
    (hcompact : IsCompact (closure {x | h x ≠ x})) : P.conclusion ε := by
  refine ⟨g.comp D.oldSourceMap, h, ?_, ?_, ?_, hcompact⟩
  · intro x hx
    change g (D.oldSourceMap x) = P.map x
    rw [hfix _ (by rw [coneBaseComplex_space]; exact mem_image_of_mem _ hx), D.old_exact]
  · intro x
    simpa only [ContinuousMap.comp_apply, D.old_exact] using hnear (D.oldSourceMap x)
  · rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hcover (Or.inl hy)
    · exact hcover (Or.inr ⟨D.oldSourceMap x,
        D.original_target_subset (mem_image_of_mem _ hx), rfl⟩)

theorem to_original_conclusion (D : NewmanPreparedMembrane P s) {ε : ℝ}
    (h : D.conclusion ε) : P.conclusion ε := by
  obtain ⟨g, h, hfix, hnear, hcover, hcompact⟩ := h
  exact D.conclusion_of_membrane g h hfix hnear hcover hcompact

end NewmanPreparedMembrane

theorem exists_newmanPreparedMembrane {n p q : ℕ}
    (P : NewmanProblem E M n p (q + 1))
    (s : Finset E) (hs : s ∈ P.target.faces) (hcard : s.card = q + 1)
    (hother : ∀ t ∈ P.target.faces, t ≠ s →
      ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet)
    (huncovered : ∃ x : P.source.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ P.map x ∉ P.openSet) :
    Nonempty (NewmanPreparedMembrane P s) := by
  have hprincipal : isPrincipalSimplex P.target s :=
    isPrincipalSimplex_of_uncovered P.decomposition hs hcard.ge huncovered
  obtain ⟨v, hv, hvs⟩ := exists_face_vertices P s hs hcard
  have hf : Finset.univ.image v ∈ P.source.faces := hvs.symm ▸ P.target_subcomplex hs
  have hboundary := single_face_boundary_covered P s hs hother v hv hvs
  have hqp : q ≤ p := by have h := P.target_dimension s hs; omega
  have hmembrane : ∃ F : C((coneAttachmentComplex P.source v hv hf).space, M),
      (∀ x : P.source.space, F (coneAttachmentSourceMap P.source v hv hf x) = P.map x) ∧
      ∀ x : (coneAttachmentComplex P.source v hv hf).space,
        x.1 ∈ (coneSplit (Fin.last (q + 1))).lowerRoof (coneVertices v) → F x ∈ P.openSet := by
    cases q with
    | zero =>
      let : PathConnectedSpace M := P.connectivity.pathConnectedSpace
      exact exists_vertex_cone_membrane P.source P.source_finite v hv hf P.openSet
        P.connectivity.nonempty P.map
    | succ r =>
      exact exists_face_cone_membrane P.source P.source_finite v hv hf P.openSet P.map hboundary
        (P.connectivity.inside r (by omega)) (P.connectivity.ambient (r + 1) (by omega))
  obtain ⟨F, hF, hroof⟩ := hmembrane
  refine ⟨⟨v, hv, hvs, hf, hprincipal, F, hF, hroof, ?_⟩⟩
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact hother t ht.1 ht.2 x hxt

omit [DecidableEq E] [DecidableEq (ConeSpace E)] in
theorem newmanConclusion_of_last_face_covered {n p q : ℕ}
    (P : NewmanProblem E M n p (q + 1))
    (s : Finset E)
    (hother : ∀ t ∈ P.target.faces, t ≠ s →
      ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet)
    (hcovered : ∀ x : P.source.space, x.1 ∈ convexHull ℝ (s : Set E) → P.map x ∈ P.openSet)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε := by
  classical
  apply newmanConclusion_of_zero_complexity P.source P.fixed P.target P.map P.obstacle_subset ?_ hε
  refine ⟨⊥, empty_subset _, fun _ ht => ht.elim, ?_⟩
  intro x hx _
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  by_cases hts : t = s
  · exact hcovered x (hts ▸ hxt)
  · exact hother t ht hts x hxt

theorem newmanConclusion_or_preparedMembrane {n p q : ℕ}
    (P : NewmanProblem E M n p (q + 1))
    (s : Finset E) (hs : s ∈ P.target.faces) (hcard : s.card = q + 1)
    (hother : ∀ t ∈ P.target.faces, t ≠ s →
      ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε ∨ Nonempty (NewmanPreparedMembrane P s) := by
  by_cases hcovered : ∀ x : P.source.space,
      x.1 ∈ convexHull ℝ (s : Set E) → P.map x ∈ P.openSet
  · exact Or.inl (newmanConclusion_of_last_face_covered P s hother hcovered hε)
  · push Not at hcovered
    exact Or.inr (exists_newmanPreparedMembrane P s hs hcard hother hcovered)

theorem singleSimplexNewmanAt_of_preparedMembranes {n p q : ℕ}
    (hmembrane : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq (ConeSpace E)],
      ∀ (P : NewmanProblem E M n p (q + 1)) (s : Finset E)
        (D : NewmanPreparedMembrane P s),
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle →
      ∀ ε : ℝ, 0 < ε → D.conclusion ε) : singleSimplexNewmanAt M n p q := by
  intro E _ _ _ P s hs hcard hother havoid ε hε
  classical
  have halt : P.conclusion ε ∨ Nonempty (NewmanPreparedMembrane P s) :=
    newmanConclusion_or_preparedMembrane P s hs hcard hother hε
  rcases halt with h | h
  · exact h
  · let D := Classical.choice h
    exact D.to_original_conclusion (hmembrane E P s D havoid ε hε)

end

end DifferentialGeometry.Topology.Engulfing
