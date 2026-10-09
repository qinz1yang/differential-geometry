import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanExpansion
import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanAssignedCharts
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementSupport

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]

omit [DecidableEq E] in
theorem simplicialRefines.old_face_subset_skeleton {P K : SimplicialComplex ℝ E}
    (href : simplicialRefines P K) (hspace : P.space = K.space)
    {t : Finset E} (ht : t ∈ K.faces) {q : ℕ} (htcard : t.card ≤ q + 1) :
    convexHull ℝ (t : Set E) ⊆ (skeleton P q).space := by
  classical
  intro x hx
  have hxP : x ∈ P.space := hspace.symm ▸ K.convexHull_subset_space ht hx
  have hxR : x ∈ (vertexRestriction P (convexHull ℝ (t : Set E))).space := by
    rw [href.vertexRestriction_space ht]
    exact ⟨hxP, hx⟩
  obtain ⟨u, hu, hxu⟩ := SimplicialComplex.mem_space_iff.mp hxR
  have hcard := (P.indep hu.1).card_le_card_of_subset_affineSpan
    (fun y hy => convexHull_subset_affineSpan _ (hu.2 hy))
  exact (skeleton P q).convexHull_subset_space ⟨hu.1, hcard.trans htcard⟩ hxu

omit [DecidableEq E] in
theorem simplicialRefines.old_skeleton_subset {P K : SimplicialComplex ℝ E}
    (href : simplicialRefines P K) (hspace : P.space = K.space) (q : ℕ) :
    (skeleton K q).space ⊆ (skeleton P q).space := by
  classical
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact href.old_face_subset_skeleton hspace ht.1 ht.2 hxt

namespace NewmanPreparedMembrane

variable [DecidableEq (ConeSpace E)] {n p q : ℕ}
  {P : NewmanProblem E M n p (q + 1)} {s : Finset E}

theorem index_le (D : NewmanPreparedMembrane P s) : q ≤ p := by
  have hc : s.card = q + 1 := by
    rw [← D.vertices_eq, Finset.card_image_of_injective _ D.independent.injective]
    simp
  have hd := P.target_dimension s D.principal.1
  omega

theorem remaining_lift_subcomplex (D : NewmanPreparedMembrane P s) :
    (coneBaseComplex D.remaining).faces ⊆ D.source.faces := by
  rintro _ ⟨t, ht, rfl⟩
  exact coneAttachmentComplex_old_faces P.source D.vertices D.independent D.source_face
    ⟨t, D.remaining_subcomplex ht, rfl⟩

theorem covered_subset_skeleton (D : NewmanPreparedMembrane P s) :
    D.covered ⊆ (skeleton D.source p).space := by
  rintro x (hx | hx)
  · have hxR : x ∈ (coneBaseComplex D.remaining).space := by
      simpa only [coneBaseComplex_space] using hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxR
    have hdim : ∀ t ∈ (coneBaseComplex D.remaining).faces, t.card ≤ p + 1 :=
      coneBaseComplex_face_card_le D.remaining (fun t ht => P.target_dimension t ht.1)
    exact (skeleton D.source p).convexHull_subset_space
      ⟨D.remaining_lift_subcomplex ht, hdim t ht⟩ hxt
  · have hroof : D.roof = simplexRoof (coneVertexSet D.vertices)
        ((coneSplit (Fin.last (q + 1))).right.image (coneVertices D.vertices)) := by
      rw [coneVertexSet, simplexRoof_image_vertices _
        (coneVertices_independent D.vertices D.independent)]
      rfl
    rw [hroof] at hx
    apply simplexRoof_subset_skeleton D.source
      (coneAttachmentComplex_cone_face P.source D.vertices D.independent D.source_face)
      (Finset.image_subset_image (Finset.subset_univ _)) ?_ hx
    have hc : (coneVertexSet D.vertices).card ≤ q + 2 :=
      Finset.card_image_le.trans (by simp)
    exact hc.trans (Nat.add_le_add_right D.index_le 2)

theorem covered_subcomplex (D : NewmanPreparedMembrane P s) :
    isSubcomplexSpace D.source D.covered := by
  have hR : isSubcomplexSpace D.source (coneInclusion '' D.remaining.space) := by
    simpa only [coneBaseComplex_space] using
      isSubcomplexSpace.of_faces_subset D.remaining_lift_subcomplex
  apply hR.union
  have hroof : D.roof = simplexRoof (coneVertexSet D.vertices)
      ((coneSplit (Fin.last (q + 1))).right.image (coneVertices D.vertices)) := by
    rw [coneVertexSet, simplexRoof_image_vertices _
      (coneVertices_independent D.vertices D.independent)]
    rfl
  rw [hroof]
  apply isSubcomplexSpace.iUnion
  intro i
  by_cases hi : i ∈ (coneSplit (Fin.last (q + 1))).right.image (coneVertices D.vertices)
  · simpa only [hi, iUnion_true] using isSubcomplexSpace.subface
      (coneAttachmentComplex_cone_face P.source D.vertices D.independent D.source_face)
      (Finset.erase_subset i _)
  · simpa only [hi, iUnion_false] using isSubcomplexSpace.empty D.source

theorem membrane_subcomplex (D : NewmanPreparedMembrane P s) :
    isSubcomplexSpace D.source D.membrane := by
  have hR : isSubcomplexSpace D.source (coneInclusion '' D.remaining.space) := by
    simpa only [coneBaseComplex_space] using
      isSubcomplexSpace.of_faces_subset D.remaining_lift_subcomplex
  apply hR.union
  simpa only [convexHull_coneVertexSet] using isSubcomplexSpace.face
    (coneAttachmentComplex_cone_face P.source D.vertices D.independent D.source_face)

theorem refined_face_support (D : NewmanPreparedMembrane P s)
    {K : SimplicialComplex ℝ (ConeSpace E)} (href : simplicialRefines K D.source)
    {V : Finset (ConeSpace E)} (hV : V ∈ K.faces)
    (hmem : convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.membrane) :
    convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.covered ∨
      (convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.simplex ∧ V.card ≤ q + 2) := by
  have hmem' : convexHull ℝ (V : Set (ConeSpace E)) ⊆
      (coneBaseComplex D.remaining).space ∪ convexHull ℝ (coneVertexSet D.vertices : Set (ConeSpace E)) := by
    simpa only [membrane, coneBaseComplex_space, convexHull_coneVertexSet] using hmem
  rcases href.convexHull_subset_or_old_face D.remaining_lift_subcomplex hV
    (coneAttachmentComplex_cone_face P.source D.vertices D.independent D.source_face) hmem' with h | h
  · exact Or.inl (h.trans (by rw [coneBaseComplex_space]; exact subset_union_left))
  · refine Or.inr ⟨by simpa only [convexHull_coneVertexSet] using h, ?_⟩
    have hc := (K.indep hV).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan _ (h (subset_convexHull ℝ _ hx)))
    exact hc.trans (Finset.card_image_le.trans (by simp))

theorem original_target_subset_skeletalCovered (D : NewmanPreparedMembrane P s)
    {K : SimplicialComplex ℝ (ConeSpace E)} (href : simplicialRefines K D.source)
    (hspace : K.space = D.source.space) :
    coneInclusion '' P.target.space ⊆ skeletalCovered K D.covered D.membrane q := by
  rintro _ ⟨x, hx, rfl⟩
  have htarget := D.original_target_subset (mem_image_of_mem coneInclusion hx)
  rw [← erasePrincipalSimplex_space_union P.target s D.principal] at hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl (mem_image_of_mem _ hx))
  · refine Or.inr ⟨htarget, ?_⟩
    have hface : coneBaseVertexSet D.vertices ∈ D.source.faces :=
      coneAttachmentComplex_old_faces P.source D.vertices D.independent D.source_face
        (coneBaseVertexSet_mem P.source D.vertices D.source_face)
    apply href.old_face_subset_skeleton hspace hface ?_ ?_
    · calc
        (coneBaseVertexSet D.vertices).card ≤ (Finset.univ.image D.vertices).card :=
          Finset.card_image_le
        _ ≤ q + 1 := Finset.card_image_le.trans (by simp)
    · rw [convexHull_coneBaseVertexSet]
      refine mem_image_of_mem _ ?_
      have heq : range D.vertices = (s : Set E) := by
        simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
          congrArg (fun t : Finset E => (t : Set E)) D.vertices_eq
      rwa [heq]

theorem conclusion_of_skeletal_expansion (D : NewmanPreparedMembrane P s)
    (K J : SimplicialComplex ℝ (ConeSpace E)) (hK : K.faces.Finite)
    (href : simplicialRefines K D.source) (hspace : K.space = D.source.space)
    (hJspace : J.space = (coneBaseComplex P.fixed).space)
    (F : C(K.space, M)) (hF : ∀ x, F x = D.map ⟨x.1, hspace ▸ x.2⟩)
    (Good : C(K.space, M) → Prop) (hGood : Good F)
    (hexp : FiniteSimplexExpansionIn K D.covered D.membrane)
    (hstep : mapSkeletalSimplexStep K J P.obstacle P.openSet Good D.covered D.membrane p q)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε := by
  have hmemK : D.membrane ⊆ K.space := fun x hx => hspace.symm ▸ D.membrane_subset_source hx
  have hAdim : D.covered ⊆ (skeleton K p).space :=
    D.covered_subset_skeleton.trans (href.old_skeleton_subset hspace p)
  have hbound : ∀ V ∈ K.faces, convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.membrane →
      convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.covered ∨ V.card ≤ q + 2 := by
    intro V hV hmem
    exact (D.refined_face_support href hV hmem).imp_right And.right
  have hstart : P.obstacle ∪ F '' (Subtype.val ⁻¹' D.covered) ⊆ P.openSet := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact P.obstacle_subset hy
    · rw [hF]
      exact D.map_covered ⟨x.1, hspace ▸ x.2⟩ hx
  obtain ⟨g, H, hgGood, hgfix, hgnear, hgcover, hcompact⟩ :=
    exists_map_engulfing_of_skeletal_expansion K J hK F P.obstacle P.openSet Good hGood
      D.index_le hstep hexp D.covered_compact (D.covered_subcomplex.refine href hspace)
      hmemK subset_rfl hAdim hbound hstart hε
  let i : C(P.source.space, K.space) :=
    ⟨fun x => ⟨coneInclusion x.1, hspace.symm ▸ (D.oldSourceMap x).2⟩,
      (coneInclusion.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _⟩
  have hFi : ∀ x, F (i x) = P.map x := by
    intro x
    rw [hF]
    exact D.old_exact x
  refine ⟨g.comp i, H, ?_, ?_, ?_, hcompact⟩
  · intro x hx
    change g (i x) = P.map x
    rw [hgfix _ (by rw [hJspace, coneBaseComplex_space]; exact mem_image_of_mem _ hx), hFi]
  · intro x
    simpa only [ContinuousMap.comp_apply, hFi] using hgnear (i x)
  · rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hgcover (Or.inl hy)
    · exact hgcover (Or.inr ⟨i x,
        D.original_target_subset_skeletalCovered href hspace (mem_image_of_mem _ hx), rfl⟩)

structure AssignedRefinement (D : NewmanPreparedMembrane P s) where
  source : SimplicialComplex ℝ (ConeSpace E)
  fixed : SimplicialComplex ℝ (ConeSpace E)
  finite : source.faces.Finite
  refines : simplicialRefines source D.source
  dimension : ∀ t ∈ source.faces, t.card ≤ p + 2
  fixed_faces : fixed.faces ⊆ source.faces
  fixed_space : fixed.space = (coneBaseComplex P.fixed).space
  fixed_refines : simplicialRefines fixed (coneBaseComplex P.fixed)
  space : source.space = D.source.space
  map : C(source.space, M)
  map_eq : ∀ x, map x = D.map ⟨x.1, space ▸ x.2⟩
  charts : source.faces → AdaptedPiecewiseLinearChart source fixed map P.obstacle n p
  assigned : facesInAssignedCharts source (fun t => (charts t).toBufferedChart) map
  expansion : FiniteSimplexExpansionIn source D.covered D.membrane

theorem exists_assignedRefinement (D : NewmanPreparedMembrane P s) :
    Nonempty D.AssignedRefinement := by
  obtain ⟨K, J, hK, href, hdim, hJK, hJspace, hJL, hexp, hspace, F, hF, b, hb⟩ :=
    exists_refinement_with_assigned_local_charts D.source (coneBaseComplex P.fixed)
      D.source_finite D.fixed_subcomplex D.source_dimension D.map
      P.obstacle_closed D.hasAdaptedPiecewiseLinearCharts_map
  exact ⟨⟨K, J, hK, href, hdim, hJK, hJspace, hJL, hspace, F, hF, b, hb,
    hexp D.covered D.membrane D.expansion⟩⟩

namespace AssignedRefinement

variable {D : NewmanPreparedMembrane P s}

theorem hasAdaptedPiecewiseLinearCharts_map (R : D.AssignedRefinement) :
    hasAdaptedPiecewiseLinearCharts R.source R.fixed R.map P.obstacle n p :=
  D.hasAdaptedPiecewiseLinearCharts_map.refine R.source R.fixed R.space R.fixed_refines
    R.fixed_space.subset R.map R.map_eq

theorem fixed_injective (R : D.AssignedRefinement) :
    Set.InjOn R.map (Subtype.val ⁻¹' R.fixed.space) := by
  intro x hx y hy hxy
  have hx' : (⟨x.1, R.space ▸ x.2⟩ : D.source.space) ∈
      Subtype.val ⁻¹' (coneBaseComplex P.fixed).space := by
    change x.1 ∈ (coneBaseComplex P.fixed).space
    rw [← R.fixed_space]
    exact hx
  have hy' : (⟨y.1, R.space ▸ y.2⟩ : D.source.space) ∈
      Subtype.val ⁻¹' (coneBaseComplex P.fixed).space := by
    change y.1 ∈ (coneBaseComplex P.fixed).space
    rw [← R.fixed_space]
    exact hy
  have heq := D.fixed_injective hx' hy' (by simpa only [← R.map_eq] using hxy)
  exact Subtype.ext (congrArg (fun z : D.source.space => z.1) heq)

def localStep (R : D.AssignedRefinement) : Prop :=
  assignedChartSimplexStep R.source R.fixed R.map
    (fun t => (R.charts t).toBufferedChart) P.obstacle P.openSet
    D.covered D.membrane p q

theorem conclusion (R : D.AssignedRefinement) (hstep : R.localStep)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε := by
  let Good := assignedMapCondition R.source R.fixed R.map
    (fun t => (R.charts t).toBufferedChart)
  have hGood : Good R.map := ⟨fun _ _ => rfl, R.assigned⟩
  exact D.conclusion_of_skeletal_expansion R.source R.fixed R.finite R.refines R.space
    R.fixed_space R.map R.map_eq Good hGood R.expansion
    (hstep.preserves_assigned_charts R.source R.fixed R.finite R.map
      (fun t => (R.charts t).toBufferedChart) P.obstacle P.openSet
      D.covered D.membrane p q) hε

end AssignedRefinement

theorem conclusion_of_assigned_chart_steps (D : NewmanPreparedMembrane P s)
    (hstep : ∀ R : D.AssignedRefinement, R.localStep)
    {ε : ℝ} (hε : 0 < ε) : P.conclusion ε := by
  let R := Classical.choice D.exists_assignedRefinement
  exact R.conclusion (hstep R) hε

end NewmanPreparedMembrane

theorem singleSimplexNewmanAt_of_assigned_chart_steps {n p q : ℕ}
    (hstep : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq (ConeSpace E)],
      ∀ (P : NewmanProblem E M n p (q + 1)) (s : Finset E)
        (D : NewmanPreparedMembrane P s),
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle →
      ∀ R : D.AssignedRefinement, R.localStep) : singleSimplexNewmanAt M n p q := by
  intro E _ _ _ P s hs hcard hother havoid ε hε
  classical
  have halt : P.conclusion ε ∨ Nonempty (NewmanPreparedMembrane P s) :=
    newmanConclusion_or_preparedMembrane P s hs hcard hother hε
  rcases halt with h | h
  · exact h
  · let D := Classical.choice h
    exact D.conclusion_of_assigned_chart_steps (hstep E P s D havoid) hε

end

end DifferentialGeometry.Topology.Engulfing
