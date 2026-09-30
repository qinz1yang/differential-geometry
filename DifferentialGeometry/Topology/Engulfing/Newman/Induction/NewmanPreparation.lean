import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData
import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanInduction
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricSubcomplex

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M]

def coveredFaces (G H : SimplicialComplex ℝ E) (f : C(G.space, M)) (U : Set M) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ H.faces ∧ ∀ x : G.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ U}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨H.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨H.down_closed hs.1 hts ht, fun x hx => hs.2 x (convexHull_mono hts hx)⟩
  indep := fun hs => H.indep hs.1
  inter_subset_convexHull := fun hs ht => H.inter_subset_convexHull hs.1 ht.1

def uncoveredFaces (G H : SimplicialComplex ℝ E) (f : C(G.space, M)) (U : Set M) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ H.faces ∧ ∃ t ∈ H.faces,
    t ∉ (coveredFaces G H f U).faces ∧ s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨H.nonempty_of_mem_faces hs.1, ?_⟩
    intro u hus hu
    obtain ⟨t, ht, hnot, hst⟩ := hs.2
    exact ⟨H.down_closed hs.1 hus hu, t, ht, hnot, hus.trans hst⟩
  indep := fun hs => H.indep hs.1
  inter_subset_convexHull := fun hs ht => H.inter_subset_convexHull hs.1 ht.1

omit [DecidableEq E] in
theorem coveredFaces_faces_subset (G H : SimplicialComplex ℝ E)
    (f : C(G.space, M)) (U : Set M) : (coveredFaces G H f U).faces ⊆ H.faces := by
  classical
  exact fun _ hs => hs.1

omit [DecidableEq E] in
theorem uncoveredFaces_faces_subset (G H : SimplicialComplex ℝ E)
    (f : C(G.space, M)) (U : Set M) : (uncoveredFaces G H f U).faces ⊆ H.faces := by
  classical
  exact fun _ hs => hs.1

omit [DecidableEq E] in
theorem covered_uncovered_faces (G H : SimplicialComplex ℝ E)
    (f : C(G.space, M)) (U : Set M) :
    H.faces = (coveredFaces G H f U).faces ∪ (uncoveredFaces G H f U).faces := by
  classical
  ext s
  constructor
  · intro hs
    by_cases hc : s ∈ (coveredFaces G H f U).faces
    · exact Or.inl hc
    · exact Or.inr ⟨hs, s, hs, hc, subset_rfl⟩
  · exact fun hs => hs.elim (fun h => h.1) (fun h => h.1)

omit [DecidableEq E] in
theorem image_coveredFaces_subset (G H : SimplicialComplex ℝ E)
    (f : C(G.space, M)) (U : Set M) :
    f '' (Subtype.val ⁻¹' (coveredFaces G H f U).space) ⊆ U := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact hs.2 x hxs

omit [DecidableEq E] in
theorem engulfingDecomposition.uncoveredFaces_card_le {G H : SimplicialComplex ℝ E}
    {f : C(G.space, M)} {U : Set M} {q : ℕ}
    (h : engulfingDecomposition G H f U q) :
    ∀ s ∈ (uncoveredFaces G H f U).faces, s.card ≤ q := by
  classical
  obtain ⟨R, Q, _, _, hfaces, hdim, hR⟩ := h
  intro s hs
  obtain ⟨t, ht, hnot, hst⟩ := hs.2
  have htQ : t ∈ Q.faces := by
    have ht' := ht
    rw [hfaces] at ht'
    rcases ht' with htR | htQ
    · exact (hnot ⟨ht, fun x hx => hR x (R.convexHull_subset_space htR hx)⟩).elim
    · exact htQ
  exact (Finset.card_le_card hst).trans (hdim t htQ)

omit [DecidableEq E] in
theorem image_uncoveredFaces_disjoint (G H : SimplicialComplex ℝ E)
    (f : C(G.space, M)) {U X : Set M}
    (hsep : ∀ s ∈ H.faces,
      (∀ x : G.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ U) ∨
      Disjoint (f '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) X) :
    Disjoint (f '' (Subtype.val ⁻¹' (uncoveredFaces G H f U).space)) X := by
  classical
  apply disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hxX
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hnot, hst⟩ := hs.2
  rcases hsep t ht with hcovered | hdisj
  · exact hnot ⟨ht, hcovered⟩
  · exact disjoint_left.mp hdisj ⟨x, convexHull_mono hst hxs, rfl⟩ hxX

omit [DecidableEq E] in
theorem exists_uncoveredFaces_avoidance_tolerance (G H : SimplicialComplex ℝ E)
    (hG : G.faces.Finite) (hH : H.faces.Finite) (f : C(G.space, M))
    {U X : Set M} (hX : IsClosed X)
    (hdisj : Disjoint (f '' (Subtype.val ⁻¹' (uncoveredFaces G H f U).space)) X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : G.space → M,
      (∀ x, dist (g x) (f x) < δ) →
      Disjoint (g '' (Subtype.val ⁻¹' (uncoveredFaces G H f U).space)) X := by
  classical
  let : CompactSpace G.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces G hG)
  have hcompact : IsCompact (Subtype.val ⁻¹' (uncoveredFaces G H f U).space : Set G.space) :=
    ((isCompact_space_of_finite_faces _
      (hH.subset (uncoveredFaces_faces_subset G H f U))).isClosed.preimage
        continuous_subtype_val).isCompact
  obtain ⟨δ, hδ, hcontrol⟩ := exists_perturbation_control f hcompact isOpen_univ hX
    (subset_univ _) hdisj
  exact ⟨δ, hδ, fun g hg => (hcontrol g (fun x _ => hg x)).2⟩

theorem exists_barycentric_subdivision_separating [FiniteDimensional ℝ E]
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite) (f : C(G.space, M))
    {U X : Set M} (hU : IsOpen U) (hX : IsClosed X) (hXU : X ⊆ U) :
    ∃ N : ℕ, ∀ s ∈ (barycentricSubdivisionIter G N).faces,
      (∀ x : G.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ U) ∨
      Disjoint (f '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) X := by
  classical
  let : CompactSpace G.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces G hG)
  let V : Bool → Set G.space := fun b => f ⁻¹' (if b then U else Xᶜ)
  have hV : ∀ b, IsOpen (V b) := by
    intro b
    cases b
    · exact hX.isOpen_compl.preimage f.continuous
    · exact hU.preimage f.continuous
  have hcover : (univ : Set G.space) ⊆ ⋃ b, V b := by
    intro x _
    by_cases hx : f x ∈ U
    · exact mem_iUnion.mpr ⟨true, hx⟩
    · exact mem_iUnion.mpr ⟨false, fun hxX => hx (hXU hxX)⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound G hG
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt (Module.finrank ℝ E) D hδ
  have hsmall : ∀ s ∈ (barycentricSubdivisionIter G N).faces,
      diam (convexHull ℝ (s : Set E)) < δ :=
    fun s hs => (hmesh.barycentricSubdivisionIter hD N s hs).trans_lt (hN N le_rfl)
  refine ⟨N, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := (barycentricSubdivisionIter G N).nonempty_of_mem_faces hs
  have haG : a ∈ G.space := by
    rw [← barycentricSubdivisionIter_space G N]
    exact (barycentricSubdivisionIter G N).subset_space hs ha
  obtain ⟨b, hb⟩ := hδcover ⟨a, haG⟩ (mem_univ _)
  have hface : ∀ x : G.space, x.1 ∈ convexHull ℝ (s : Set E) → x ∈ V b := by
    intro x hx
    apply hb
    apply mem_ball.mpr
    change dist x.1 a < δ
    exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
      hx (subset_convexHull ℝ _ ha)).trans_lt (hsmall s hs)
  cases b with
  | false =>
      refine Or.inr (disjoint_left.mpr ?_)
      rintro y ⟨x, hx, rfl⟩ hxX
      exact hface x hx hxX
  | true => exact Or.inl hface

theorem engulfingDecomposition.subdivide
    {G H : SimplicialComplex ℝ E} {f : C(G.space, M)} {U : Set M} {q : ℕ}
    (h : engulfingDecomposition G H f U q) (N : ℕ)
    (g : C((barycentricSubdivisionIter G N).space, M))
    (hg : ∀ x, g x = f ⟨x.1, (barycentricSubdivisionIter_space G N) ▸ x.2⟩) :
    engulfingDecomposition (barycentricSubdivisionIter G N)
      (barycentricSubdivisionIter H N) g U q := by
  obtain ⟨R, Q, hRH, hQH, hfaces, hdim, hR⟩ := h
  refine ⟨barycentricSubdivisionIter R N, barycentricSubdivisionIter Q N,
    barycentricSubdivisionIter_faces_subset hRH N,
    barycentricSubdivisionIter_faces_subset hQH N,
    barycentricSubdivisionIter_faces_union H R Q hfaces N,
    barycentricSubdivisionIter_face_card_le_nat Q hdim N, ?_⟩
  intro x hx
  rw [hg]
  apply hR
  simpa only [barycentricSubdivisionIter_space] using hx

end DifferentialGeometry.Topology.Engulfing
