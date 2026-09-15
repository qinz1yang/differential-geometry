import External.ClassificationOfSurfaces.Moise.PolygonalSchoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_pos_uniform_fintype {ι : Type*} [Finite ι]
    (P : ι → ℝ → Prop)
    (hP : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P i δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
  classical
  let _ := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      exact ⟨1, by norm_num, fun i => isEmptyElim i⟩
  | inr hι =>
      let values : Finset ℝ := Finset.univ.image fun i => Classical.choose (hP i)
      have hvalues : values.Nonempty := by
        let i : ι := Classical.choice hι
        exact ⟨Classical.choose (hP i),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      let ε := values.min' hvalues
      have hε : 0 < ε := by
        have hmem : ε ∈ values := Finset.min'_mem values hvalues
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        rw [← hi]
        exact (Classical.choose_spec (hP i)).1
      refine ⟨ε, hε, ?_⟩
      intro i δ hδ hδε
      apply (Classical.choose_spec (hP i)).2 δ hδ
      exact hδε.trans_le (Finset.min'_le values
        (Classical.choose (hP i)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

private theorem exists_pos_uniform_finset {α : Type*}
    (s : Finset α) (P : α → ℝ → Prop)
    (hP : ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P x δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ∀ δ : ℝ, 0 < δ → δ < ε → P x δ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨εx, hεx, hx⟩ := hP x (Finset.mem_insert_self x s)
      obtain ⟨εs, hεs, hs⟩ := ih fun y hy => hP y (Finset.mem_insert_of_mem hy)
      refine ⟨min εx εs, lt_min hεx hεs, ?_⟩
      intro y hy δ hδ hδε
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hx δ hδ (hδε.trans_le (min_le_left _ _))
      · exact hs y hy δ hδ (hδε.trans_le (min_le_right _ _))

theorem TriangleMesh.exists_eventually_transportedThinKitePatch_inter_edge_subset_baseEndpoints
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (e : Finset M.Vertex) (he : e ∈ M.edges)
    (hcommon : e ∩ T.1 ⊆ M.freeTriangleBaseEdge T k)
    (hcard : (e ∩ T.1).card ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch (M.freeTriangleAffineEquiv T k) δ ∩
          convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  have hecard := M.card_of_mem_edges he
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  let a := E.symm (M.position v)
  let b := E.symm (M.position w)
  have hab : a ≠ b := by
    intro hab
    apply hvw
    apply M.position_injective
    simpa [a, b] using congrArg E hab
  have hcarrier :
      convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position v) (M.position w) := by
    rw [show M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hsegmentImage : E '' segment ℝ a b =
      segment ℝ (M.position v) (M.position w) := by
    calc
      E '' segment ℝ a b = segment ℝ (E a) (E b) := image_segment ℝ E.toAffineMap a b
      _ = segment ℝ (M.position v) (M.position w) := by simp [a, b]
  have heFace : ({v, w} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
    have heuData := Finset.mem_powersetCard.mp heu
    exact M.mem_faces_iff.mpr
      ⟨by simp, u, hu, by simpa using heuData.1⟩
  have hTFace : T.1 ∈ M.toPlaneComplex.simplexes :=
    M.toPlaneComplex.mem_simplexes_of_mem_cells T.2
  have hface := M.toPlaneComplex.face_inter ({v, w} : Finset M.Vertex) heFace T.1 hTFace
  change convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) ∩
      M.triangleCarrier T.1 = convexHull ℝ
        (M.position '' ((({v, w} : Finset M.Vertex) ∩ T.1 : Finset M.Vertex) :
          Set M.Vertex)) at hface
  have hEleft : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have hEright : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have hinter : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
      {planePoint (-1) 0, planePoint 1 0} := by
    intro p hp
    have hpEdge : E p ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage]
      exact ⟨p, hp.1, rfl⟩
    have hpTriangle : E p ∈ M.triangleCarrier T.1 := by
      rw [← M.freeTriangleAffineEquiv_image_triangle T k]
      exact ⟨p, hp.2, rfl⟩
    have hpCommon : E p ∈ convexHull ℝ
        (M.position '' ((({v, w} : Finset M.Vertex) ∩ T.1 : Finset M.Vertex) :
          Set M.Vertex)) := by
      rw [← hface]
      exact ⟨hpEdge, hpTriangle⟩
    obtain hempty | hnonempty :=
        (({v, w} : Finset M.Vertex) ∩ T.1).eq_empty_or_nonempty
    · rw [hempty] at hpCommon
      simp at hpCommon
    · obtain ⟨x, hx⟩ := hnonempty
      have hsingleton : ({v, w} : Finset M.Vertex) ∩ T.1 = {x} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hx, fun y hy => ?_⟩
        by_contra hyx
        have hpair : ({x, y} : Finset M.Vertex) ⊆
            ({v, w} : Finset M.Vertex) ∩ T.1 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have hpairCard := Finset.card_le_card hpair
        have hxy : x ≠ y := Ne.symm hyx
        simp [hxy] at hpairCard
        omega
      rw [hsingleton] at hpCommon
      have hpEq : E p = M.position x := by simpa using hpCommon
      have hxBase : x ∈ M.freeTriangleBaseEdge T k := hcommon hx
      have hxImage : M.position x ∈
          ({M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} : Set Plane) := by
        rw [← M.image_freeTriangleBaseEdge T k]
        exact ⟨x, hxBase, rfl⟩
      rcases hxImage with hx0 | hx1
      · exact Or.inl (E.injective (hpEq.trans (hx0.trans hEleft.symm)))
      · exact Or.inr (E.injective (hpEq.trans (hx1.trans hEright.symm)))
  let v0 := M.orderedVertex T ((Equiv.swap 2 k) 0)
  let v1 := M.orderedVertex T ((Equiv.swap 2 k) 1)
  have hE0 : E (planePoint (-1) 0) = M.position v0 := by
    exact hEleft
  have hE1 : E (planePoint 1 0) = M.position v1 := by
    exact hEright
  have hleftEndpoint : planePoint (-1) 0 ∈ segment ℝ a b →
      a = planePoint (-1) 0 ∨ b = planePoint (-1) 0 := by
    intro hleft
    have hpEdge : M.position v0 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE0]
      exact ⟨planePoint (-1) 0, hleft, rfl⟩
    have hv0 : v0 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv0
    rcases hv0 with hv0 | hv0
    · left
      apply E.injective
      simp [a, hv0, hE0]
    · right
      apply E.injective
      simp [b, hv0, hE0]
  have hrightEndpoint : planePoint 1 0 ∈ segment ℝ a b →
      a = planePoint 1 0 ∨ b = planePoint 1 0 := by
    intro hright
    have hpEdge : M.position v1 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE1]
      exact ⟨planePoint 1 0, hright, rfl⟩
    have hv1 : v1 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
    rcases hv1 with hv1 | hv1
    · left
      apply E.injective
      simp [a, hv1, hE1]
    · right
      apply E.injective
      simp [b, hv1, hE1]
  have hnotBoth : ¬(planePoint (-1) 0 ∈ segment ℝ a b ∧
      planePoint 1 0 ∈ segment ℝ a b) := by
    rintro ⟨hleft, hright⟩
    have hv0 : v0 ∈ ({v, w} : Finset M.Vertex) := by
      have hpEdge : M.position v0 ∈
          convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
        rw [hcarrier, ← hsegmentImage, ← hE0]
        exact ⟨planePoint (-1) 0, hleft, rfl⟩
      exact M.vertex_mem_edge_of_position_mem_edgeCarrier T.2
        (M.orderedVertex_mem T _) he hpEdge
    have hv1 : v1 ∈ ({v, w} : Finset M.Vertex) := by
      have hpEdge : M.position v1 ∈
          convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
        rw [hcarrier, ← hsegmentImage, ← hE1]
        exact ⟨planePoint 1 0, hright, rfl⟩
      exact M.vertex_mem_edge_of_position_mem_edgeCarrier T.2
        (M.orderedVertex_mem T _) he hpEdge
    have hbaseSubset : M.freeTriangleBaseEdge T k ⊆
        ({v, w} : Finset M.Vertex) ∩ T.1 := by
      rw [M.freeTriangleBaseEdge_eq_orderedPair T k]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hv0, M.orderedVertex_mem T _⟩
      · exact Finset.mem_inter.mpr ⟨hv1, M.orderedVertex_mem T _⟩
    have hcardBase := Finset.card_le_card hbaseSubset
    rw [M.freeTriangleBaseEdge_card T k] at hcardBase
    omega
  obtain ⟨ε, hε, havoid⟩ := exists_thinKitePatch_inter_segment_subset_baseEndpoints
    hab hinter hleftEndpoint hrightEndpoint hnotBoth
  refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
  obtain ⟨q, hqPatch, rfl⟩ := hp.1
  have hqSegment : q ∈ segment ℝ a b := by
    have : E q ∈ segment ℝ (M.position v) (M.position w) := by
      rw [← hcarrier]
      exact hp.2
    rw [← hsegmentImage] at this
    obtain ⟨r, hr, hEq⟩ := this
    exact E.injective hEq ▸ hr
  rcases havoid δ hδ hδε ⟨hqPatch, hqSegment⟩ with hq | hq
  · exact Or.inl (hq ▸ hEleft)
  · exact Or.inr (hq ▸ hEright)

theorem TriangleMesh.exists_supported_triangle_push_fixing_boundaryCarrier_and_family
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (htrace : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
    {ι : Type*} [Finite ι] (A : ι → Set Plane)
    (hA : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch (M.freeTriangleAffineEquiv T k) δ ∩ A i ⊆
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1})
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id Uᶜ ∧
        EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id (M.boundaryCarrier \ M.triangleCarrier T.1) ∧
        EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id (⋃ i, A i) ∧
        transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ ''
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  obtain ⟨εU, hεU, hpatchU⟩ :=
    exists_eventually_transportedThinKitePatch_subset_open E U hU (by
      rw [M.freeTriangleAffineEquiv_image_triangle T k]
      exact hTU)
  let movingEdges := M.allBoundaryEdges.erase (M.freeTriangleBaseEdge T k)
  let P : Finset M.Vertex → ℝ → Prop := fun e δ =>
    transportedThinKitePatch E δ ∩
        convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1}
  have hlocal : ∀ e ∈ movingEdges, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P e δ := by
    intro e he
    have heData := Finset.mem_erase.mp he
    exact M.exists_transportedThinKitePatch_inter_boundaryEdge_subset_baseEndpoints
      T k htrace e (M.mem_allBoundaryEdges_iff.mp heData.2) heData.1
  obtain ⟨εB, hεB, hpatchB⟩ := exists_pos_uniform_finset movingEdges P hlocal
  obtain ⟨εA, hεA, hpatchA⟩ := exists_pos_uniform_fintype
    (fun i δ => transportedThinKitePatch E δ ∩ A i ⊆
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1}) hA
  let δ := min εU (min εB εA) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδU : δ < εU := by
    dsimp [δ]
    nlinarith [min_le_left εU (min εB εA), lt_min hεU (lt_min hεB hεA)]
  have hδB : δ < εB := by
    dsimp [δ]
    nlinarith [min_le_left εB εA, min_le_right εU (min εB εA),
      lt_min hεU (lt_min hεB hεA)]
  have hδA : δ < εA := by
    dsimp [δ]
    nlinarith [min_le_right εB εA, min_le_right εU (min εB εA),
      lt_min hεU (lt_min hεB hεA)]
  have hleft : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have hright : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have hfixEndpoint (p : Plane)
      (hp : p = M.freeTriangleOrder T k 0 ∨ p = M.freeTriangleOrder T k 1) :
      transportedThinKiteHomeomorph E δ hδ p = p := by
    rcases hp with rfl | rfl
    · rw [← hleft]
      change E (thinKiteAmbientHomeomorph δ hδ (E.symm (E (planePoint (-1) 0)))) =
        E (planePoint (-1) 0)
      rw [E.symm_apply_apply]
      have hm := thinKiteAmbientHomeomorph_leftSpoke δ hδ 0 (by simp)
      rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_zero] at hm
      rw [hm]
    · rw [← hright]
      change E (thinKiteAmbientHomeomorph δ hδ (E.symm (E (planePoint 1 0)))) =
        E (planePoint 1 0)
      rw [E.symm_apply_apply]
      have hm := thinKiteAmbientHomeomorph_rightSpoke δ hδ 0 (by simp)
      rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_zero] at hm
      rw [hm]
  refine ⟨δ, hδ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hmem
    exact hp (hpatchU δ hδ hδU hmem)
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hpPatch
    have hpBoundary := hp.1
    change p ∈ ⋃ e ∈ M.allBoundaryEdges,
      convexHull ℝ (M.position '' (e : Set M.Vertex)) at hpBoundary
    obtain ⟨e, hpBoundary⟩ := Set.mem_iUnion.mp hpBoundary
    obtain ⟨heBoundary, hpEdge⟩ := Set.mem_iUnion.mp hpBoundary
    by_cases heBase : e = M.freeTriangleBaseEdge T k
    · subst e
      apply hp.2
      exact convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k)) hpEdge
    · have heMoving : e ∈ movingEdges := Finset.mem_erase.mpr ⟨heBase, heBoundary⟩
      have hpEndpoint := hpatchB e heMoving δ hδ hδB ⟨hpPatch, hpEdge⟩
      apply hp.2
      rcases hpEndpoint with rfl | rfl
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 0),
          M.orderedVertex_mem T _, rfl⟩
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 1),
          M.orderedVertex_mem T _, rfl⟩
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    by_cases hpPatch : p ∈ transportedThinKitePatch E δ
    · exact hfixEndpoint p (hpatchA i δ hδ hδA ⟨hpPatch, hpi⟩)
    · exact transportedThinKiteHomeomorph_eqOn_compl E δ hδ hpPatch
  · have hmove := transportedThinKiteHomeomorph_image_baseSegment E δ hδ
    have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := hleft
    have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := hright
    have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
    simpa only [E, h0, h1, h2] using hmove

theorem PolygonalCircle.exists_thinKite_fixing_outside_triangle_and_family
    (K : PolygonalCircle)
    (hleft : K.IsVertexPoint (planePoint (-1) 0))
    (hcenter : K.IsVertexPoint (planePoint 0 0))
    (hright : K.IsVertexPoint (planePoint 1 0))
    (htrace : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0))
    {ι : Type*} [Finite ι] (A : ι → Set Plane)
    (hA : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ A i ⊆ {planePoint (-1) 0, planePoint 1 0})
    (W : Set Plane) (hW : IsOpen W)
    (htriangleW : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ W) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, thinKitePatch δ ⊆ W ∧
      EqOn (thinKiteAmbientHomeomorph δ hδ) id
        (K.carrier \ convexHull ℝ (Set.range kiteTrianglePosition)) ∧
      EqOn (thinKiteAmbientHomeomorph δ hδ) id (⋃ i, A i) := by
  classical
  let openBase := openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)
  let endpoints : Set Plane := {planePoint (-1) 0, planePoint 1 0}
  have hbaseTriangle : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆
      convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply (convex_convexHull ℝ _).segment_subset
    · exact subset_convexHull ℝ _ ⟨0, by simp [kiteTrianglePosition]⟩
    · exact subset_convexHull ℝ _ ⟨1, by simp [kiteTrianglePosition]⟩
  let P : ZMod K.n → ℝ → Prop := fun i δ =>
    Disjoint (K.edgeSegment i) openBase → thinKitePatch δ ∩ K.edgeSegment i ⊆ endpoints
  have hlocal : ∀ i, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
    intro i
    by_cases hdisjoint : Disjoint (K.edgeSegment i) openBase
    swap
    · exact ⟨1, by norm_num, fun _ _ _ hd => False.elim (hdisjoint hd)⟩
    have hinter : K.edgeSegment i ∩
        convexHull ℝ (Set.range kiteTrianglePosition) ⊆ endpoints := by
      rintro p ⟨hpEdge, hpTriangle⟩
      have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
        rw [← htrace]
        exact ⟨K.edgeSegment_subset_carrier i hpEdge, hpTriangle⟩
      have hpNotOpen : p ∉ openBase := fun hpOpen =>
        Set.disjoint_left.mp hdisjoint hpEdge hpOpen
      rw [← insert_endpoints_openSegment] at hpBase
      simp only [Set.mem_insert_iff] at hpBase
      rcases hpBase with hp | hp | hp
      · exact Or.inl hp
      · exact Or.inr hp
      · exact False.elim (hpNotOpen hp)
    have hleftEndpoint : planePoint (-1) 0 ∈ K.edgeSegment i →
        K.vertex i = planePoint (-1) 0 ∨ K.vertex (i + 1) = planePoint (-1) 0 := by
      intro hp
      rcases (hleft.mem_edgeSegment_iff i).mp hp with hp | hp
      · exact Or.inl hp.symm
      · exact Or.inr hp.symm
    have hrightEndpoint : planePoint 1 0 ∈ K.edgeSegment i →
        K.vertex i = planePoint 1 0 ∨ K.vertex (i + 1) = planePoint 1 0 := by
      intro hp
      rcases (hright.mem_edgeSegment_iff i).mp hp with hp | hp
      · exact Or.inl hp.symm
      · exact Or.inr hp.symm
    have hnotBoth : ¬(planePoint (-1) 0 ∈ K.edgeSegment i ∧
        planePoint 1 0 ∈ K.edgeSegment i) := by
      rintro ⟨hL, hR⟩
      have hcenterBase : planePoint 0 0 ∈ openBase := by
        change planePoint 0 0 ∈ openSegment ℝ (planePoint (-1) 0) (planePoint 1 0)
        rw [openSegment_eq_image_lineMap]
        refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
        ext j
        fin_cases j <;> norm_num [AffineMap.lineMap_apply_module, planePoint]
      have hcenterEdge : planePoint 0 0 ∈ K.edgeSegment i :=
        (convex_segment (𝕜 := ℝ) (K.vertex i) (K.vertex (i + 1))).segment_subset
          hL hR (openSegment_subset_segment ℝ _ _ hcenterBase)
      exact Set.disjoint_left.mp hdisjoint hcenterEdge hcenterBase
    obtain ⟨ε, hε, havoid⟩ :=
      exists_thinKitePatch_inter_segment_subset_baseEndpoints
        (K.adjacent_ne i) hinter hleftEndpoint hrightEndpoint hnotBoth
    exact ⟨ε, hε, fun δ hδ hδε _ => havoid δ hδ hδε⟩
  obtain ⟨εK, hεK, havoid⟩ := exists_pos_uniform_fintype P hlocal
  obtain ⟨εW, hεW, hpatchW⟩ :=
    exists_thinKitePatch_subset_open_normalized W hW htriangleW
  obtain ⟨εA, hεA, hpatchA⟩ := exists_pos_uniform_fintype
    (fun i δ => thinKitePatch δ ∩ A i ⊆ endpoints) hA
  let δ := min εK (min εW εA) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδK : δ < εK := by
    dsimp [δ]
    nlinarith [min_le_left εK (min εW εA), lt_min hεK (lt_min hεW hεA)]
  have hδW : δ < εW := by
    dsimp [δ]
    nlinarith [min_le_left εW εA, min_le_right εK (min εW εA),
      lt_min hεK (lt_min hεW hεA)]
  have hδA : δ < εA := by
    dsimp [δ]
    nlinarith [min_le_right εW εA, min_le_right εK (min εW εA),
      lt_min hεK (lt_min hεW hεA)]
  have hfixEndpoint (p : Plane)
      (hp : p = planePoint (-1) 0 ∨ p = planePoint 1 0) :
      thinKiteAmbientHomeomorph δ hδ p = p := by
    rcases hp with rfl | rfl
    · have hm := thinKiteAmbientHomeomorph_leftSpoke δ hδ 0 (by simp)
      simpa using hm
    · have hm := thinKiteAmbientHomeomorph_rightSpoke δ hδ 0 (by simp)
      simpa using hm
  refine ⟨δ, hδ, hpatchW δ hδ hδW, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hpEdge⟩ := Set.mem_iUnion.mp hp.1
    have hdisjoint : Disjoint (K.edgeSegment i) openBase := by
      rcases K.edgeSegment_subset_normalized_baseHalf_or_disjoint
          (by
            intro q hq
            have : q ∈ K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
              rw [htrace]
              exact hq
            exact this.1)
          hleft hcenter hright i with hL | hR | hd
      · apply False.elim
        apply hp.2
        apply hbaseTriangle
        rw [baseSegment_eq_spokes]
        exact Or.inl (hL hpEdge)
      · apply False.elim
        apply hp.2
        apply hbaseTriangle
        rw [baseSegment_eq_spokes]
        right
        rw [segment_symm]
        exact hR hpEdge
      · exact hd
    apply thinKiteAmbientHomeomorph_eqOn_compl δ hδ
    intro hpPatch
    have hpEndpoint := havoid i δ hδ hδK hdisjoint ⟨hpPatch, hpEdge⟩
    rcases hpEndpoint with hpLeft | hpRight
    · apply hp.2
      rw [hpLeft]
      exact subset_convexHull ℝ _ ⟨0, by simp [kiteTrianglePosition]⟩
    · apply hp.2
      rw [hpRight]
      exact subset_convexHull ℝ _ ⟨1, by simp [kiteTrianglePosition]⟩
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    by_cases hpPatch : p ∈ thinKitePatch δ
    · exact hfixEndpoint p (hpatchA i δ hδ hδA ⟨hpPatch, hpi⟩)
    · exact thinKiteAmbientHomeomorph_eqOn_compl δ hδ hpPatch

end DifferentialGeometry.Topology.PiecewiseLinear
