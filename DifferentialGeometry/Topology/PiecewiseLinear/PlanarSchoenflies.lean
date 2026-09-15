import External.ClassificationOfSurfaces.Moise.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def planeComplexOfSimplicialComplex
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] : PlaneComplex := by
  classical
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  exact
    { Vertex := K.vertices
      position := Subtype.val
      position_injective := Subtype.val_injective
      simplexes := Finset.univ.filter fun s => s.map e ∈ K.faces
      nonempty_of_mem := by
        intro s hs
        obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces (Finset.mem_filter.mp hs).2
        obtain ⟨v, hv, _⟩ := Finset.mem_map.mp hx
        exact ⟨v, hv⟩
      card_le_three := by
        intro s hs
        have hind := K.indep (Finset.mem_filter.mp hs).2
        have hcard := hind.card_le_finrank_succ
        have hdim := Submodule.finrank_le (vectorSpan ℝ (range ((↑) : s.map e → Plane)))
        have hbound : Fintype.card (s.map e) ≤ Module.finrank ℝ Plane + 1 :=
          hcard.trans (Nat.add_le_add_right hdim 1)
        simpa [Plane] using hbound
      down_closed := by
        intro s hs t hts ht
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, K.down_closed (Finset.mem_filter.mp hs).2
          (Finset.map_subset_map.mpr hts) ht.map⟩
      affineIndependent := by
        intro s hs
        let e' : s ↪ s.map e :=
          ⟨fun v => ⟨e v.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩,
            by
              intro v w h
              apply Subtype.ext
              apply e.injective
              exact congrArg (fun z : s.map e => (z : Plane)) h⟩
        exact (K.indep (Finset.mem_filter.mp hs).2).comp_embedding e'
      face_inter := by
        intro s hs t ht
        have h := K.convexHull_inter_convexHull
          (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2
        simp only [Finset.coe_map] at h
        rw [← Set.image_inter e.injective] at h
        rw [Finset.coe_inter]
        exact h }

theorem planeComplexOfSimplicialComplex_cellCarrier
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (s : Finset K.vertices) :
    (planeComplexOfSimplicialComplex K).cellCarrier s =
      convexHull ℝ ((s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset Plane) : Set Plane) := by
  simp only [planeComplexOfSimplicialComplex, PlaneComplex.cellCarrier, Finset.coe_map]
  rfl

theorem planeComplexOfSimplicialComplex_support
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] :
    (planeComplexOfSimplicialComplex K).support = K.space := by
  classical
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  have hmem (s : Finset K.vertices) :
      s ∈ (planeComplexOfSimplicialComplex K).simplexes ↔ s.map e ∈ K.faces := by
    change s ∈ Finset.univ.filter (fun s => s.map e ∈ K.faces) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcarrier (s : Finset K.vertices) :
      (planeComplexOfSimplicialComplex K).cellCarrier s =
        convexHull ℝ ((s.map e : Finset Plane) : Set Plane) := by
    simp only [planeComplexOfSimplicialComplex, PlaneComplex.cellCarrier, Finset.coe_map]
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact K.convexHull_subset_space ((hmem s).mp hs) ((hcarrier s).le hxs)
  · intro hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have hv (v : Plane) (hvs : v ∈ s) : v ∈ K.vertices :=
      K.down_closed hs (by simpa using hvs) (Finset.singleton_nonempty v)
    let t : Finset K.vertices := s.attach.map
      ⟨fun v => ⟨v.1, hv v.1 v.2⟩, by
        intro v w h
        apply Subtype.ext
        exact congrArg (fun z : K.vertices => (z : Plane)) h⟩
    have ht : t.map e = s := by
      ext v
      constructor
      · intro hv'
        obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv'
        obtain ⟨w, _, hwu⟩ := Finset.mem_map.mp hu
        subst u
        exact huv ▸ w.property
      · intro hvs
        refine Finset.mem_map.mpr ⟨⟨v, hv v hvs⟩, ?_, rfl⟩
        exact Finset.mem_map.mpr ⟨⟨v, hvs⟩, Finset.mem_attach _ _, rfl⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, (hmem t).mpr (ht.symm ▸ hs), ?_⟩
    rw [hcarrier, ht]
    exact hxs

theorem isHPolytope_cellCarrier (K : PlaneComplex) {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) : IsHPolytope (K.cellCarrier s) := by
  classical
  have hind : AffineIndependent ℝ ((↑) : s.image K.position → Plane) := by
    refine affineIndependent_finset_coe (K.affineIndependent s hs) ?_
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨⟨v, hv⟩, rfl⟩
  simpa only [PlaneComplex.cellCarrier, Finset.coe_image] using
    isHPolytope_convexHull_of_affineIndependent (s.image K.position) hind

theorem isPolyhedron_support (K : PlaneComplex) : IsPolyhedron K.support := by
  refine ⟨K.simplexes, inferInstance, fun s => K.cellCarrier s.1,
    fun s => isHPolytope_cellCarrier K s.2, ?_⟩
  simp only [PlaneComplex.support, Set.iUnion_subtype]

theorem isPiecewiseAffineOn_of_isPLOnSet {f : Plane → Plane} {A : Set Plane}
    (hf : IsPLOnSet A f) : IsPiecewiseAffineOn f A := by
  obtain ⟨K, hK, L, hLK, hL⟩ := hf
  rw [← hK, ← hLK.1]
  have h := isPiecewiseAffineOn_of_forall_isHPolytope (fun s : L.simplexes => L.cellCarrier s.1)
    (fun s => isHPolytope_cellCarrier L s.2) fun s => hL s.1 s.2
  simpa only [PlaneComplex.support, Set.iUnion_subtype] using h

theorem isPLOnSet_of_isPiecewiseAffineOn {f : Plane → Plane} {A : Set Plane}
    (hA : IsPolyhedron A) (hf : IsPiecewiseAffineOn f A) : IsPLOnSet A f := by
  classical
  obtain ⟨K, hfin, rfl⟩ := hA.exists_simplicialComplex
  have := hfin.to_subtype
  obtain ⟨L, hLK, hfinL, haff⟩ := hf.exists_isSubdivision_affineOn_faces K
  have := hfinL.to_subtype
  let R := planeComplexOfSimplicialComplex L
  refine ⟨R, (planeComplexOfSimplicialComplex_support L).trans hLK.space_eq,
    R, PlaneComplex.Subdivides.refl R, ?_⟩
  intro s hs
  let e : L.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  have hsL : s.map e ∈ L.faces := (Finset.mem_filter.mp hs).2
  obtain ⟨g, hg⟩ := haff (s.map e) hsL
  refine ⟨g, ?_⟩
  exact (planeComplexOfSimplicialComplex_cellCarrier L s) ▸ hg

theorem isPLHomeomorphOn_of_finitePLHomeomorphOn {h : Plane ≃ₜ Plane} {A : Set Plane}
    (F : FinitePLHomeomorphOn h A) : IsPLHomeomorphOn h A (h '' A) := by
  have hbij : BijOn h A (h '' A) := h.injective.injOn.bijOn_image
  refine ⟨hbij, isPiecewiseAffineOn_of_isPLOnSet F.isPLOnSet, ?_⟩
  refine (isPiecewiseAffineOn_of_isPLOnSet F.symm.isPLOnSet).congr fun y hy => ?_
  apply h.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (h.apply_symm_apply y).symm

private theorem exists_refinement_containing_complex_vertices
    (J : PolygonalCircle) (K : PlaneComplex) (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support) :
    ∃ J' : PolygonalCircle, J'.carrier = J.carrier ∧
      ∀ v : K.Vertex, J'.IsVertexPoint (K.position v) := by
  classical
  let F : Finset Plane := Finset.univ.image K.position
  have hF : ∀ p ∈ F, p ∈ J.carrier := by
    intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
    rw [← hsupport]
    exact hvertex v
  obtain ⟨J', hcarrier, hvertices⟩ := J.exists_refinement_vertices F hF
  refine ⟨J', hcarrier, fun v => hvertices (K.position v) ?_⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

private theorem exists_face_containing_polygon_edge
    (K : PlaneComplex) (J : PolygonalCircle)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ J.carrier →
      J.IsVertexPoint (K.position v))
    (i : ZMod J.n) :
    ∃ s ∈ K.simplexes, J.edgeSegment i ⊆ K.cellCarrier s := by
  let P := J.vertex i
  let Q := J.vertex (i + 1)
  let m := AffineMap.lineMap P Q (1 / 2 : ℝ)
  have hPQ : P ≠ Q := J.adjacent_ne i
  have hmOpen : m ∈ openSegment ℝ P Q := by
    exact lineMap_mem_openSegment ℝ P Q (by constructor <;> norm_num)
  have hmEdge : m ∈ J.edgeSegment i :=
    openSegment_subset_segment ℝ P Q hmOpen
  have hmSupport : m ∈ K.support := by
    rw [hsupport]
    exact J.edgeSegment_subset_carrier i hmEdge
  rw [PlaneComplex.support] at hmSupport
  simp only [Set.mem_iUnion] at hmSupport
  obtain ⟨s, hs, hms⟩ := hmSupport
  have hm_ne_left : m ≠ P := by
    intro h
    rw [h] at hmOpen
    exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hmOpen)
  have hm_ne_right : m ≠ Q := by
    intro h
    rw [h] at hmOpen
    exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hmOpen)
  have hm_ne_vertex (v : K.Vertex) : m ≠ K.position v := by
    intro hmv
    have hvEdge : K.position v ∈ J.edgeSegment i := by
      rw [← hmv]
      exact hmEdge
    rcases (hvertex v (J.edgeSegment_subset_carrier i hvEdge)).mem_edgeSegment_iff i |>.mp
      hvEdge with hv | hv
    · exact hm_ne_left (hmv.trans hv)
    · exact hm_ne_right (hmv.trans hv)
  have hscard : s.card = 2 := by
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hsle := hgraph s hs
    have hone_or_two : s.card = 1 ∨ s.card = 2 := by omega
    rcases hone_or_two with hone | htwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hmv : m = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hms
      exact (hm_ne_vertex v hmv).elim
    · exact htwo
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hscard
  let A := K.position v
  let B := K.position w
  have hAB : A ≠ B := by
    intro h
    exact hvw (K.position_injective (by simpa [A, B] using h))
  have himage : K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex) =
      ({K.position v, K.position w} : Set Plane) := by
    ext x
    simp [eq_comm]
  have hmABSegment : m ∈ segment ℝ A B := by
    simpa only [PlaneComplex.cellCarrier, himage, convexHull_pair, A, B] using hms
  have hmAB : m ∈ openSegment ℝ A B := by
    rw [← insert_endpoints_openSegment] at hmABSegment
    rcases hmABSegment with h | h | h
    · exact (hm_ne_vertex v (by simpa [A] using h)).elim
    · exact (hm_ne_vertex w (by simpa [B] using h)).elim
    · exact h
  have hbaseAB : segment ℝ A B ⊆ J.carrier := by
    rw [← hsupport]
    simpa only [PlaneComplex.cellCarrier, himage, convexHull_pair, A, B] using
      (K.cellCarrier_subset_support hs)
  obtain ⟨y, hym, hyEdge, hyAB⟩ :=
    J.exists_second_basePoint_of_edge_inter_openSegment hAB hbaseAB hmEdge hmAB
  have hmPQline : m ∈ affineSpan ℝ ({P, Q} : Set Plane) :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨1 / 2, rfl⟩
  have hyPQline : y ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [PolygonalCircle.edgeSegment, segment_eq_image_lineMap] at hyEdge
    obtain ⟨r, -, hry⟩ := hyEdge
    exact ⟨r, by simpa [P, Q] using hry⟩
  have hmABline : m ∈ affineSpan ℝ ({A, B} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [openSegment_eq_image_lineMap] at hmAB
    exact ⟨hmAB.choose, hmAB.choose_spec.2⟩
  have hyABline : y ∈ affineSpan ℝ ({A, B} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [segment_eq_image_lineMap] at hyAB
    obtain ⟨r, -, hry⟩ := hyAB
    exact ⟨r, hry⟩
  have hlinePQ : affineSpan ℝ ({m, y} : Set Plane) =
      affineSpan ℝ ({P, Q} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hmPQline hyPQline hym.symm
  have hlineAB : affineSpan ℝ ({m, y} : Set Plane) =
      affineSpan ℝ ({A, B} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hmABline hyABline hym.symm
  have hABlinePQ : affineSpan ℝ ({A, B} : Set Plane) =
      affineSpan ℝ ({P, Q} : Set Plane) := hlineAB.symm.trans hlinePQ
  have hAline : A ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [← hABlinePQ]
    exact subset_affineSpan ℝ ({A, B} : Set Plane) (by simp)
  have hBline : B ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [← hABlinePQ]
    exact subset_affineSpan ℝ ({A, B} : Set Plane) (by simp)
  have hAoutside : A ∉ openSegment ℝ P Q := by
    intro hAopen
    have hAedge : A ∈ J.edgeSegment i :=
      openSegment_subset_segment ℝ P Q hAopen
    rcases (hvertex v (J.edgeSegment_subset_carrier i hAedge)).mem_edgeSegment_iff i |>.mp
      hAedge with hA | hA
    · have hA' : A = P := by simpa [A, P] using hA
      rw [hA'] at hAopen
      exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hAopen)
    · have hA' : A = Q := by simpa [A, Q] using hA
      rw [hA'] at hAopen
      exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hAopen)
  have hBoutside : B ∉ openSegment ℝ P Q := by
    intro hBopen
    have hBedge : B ∈ J.edgeSegment i :=
      openSegment_subset_segment ℝ P Q hBopen
    rcases (hvertex w (J.edgeSegment_subset_carrier i hBedge)).mem_edgeSegment_iff i |>.mp
      hBedge with hB | hB
    · have hB' : B = P := by simpa [B, P] using hB
      rw [hB'] at hBopen
      exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hBopen)
    · have hB' : B = Q := by simpa [B, Q] using hB
      rw [hB'] at hBopen
      exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hBopen)
  refine ⟨{v, w}, hs, ?_⟩
  simpa only [PolygonalCircle.edgeSegment, P, Q, PlaneComplex.cellCarrier,
    himage, convexHull_pair, A, B] using
      segment_subset_of_midpoint_mem_openSegment hPQ hAline hBline hmAB
        hAoutside hBoutside

private theorem exists_polygonalCircle_image_of_affineOn_complex
    (J : PolygonalCircle) (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, J.IsVertexPoint (K.position v))
    {f : Plane → Plane} (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    ∃ J' : PolygonalCircle, J'.carrier = f '' J.carrier := by
  have hinjJ : Set.InjOn f J.carrier := by simpa [← hsupport] using hinj
  have hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i =
        segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1))) := by
    intro i
    obtain ⟨s, hs, his⟩ :=
      exists_face_containing_polygon_edge K J hgraph hsupport (fun v _ => hvertex v) i
    exact (haffine s hs).image_segment his
  let J' := J.mapEmbedding f hinjJ hedge
  exact ⟨J', J.mapEmbedding_carrier f hinjJ hedge⟩

theorem exists_polygonalCircle_image_of_isPLOnSet (J : PolygonalCircle)
    {f : Plane → Plane} (hpl : IsPLOnSet J.carrier f)
    (hinj : Set.InjOn f J.carrier) :
    ∃ J' : PolygonalCircle, J'.carrier = f '' J.carrier := by
  obtain ⟨K, hKsupport, L, hLK, hLaffine⟩ := hpl
  let A : PlaneComplex := PlaneComplex.active L
  have hAsupport : A.support = J.carrier := by
    change (PlaneComplex.active L).support = J.carrier
    rw [L.active_support, hLK.1, hKsupport]
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    exact A.card_le_two_of_support_eq_frontier J.isCompact_closedRegion.isClosed
      (hAsupport.trans J.frontier_closedRegion.symm) hs
  have hAvertex : ∀ v : A.Vertex, A.position v ∈ A.support := by
    intro v
    change L.position v.1 ∈ (PlaneComplex.active L).support
    rw [L.active_support]
    exact v.2
  have hAaffine : ∀ s ∈ A.simplexes, IsAffineOn f (A.cellCarrier s) := by
    intro s hs
    change IsAffineOn f ((PlaneComplex.active L).cellCarrier s)
    erw [L.active_cellCarrier]
    exact hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
  obtain ⟨R, hRcarrier, hRvertices⟩ :=
    exists_refinement_containing_complex_vertices J A hAsupport hAvertex
  have hARsupport : A.support = R.carrier := hAsupport.trans hRcarrier.symm
  obtain ⟨R', hR'image⟩ := exists_polygonalCircle_image_of_affineOn_complex R A hAgraph
    hARsupport (fun v => hRvertices v) (by rw [hAsupport]; exact hinj) hAaffine
  exact ⟨R', by rw [hR'image, hRcarrier]⟩

theorem isPLBall_two_of_isTriangle {C : Set Plane} (hC : IsTriangle C) : IsPLBall 2 C := by
  classical
  obtain ⟨p, hp, rfl⟩ := hC
  let T : Finset Plane := Finset.univ.image p
  have hT : AffineIndependent ℝ ((↑) : T → Plane) := by
    refine affineIndependent_finset_coe hp ?_
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩
  have hcard : T.card = 2 + 1 := by
    rw [Finset.card_image_of_injective _ hp.injective]
    rfl
  simpa only [T, Finset.coe_image, Finset.coe_univ, image_univ] using
    isPLBall_convexHull_of_affineIndependent T hT hcard

theorem isPLBall_two_closedRegion (J : PolygonalCircle) : IsPLBall 2 J.closedRegion := by
  obtain ⟨h, F, ⟨C, hC, _, hJC⟩, _⟩ :=
    J.polygonal_schoenflies_rel univ isOpen_univ (subset_univ _)
  have hpl : IsPLHomeomorphOn h J.closedRegion C := by
    have hF := isPLHomeomorphOn_of_finitePLHomeomorphOn F
    rwa [J.closedRegionMesh_support, hJC] at hF
  exact (isPLBall_two_of_isTriangle hC).of_isPLHomeomorphOn hpl.symm

theorem frontier_closedRegion (J : PolygonalCircle) : frontier J.closedRegion = J.carrier :=
  J.frontier_closedRegion

theorem isPLSphere_one_frontier_of_isTriangle {C : Set Plane} (hC : IsTriangle C) :
    IsPLSphere 1 (frontier C) := by
  classical
  obtain ⟨p, hp, rfl⟩ := hC
  let T : Finset Plane := Finset.univ.image p
  have hT : AffineIndependent ℝ ((↑) : T → Plane) := by
    refine affineIndependent_finset_coe hp ?_
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩
  have hcard : T.card = 1 + 2 := by
    rw [Finset.card_image_of_injective _ hp.injective]
    rfl
  have hspan : affineSpan ℝ (T : Set Plane) = ⊤ := by
    rw [show (T : Set Plane) = range p by simp [T]]
    exact (affineBasisOfTriangle p hp).tot
  simpa only [T, Finset.coe_image, Finset.coe_univ, image_univ] using
    isPLSphere_frontier_convexHull T hT hspan hcard

theorem isPolyhedron_carrier (J : PolygonalCircle) : IsPolyhedron J.carrier := by
  rw [← J.edgeComplex_support]
  exact isPolyhedron_support J.edgeComplex

theorem isPLSphere_one_carrier (J : PolygonalCircle) : IsPLSphere 1 J.carrier := by
  obtain ⟨h, F, ⟨C, hC, hboundary, hregion⟩, _⟩ :=
    J.polygonal_schoenflies_rel univ isOpen_univ (subset_univ _)
  have hpl : IsPLHomeomorphOn h J.closedRegion C := by
    have hF := isPLHomeomorphOn_of_finitePLHomeomorphOn F
    rwa [J.closedRegionMesh_support, hregion] at hF
  have hsub : J.carrier ⊆ J.closedRegion := by
    rw [J.closedRegion_eq_union]
    exact subset_union_right
  have hplBoundary := hpl.restrict (isPolyhedron_carrier J) hsub
  rw [hboundary] at hplBoundary
  exact (isPLSphere_one_frontier_of_isTriangle hC).of_isPLHomeomorphOn hplBoundary.symm

def polygonalCircleOfAffineIndependentTriple (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) : PolygonalCircle where
  n := 3
  three_le := le_rfl
  vertex := p
  adjacent_ne := fun i => hp.injective.ne ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  consecutive_inter := by
    have htriple (a b c : Fin 3) (h : Function.Injective ![a, b, c]) :
        AffineIndependent ℝ ![p a, p b, p c] := by
      have heq : ![p a, p b, p c] = p ∘ ![a, b, c] := by
        funext j
        fin_cases j <;> rfl
      rw [heq]
      exact hp.comp_embedding ⟨![a, b, c], h⟩
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hcase with rfl | rfl | rfl
    · exact segment_inter_segment_of_affineIndependent (htriple 0 1 2 (by decide))
    · exact segment_inter_segment_of_affineIndependent (htriple 1 2 0 (by decide))
    · exact segment_inter_segment_of_affineIndependent (htriple 2 0 1 (by decide))
  nonadjacent_disjoint := fun i j h₁ h₂ h₃ =>
    absurd ((by decide : ∀ i j : ZMod 3, i ≠ j → i ≠ j + 1 → j = i + 1) i j h₁ h₂) h₃

theorem exists_polygonalCircle_of_isPLSphere_one {S : Set Plane} (hS : IsPLSphere 1 S) :
    ∃ J : PolygonalCircle, J.carrier = S := by
  let J := polygonalCircleOfAffineIndependentTriple standardTrianglePosition
    standardTrianglePosition_affineIndependent
  obtain ⟨g, hg⟩ := isPLSphere_one_carrier J
  obtain ⟨f, hf⟩ := hS
  have h := hg.symm.trans hf
  obtain ⟨J', hJ'⟩ := exists_polygonalCircle_image_of_isPLOnSet J
    (isPLOnSet_of_isPiecewiseAffineOn (isPolyhedron_carrier J) h.isPiecewiseAffineOn)
    h.bijOn.injOn
  exact ⟨J', hJ'.trans h.image_eq⟩

theorem isPLBall_of_isPLSphere_one {S : Set Plane} (hS : IsPLSphere 1 S) :
    ∃ D : Set Plane, IsPLBall 2 D ∧ frontier D = S ∧ Bornology.IsBounded D := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLSphere_one hS
  exact ⟨J.closedRegion, isPLBall_two_closedRegion J, J.frontier_closedRegion,
    J.isCompact_closedRegion.isBounded⟩

theorem exists_isPLHomeomorphOn_straighten_on_closedRegion (J : PolygonalCircle)
    {U : Set Plane} (hU : IsOpen U) (hregion : J.closedRegion ⊆ U) :
    ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
      IsPLHomeomorphOn h J.closedRegion C ∧ h '' J.carrier = frontier C ∧ EqOn h id Uᶜ := by
  obtain ⟨h, F, ⟨C, hC, hboundary, himage⟩, hfix⟩ :=
    J.polygonal_schoenflies_rel U hU hregion
  refine ⟨h, C, hC, ?_, hboundary, hfix⟩
  have hF := isPLHomeomorphOn_of_finitePLHomeomorphOn F
  rwa [J.closedRegionMesh_support, himage] at hF

theorem exists_isPLHomeomorphOn_straighten_of_isPLSphere_one_on_closedRegion
    {S : Set Plane} (hS : IsPLSphere 1 S) :
    ∃ D : Set Plane, IsPLBall 2 D ∧ frontier D = S ∧ Bornology.IsBounded D ∧
      ∀ U : Set Plane, IsOpen U → D ⊆ U →
        ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
          IsPLHomeomorphOn h D C ∧ h '' S = frontier C ∧ EqOn h id Uᶜ := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLSphere_one hS
  refine ⟨J.closedRegion, isPLBall_two_closedRegion J, J.frontier_closedRegion,
    J.isCompact_closedRegion.isBounded, ?_⟩
  intro U hU hJU
  exact exists_isPLHomeomorphOn_straighten_on_closedRegion J hU hJU

end DifferentialGeometry.Topology.PiecewiseLinear
