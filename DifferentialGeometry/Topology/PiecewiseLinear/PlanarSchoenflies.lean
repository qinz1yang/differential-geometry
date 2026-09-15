import External.ClassificationOfSurfaces.Moise.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle

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
    let t : Finset K.vertices := s.subtype (fun v => v ∈ K.vertices)
    have ht : t.map e = s := Finset.subtype_map_of_mem hv
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, (hmem t).mpr (ht.symm ▸ hs), ?_⟩
    rw [hcarrier, ht]
    exact hxs

theorem planeComplexOfSimplicialComplex_isPure2
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    (planeComplexOfSimplicialComplex K).IsPure2 := by
  classical
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  intro s hs
  have hsK : s.map e ∈ K.faces := (Finset.mem_filter.mp hs).2
  obtain ⟨t, ht, hst, hcard⟩ := exists_face_superset_card_eq_of_isPLBall K hK hsK
  let u : Finset K.vertices := t.subtype (fun v => v ∈ K.vertices)
  have hu : u.map e = t := Finset.subtype_map_of_mem fun v hv =>
    K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  refine ⟨u, ?_, ?_, ?_⟩
  · change u ∈ Finset.univ.filter (fun r => r.map e ∈ K.faces)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.symm ▸ ht⟩
  · have hsu : s.map e ⊆ u.map e := by rwa [hu]
    exact Finset.map_subset_map.mp hsu
  · change u.card = 3
    rw [← Finset.card_map e, hu, hcard]

theorem planeComplexOfSimplicialComplex_toTriangleMesh_support
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    (planeComplexOfSimplicialComplex K).toTriangleMesh.toPlaneComplex.support = K.space := by
  rw [(planeComplexOfSimplicialComplex K).toTriangleMesh_support
    (planeComplexOfSimplicialComplex_isPure2 K hK),
    planeComplexOfSimplicialComplex_support]

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

theorem exists_polygonalCircle_of_isPLBall_two {D : Set Plane} (hD : IsPLBall 2 D) :
    ∃ J : PolygonalCircle, J.closedRegion = D := by
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLSphere_one hD.isPLSphere_frontier
  exact ⟨J, (J.eq_closedRegion_of_isCompact_frontier_eq hD.isPolyhedron.isCompact
    hJ.symm hD.interior_nonempty).symm⟩

theorem isPLBall_two_iff_exists_polygonalCircle {D : Set Plane} :
    IsPLBall 2 D ↔ ∃ J : PolygonalCircle, J.closedRegion = D := by
  refine ⟨exists_polygonalCircle_of_isPLBall_two, ?_⟩
  rintro ⟨J, rfl⟩
  exact isPLBall_two_closedRegion J

theorem isPLBall_of_isPLSphere_one {S : Set Plane} (hS : IsPLSphere 1 S) :
    ∃ D : Set Plane, IsPLBall 2 D ∧ frontier D = S ∧ Bornology.IsBounded D := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLSphere_one hS
  exact ⟨J.closedRegion, isPLBall_two_closedRegion J, J.frontier_closedRegion,
    J.isCompact_closedRegion.isBounded⟩

theorem isPLHomeomorphOn_transportedThinKiteHomeomorph
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ) :
    IsPLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ) univ univ := by
  let F := transportedThinKiteHomeomorphFinitePL e δ hδ
  have hP : IsPolyhedron (transportedThinKitePatch e δ) := by
    rw [← F.support_eq]
    exact isPolyhedron_support F.complex
  have hpl := isPLHomeomorphOn_of_finitePLHomeomorphOn F
  rw [transportedThinKiteHomeomorph_image] at hpl
  exact hpl.univ_of_eqOn_compl hP (transportedThinKiteHomeomorph_eqOn_compl e δ hδ)

theorem exists_isPLHomeomorphOn_remove_oneEdgeFree_triangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k)
    (hmore : 1 < M.triangles.card)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, ∃ J' : PolygonalCircle,
      IsPLHomeomorphOn g univ univ ∧
      Set.EqOn g id Uᶜ ∧
        g '' frontier M.toPlaneComplex.support =
          frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
  have hbaseImage : E '' segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    change affineEquivHomeomorph E ''
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) = _
    simpa only [h0, h1] using affineEquivHomeomorph_image_segment E
      (planePoint (-1) 0) (planePoint 1 0)
  have htriangleImage : E '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := M.freeTriangleAffineEquiv_image_triangle T k
  have hedgeNormalize : ∀ i : ZMod J.n,
      affineEquivHomeomorph E.symm '' J.edgeSegment i =
        segment ℝ (E.symm (J.vertex i)) (E.symm (J.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E.symm _ _
  let L := J.mapHomeomorph (affineEquivHomeomorph E.symm) hedgeNormalize
  have hLcarrier : L.carrier = E.symm '' J.carrier := by
    exact J.mapHomeomorph_carrier (affineEquivHomeomorph E.symm) hedgeNormalize
  have hbaseTriangle : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆
      convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply (convex_convexHull ℝ (Set.range kiteTrianglePosition)).segment_subset
    · apply subset_convexHull
      exact ⟨0, by simp [kiteTrianglePosition]⟩
    · apply subset_convexHull
      exact ⟨1, by simp [kiteTrianglePosition]⟩
  have htraceL : L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpL, hpTriangle⟩
      rw [hLcarrier] at hpL
      obtain ⟨q, hqJ, hqp⟩ := hpL
      have hq : q = E p := by
        apply E.symm.injective
        simpa using hqp
      have hpFrontier : E p ∈ frontier M.toPlaneComplex.support := by
        rw [hsupport, J.frontier_closedRegion]
        simpa [hq] using hqJ
      have hpWorldTriangle : E p ∈ M.triangleCarrier T.1 := by
        rw [← htriangleImage]
        exact ⟨p, hpTriangle, rfl⟩
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hfree]
        exact ⟨hpFrontier, hpWorldTriangle⟩
      rw [← hbaseImage] at hpWorldBase
      obtain ⟨r, hr, hrp⟩ := hpWorldBase
      exact E.injective hrp ▸ hr
    · intro p hpBase
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hbaseImage]
        exact ⟨p, hpBase, rfl⟩
      have hpFrontier : E p ∈ frontier M.toPlaneComplex.support := by
        exact (hfree.symm ▸ hpWorldBase).1
      have hpJ : E p ∈ J.carrier := by
        rwa [hsupport, J.frontier_closedRegion] at hpFrontier
      constructor
      · rw [hLcarrier]
        exact ⟨E p, hpJ, by simp⟩
      · exact hbaseTriangle hpBase
  let F : Finset Plane :=
    {planePoint (-1) 0, planePoint 0 0, planePoint 1 0}
  have hF : ∀ p ∈ F, p ∈ L.carrier := by
    intro p hp
    have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact left_mem_segment ℝ _ _
      · rw [baseSegment_eq_spokes]
        exact Or.inl (right_mem_segment ℝ _ _)
      · exact right_mem_segment ℝ _ _
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hpBase
    exact this.1
  obtain ⟨K, hKcarrier, hKF⟩ := L.exists_refinement_vertices F hF
  have hleft : K.IsVertexPoint (planePoint (-1) 0) := hKF _ (by simp [F])
  have hcenter : K.IsVertexPoint (planePoint 0 0) := hKF _ (by simp [F])
  have hright : K.IsVertexPoint (planePoint 1 0) := hKF _ (by simp [F])
  have htraceK : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    rw [hKcarrier, htraceL]
  have hbaseK : segment ℝ (planePoint (-1) 0) (planePoint 1 0) ⊆ K.carrier := by
    intro p hp
    rw [hKcarrier]
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hp
    exact this.1
  obtain ⟨δ, hδ, hfixU, hfixBoundary, hmove⟩ :=
    M.exists_supported_triangle_push_fixing_boundaryCarrier T k hfree U hU hTU
  let thin := thinKiteAmbientHomeomorph δ hδ
  let g := transportedThinKiteHomeomorph E δ hδ
  have g_apply (p : Plane) : g p = E (thin (E.symm p)) := rfl
  have hfixK : Set.EqOn thin id
      (K.carrier \ convexHull ℝ (Set.range kiteTrianglePosition)) := by
    intro p hp
    have hpL : p ∈ L.carrier := hKcarrier ▸ hp.1
    rw [hLcarrier] at hpL
    obtain ⟨q, hqJ, hqp⟩ := hpL
    have hq : q = E p := by
      apply E.symm.injective
      simpa using hqp
    have hpJ : E p ∈ J.carrier := hq ▸ hqJ
    have hpBoundary : E p ∈ M.boundaryCarrier := by
      rw [M.boundaryCarrier_eq_frontier_of_polygonalDisk J hsupport,
        hsupport, J.frontier_closedRegion]
      exact hpJ
    have hpNotTriangle : E p ∉ M.triangleCarrier T.1 := by
      intro hpTriangle
      rw [← htriangleImage] at hpTriangle
      obtain ⟨r, hr, hrp⟩ := hpTriangle
      apply hp.2
      have : r = p := E.injective hrp
      simpa [this] using hr
    have hg := hfixBoundary ⟨hpBoundary, hpNotTriangle⟩
    change thin p = p
    have hge : E (thin p) = E p := by
      change g (E p) = E p at hg
      rw [g_apply, E.symm_apply_apply] at hg
      exact hg
    exact E.injective hge
  obtain ⟨H, hHcarrier⟩ := K.exists_thinKite_image δ hδ hbaseK
    hleft hcenter hright htraceK hfixK
  have hedgeWorld : ∀ i : ZMod H.n,
      affineEquivHomeomorph E '' H.edgeSegment i =
        segment ℝ (E (H.vertex i)) (E (H.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E _ _
  let J' := H.mapHomeomorph (affineEquivHomeomorph E) hedgeWorld
  have hJ'carrier : J'.carrier = g '' J.carrier := by
    dsimp [J']
    rw [H.mapHomeomorph_carrier (affineEquivHomeomorph E) hedgeWorld,
      hHcarrier, hKcarrier, hLcarrier]
    ext p
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, ⟨r, ⟨s, hs, hsr⟩, hrq⟩, hqp⟩
      refine ⟨s, hs, ?_⟩
      calc
        g s = E (thin (E.symm s)) := g_apply s
        _ = E (thin r) := congrArg (fun z => E (thin z)) hsr
        _ = E q := congrArg E hrq
        _ = p := hqp
    · rintro ⟨s, hs, hsp⟩
      refine ⟨thin (E.symm s), ⟨E.symm s, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
      change E (thin (E.symm s)) = p
      exact (g_apply s).symm.trans hsp
  have hfrontier : g '' frontier M.toPlaneComplex.support =
      frontier (M.eraseTriangle T.1).toPlaneComplex.support :=
    M.image_frontier_eq_eraseTriangle_frontier_of_oneEdgeFree T k hfree g
      (by
        intro p hp
        exact hfixBoundary ⟨(by
          rw [M.boundaryCarrier_eq_frontier_of_polygonalDisk J hsupport]
          exact hp.1), hp.2⟩)
      hmove
  have hnewFrontier : frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      J'.carrier := by
    calc
      frontier (M.eraseTriangle T.1).toPlaneComplex.support =
          g '' frontier M.toPlaneComplex.support := hfrontier.symm
      _ = g '' J.carrier := by rw [hsupport, J.frontier_closedRegion]
      _ = J'.carrier := hJ'carrier.symm
  have hinterior : (interior (M.eraseTriangle T.1).toPlaneComplex.support).Nonempty := by
    have hcard := M.card_eraseTriangle_triangles T.2
    have hpos : 0 < (M.eraseTriangle T.1).triangles.card := by omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    let R : (M.eraseTriangle T.1).Triangle := ⟨t, ht⟩
    obtain ⟨p, hp⟩ := (M.eraseTriangle T.1).interior_triangleCarrier_nonempty R
    refine ⟨p, interior_mono ?_ hp⟩
    rw [(M.eraseTriangle T.1).toPlaneComplex_support]
    intro q hq
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hq⟩⟩
  have hremaining : (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion :=
    J'.eq_closedRegion_of_isCompact_frontier_eq
      (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hnewFrontier hinterior
  exact ⟨g, J',
    isPLHomeomorphOn_transportedThinKiteHomeomorph E δ hδ,
    hfixU, hfrontier, hremaining⟩

theorem exists_isPLHomeomorphOn_remove_twoEdgeFree_triangle
    (M : TriangleMesh) (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, ∃ J' : PolygonalCircle,
      IsPLHomeomorphOn g univ univ ∧
      Set.EqOn g id Uᶜ ∧
        g '' frontier M.toPlaneComplex.support =
          frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
  classical
  obtain ⟨J', hremaining, hregionInter⟩ :=
    M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k hfree
  let E := M.freeTriangleAffineEquiv T k
  have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
  have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
  have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
    simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
  have hbaseImage : E '' segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    change affineEquivHomeomorph E ''
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) = _
    simpa only [h0, h1] using affineEquivHomeomorph_image_segment E
      (planePoint (-1) 0) (planePoint 1 0)
  have htriangleImage : E '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := M.freeTriangleAffineEquiv_image_triangle T k
  have htraceWorld : J'.carrier ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpCarrier, hpTriangle⟩
      rw [← hregionInter]
      constructor
      · rw [J'.closedRegion_eq_union]
        exact Or.inr hpCarrier
      · exact hpTriangle
    · intro p hpBase
      have hpData : p ∈ J'.closedRegion ∩ M.triangleCarrier T.1 := by
        rw [hregionInter]
        exact hpBase
      have hpFrontier : p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
        rw [M.frontier_eraseTriangle_support T]
        exact Or.inr ⟨hremaining ▸ hpData.1, hpData.2⟩
      rw [hremaining, J'.frontier_closedRegion] at hpFrontier
      exact ⟨hpFrontier, hpData.2⟩
  have hedgeNormalize : ∀ i : ZMod J'.n,
      affineEquivHomeomorph E.symm '' J'.edgeSegment i =
        segment ℝ (E.symm (J'.vertex i)) (E.symm (J'.vertex (i + 1))) := by
    intro i
    exact affineEquivHomeomorph_image_segment E.symm _ _
  let L := J'.mapHomeomorph (affineEquivHomeomorph E.symm) hedgeNormalize
  have hLcarrier : L.carrier = E.symm '' J'.carrier :=
    J'.mapHomeomorph_carrier (affineEquivHomeomorph E.symm) hedgeNormalize
  have htraceL : L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpL, hpTriangle⟩
      rw [hLcarrier] at hpL
      obtain ⟨q, hq, hqp⟩ := hpL
      have hqE : q = E p := by
        apply E.symm.injective
        simpa using hqp
      have hpWorld : E p ∈ J'.carrier ∩ M.triangleCarrier T.1 := by
        constructor
        · simpa [hqE] using hq
        · rw [← htriangleImage]
          exact ⟨p, hpTriangle, rfl⟩
      have hpBase := htraceWorld ▸ hpWorld
      rw [← hbaseImage] at hpBase
      obtain ⟨r, hr, hrp⟩ := hpBase
      exact E.injective hrp ▸ hr
    · intro p hpBase
      have hpWorldBase : E p ∈
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
        rw [← hbaseImage]
        exact ⟨p, hpBase, rfl⟩
      have hpWorld := htraceWorld.symm ▸ hpWorldBase
      constructor
      · rw [hLcarrier]
        exact ⟨E p, hpWorld.1, by simp⟩
      · rw [← htriangleImage] at hpWorld
        obtain ⟨r, hr, hrp⟩ := hpWorld.2
        exact E.injective hrp ▸ hr
  let F : Finset Plane :=
    {planePoint (-1) 0, planePoint 0 0, planePoint 1 0}
  have hF : ∀ p ∈ F, p ∈ L.carrier := by
    intro p hp
    have hpBase : p ∈ segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact left_mem_segment ℝ _ _
      · rw [baseSegment_eq_spokes]
        exact Or.inl (right_mem_segment ℝ _ _)
      · exact right_mem_segment ℝ _ _
    have : p ∈ L.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) := by
      rw [htraceL]
      exact hpBase
    exact this.1
  obtain ⟨K, hKcarrier, hKF⟩ := L.exists_refinement_vertices F hF
  have hleft : K.IsVertexPoint (planePoint (-1) 0) := hKF _ (by simp [F])
  have hcenter : K.IsVertexPoint (planePoint 0 0) := hKF _ (by simp [F])
  have hright : K.IsVertexPoint (planePoint 1 0) := hKF _ (by simp [F])
  have htraceK : K.carrier ∩ convexHull ℝ (Set.range kiteTrianglePosition) =
      segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
    rw [hKcarrier, htraceL]
  let W := E ⁻¹' U
  have hW : IsOpen W := hU.preimage E.toAffineMap.continuous_of_finiteDimensional
  have htriangleW : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ W := by
    intro p hp
    exact hTU (htriangleImage ▸ ⟨p, hp, rfl⟩)
  obtain ⟨δ, hδ, hpatchW, hfixK⟩ :=
    K.exists_thinKite_fixing_outside_triangle hleft hcenter hright htraceK
      W hW htriangleW
  let thin := thinKiteAmbientHomeomorph δ hδ
  let push := transportedThinKiteHomeomorph E δ hδ
  have push_apply (p : Plane) : push p = E (thin (E.symm p)) := rfl
  have hfixU : Set.EqOn push id Uᶜ := by
    intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hpPatch
    obtain ⟨q, hq, rfl⟩ := hpPatch
    exact hp (hpatchW hq)
  have hfixWorld : Set.EqOn push id
      (J'.carrier \ M.triangleCarrier T.1) := by
    intro p hp
    have hpK : E.symm p ∈ K.carrier := by
      rw [hKcarrier, hLcarrier]
      exact ⟨p, hp.1, rfl⟩
    have hpNotTriangle : E.symm p ∉
        convexHull ℝ (Set.range kiteTrianglePosition) := by
      intro hpTriangle
      apply hp.2
      rw [← htriangleImage]
      exact ⟨E.symm p, hpTriangle, by simp⟩
    have hpFix := hfixK ⟨hpK, hpNotTriangle⟩
    change push p = p
    rw [push_apply, hpFix]
    simp
  have hnewFrontier : frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    rw [M.frontier_eraseTriangle_support T, hremaining, hregionInter]
  have hfixOutside : Set.EqOn push id
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) := by
    intro p hp
    apply hfixWorld
    constructor
    · have hpNew : p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
        rw [hnewFrontier]
        exact Or.inl hp
      rwa [hremaining, J'.frontier_closedRegion] at hpNew
    · exact hp.2
  have hmove : push '' segment ℝ (M.freeTriangleOrder T k 0)
        (M.freeTriangleOrder T k 1) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) :=
    by simpa only [push, h0, h1, h2] using
      transportedThinKiteHomeomorph_image_baseSegment E δ hδ
  have hpush : push '' frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      frontier M.toPlaneComplex.support := by
    rw [hnewFrontier, Set.image_union, hmove]
    conv_rhs =>
      rw [M.frontier_eq_outside_triangle_union_apex_of_twoEdgeFree T k hfree]
    congr 1
    apply Set.Subset.antisymm
    · rintro p ⟨q, hq, rfl⟩
      rw [hfixOutside hq]
      exact hq
    · intro p hp
      exact ⟨p, hp, hfixOutside hp⟩
  let pull := push.symm
  have hpullFix : Set.EqOn pull id Uᶜ := by
    intro p hp
    have hpp : push p = p := hfixU hp
    exact push.symm_apply_eq.mpr hpp.symm
  have hpull : pull '' frontier M.toPlaneComplex.support =
      frontier (M.eraseTriangle T.1).toPlaneComplex.support := by
    rw [← hpush, Set.image_image]
    simp [pull]
  exact ⟨pull, J',
    (isPLHomeomorphOn_transportedThinKiteHomeomorph E δ hδ).homeomorph_symm,
    hpullFix, hpull, hremaining⟩

theorem exists_isPLHomeomorphOn_remove_geometricallyFree_triangle
    (M : TriangleMesh) (hM : IsPLBall 2 M.toPlaneComplex.support)
    (T : M.Triangle) (hfree : M.IsGeometricallyFreeTriangle T)
    (hmore : 1 < M.triangles.card) {U : Set Plane} (hU : IsOpen U)
    (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      g '' M.toPlaneComplex.support = (M.eraseTriangle T.1).toPlaneComplex.support ∧
      IsPLBall 2 (M.eraseTriangle T.1).toPlaneComplex.support := by
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two hM
  obtain ⟨g, J', hg, hfix, hfront, hsupport⟩ :
      ∃ (g : Plane ≃ₜ Plane) (J' : PolygonalCircle),
        IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
        g '' frontier M.toPlaneComplex.support =
          frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
        (M.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
    obtain ⟨k, h | h⟩ := hfree
    · exact exists_isPLHomeomorphOn_remove_oneEdgeFree_triangle M J hJ.symm T k h hmore U hU hTU
    · exact exists_isPLHomeomorphOn_remove_twoEdgeFree_triangle M J hJ.symm T k h U hU hTU
  have himage := PolygonalCircle.TriangleMesh.image_support_eq_of_polygonalDisk_frontier
    M J' ⟨T.1, T.property⟩ g (M.eraseTriangle T.1) hfront hsupport
  refine ⟨g, hg, hfix, himage, ?_⟩
  rw [hsupport]
  exact isPLBall_two_closedRegion J'

theorem exists_isPLHomeomorphOn_straighten_to_triangle (M : TriangleMesh) (K : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = K.closedRegion)
    {U : Set Plane} (hU : IsOpen U) (hsubset : M.toPlaneComplex.support ⊆ U)
    (T₀ : M.Triangle) :
    ∃ h : Plane ≃ₜ Plane, IsPLHomeomorphOn h univ univ ∧
      h '' M.toPlaneComplex.support = M.triangleCarrier T₀.1 ∧ EqOn h id Uᶜ := by
  induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M K with
  | h n ih =>
    have htriangles : M.triangles.Nonempty := ⟨T₀.1, T₀.2⟩
    have hpos : 0 < M.triangles.card := Finset.card_pos.mpr htriangles
    by_cases hcard : M.triangles.card = 1
    · have hsingleton : M.triangles = {T₀.1} :=
        (Finset.card_eq_one.mp hcard).elim fun t ht => by
          have hT₀ : T₀.1 = t := Finset.mem_singleton.mp (ht ▸ T₀.2)
          rwa [← hT₀] at ht
      have hsupport₀ : M.toPlaneComplex.support = M.triangleCarrier T₀.1 := by
        simp only [M.toPlaneComplex_support, hsingleton, Finset.mem_singleton, iUnion_iUnion_eq_left]
        rfl
      refine ⟨Homeomorph.refl Plane, ?_, ?_, fun _ _ => rfl⟩
      · exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
          (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx =>
            (bijOn_id univ).invOn_invFunOn.1 hx⟩
      · exact (image_id _).trans hsupport₀
    · have hmore : 1 < M.triangles.card := by omega
      obtain ⟨T₁, T₂, hT₁T₂, hT₁free, hT₂free⟩ :=
        M.exists_two_geometricallyFreeTriangles_of_polygonalDisk K hsupport hmore
      obtain ⟨T, hTT₀, hTfree⟩ : ∃ T : M.Triangle,
          T.1 ≠ T₀.1 ∧ M.IsGeometricallyFreeTriangle T := by
        by_cases hT₁ : T₁.1 = T₀.1
        · exact ⟨T₂, fun hT₂ => hT₁T₂ (hT₁.trans hT₂.symm), hT₂free⟩
        · exact ⟨T₁, hT₁, hT₁free⟩
      let T₀' : (M.eraseTriangle T.1).Triangle :=
        ⟨T₀.1, Finset.mem_erase.mpr ⟨hTT₀.symm, T₀.2⟩⟩
      have hTU : M.triangleCarrier T.1 ⊆ U := by
        intro p hp
        apply hsubset
        rw [M.toPlaneComplex_support]
        exact mem_iUnion_of_mem T.1 (mem_iUnion_of_mem T.2 hp)
      have hcardErase := M.card_eraseTriangle_triangles T.2
      have hlt : (M.eraseTriangle T.1).triangles.card < M.triangles.card := by omega
      have hsubsetErase : (M.eraseTriangle T.1).toPlaneComplex.support ⊆ U :=
        (M.eraseTriangle_support_subset T.1).trans hsubset
      have hM : IsPLBall 2 M.toPlaneComplex.support := by
        rw [hsupport]
        exact isPLBall_two_closedRegion K
      obtain ⟨g, hg, hfix, himage, herase⟩ :=
        exists_isPLHomeomorphOn_remove_geometricallyFree_triangle M hM T hTfree hmore hU hTU
      obtain ⟨K', hK'⟩ := exists_polygonalCircle_of_isPLBall_two herase
      have hsupport' := hK'.symm
      obtain ⟨H, hH, himageH, hfixH⟩ :=
        ih (M.eraseTriangle T.1).triangles.card (by simpa [hcardM] using hlt)
          (M.eraseTriangle T.1) K' hsupport' hsubsetErase T₀' rfl
      refine ⟨g.trans H, hg.trans hH, ?_, ?_⟩
      · change (fun x => H (g x)) '' M.toPlaneComplex.support = M.triangleCarrier T₀.1
        rw [← image_image H g, himage]
        exact himageH
      · intro x hx
        change H (g x) = x
        rw [hfix hx, id_eq]
        exact hfixH hx

theorem exists_isPLHomeomorphOn_straighten_to_triangle_of_isPLBall
    (M : TriangleMesh) (hM : IsPLBall 2 M.toPlaneComplex.support)
    {U : Set Plane} (hU : IsOpen U) (hsubset : M.toPlaneComplex.support ⊆ U) (T₀ : M.Triangle) :
    ∃ h : Plane ≃ₜ Plane, IsPLHomeomorphOn h univ univ ∧
      h '' M.toPlaneComplex.support = M.triangleCarrier T₀.1 ∧ EqOn h id Uᶜ := by
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two hM
  exact exists_isPLHomeomorphOn_straighten_to_triangle M J hJ.symm hU hsubset T₀

private theorem mem_planeComplex_cells (K : PlaneComplex) {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (hcard : s.card = 3) : s ∈ K.cells :=
  Finset.mem_filter.mpr ⟨hs, hcard⟩

theorem exists_isPLHomeomorphOn_straighten_to_face
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {s : Finset Plane} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {U : Set Plane} (hU : IsOpen U) (hKU : K.space ⊆ U) :
    ∃ h : Plane ≃ₜ Plane, IsPLHomeomorphOn h univ univ ∧
      h '' K.space = convexHull ℝ (s : Set Plane) ∧ EqOn h id Uᶜ := by
  classical
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  let t := s.subtype (fun v => v ∈ K.vertices)
  have ht : t.map e = s := Finset.subtype_map_of_mem fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have htmem : t ∈ (planeComplexOfSimplicialComplex K).simplexes := by
    change t ∈ Finset.univ.filter (fun r => r.map e ∈ K.faces)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.symm ▸ hs⟩
  have htcard : t.card = 3 := by rw [← Finset.card_map e, ht, hcard]
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  let T₀ : M.Triangle := ⟨t, mem_planeComplex_cells _ htmem htcard⟩
  have hsupport : M.toPlaneComplex.support = K.space :=
    planeComplexOfSimplicialComplex_toTriangleMesh_support K hK
  have hM : IsPLBall 2 M.toPlaneComplex.support := hsupport.symm ▸ hK
  obtain ⟨h, hpl, himage, hfix⟩ := exists_isPLHomeomorphOn_straighten_to_triangle_of_isPLBall
    M hM hU (hsupport.trans_le hKU) T₀
  have hcarrier : M.triangleCarrier T₀.1 = convexHull ℝ (s : Set Plane) := by
    change convexHull ℝ (e '' (t : Set K.vertices)) = _
    rw [← Finset.coe_map e, ht]
  exact ⟨h, hpl, by simpa only [hsupport, hcarrier] using himage, hfix⟩

theorem exists_isPLHomeomorphOn_straighten (J : PolygonalCircle)
    {U : Set Plane} (hU : IsOpen U) (hregion : J.closedRegion ⊆ U) :
    ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
      IsPLHomeomorphOn h univ univ ∧ h '' J.closedRegion = C ∧
      h '' J.carrier = frontier C ∧ EqOn h id Uᶜ := by
  have htriangles : J.closedRegionMesh.triangles.Nonempty := by
    by_contra hempty
    have hempty' := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hvertexClosed : J.vertex 0 ∈ J.closedRegion := by
      rw [J.closedRegion_eq_union]
      exact Or.inr (J.vertex_mem_carrier 0)
    rw [← J.closedRegionMesh_support, J.closedRegionMesh.toPlaneComplex_support, hempty'] at hvertexClosed
    simp at hvertexClosed
  obtain ⟨T, hT⟩ := htriangles
  obtain ⟨h, hpl, himage, hfix⟩ := exists_isPLHomeomorphOn_straighten_to_triangle
    J.closedRegionMesh J J.closedRegionMesh_support hU
    (J.closedRegionMesh_support.trans_le hregion) ⟨T, hT⟩
  rw [J.closedRegionMesh_support] at himage
  have htriangle : IsTriangle (J.closedRegionMesh.triangleCarrier T) := by
    refine ⟨J.closedRegionMesh.position ∘ J.closedRegionMesh.orderedVertex ⟨T, hT⟩,
      J.closedRegionMesh.orderedVertex_affineIndependent ⟨T, hT⟩, ?_⟩
    rw [range_comp, J.closedRegionMesh.range_orderedVertex ⟨T, hT⟩]
    rfl
  refine ⟨h, J.closedRegionMesh.triangleCarrier T, htriangle, hpl, himage, ?_, hfix⟩
  rw [← J.frontier_closedRegion, h.image_frontier, himage]

theorem exists_isPLHomeomorphOn_straighten_of_isPLSphere_one
    {S : Set Plane} (hS : IsPLSphere 1 S) :
    ∃ D : Set Plane, IsPLBall 2 D ∧ frontier D = S ∧ Bornology.IsBounded D ∧
      ∀ U : Set Plane, IsOpen U → D ⊆ U →
        ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
          IsPLHomeomorphOn h univ univ ∧ h '' D = C ∧
          h '' S = frontier C ∧ EqOn h id Uᶜ := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLSphere_one hS
  refine ⟨J.closedRegion, isPLBall_two_closedRegion J, J.frontier_closedRegion,
    J.isCompact_closedRegion.isBounded, ?_⟩
  intro U hU hJU
  exact exists_isPLHomeomorphOn_straighten J hU hJU

theorem exists_isPLHomeomorphOn_straighten_on_closedRegion (J : PolygonalCircle)
    {U : Set Plane} (hU : IsOpen U) (hregion : J.closedRegion ⊆ U) :
    ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
      IsPLHomeomorphOn h J.closedRegion C ∧ h '' J.carrier = frontier C ∧ EqOn h id Uᶜ := by
  obtain ⟨h, C, hC, hpl, himage, hboundary, hfix⟩ :=
    exists_isPLHomeomorphOn_straighten J hU hregion
  refine ⟨h, C, hC, ?_, hboundary, hfix⟩
  have hrestriction := hpl.restrict (isPLBall_two_closedRegion J).isPolyhedron (subset_univ _)
  rwa [himage] at hrestriction

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

theorem exists_isPLHomeomorphOn_straighten_of_isPLBall_two {D : Set Plane}
    (hD : IsPLBall 2 D) {U : Set Plane} (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (h : Plane ≃ₜ Plane) (C : Set Plane), IsTriangle C ∧
      IsPLHomeomorphOn h univ univ ∧ h '' D = C ∧
      h '' frontier D = frontier C ∧ EqOn h id Uᶜ := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLBall_two hD
  simpa only [J.frontier_closedRegion] using exists_isPLHomeomorphOn_straighten J hU hDU

end DifferentialGeometry.Topology.PiecewiseLinear
