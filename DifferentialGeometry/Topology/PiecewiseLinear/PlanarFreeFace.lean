import DifferentialGeometry.Topology.PiecewiseLinear.PlanarRelativeDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem iUnion_convexHull_erase_singleton_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (q : Fin 3 → E) (hq : Function.Injective q) :
    ⋃ v ∈ ({q 2} : Finset E),
        convexHull ℝ ((((Finset.univ.image q).erase v : Finset E) : Set E)) =
      segment ℝ (q 0) (q 1) := by
  have h01 : q 0 ≠ q 1 := hq.ne (by decide)
  have h02 : q 0 ≠ q 2 := hq.ne (by decide)
  have h12 : q 1 ≠ q 2 := hq.ne (by decide)
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  have himage : Finset.image q ({0, 1, 2} : Finset (Fin 3)) = {q 0, q 1, q 2} := by
    simp
  have herase : ({q 0, q 1, q 2} : Finset E).erase (q 2) = {q 0, q 1} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx2, hx0 | hx1 | hx2'⟩
      · exact Or.inl hx0
      · exact Or.inr hx1
      · exact (hx2 hx2').elim
    · rintro (hx0 | hx1)
      · exact ⟨fun hx2 => h02 (hx0.symm.trans hx2), Or.inl hx0⟩
      · exact ⟨fun hx2 => h12 (hx1.symm.trans hx2), Or.inr (Or.inl hx1)⟩
  rw [himage]
  calc
    (⋃ v ∈ ({q 2} : Finset E),
        convexHull ℝ (((({q 0, q 1, q 2} : Finset E).erase v : Finset E) : Set E))) =
        convexHull ℝ (((({q 0, q 1, q 2} : Finset E).erase (q 2) : Finset E) : Set E)) := by
      simp
    _ = segment ℝ (q 0) (q 1) := by rw [herase, Finset.coe_pair, convexHull_pair]

open Classical in
theorem iUnion_convexHull_erase_pair_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (q : Fin 3 → E) (hq : Function.Injective q) :
    ⋃ v ∈ ({q 0, q 1} : Finset E),
        convexHull ℝ ((((Finset.univ.image q).erase v : Finset E) : Set E)) =
      segment ℝ (q 0) (q 2) ∪ segment ℝ (q 1) (q 2) := by
  have h01 : q 0 ≠ q 1 := hq.ne (by decide)
  have h02 : q 0 ≠ q 2 := hq.ne (by decide)
  have h12 : q 1 ≠ q 2 := hq.ne (by decide)
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  have himage : Finset.image q ({0, 1, 2} : Finset (Fin 3)) = {q 0, q 1, q 2} := by
    simp
  have herase0 : ({q 0, q 1, q 2} : Finset E).erase (q 0) = {q 1, q 2} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx0, hx0' | hx1 | hx2⟩
      · exact (hx0 hx0').elim
      · exact Or.inl hx1
      · exact Or.inr hx2
    · rintro (hx1 | hx2)
      · exact ⟨fun hx0 => h01 (hx0.symm.trans hx1), Or.inr (Or.inl hx1)⟩
      · exact ⟨fun hx0 => h02 (hx0.symm.trans hx2), Or.inr (Or.inr hx2)⟩
  have herase1 : ({q 0, q 1, q 2} : Finset E).erase (q 1) = {q 0, q 2} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx1, hx0 | hx1' | hx2⟩
      · exact Or.inl hx0
      · exact (hx1 hx1').elim
      · exact Or.inr hx2
    · rintro (hx0 | hx2)
      · exact ⟨fun hx1 => h01 (hx0.symm.trans hx1), Or.inl hx0⟩
      · exact ⟨fun hx1 => h12 (hx1.symm.trans hx2), Or.inr (Or.inr hx2)⟩
  rw [himage]
  calc
    (⋃ v ∈ ({q 0, q 1} : Finset E),
        convexHull ℝ (((({q 0, q 1, q 2} : Finset E).erase v : Finset E) : Set E))) =
        convexHull ℝ (((({q 0, q 1, q 2} : Finset E).erase (q 0) : Finset E) : Set E)) ∪
          convexHull ℝ (((({q 0, q 1, q 2} : Finset E).erase (q 1) : Finset E) : Set E)) := by
      simp
    _ = segment ℝ (q 0) (q 2) ∪ segment ℝ (q 1) (q 2) := by
      rw [herase0, herase1, Finset.coe_pair, Finset.coe_pair, convexHull_pair,
        convexHull_pair, union_comm]

private theorem mem_planeComplex_cells' (K : PlaneComplex) {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (hcard : s.card = 3) : s ∈ K.cells :=
  Finset.mem_filter.mpr ⟨hs, hcard⟩

open Classical in
theorem planeComplexOfSimplicialComplex_eraseTriangle_support
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (t : Finset K.vertices) :
    (((planeComplexOfSimplicialComplex K).toTriangleMesh).eraseTriangle t).toPlaneComplex.support =
      (eraseTriangleComplex K (t.map ⟨Subtype.val, Subtype.val_injective⟩)).space := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  have hmem (u : Finset K.vertices) :
      u ∈ M.triangles ↔ u.map e ∈ K.faces ∧ u.card = 3 := by
    change u ∈ (Finset.univ.filter (fun r : Finset K.vertices => r.map e ∈ K.faces)).filter
      (fun r => r.card = 3) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcarrier (u : Finset K.vertices) :
      convexHull ℝ ((M.eraseTriangle t).position '' (u : Set K.vertices)) =
        convexHull ℝ ((u.map e : Finset Plane) : Set Plane) := by
    rw [Finset.coe_map]
    rfl
  change (M.eraseTriangle t).toPlaneComplex.support = (eraseTriangleComplex K (t.map e)).space
  rw [TriangleMesh.toPlaneComplex_support, eraseTriangleComplex_space]
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hu' : u ≠ t ∧ u ∈ M.triangles := Finset.mem_erase.mp hu
    have huK := (hmem u).mp hu'.2
    refine mem_iUnion₂.mpr ⟨u.map e, ⟨huK.1, ?_, ?_⟩, ?_⟩
    · exact (Finset.card_map e (s := (u : Finset K.vertices))).trans huK.2
    · exact fun h => hu'.1 (Finset.map_injective e h)
    · exact (hcarrier u) ▸ hxu
  · intro hx
    obtain ⟨u, ⟨huK, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
    let r := u.subtype (fun v => v ∈ K.vertices)
    have hr : r.map e = u := Finset.subtype_map_of_mem fun v hv =>
      K.down_closed huK (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hrmem : r ∈ M.triangles := (hmem r).mpr ⟨hr.symm ▸ huK, by
      rw [← Finset.card_map e, hr, hucard]⟩
    have hrne : r ≠ t := fun h => hut (hr.symm.trans (congrArg (Finset.map e) h))
    refine mem_iUnion₂.mpr ⟨r, Finset.mem_erase.mpr ⟨hrne, hrmem⟩, ?_⟩
    exact (hcarrier r).symm ▸ (show x ∈ convexHull ℝ ((r.map e : Finset Plane) : Set Plane) from hr.symm ▸ hxu)

theorem one_lt_triangles_card_of_support_ne_triangleCarrier (M : TriangleMesh)
    (T : M.Triangle) (hne : M.toPlaneComplex.support ≠ M.triangleCarrier T.1) :
    1 < M.triangles.card := by
  have hnonempty : M.triangles.Nonempty := ⟨T.1, T.2⟩
  have hpos : 0 < M.triangles.card := Finset.card_pos.mpr hnonempty
  by_contra h
  have hcard : M.triangles.card = 1 := by omega
  have hsingleton : M.triangles = {T.1} :=
    (Finset.card_eq_one.mp hcard).elim fun t ht => by
      have hT : T.1 = t := Finset.mem_singleton.mp (ht ▸ T.2)
      rwa [← hT] at ht
  apply hne
  simp only [M.toPlaneComplex_support, hsingleton, Finset.mem_singleton,
    iUnion_iUnion_eq_left]
  rfl

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_of_frontier_inter
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t s : Finset Plane} (ht : t ∈ K.faces)
    (htcard : t.card = 3) (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : frontier K.space ∩ convexHull ℝ (t : Set Plane) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane))
    (hne : K.space ≠ convexHull ℝ (t : Set Plane))
    {U : Set Plane} (hU : IsOpen U) (htU : convexHull ℝ (t : Set Plane) ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      EqOn g id (frontier K.space \ convexHull ℝ (t : Set Plane)) ∧
      g '' K.space = (eraseTriangleComplex K t).space ∧
      IsPLBall 2 (eraseTriangleComplex K t).space := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  let r := t.subtype (fun v => v ∈ K.vertices)
  have hr : r.map e = t := Finset.subtype_map_of_mem fun v hv =>
    K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hrmem : r ∈ (planeComplexOfSimplicialComplex K).simplexes := by
    change r ∈ Finset.univ.filter (fun u => u.map e ∈ K.faces)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.symm ▸ ht⟩
  have hrcard : r.card = 3 := by rw [← Finset.card_map e, hr, htcard]
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  let T : M.Triangle := ⟨r, mem_planeComplex_cells' _ hrmem hrcard⟩
  have hsupport : M.toPlaneComplex.support = K.space :=
    planeComplexOfSimplicialComplex_toTriangleMesh_support K hK
  have hposition : M.position '' (T.1 : Set M.Vertex) = (t : Set Plane) := by
    change ((fun x : K.vertices => (x : Plane)) '' (r : Set K.vertices)) = (t : Set Plane)
    rw [← hr, Finset.coe_map]
    rfl
  have hcarrier : M.triangleCarrier T.1 = convexHull ℝ (t : Set Plane) :=
    congrArg (convexHull ℝ) hposition
  have hmore : 1 < M.triangles.card :=
    one_lt_triangles_card_of_support_ne_triangleCarrier M T (by rwa [hsupport, hcarrier])
  obtain ⟨p, hp, hs⟩ : ∃ p ∈ t, s = {p} ∨ s = t.erase p := by
    rcases hscard with hscard | hscard
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hscard
      exact ⟨p, hst (Finset.mem_singleton_self p), Or.inl rfl⟩
    · obtain ⟨p, hpt, hps⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : s.card < t.card)
      refine ⟨p, hpt, Or.inr (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
      · exact fun v hv => Finset.mem_erase.mpr ⟨fun hvp => hps (hvp ▸ hv), hst hv⟩
      · rw [Finset.card_erase_of_mem hpt, htcard, hscard]
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, M.position (M.orderedVertex T k) = p := by
    have hp' : p ∈ M.position '' (T.1 : Set M.Vertex) := hposition.symm ▸ hp
    rwa [← M.range_orderedVertex T, ← range_comp] at hp'
  let q := M.freeTriangleOrder T k
  have hq : Function.Injective q := (M.freeTriangleOrder_affineIndependent T k).injective
  have hq2 : q 2 = p := by simpa [q, TriangleMesh.freeTriangleOrder] using hk
  have htq : t = Finset.univ.image q := by
    apply Finset.coe_injective
    calc
      (t : Set Plane) = M.position '' (T.1 : Set M.Vertex) := hposition.symm
      _ = Set.range q := (M.range_freeTriangleOrder T k).symm
      _ = (Finset.univ.image q : Finset Plane) := by ext x; simp
  have hfree : M.IsGeometricallyFreeTriangle T := by
    refine ⟨k, ?_⟩
    rcases hs with hs | hs
    · left
      change frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 = _
      rw [hsupport, hcarrier, htrace, hs, ← hq2, htq]
      exact iUnion_convexHull_erase_singleton_triangle q hq
    · right
      have hs' : s = {q 0, q 1} := by
        rw [hs, ← hq2, htq, ← Finset.image_erase hq]
        rw [show (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]
        simp
      change frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 = _
      rw [hsupport, hcarrier, htrace, hs', htq]
      exact iUnion_convexHull_erase_pair_triangle q hq
  have herase : (M.eraseTriangle T.1).toPlaneComplex.support =
      (eraseTriangleComplex K t).space := by
    have h := planeComplexOfSimplicialComplex_eraseTriangle_support K r
    exact h.trans (congrArg (fun u => (eraseTriangleComplex K u).space) hr)
  obtain ⟨g, hg, hfix, hboundary, himage, hball⟩ :=
    exists_isPLHomeomorphOn_remove_geometricallyFree_triangle_fixing_frontier
      M (hsupport.symm ▸ hK) T hfree hmore hU (hcarrier.trans_le htU)
  exact ⟨g, hg, hfix, by rwa [hsupport, hcarrier] at hboundary,
    by rwa [hsupport, herase] at himage, herase ▸ hball⟩

open Classical in
theorem exists_isPLBall_eraseTriangleComplex_with_intersections
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t₀ : Finset Plane} (ht₀ : t₀ ∈ K.faces)
    (ht₀card : t₀.card = 3) (hne : K.space ≠ convexHull ℝ (t₀ : Set Plane)) :
    ∃ t s : Finset Plane, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      s ∈ K.faces ∧ s ⊆ t ∧ (s.card = 1 ∨ s.card = 2) ∧
      frontier K.space ∩ convexHull ℝ (t : Set Plane) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane) ∧
      (∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
        (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) ∧
      IsPLBall 2 (eraseTriangleComplex K t).space ∧
      ∀ U : Set Plane, IsOpen U → convexHull ℝ (t : Set Plane) ⊆ U →
        ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
          EqOn g id (frontier K.space \ convexHull ℝ (t : Set Plane)) ∧
          g '' K.space = (eraseTriangleComplex K t).space := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  let t₀' := t₀.subtype (fun v => v ∈ K.vertices)
  have ht₀map : t₀'.map e = t₀ := Finset.subtype_map_of_mem fun v hv =>
    K.down_closed ht₀ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have ht₀mem : t₀' ∈ (planeComplexOfSimplicialComplex K).simplexes := by
    change t₀' ∈ Finset.univ.filter (fun r => r.map e ∈ K.faces)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀map.symm ▸ ht₀⟩
  have ht₀card' : t₀'.card = 3 := by rw [← Finset.card_map e, ht₀map, ht₀card]
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  let T₀ : M.Triangle := ⟨t₀', mem_planeComplex_cells' _ ht₀mem ht₀card'⟩
  have hsupport : M.toPlaneComplex.support = K.space :=
    planeComplexOfSimplicialComplex_toTriangleMesh_support K hK
  have hcarrier₀ : M.triangleCarrier T₀.1 = convexHull ℝ (t₀ : Set Plane) := by
    change (planeComplexOfSimplicialComplex K).cellCarrier t₀' = _
    rw [planeComplexOfSimplicialComplex_cellCarrier, ht₀map]
  have hmore : 1 < M.triangles.card :=
    one_lt_triangles_card_of_support_ne_triangleCarrier M T₀ (by rwa [hsupport, hcarrier₀])
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two (hsupport.symm ▸ hK)
  obtain ⟨T₁, T₂, hT₁T₂, hT₁free, hT₂free⟩ :=
    M.exists_two_geometricallyFreeTriangles_of_polygonalDisk J hJ.symm hmore
  obtain ⟨T, hTT₀, hTfree⟩ : ∃ T : M.Triangle,
      T.1 ≠ T₀.1 ∧ M.IsGeometricallyFreeTriangle T := by
    by_cases hT₁ : T₁.1 = T₀.1
    · exact ⟨T₂, fun hT₂ => hT₁T₂ (hT₁.trans hT₂.symm), hT₂free⟩
    · exact ⟨T₁, hT₁, hT₁free⟩
  let r : Finset K.vertices := T.1
  let t := r.map e
  have hTsimplex : T.1 ∈ (planeComplexOfSimplicialComplex K).simplexes :=
    (planeComplexOfSimplicialComplex K).mem_simplexes_of_mem_cells T.2
  have htK : t ∈ K.faces := by
    change r.map e ∈ K.faces
    simpa only [r] using (Finset.mem_filter.mp hTsimplex).2
  have htcard : t.card = 3 := by
    calc
      t.card = r.card := Finset.card_map e
      _ = T.1.card := by rfl
      _ = 3 := M.card_triangle T.1 T.2
  have htt₀ : t ≠ t₀ := by
    intro h
    apply hTT₀
    have hr : r = t₀' := by
      apply Finset.map_injective e
      rw [ht₀map]
      exact h
    exact hr
  have hposition : M.position '' (T.1 : Set M.Vertex) = (t : Set Plane) := by
    change ((fun x : K.vertices => (x : Plane)) '' (r : Set K.vertices)) =
      ((r.map e : Finset Plane) : Set Plane)
    rw [Finset.coe_map]
    rfl
  let q := M.freeTriangleOrder T hTfree.choose
  have hq : Function.Injective q := (M.freeTriangleOrder_affineIndependent T hTfree.choose).injective
  have htq : t = Finset.univ.image q := by
    apply Finset.coe_injective
    calc
      (t : Set Plane) = M.position '' (T.1 : Set M.Vertex) := hposition.symm
      _ = Set.range q := by
        simpa only [q] using (M.range_freeTriangleOrder T hTfree.choose).symm
      _ = (Finset.univ.image q : Finset Plane) := by
        ext x
        simp
  have hcarrier : M.triangleCarrier T.1 = convexHull ℝ (t : Set Plane) := by
    exact congrArg (convexHull ℝ) hposition
  have herase : (M.eraseTriangle T.1).toPlaneComplex.support =
      (eraseTriangleComplex K t).space :=
    planeComplexOfSimplicialComplex_eraseTriangle_support K r
  have hremove (U : Set Plane) (hU : IsOpen U)
      (htU : convexHull ℝ (t : Set Plane) ⊆ U) :
      ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
        EqOn g id (frontier K.space \ convexHull ℝ (t : Set Plane)) ∧
        g '' K.space = (eraseTriangleComplex K t).space := by
    obtain ⟨g, hg, hfix, hboundary, himage, -⟩ :=
      exists_isPLHomeomorphOn_remove_geometricallyFree_triangle_fixing_frontier
        M (hsupport.symm ▸ hK) T hTfree hmore hU (hcarrier.trans_le htU)
    exact ⟨g, hg, hfix, by rwa [hsupport, hcarrier] at hboundary,
      by rwa [hsupport, herase] at himage⟩
  have hball : IsPLBall 2 (eraseTriangleComplex K t).space := by
    obtain ⟨g, hg, -, -, himage⟩ := hremove univ isOpen_univ (subset_univ _)
    exact himage ▸ hK.of_isPLHomeomorphOn (hg.restrict hK.isPolyhedron (subset_univ _))
  have hother (u : Finset Plane) (hu : u ∈ K.faces) (hucard : u.card = 3) :
      ∃ R : M.Triangle, R.1.map e = u := by
    let r' := u.subtype (fun v => v ∈ K.vertices)
    have hr' : r'.map e = u := Finset.subtype_map_of_mem fun v hv =>
      K.down_closed hu (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hr'simplex : r' ∈ (planeComplexOfSimplicialComplex K).simplexes := by
      change r' ∈ Finset.univ.filter (fun r => r.map e ∈ K.faces)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'.symm ▸ hu⟩
    have hr'card : r'.card = 3 := by rw [← Finset.card_map e, hr', hucard]
    exact ⟨⟨r', mem_planeComplex_cells' _ hr'simplex hr'card⟩, hr'⟩
  let eM : M.Vertex ↪ Plane := ⟨M.position, M.position_injective⟩
  have hintercard (R : M.Triangle) :
      ((R.1.map e) ∩ t).card = (R.1 ∩ T.1).card := by
    change ((R.1.map eM) ∩ (T.1.map eM)).card = _
    rw [← Finset.map_inter, Finset.card_map]
  have hbaseImage : (M.freeTriangleBaseEdge T hTfree.choose).map e = {q 0, q 1} := by
    let b : Finset M.Vertex := M.freeTriangleBaseEdge T hTfree.choose
    change b.map eM = {q 0, q 1}
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_pair]
    exact M.image_freeTriangleBaseEdge T hTfree.choose
  rcases hTfree.choose_spec with hone | htwo
  · let s : Finset Plane := {q 2}
    have hsSub : s ⊆ t := by
      rw [htq]
      intro x hx
      simp only [s, Finset.mem_singleton] at hx
      subst x
      exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
    have hsK : s ∈ K.faces :=
      K.down_closed htK hsSub (Finset.singleton_nonempty (q 2))
    refine ⟨t, s, htK, htcard, htt₀, hsK, hsSub, Or.inl (Finset.card_singleton _),
      ?_, ?_, hball, hremove⟩
    · rw [← hsupport, ← hcarrier, hone]
      simpa only [s, htq] using iUnion_convexHull_erase_singleton_triangle q hq |>.symm
    · intro u hu hucard hsu
      obtain ⟨R, hRu⟩ := hother u hu hucard
      have hapex : M.orderedVertex T hTfree.choose ∉ R.1 := by
        intro hv
        apply hsu
        apply Finset.singleton_subset_iff.mpr
        have hq2 : q 2 = M.position (M.orderedVertex T hTfree.choose) := by
          simp only [q, TriangleMesh.freeTriangleOrder, Equiv.swap_apply_left]
        rw [hq2, ← hRu]
        exact Finset.mem_map.mpr ⟨M.orderedVertex T hTfree.choose, hv, rfl⟩
      have hi := TriangleMesh.inter_subset_freeTriangleBaseEdge_of_oneEdgeFree
        M T hTfree.choose hone R.2 hapex
      refine ⟨?_, ?_⟩
      · rw [← hRu, hintercard]
        exact hi.2
      · intro hscard
        have hsone : s.card = 1 := Finset.card_singleton _
        omega
  · let s : Finset Plane := {q 0, q 1}
    have hsSub : s ⊆ t := by
      rw [htq]
      intro x hx
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    have hsne : s.Nonempty := ⟨q 0, Finset.mem_insert_self _ _⟩
    have hsK : s ∈ K.faces := K.down_closed htK hsSub hsne
    refine ⟨t, s, htK, htcard, htt₀, hsK, hsSub,
      Or.inr (Finset.card_pair (hq.ne (by decide))), ?_, ?_, hball, hremove⟩
    · rw [← hsupport, ← hcarrier, htwo]
      simpa only [s, htq] using iUnion_convexHull_erase_pair_triangle q hq |>.symm
    · intro u hu hucard hsu
      obtain ⟨R, hRu⟩ := hother u hu hucard
      have hbase : ¬M.freeTriangleBaseEdge T hTfree.choose ⊆ R.1 := by
        intro hbase
        apply hsu
        change {q 0, q 1} ⊆ u
        rw [← hbaseImage, ← hRu]
        exact Finset.map_subset_map.mpr hbase
      have hi := TriangleMesh.inter_subset_freeTriangleBaseEdge_of_twoEdgeFree
        M (hsupport.symm ▸ hK) T hTfree.choose htwo R.2 hbase
      refine ⟨?_, fun _ => ?_⟩
      · rw [← hRu, hintercard]
        exact hi.2
      · change u ∩ t ⊆ {q 0, q 1}
        rw [← hRu, ← hbaseImage]
        change R.1.map eM ∩ T.1.map eM ⊆ (M.freeTriangleBaseEdge T hTfree.choose).map eM
        rw [← Finset.map_inter]
        exact Finset.map_subset_map.mpr hi.1

open Classical in
theorem exists_isPLBall_eraseTriangleComplex_of_isPLBall_two
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t₀ : Finset Plane} (ht₀ : t₀ ∈ K.faces)
    (ht₀card : t₀.card = 3) (hne : K.space ≠ convexHull ℝ (t₀ : Set Plane)) :
    ∃ t s : Finset Plane, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      s ∈ K.faces ∧ s ⊆ t ∧ (s.card = 1 ∨ s.card = 2) ∧
      frontier K.space ∩ convexHull ℝ (t : Set Plane) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane) ∧
      IsPLBall 2 (eraseTriangleComplex K t).space ∧
      ∀ U : Set Plane, IsOpen U → convexHull ℝ (t : Set Plane) ⊆ U →
        ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
          EqOn g id (frontier K.space \ convexHull ℝ (t : Set Plane)) ∧
          g '' K.space = (eraseTriangleComplex K t).space := by
  obtain ⟨t, s, ht, htc, htt, hs, hst, hsc, htrace, -, hball, hremove⟩ :=
    exists_isPLBall_eraseTriangleComplex_with_intersections K hK ht₀ ht₀card hne
  exact ⟨t, s, ht, htc, htt, hs, hst, hsc, htrace, hball, hremove⟩

open Classical in
theorem exists_faceStar_center_of_isPLBall_two
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t₀ : Finset Plane} (ht₀ : t₀ ∈ K.faces)
    (ht₀card : t₀.card = 3) (hne : K.space ≠ convexHull ℝ (t₀ : Set Plane)) :
    ∃ t s : Finset Plane, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      s ∈ K.faces ∧ s ⊆ t ∧
      frontier K.space ∩ convexHull ℝ (t : Set Plane) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane) := by
  obtain ⟨t, s, ht, htc, htt, hs, hst, -, htrace, -, -⟩ :=
    exists_isPLBall_eraseTriangleComplex_of_isPLBall_two K hK ht₀ ht₀card hne
  exact ⟨t, s, ht, htc, htt, hs, hst, htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
