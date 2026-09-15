import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
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
      simp [h01]
    _ = segment ℝ (q 0) (q 2) ∪ segment ℝ (q 1) (q 2) := by
      rw [herase0, herase1, Finset.coe_pair, Finset.coe_pair, convexHull_pair,
        convexHull_pair, union_comm]

private theorem mem_planeComplex_cells' (K : PlaneComplex) {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (hcard : s.card = 3) : s ∈ K.cells :=
  Finset.mem_filter.mpr ⟨hs, hcard⟩

open Classical in
theorem exists_faceStar_center_of_isPLBall_two
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t₀ : Finset Plane} (ht₀ : t₀ ∈ K.faces)
    (ht₀card : t₀.card = 3) (hne : K.space ≠ convexHull ℝ (t₀ : Set Plane)) :
    ∃ t s : Finset Plane, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      s ∈ K.faces ∧ s ⊆ t ∧
      frontier K.space ∩ convexHull ℝ (t : Set Plane) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane) := by
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
  have hmore : 1 < M.triangles.card := by
    have hnonempty : M.triangles.Nonempty := ⟨T₀.1, T₀.2⟩
    have hpos : 0 < M.triangles.card := Finset.card_pos.mpr hnonempty
    by_contra h
    have hcard : M.triangles.card = 1 := by omega
    have hsingleton : M.triangles = {T₀.1} :=
      (Finset.card_eq_one.mp hcard).elim fun t ht => by
        have hT₀ : T₀.1 = t := Finset.mem_singleton.mp (ht ▸ T₀.2)
        rwa [← hT₀] at ht
    have hsupport₀ : M.toPlaneComplex.support = M.triangleCarrier T₀.1 := by
      simp only [M.toPlaneComplex_support, hsingleton, Finset.mem_singleton,
        iUnion_iUnion_eq_left]
      rfl
    have hcarrier₀ : M.triangleCarrier T₀.1 = convexHull ℝ (t₀ : Set Plane) := by
      change (planeComplexOfSimplicialComplex K).cellCarrier t₀' = _
      rw [planeComplexOfSimplicialComplex_cellCarrier, ht₀map]
    exact hne (hsupport.symm.trans (hsupport₀.trans hcarrier₀))
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
    refine ⟨t, s, htK, htcard, htt₀, hsK, hsSub, ?_⟩
    rw [← hsupport, ← hcarrier]
    change frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 = _
    rw [hone]
    simpa only [s, htq] using iUnion_convexHull_erase_singleton_triangle q hq |>.symm
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
    refine ⟨t, s, htK, htcard, htt₀, hsK, hsSub, ?_⟩
    rw [← hsupport, ← hcarrier]
    change frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 = _
    rw [htwo]
    simpa only [s, htq] using iUnion_convexHull_erase_pair_triangle q hq |>.symm

end DifferentialGeometry.Topology.PiecewiseLinear
