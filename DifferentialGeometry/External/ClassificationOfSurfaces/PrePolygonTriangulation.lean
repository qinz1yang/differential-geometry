/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Modified from PolygonalPolyhedron.lean at e3c7230fe78d7b056a415d9ecae6f77887046b32:
use local PrePolygon/inside/outside and a private canonical Mathlib adapter;
remove the duplicate upstream polygonal Jordan dependency. See MODIFICATIONS.md.
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (Plane PlaneComplex TriangleMesh planePoint planePoint_apply_zero planePoint_apply_one
    affineIndependent_plane_triple_of_det_ne_zero mem_convexHull_range_fin3_of_weights)

private def planeComplexToAbstract (K : PlaneComplex) :
    PreAbstractSimplicialComplex K.Vertex where
  faces := K.simplexes
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem s hs, ?_⟩
    intro t hts ht
    exact K.down_closed s hs t hts ht

private noncomputable def planeComplexToSimplicialComplex (K : PlaneComplex) :
    Geometry.SimplicialComplex ℝ Plane := by
  classical
  refine
    { (planeComplexToAbstract K).map K.position with
      indep := ?_
      inter_subset_convexHull := ?_ }
  · rintro s ⟨t, ht, rfl⟩
    apply LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_finset_coe
      (K.affineIndependent t ht)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro s t ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
    have hfaces : convexHull ℝ (K.position '' (S : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (T : Set K.Vertex)) =
          convexHull ℝ (K.position '' ((S ∩ T : Finset K.Vertex) : Set K.Vertex)) :=
      K.face_inter S hS T hT
    simpa only [Finset.coe_image, Finset.coe_inter,
      Set.image_inter K.position_injective] using hfaces.le

private theorem planeComplexToSimplicialComplex_faces_finite (K : PlaneComplex) :
    (planeComplexToSimplicialComplex K).faces.Finite := by
  classical
  change ((fun s : Finset K.Vertex => s.image K.position) ''
    (K.simplexes : Set (Finset K.Vertex))).Finite
  exact K.simplexes.finite_toSet.image _

private theorem planeComplexToSimplicialComplex_space (K : PlaneComplex) :
    (planeComplexToSimplicialComplex K).space = K.support := by
  classical
  have hcarrier (t : Finset K.Vertex) :
      convexHull ℝ (t.image K.position : Set Plane) = K.cellCarrier t := by
    rw [PlaneComplex.cellCarrier, Finset.coe_image]
  change (⋃ s ∈ ((fun t : Finset K.Vertex => t.image K.position) ''
      (K.simplexes : Set (Finset K.Vertex))), convexHull ℝ (s : Set Plane)) =
    ⋃ t ∈ K.simplexes, K.cellCarrier t
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨t, ht, rfl⟩ := hs
    exact Set.mem_iUnion₂.mpr ⟨t, ht, hcarrier t ▸ hx⟩
  · intro hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨t.image K.position, ⟨t, ht, rfl⟩,
      (hcarrier t).symm ▸ hx⟩

private theorem planeComplexToSimplicialComplex_pure (K : PlaneComplex)
    (hpure : K.IsPure2) :
    ∀ s ∈ (planeComplexToSimplicialComplex K).faces,
      ∃ t ∈ (planeComplexToSimplicialComplex K).faces, s ⊆ t ∧ t.card = 3 := by
  classical
  rintro s ⟨S, hS, rfl⟩
  obtain ⟨T, hT, hST, hcard⟩ := hpure S hS
  refine ⟨T.image K.position, ⟨T, hT, rfl⟩, Finset.image_subset_image hST, ?_⟩
  rw [Finset.card_image_of_injective _ K.position_injective, hcard]

namespace Schoenflies.PrePolygon

variable {m : ℕ} (P : PrePolygon m)

private theorem isCompact_closure_inside : IsCompact (closure (Schoenflies.inside P.carrier)) :=
  P.isSeparating_carrier.isBounded_inside.isCompact_closure

private theorem closure_inside_eq_union :
    closure (Schoenflies.inside P.carrier) = Schoenflies.inside P.carrier ∪ P.carrier :=
  (IsRegionOf.inside P.carrier).closure_eq P.isSeparating_carrier

private noncomputable def edgeNormalLinear (p q : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := (q - p) 0 * x 1 - (q - p) 1 * x 0
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private noncomputable def edgeLine (i : ZMod (m + 3)) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x => edgeNormalLinear (P.vertex i) (P.vertex (i + 1))
      (x - P.vertex i))
    (edgeNormalLinear (P.vertex i) (P.vertex (i + 1))) (P.vertex i) (by
      intro x
      simp)

@[simp] private theorem edgeLine_initial (i : ZMod (m + 3)) :
    P.edgeLine i (P.vertex i) = 0 := by
  simp [edgeLine]

@[simp] private theorem edgeLine_terminal (i : ZMod (m + 3)) :
    P.edgeLine i (P.vertex (i + 1)) = 0 := by
  simp [edgeLine, edgeNormalLinear]
  ring

private theorem edgeLine_eq_zero_of_mem_edge (i : ZMod (m + 3)) {x : Plane}
    (hx : x ∈ P.edge i) : P.edgeLine i x = 0 := by
  rw [edge, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp [edgeLine, edgeNormalLinear]
  ring

private theorem edgeLine_surjective (i : ZMod (m + 3)) : Function.Surjective (P.edgeLine i) := by
  let dx : ℝ := (P.vertex (i + 1) - P.vertex i) 0
  let dy : ℝ := (P.vertex (i + 1) - P.vertex i) 1
  have hxy : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    push Not at h
    apply P.vertex_ne_succ i
    ext j
    fin_cases j
    · exact (sub_eq_zero.mp (by simpa [dx, PiLp.sub_apply] using h.1)).symm
    · exact (sub_eq_zero.mp (by simpa [dy, PiLp.sub_apply] using h.2)).symm
  have hden : dx ^ 2 + dy ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  intro y
  refine ⟨P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx, ?_⟩
  change (P.vertex (i + 1) - P.vertex i) 0 *
      (P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - P.vertex i) 1 -
      (P.vertex (i + 1) - P.vertex i) 1 *
      (P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - P.vertex i) 0 = y
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, planePoint_apply_zero,
    planePoint_apply_one, smul_eq_mul]
  ring_nf
  field_simp [hden]
  dsimp [dx, dy]
  ring_nf

private theorem interior_edgeLine_nonneg (i : ZMod (m + 3)) :
    interior {x | 0 ≤ P.edgeLine i x} = {x | 0 < P.edgeLine i x} := by
  let f := P.edgeLine i
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (P.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

private theorem interior_edgeLine_nonpos (i : ZMod (m + 3)) :
    interior {x | P.edgeLine i x ≤ 0} = {x | P.edgeLine i x < 0} := by
  let f := P.edgeLine i
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (P.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

private noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (ZMod (m + 3))).toList.map P.edgeLine

private theorem edgeLine_mem_edgeLines (i : ZMod (m + 3)) : P.edgeLine i ∈ P.edgeLines := by
  simp [edgeLines]

private noncomputable def enclosingRadius : ℝ :=
  max (P.isCompact_closure_inside.isBounded.subset_closedBall (0 : Plane)).choose 1

private theorem enclosingRadius_pos : 0 < P.enclosingRadius := by
  unfold enclosingRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

private theorem closedRegion_subset_enclosingBall :
    (closure (Schoenflies.inside P.carrier)) ⊆ Metric.closedBall (0 : Plane) P.enclosingRadius := by
  intro x hx
  have h := (P.isCompact_closure_inside.isBounded.subset_closedBall (0 : Plane)).choose_spec hx
  rw [Metric.mem_closedBall] at h ⊢
  exact h.trans (le_max_left _ _)

private def enclosingTriangleVertices (R : ℝ) : Fin 3 → Plane :=
  ![planePoint (-3 * R) (-2 * R), planePoint (3 * R) (-2 * R), planePoint 0 (4 * R)]

private theorem enclosingTriangleVertices_affineIndependent {R : ℝ} (hR : 0 < R) :
    AffineIndependent ℝ (enclosingTriangleVertices R) := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

private theorem closedBall_subset_enclosingTriangle {R : ℝ} (hR : 0 < R) :
    Metric.closedBall (0 : Plane) R ⊆
      convexHull ℝ (Set.range (enclosingTriangleVertices R)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hx0 := PiLp.norm_apply_le (p := 2) x (0 : Fin 2)
  have hx1 := PiLp.norm_apply_le (p := 2) x (1 : Fin 2)
  simp only [Real.norm_eq_abs] at hx0 hx1
  have hx0lo : -R ≤ x 0 := by linarith [neg_abs_le (x 0)]
  have hx0hi : x 0 ≤ R := by linarith [le_abs_self (x 0)]
  have hx1lo : -R ≤ x 1 := by linarith [neg_abs_le (x 1)]
  have hx1hi : x 1 ≤ R := by linarith [le_abs_self (x 1)]
  let w : Fin 3 → ℝ :=
    ![(4 * R - x 1 - 2 * x 0) / (12 * R),
      (4 * R - x 1 + 2 * x 0) / (12 * R),
      (x 1 + 2 * R) / (6 * R)]
  apply mem_convexHull_range_fin3_of_weights _ x w
  · intro i
    fin_cases i
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
  · change (4 * R - x 1 - 2 * x 0) / (12 * R) +
        (4 * R - x 1 + 2 * x 0) / (12 * R) +
        (x 1 + 2 * R) / (6 * R) = 1
    field_simp [hR.ne']
    ring
  · ext i
    fin_cases i <;> simp [w, enclosingTriangleVertices, planePoint]
    all_goals field_simp [hR.ne']; ring

private noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (enclosingTriangleVertices P.enclosingRadius)
    (enclosingTriangleVertices_affineIndependent P.enclosingRadius_pos)

private theorem closedRegion_subset_enclosingMesh_support :
    (closure (Schoenflies.inside P.carrier)) ⊆ P.enclosingMesh.toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact P.closedRegion_subset_enclosingBall.trans
    (closedBall_subset_enclosingTriangle P.enclosingRadius_pos)

private noncomputable def arrangementMesh : TriangleMesh :=
  P.enclosingMesh.refineByLines P.edgeLines

private theorem arrangementMesh_support :
    P.arrangementMesh.toPlaneComplex.support = P.enclosingMesh.toPlaneComplex.support :=
  P.enclosingMesh.refineByLines_support P.edgeLines

private theorem arrangementMesh_isMonochromatic (i : ZMod (m + 3)) :
    P.arrangementMesh.IsMonochromatic (P.edgeLine i) :=
  P.enclosingMesh.refineByLines_isMonochromatic_of_mem P.edgeLines (P.edgeLine_mem_edgeLines i)

private theorem closedRegion_subset_arrangementMesh_support :
    (closure (Schoenflies.inside P.carrier)) ⊆ P.arrangementMesh.toPlaneComplex.support := by
  rw [P.arrangementMesh_support]
  exact P.closedRegion_subset_enclosingMesh_support

private def arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) : Set Plane :=
  convexHull ℝ (P.arrangementMesh.position '' (t : Set _))

private theorem convex_arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) :
    Convex ℝ (P.arrangementTriangleCarrier t) :=
  convex_convexHull ℝ _

private theorem isClosed_arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) :
    IsClosed (P.arrangementTriangleCarrier t) :=
  (t.finite_toSet.image P.arrangementMesh.position).isClosed_convexHull ℝ

private theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    (interior (P.arrangementTriangleCarrier t)).Nonempty := by
  apply (P.convex_arrangementTriangleCarrier t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t => P.arrangementMesh.position v) =
      P.arrangementMesh.position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  have hAI := P.arrangementMesh.affineIndependent_triangle t ht
  apply hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, P.arrangementMesh.card_triangle t ht]
  simp

private theorem closure_interior_arrangementTriangleCarrier
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    closure (interior (P.arrangementTriangleCarrier t)) = P.arrangementTriangleCarrier t := by
  calc
    closure (interior (P.arrangementTriangleCarrier t)) =
        closure (P.arrangementTriangleCarrier t) :=
      (P.convex_arrangementTriangleCarrier t).closure_interior_eq_closure_of_nonempty_interior
        (P.arrangementTriangleCarrier_interior_nonempty ht)
    _ = P.arrangementTriangleCarrier t := (P.isClosed_arrangementTriangleCarrier t).closure_eq

private theorem arrangementTriangle_interior_disjoint_carrier
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    Disjoint
      (interior (P.arrangementTriangleCarrier t))
      P.carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : P.edgeLine i x = 0 := P.edgeLine_eq_zero_of_mem_edge i hxi
  rcases P.arrangementMesh_isMonochromatic i t ht with hpos | hneg
  · have hsubset : P.arrangementTriangleCarrier t ⊆
        {y | 0 ≤ P.edgeLine i y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage (P.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [P.interior_edgeLine_nonneg i] at hxstrict
    change 0 < P.edgeLine i x at hxstrict
    linarith
  · have hsubset : P.arrangementTriangleCarrier t ⊆
        {y | P.edgeLine i y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage (P.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [P.interior_edgeLine_nonpos i] at hxstrict
    change P.edgeLine i x < 0 at hxstrict
    linarith

private theorem arrangementTriangle_interior_side
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.inside P.carrier) ∨
      interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.outside P.carrier) := by
  let s := interior (P.arrangementTriangleCarrier t)
  have hsconn : IsPreconnected s :=
    (P.convex_arrangementTriangleCarrier t).interior.isPreconnected
  have hscarrier : s ⊆ P.carrierᶜ := by
    intro x hx
    exact Set.disjoint_left.mp (P.arrangementTriangle_interior_disjoint_carrier ht) hx
  have hsunion : s ⊆ (Schoenflies.inside P.carrier) ∪ (Schoenflies.outside P.carrier) := by
    rw [Schoenflies.inside_union_outside P.carrier]
    exact hscarrier
  obtain ⟨x, hx⟩ := P.arrangementTriangleCarrier_interior_nonempty ht
  have hxside := hsunion hx
  rcases hxside with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union P.isSeparating_carrier.isOpen_inside
      P.isSeparating_carrier.isOpen_outside
      (Schoenflies.disjoint_inside_outside (C := P.carrier)) hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union P.isSeparating_carrier.isOpen_inside
      P.isSeparating_carrier.isOpen_outside
      (Schoenflies.disjoint_inside_outside (C := P.carrier)) hsunion ⟨x, hx, hxout⟩

private def isInteriorArrangementTriangle (t : Finset P.arrangementMesh.Vertex) : Prop :=
  interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.inside P.carrier)

private noncomputable def closedRegionMesh : TriangleMesh :=
  by
    classical
    exact P.arrangementMesh.restrictTriangles P.isInteriorArrangementTriangle

private theorem closedRegionMesh_triangle_mem {t : Finset P.closedRegionMesh.Vertex} :
    t ∈ P.closedRegionMesh.triangles ↔
      t ∈ P.arrangementMesh.triangles ∧ P.isInteriorArrangementTriangle t := by
  classical
  exact P.arrangementMesh.mem_restrictTriangles_triangles P.isInteriorArrangementTriangle

private theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles)
    (hinside : P.isInteriorArrangementTriangle t) :
    P.arrangementTriangleCarrier t ⊆ (closure (Schoenflies.inside P.carrier)) := by
  rw [← P.closure_interior_arrangementTriangleCarrier ht]
  exact closure_mono hinside

private theorem closedRegionMesh_support_subset :
    P.closedRegionMesh.toPlaneComplex.support ⊆ (closure (Schoenflies.inside P.carrier)) := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := P.closedRegionMesh_triangle_mem.mp ht
  exact P.arrangementTriangleCarrier_subset_closedRegion htarr htinside hxt

private theorem interiorRegion_subset_closedRegionMesh_support :
    (Schoenflies.inside P.carrier) ⊆ P.closedRegionMesh.toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
    rw [P.closure_inside_eq_union]
    exact Or.inl hxinside
  have hxsupport := P.closedRegion_subset_arrangementMesh_support hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (P.arrangementTriangleCarrier t)) := by
    rw [P.closure_interior_arrangementTriangleCarrier ht]
    exact hxt
  have hxclosureInter :
      x ∈ closure ((Schoenflies.inside P.carrier) ∩ interior (P.arrangementTriangleCarrier t)) :=
    P.isSeparating_carrier.isOpen_inside.inter_closure ⟨hxinside, hxclosure⟩
  have hmeet' :
      ((Schoenflies.inside P.carrier) ∩ interior (P.arrangementTriangleCarrier t)).Nonempty :=
    Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have hmeet :
      (interior (P.arrangementTriangleCarrier t) ∩ (Schoenflies.inside P.carrier)).Nonempty := by
    obtain ⟨y, hyinside, hyt⟩ := hmeet'
    exact ⟨y, hyt, hyinside⟩
  have htinside : P.isInteriorArrangementTriangle t := by
    rcases P.arrangementTriangle_interior_side ht with hin | hout
    · exact hin
    · obtain ⟨y, hyt, hyinside⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp
        (Schoenflies.disjoint_inside_outside (C := P.carrier)) hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, P.closedRegionMesh_triangle_mem.mpr ⟨ht, htinside⟩, hxt⟩

private theorem closedRegionMesh_support :
    P.closedRegionMesh.toPlaneComplex.support = (closure (Schoenflies.inside P.carrier)) := by
  apply Set.Subset.antisymm P.closedRegionMesh_support_subset
  exact closure_minimal
    P.interiorRegion_subset_closedRegionMesh_support
    P.closedRegionMesh.toPlaneComplex.isCompact_support.isClosed

private theorem disjoint_carrier_exteriorRegion :
    Disjoint P.carrier (Schoenflies.outside P.carrier) := by
  rw [Set.disjoint_left]
  intro x hxcarrier hxexterior
  have hxcompl : x ∈ P.carrierᶜ := by
    rw [← Schoenflies.inside_union_outside P.carrier]
    exact Or.inr hxexterior
  exact hxcompl hxcarrier

private theorem disjoint_closedRegion_exteriorRegion :
    Disjoint (closure (Schoenflies.inside P.carrier)) (Schoenflies.outside P.carrier) := by
  rw [P.closure_inside_eq_union]
  exact (Schoenflies.disjoint_inside_outside (C := P.carrier)).sup_left
    P.disjoint_carrier_exteriorRegion

private theorem frontier_closedRegion :
    frontier (closure (Schoenflies.inside P.carrier)) = P.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
      have hx' := frontier_subset_closure hx
      simpa [P.isCompact_closure_inside.isClosed.closure_eq] using hx'
    rw [P.closure_inside_eq_union] at hxclosed
    rcases hxclosed with hxinside | hxcarrier
    · have hxint : x ∈ interior (closure (Schoenflies.inside P.carrier)) :=
        interior_maximal (by rw [P.closure_inside_eq_union]; exact Set.subset_union_left)
          P.isSeparating_carrier.isOpen_inside hxinside
      exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier hxint hx
    · exact hxcarrier
  · intro x hxcarrier
    have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
      rw [P.closure_inside_eq_union]
      exact Or.inr hxcarrier
    rw [P.isCompact_closure_inside.isClosed.frontier_eq]
    refine ⟨hxclosed, ?_⟩
    intro hxint
    have hxclosureExterior : x ∈ closure (Schoenflies.outside P.carrier) :=
      frontier_subset_closure (P.isSeparating_carrier.frontier_outside.symm ▸ hxcarrier)
    have hxclosureInter :
        x ∈ closure (interior (closure (Schoenflies.inside P.carrier)) ∩
          Schoenflies.outside P.carrier) :=
      isOpen_interior.inter_closure ⟨hxint, hxclosureExterior⟩
    obtain ⟨y, hyint, hyexterior⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
    exact Set.disjoint_left.mp P.disjoint_closedRegion_exteriorRegion
      (interior_subset hyint) hyexterior

private theorem interior_closedRegion :
    interior (closure (Schoenflies.inside P.carrier)) = Schoenflies.inside P.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    have hpClosed : p ∈ (closure (Schoenflies.inside P.carrier)) := interior_subset hp
    rw [P.closure_inside_eq_union] at hpClosed
    rcases hpClosed with hpInside | hpCarrier
    · exact hpInside
    · have hpFrontier : p ∈ frontier (closure (Schoenflies.inside P.carrier)) := by
        rw [P.frontier_closedRegion]
        exact hpCarrier
      exact (Set.disjoint_left.mp disjoint_interior_frontier hp hpFrontier).elim
  · exact interior_maximal (by rw [P.closure_inside_eq_union]; exact Set.subset_union_left)
      P.isSeparating_carrier.isOpen_inside

private theorem isConnected_closedRegion :
    IsConnected (closure (Schoenflies.inside P.carrier)) :=
  P.isSeparating_carrier.isConnected_inside.closure

theorem exists_triangle_mesh_inside :
    ∃ M : TriangleMesh,
      M.toPlaneComplex.support = closure (Schoenflies.inside P.carrier) ∧
        frontier M.toPlaneComplex.support = P.carrier := by
  refine ⟨P.closedRegionMesh, P.closedRegionMesh_support, ?_⟩
  rw [P.closedRegionMesh_support]
  exact P.frontier_closedRegion

theorem exists_simplicial_complex_inside :
    ∃ K : Geometry.SimplicialComplex ℝ Plane,
      K.faces.Finite ∧ K.space = closure (Schoenflies.inside P.carrier) ∧
        ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  refine ⟨planeComplexToSimplicialComplex P.closedRegionMesh.toPlaneComplex,
    planeComplexToSimplicialComplex_faces_finite _, ?_,
    planeComplexToSimplicialComplex_pure _ P.closedRegionMesh.toPlaneComplex_isPure2⟩
  exact (planeComplexToSimplicialComplex_space _).trans P.closedRegionMesh_support

end Schoenflies.PrePolygon
