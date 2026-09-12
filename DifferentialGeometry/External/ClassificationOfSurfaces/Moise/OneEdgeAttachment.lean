/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Selected and regrouped for this project; see ../MODIFICATIONS.md.
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.FreeTriangle

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Order a triangle so that index `2` is a specified opposite vertex. -/
noncomputable def freeTriangleOrder (T : M.Triangle) (k : Fin 3) : Fin 3 → Plane :=
  fun i => M.position (M.orderedVertex T ((Equiv.swap 2 k) i))

theorem freeTriangleOrder_affineIndependent (T : M.Triangle) (k : Fin 3) :
    AffineIndependent ℝ (M.freeTriangleOrder T k) := by
  exact (M.orderedVertex_affineIndependent T).comp_embedding (Equiv.swap 2 k).toEmbedding

theorem triangle_eq_orderedVertices (T : M.Triangle) :
    T.1 = {M.orderedVertex T 0, M.orderedVertex T 1, M.orderedVertex T 2} := by
  ext v
  constructor
  · intro hv
    have hvRange : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact hv
    obtain ⟨i, rfl⟩ := hvRange
    fin_cases i <;> simp
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact M.orderedVertex_mem T 0
    · exact M.orderedVertex_mem T 1
    · exact M.orderedVertex_mem T 2

theorem triangleEdges_eq_orderedEdges (T : M.Triangle) :
    M.triangleEdges T.1 =
      {{M.orderedVertex T 0, M.orderedVertex T 1},
        {M.orderedVertex T 0, M.orderedVertex T 2},
        {M.orderedVertex T 1, M.orderedVertex T 2}} := by
  rw [triangleEdges, M.triangle_eq_orderedVertices T]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  ext e
  rw [Finset.mem_powersetCard]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hesub, hecard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
    have ha := hesub (by simp : a ∈ ({a, b} : Finset M.Vertex))
    have hb := hesub (by simp : b ∈ ({a, b} : Finset M.Vertex))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
  · intro he
    rcases he with rfl | rfl | rfl
    all_goals
      constructor
      · simp
      · simp_all

/-- Moise's first free-triangle case: the frontier meets the triangle in exactly its base edge. -/
def IsOneEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1)

/-- The relative interior of the base in the Figure 3.3 ordering misses both apex edges. -/
theorem freeTriangleBase_diff_endpoints_disjoint_apexEdges (T : M.Triangle) (k : Fin 3) :
    Disjoint
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) \
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1})
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  have habc : AffineIndependent ℝ ![a, b, c] := by
    convert M.freeTriangleOrder_affineIndependent T k using 1
    funext i
    fin_cases i <;> rfl
  have hbac : AffineIndependent ℝ ![b, a, c] := by
    convert habc.comp_embedding (Equiv.swap (0 : Fin 3) 1).toEmbedding using 1
    funext i
    fin_cases i <;> rfl
  have h0 : segment ℝ a b ∩ segment ℝ a c = {a} := by
    simpa only [segment_symm ℝ b a] using
      (segment_inter_segment_of_affineIndependent (x := b) (y := a) (z := c) hbac)
  have h1 : segment ℝ a b ∩ segment ℝ b c = {b} :=
    segment_inter_segment_of_affineIndependent (x := a) (y := b) (z := c) habc
  rw [Set.disjoint_left]
  change ∀ ⦃x⦄, x ∈ segment ℝ a b \ {a, b} →
    x ∈ segment ℝ a c ∪ segment ℝ b c → False
  rintro x ⟨hxBase, hxEnds⟩ (hxApex0 | hxApex1)
  · have hx : x ∈ ({a} : Set Plane) := by
      rw [← h0]
      exact ⟨hxBase, hxApex0⟩
    exact hxEnds (Or.inl (Set.mem_singleton_iff.mp hx))
  · have hx : x ∈ ({b} : Set Plane) := by
      rw [← h1]
      exact ⟨hxBase, hxApex1⟩
    exact hxEnds (Or.inr (Set.mem_singleton_iff.mp hx))

/-- The abstract mesh edge underlying the base in the Figure 3.3 ordering. -/
noncomputable def freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  (Finset.univ.erase k).image (M.orderedVertex T)

/-- The first abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge0 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 0),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

/-- The second abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge1 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 1),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

theorem freeTriangleBaseEdge_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleBaseEdge T k).card = 2 := by
  rw [freeTriangleBaseEdge, Finset.card_image_of_injective _ (M.orderedVertex_injective T),
    Finset.card_erase_of_mem (Finset.mem_univ k)]
  decide

theorem freeTriangleBaseEdge_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ⊆ T.1 := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact M.orderedVertex_mem T i

theorem freeTriangleBaseEdge_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleBaseEdge_subset T k, M.freeTriangleBaseEdge_card T k⟩⟩

theorem freeTriangleApexEdge0_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge0 T k).card = 2 := by
  rw [freeTriangleApexEdge0, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge1_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge1 T k).card = 2 := by
  rw [freeTriangleApexEdge1, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge0_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge0 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge0, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem freeTriangleApexEdge1_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge1 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem image_freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) :
    M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex) =
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  rw [Finset.image_insert, Finset.image_singleton]
  ext p
  simp [freeTriangleOrder, eq_comm]

theorem freeTriangleBaseEdge_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  rw [M.image_freeTriangleBaseEdge T k, convexHull_pair]

theorem freeTriangleApexEdge0_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge0, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem freeTriangleApexEdge1_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 1, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge1, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem triangleEdges_eq_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    M.triangleEdges T.1 =
      {M.freeTriangleBaseEdge T k, M.freeTriangleApexEdge0 T k,
        M.freeTriangleApexEdge1 T k} := by
  rw [M.triangleEdges_eq_orderedEdges T]
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  fin_cases k
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.zero_eta, Equiv.swap_apply_right,
      Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero,
      Finset.image_insert, Finset.image_singleton, freeTriangleApexEdge0,
      freeTriangleApexEdge1]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
      ↓reduceIte, zero_ne_one, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]
    have h10 : ({M.orderedVertex T 1, M.orderedVertex T 0} : Finset M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 1} := Finset.pair_comm _ _
    rw [h10]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.reduceFinMk, Equiv.swap_self,
      Equiv.refl_apply, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]

/-- Every triangle vertex lies on one of the two apex edges. -/
theorem triangleVertex_mem_freeTriangleApexEdges (T : M.Triangle) (k : Fin 3)
    {v : M.Vertex} (hv : v ∈ T.1) :
    M.position v ∈
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  have hvRange : v ∈ Set.range (M.orderedVertex T) := by
    rw [M.range_orderedVertex T]
    exact hv
  obtain ⟨i, rfl⟩ := hvRange
  fin_cases k <;> fin_cases i <;>
    simp [freeTriangleOrder, Equiv.swap_apply_def, left_mem_segment,
      right_mem_segment]

end TriangleMesh

/-- In the one-edge Figure 3.3 case, the base is exactly an incidence-one mesh edge. -/
theorem TriangleMesh.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    M.IsBoundaryEdge (M.freeTriangleBaseEdge T k) := by
  let e := M.freeTriangleBaseEdge T k
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleBaseEdge_card T k)
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := by
    rwa [← M.freeTriangleBaseEdge_carrier T k]
  have hpTrace : p ∈ frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 := by
    rw [hfree]
    exact hpBase
  obtain ⟨d, hdBoundary, hpd⟩ :=
    (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hpv).mp hpTrace.1
  have hed : e = d := M.edge_eq_of_nonvertex_mem_edgeCarriers
    (M.freeTriangleBaseEdge_mem_edges T k) hdBoundary.1 hpEdge hpd hpv
  change M.IsBoundaryEdge e
  rw [hed]
  exact hdBoundary

private theorem TriangleMesh.not_isBoundaryEdge_freeTriangleApexEdge0_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    ¬M.IsBoundaryEdge (M.freeTriangleApexEdge0 T k) := by
  intro hedgeBoundary
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleApexEdge0_card T k)
  have hpApex : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 2) := by
    rwa [← M.freeTriangleApexEdge0_carrier T k]
  have hpFrontier := M.mem_frontier_of_mem_boundaryEdge hedgeBoundary hpEdge hpv
  have hpTriangle : p ∈ M.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono (M.freeTriangleApexEdge0_subset T k)) hpEdge
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := hfree ▸ ⟨hpFrontier, hpTriangle⟩
  have hpEnds : p ∉ ({M.freeTriangleOrder T k 0,
      M.freeTriangleOrder T k 1} : Set Plane) := by
    rintro (hp0 | hp1)
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 0)) hp0
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 1)) hp1
  exact Set.disjoint_left.mp
    (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k)
    ⟨hpBase, hpEnds⟩ (Or.inl hpApex)

private theorem TriangleMesh.not_isBoundaryEdge_freeTriangleApexEdge1_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    ¬M.IsBoundaryEdge (M.freeTriangleApexEdge1 T k) := by
  intro hedgeBoundary
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier
    (M.freeTriangleApexEdge1_card T k)
  have hpApex : p ∈ segment ℝ (M.freeTriangleOrder T k 1)
      (M.freeTriangleOrder T k 2) := by
    rwa [← M.freeTriangleApexEdge1_carrier T k]
  have hpFrontier := M.mem_frontier_of_mem_boundaryEdge hedgeBoundary hpEdge hpv
  have hpTriangle : p ∈ M.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono (M.freeTriangleApexEdge1_subset T k)) hpEdge
  have hpBase : p ∈ segment ℝ (M.freeTriangleOrder T k 0)
      (M.freeTriangleOrder T k 1) := hfree ▸ ⟨hpFrontier, hpTriangle⟩
  have hpEnds : p ∉ ({M.freeTriangleOrder T k 0,
      M.freeTriangleOrder T k 1} : Set Plane) := by
    rintro (hp0 | hp1)
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 0)) hp0
    · exact hpv (M.orderedVertex T ((Equiv.swap 2 k) 1)) hp1
  exact Set.disjoint_left.mp
    (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k)
    ⟨hpBase, hpEnds⟩ (Or.inr hpApex)

/-- A non-boundary edge of `T` is carried by the support remaining after `T` is deleted. -/
theorem TriangleMesh.edgeCarrier_subset_eraseTriangle_support_of_not_boundary
    (M : TriangleMesh) (T : M.Triangle) {e : Finset M.Vertex}
    (hecard : e.card = 2) (heT : e ⊆ T.1) (heNotBoundary : ¬M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.eraseTriangle T.1).toPlaneComplex.support := by
  have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
    T.2 hecard heT heNotBoundary
  have hTmem : T.1 ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
  have hother : ∃ u ∈ M.incidentTriangles e, u ≠ T.1 := by
    by_contra h
    push Not at h
    have hsingle : M.incidentTriangles e = {T.1} := by
      ext u
      constructor
      · exact fun hu => Finset.mem_singleton.mpr (h u hu)
      · intro hu
        rw [Finset.mem_singleton.mp hu]
        exact hTmem
    rw [hsingle] at hcard
    simp at hcard
  obtain ⟨u, hu, huT⟩ := hother
  have huData := M.mem_incidentTriangles_iff.mp hu
  rw [TriangleMesh.toPlaneComplex_support]
  exact Set.subset_iUnion_of_subset u <| Set.subset_iUnion_of_subset
    (Finset.mem_erase.mpr ⟨huT, huData.1⟩)
      (convexHull_mono (Set.image_mono huData.2))

/-- In the one-edge case, the surviving support attaches to the deleted triangle exactly along
the two apex edges. -/
theorem TriangleMesh.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  let e0 := M.freeTriangleApexEdge0 T k
  let e1 := M.freeTriangleApexEdge1 T k
  have hbaseBoundary := M.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree T k hfree
  have he0Not := M.not_isBoundaryEdge_freeTriangleApexEdge0_of_oneEdgeFree T k hfree
  have he1Not := M.not_isBoundaryEdge_freeTriangleApexEdge1_of_oneEdgeFree T k hfree
  apply Set.Subset.antisymm
  · rintro p ⟨hpErase, hpT⟩
    rw [TriangleMesh.toPlaneComplex_support] at hpErase
    simp only [TriangleMesh.eraseTriangle_triangles, Set.mem_iUnion] at hpErase
    obtain ⟨u, hu, hpU⟩ := hpErase
    have huData := Finset.mem_erase.mp hu
    let U : M.Triangle := ⟨u, huData.2⟩
    let e : Finset M.Vertex := T.1 ∩ U.1
    have hpInter : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
      rw [show e = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
      exact ⟨hpT, hpU⟩
    have heCardLe : e.card ≤ 2 := by
      have hesub : e ⊆ T.1 := by
        intro v hv
        exact Finset.inter_subset_left hv
      have hle : e.card ≤ T.1.card := Finset.card_le_card hesub
      rw [M.card_triangle T.1 T.2] at hle
      by_contra h
      have heCard : e.card = 3 := by omega
      have heT : e = T.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by rw [heCard, M.card_triangle T.1 T.2])
      have hsub : T.1 ⊆ U.1 := by
        rw [← heT]
        exact Finset.inter_subset_right
      have hTU : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsub (by
        rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
      exact huData.1 hTU.symm
    have heNonempty : e.Nonempty := by
      by_contra h
      have heEmpty := Finset.not_nonempty_iff_eq_empty.mp h
      rw [heEmpty] at hpInter
      simp at hpInter
    have heCardCases : e.card = 1 ∨ e.card = 2 := by
      have hpos := Finset.card_pos.mpr heNonempty
      omega
    rcases heCardCases with heCard | heCard
    · obtain ⟨v, heq⟩ := Finset.card_eq_one.mp heCard
      have hpv : p = M.position v := by
        rw [heq] at hpInter
        simpa using hpInter
      have hvT : v ∈ T.1 := by
        have hvE : v ∈ e := by rw [heq]; simp
        exact Finset.inter_subset_left hvE
      rw [hpv]
      exact M.triangleVertex_mem_freeTriangleApexEdges T k hvT
    · have heTriangle : e ∈ M.triangleEdges T.1 :=
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, heCard⟩
      have heNotBoundary : ¬M.IsBoundaryEdge e := by
        intro heBoundary
        have hTinc : T.1 ∈ M.incidentTriangles e :=
          M.mem_incidentTriangles_iff.mpr ⟨T.2, Finset.inter_subset_left⟩
        have hUinc : U.1 ∈ M.incidentTriangles e :=
          M.mem_incidentTriangles_iff.mpr ⟨U.2, Finset.inter_subset_right⟩
        have htwo : 1 < (M.incidentTriangles e).card :=
          Finset.one_lt_card.mpr ⟨T.1, hTinc, U.1, hUinc, huData.1.symm⟩
        rw [heBoundary.2] at htwo
        omega
      rw [M.triangleEdges_eq_freeTriangleEdges T k] at heTriangle
      simp only [Finset.mem_insert, Finset.mem_singleton] at heTriangle
      rcases heTriangle with heBase | he0 | he1
      · exact False.elim <| heNotBoundary (heBase ▸ hbaseBoundary)
      · left
        rw [← M.freeTriangleApexEdge0_carrier T k, ← he0]
        exact hpInter
      · right
        rw [← M.freeTriangleApexEdge1_carrier T k, ← he1]
        exact hpInter
  · rintro p (hp0 | hp1)
    · have hpEdge : p ∈ convexHull ℝ
          (M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex)) := by
        rwa [M.freeTriangleApexEdge0_carrier T k]
      exact ⟨M.edgeCarrier_subset_eraseTriangle_support_of_not_boundary T
          (M.freeTriangleApexEdge0_card T k)
          (M.freeTriangleApexEdge0_subset T k) he0Not hpEdge,
        convexHull_mono (Set.image_mono (M.freeTriangleApexEdge0_subset T k)) hpEdge⟩
    · have hpEdge : p ∈ convexHull ℝ
          (M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex)) := by
        rwa [M.freeTriangleApexEdge1_carrier T k]
      exact ⟨M.edgeCarrier_subset_eraseTriangle_support_of_not_boundary T
          (M.freeTriangleApexEdge1_card T k)
          (M.freeTriangleApexEdge1_subset T k) he1Not hpEdge,
        convexHull_mono (Set.image_mono (M.freeTriangleApexEdge1_subset T k)) hpEdge⟩

/-- Exact frontier update in the one-edge Figure 3.3 case. -/
theorem TriangleMesh.frontier_eraseTriangle_support_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  rw [M.frontier_eraseTriangle_support T,
    M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree]

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
