/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Selected and regrouped for this project; see ../MODIFICATIONS.md.
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.OneEdgeAttachment

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise
namespace TriangleMesh

variable (M : TriangleMesh)

/-- Moise's second free-triangle case: the frontier meets the triangle in exactly the two edges
through the apex. -/
def IsTwoEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)

/-- The `IsGeometricallyFreeTriangle` declaration. -/
def IsGeometricallyFreeTriangle (T : M.Triangle) : Prop :=
  ∃ k : Fin 3, M.IsOneEdgeFreeTriangle T k ∨ M.IsTwoEdgeFreeTriangle T k

theorem freeTriangleBaseSegment_eq_oppositeEdgeCarrier (T : M.Triangle) (k : Fin 3) :
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
      convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
  fin_cases k
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 2))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (0 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide]
    simp [convexHull_pair, segment_symm]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 2)) =
      convexHull ℝ (((Finset.univ.erase (1 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide]
    simp [convexHull_pair]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (2 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide]
    simp [convexHull_pair]

theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_one (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 1) :
    M.IsGeometricallyFreeTriangle T := by
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2.1
  refine ⟨k, Or.inl ?_⟩
  rw [IsOneEdgeFreeTriangle, M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices,
    hboundary]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [M.freeTriangleBaseSegment_eq_oppositeEdgeCarrier T k, hedge, Finset.coe_image]

/-- Moise's second free-triangle case: if exactly two edges of a triangle lie on the mesh
frontier, their common endpoint can be chosen as the apex of the Figure 3.3 move. -/
theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_two (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 2) :
    M.IsGeometricallyFreeTriangle T := by
  have hproper : M.boundaryEdges T.1 ⊂ M.triangleEdges T.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨M.boundaryEdges_subset_triangleEdges T.1, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    rw [hcard, M.card_triangleEdges T.2] at this
    omega
  obtain ⟨e, heTriangle, heBoundary⟩ := Finset.exists_of_ssubset hproper
  have heData := Finset.mem_powersetCard.mp heTriangle
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2
  have hboundary : M.boundaryEdges T.1 = (M.triangleEdges T.1).erase e := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      exact Finset.mem_erase.mpr
        ⟨fun hde => heBoundary (hde ▸ hd), M.boundaryEdges_subset_triangleEdges T.1 hd⟩
    · rw [hcard, Finset.card_erase_of_mem heTriangle, M.card_triangleEdges T.2]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have hEdge01Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge02Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 2} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 2} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge01Edge02 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 0, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h12 h'.2) (fun h' => h02 h'.1)
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hUnion (a b : Finset M.Vertex) :
      (⋃ d ∈ ({a, b} : Finset (Finset M.Vertex)),
        convexHull ℝ (M.position '' (d : Set M.Vertex))) =
        convexHull ℝ (M.position '' (a : Set M.Vertex)) ∪
          convexHull ℝ (M.position '' (b : Set M.Vertex)) := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, Set.mem_union]
    constructor
    · rintro ⟨d, rfl | rfl, hp⟩
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨a, Or.inl rfl, hp⟩
      · exact ⟨b, Or.inr rfl, hp⟩
  refine ⟨k, Or.inr ?_⟩
  rw [IsTwoEdgeFreeTriangle,
    M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices, hboundary]
  fin_cases k
  · have he : e = {M.orderedVertex T 1, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (0 : Fin 3)) = _
      rw [show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 1, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 0, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hne rfl).elim
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge12, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12, Or.inr (Or.inl rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder, segment_symm, Equiv.swap_apply_def, Set.union_comm]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (1 : Fin 3)) = _
      rw [show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (hne rfl).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp only [freeTriangleOrder]
    simp only [Equiv.swap_apply_def]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one, zero_ne_one]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 1} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (2 : Fin 3)) = _
      rw [show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 1} =
          {{M.orderedVertex T 0, M.orderedVertex T 2},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact (hne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02.symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨hEdge01Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder]

/-- The finite conclusion used by Moise's cutting induction.  Once a weakly free triangle has
an edge-neighbor and no isolated frontier vertex, its frontier trace is one of the two
configurations in Figure 3.3. -/
theorem isGeometricallyFreeTriangle_of_isFreeTriangle
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1) :
    M.IsGeometricallyFreeTriangle T := by
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  rcases hcases with hcard | hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_one T hvertices hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two T hvertices hcard

/-- The exact diagonal configuration in the hard branch of Moise Chapter 3, Theorem 3.  If a
weakly free triangle is not one of the Figure 3.3 configurations, it has one boundary edge and
an isolated opposite boundary vertex; the other two edges are the cutting diagonals. -/
theorem exists_cutting_diagonal_configuration
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a b v : M.Vertex,
      a ≠ b ∧ v ≠ a ∧ v ≠ b ∧
      T.1 = {a, b, v} ∧ M.boundaryEdges T.1 = {{a, b}} ∧
      M.position v ∈ frontier M.toPlaneComplex.support := by
  rw [HasNoIsolatedFrontierVertex] at hnot
  push Not at hnot
  obtain ⟨v, hvFrontier, hvTriangle, hvBoundary⟩ := hnot
  have hvT : v ∈ T.1 :=
    M.vertex_mem_triangle_of_frontier_not_mem_boundaryEdges T v hvFrontier hvTriangle hvBoundary
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcardCases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  have hcard : (M.boundaryEdges T.1).card = 1 := by
    rcases hcardCases with hcard | hcard
    · exact hcard
    · exfalso
      obtain ⟨e, f, hef, hboundary⟩ := Finset.card_eq_two.mp hcard
      have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have hfMem : f ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have heData := M.mem_boundaryEdges_iff.mp heMem
      have hfData := M.mem_boundaryEdges_iff.mp hfMem
      have hvNotE : v ∉ e := by
        intro hve
        exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
      have hvNotF : v ∉ f := by
        intro hvf
        exact hvBoundary f hfMem (subset_convexHull ℝ _ ⟨v, hvf, rfl⟩)
      have heraseCard : (T.1.erase v).card = 2 := by
        rw [Finset.card_erase_of_mem hvT, M.card_triangle T.1 T.2]
      have heErase : e = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotE (hwv ▸ hw), heData.1 hw⟩)
          (by rw [heData.2.1, heraseCard])
      have hfErase : f = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotF (hwv ▸ hw), hfData.1 hw⟩)
          (by rw [hfData.2.1, heraseCard])
      exact hef (heErase.trans hfErase.symm)
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  have hvNotE : v ∉ e := by
    intro hve
    exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp heData.2.1
  have hva : v ≠ a := fun h => hvNotE (h ▸ by simp)
  have hvb : v ≠ b := fun h => hvNotE (h ▸ by simp)
  have htriangle : T.1 = {a, b, v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact heData.1 (by simp)
      · exact heData.1 (by simp)
      · exact hvT
    · rw [M.card_triangle T.1 T.2]
      have hcardTriple : ({a, b, v} : Finset M.Vertex).card = 3 := by
        simp [hab, Ne.symm hva, Ne.symm hvb]
      omega
  exact ⟨a, b, v, hab, hva, hvb, htriangle, hboundary, hvFrontier⟩

-- Normalizing all six finite-order cases for the three geometric edges exceeds the default.
/-- The frontier of a maximal triangle is covered by the base and the two apex edges in every
Figure 3.3 ordering. -/
theorem frontier_triangleCarrier_subset_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    frontier (M.triangleCarrier T.1) ⊆
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  intro p hp
  obtain ⟨e, hecard, heT, hpe⟩ := M.exists_edge_of_mem_frontier_triangle T.2 hp
  have he : e ∈ M.triangleEdges T.1 :=
    Finset.mem_powersetCard.mpr ⟨heT, hecard⟩
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext q; simp [eq_comm]]
    exact convexHull_pair _ _
  rw [M.triangleEdges_eq_orderedEdges T] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  have hpEdges : p ∈
      segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
        (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
          segment ℝ (M.position (M.orderedVertex T 1))
            (M.position (M.orderedVertex T 2))) := by
    rcases he with rfl | rfl | rfl
    · rw [hcarrier] at hpe
      exact Or.inl hpe
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inl hpe)
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inr hpe)
  have horder :
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
          (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) =
        segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
          (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
            segment ℝ (M.position (M.orderedVertex T 1))
              (M.position (M.orderedVertex T 2))) := by
    ext x
    simp only [Set.mem_union]
    have hsymm (a b : Plane) : x ∈ segment ℝ a b ↔ x ∈ segment ℝ b a := by
      rw [segment_symm]
    have h01 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))
    have h02 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 2))
    have h12 := hsymm (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))
    fin_cases k
    · simp only [freeTriangleOrder, Fin.isValue, Fin.zero_eta, Equiv.swap_apply_right,
        Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h12.mpr h))
        · exact Or.inr (Or.inl (h02.mpr h))
        · exact Or.inl (h01.mpr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h01.mp h))
        · exact Or.inr (Or.inl (h02.mp h))
        · exact Or.inl (h12.mp h)
    · simp only [freeTriangleOrder, Fin.isValue, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
        ↓reduceIte, zero_ne_one]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mpr h))
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mp h))
    · simp [freeTriangleOrder]
  rwa [horder]

end TriangleMesh
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
