/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicCellMarkedPrism
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedPrismChain
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCylinderUntwisting

open Set Fin.NatCast

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_cylindricalDiagram_derivedNeighborhood_circle_marked
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space)
    (hinterior : ∀ s ∈ L.faces, s ∉ (boundaryComplex 3 K).faces)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P) :
    ∃ φ : EuclideanSpace ℝ (Fin 2) × ℝ → E,
      IsCylindricalDiagram φ P (derivedNeighborhood K L).space ∧
      φ (a, 0) = φ (a, 1) ∧ φ '' ({a} ×ˢ Icc (0 : ℝ) 1) = L.space := by
  obtain ⟨n, hn, e, he⟩ := exists_cyclic_face_order L hL hconn
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = m + 3 := by omega
  clear hm
  subst n
  let C : ℕ → Set E := fun k => (derivedNeighborhoodCell K (e (↑k : Fin (m + 3))).val).space
  let D : ℕ → Set E := fun k => C k ∩
    (derivedNeighborhoodCell K (e ((↑k : Fin (m + 3)) - 1)).val).space
  let z : ℕ → E := fun k => dualFaceCrossing (e (↑k : Fin (m + 3))).val
    (e ((↑k : Fin (m + 3)) - 1)).val
  have hcast (k : ℕ) (hk : k < m + 3) : (↑k : Fin (m + 3)).val = k :=
    Nat.mod_eq_of_lt hk
  have hprev (i : Fin (m + 3)) : (SimpleGraph.cycleGraph (m + 3)).Adj i (i - 1) := by
    change i - 1 ∈ (SimpleGraph.cycleGraph (m + 3)).neighborSet i
    rw [SimpleGraph.cycleGraph_neighborSet]
    exact mem_insert _ _
  obtain ⟨g, hg, hga⟩ := exists_isPLHomeomorphOn_cellInterface_marked K hK
    (hLK (e 0).property) (hLK (e (0 - 1)).property) (hinterior _ (e 0).property)
    (fun h => ((he 0 (0 - 1)).mp (hprev 0)).1 (Subtype.ext h))
    ((he 0 (0 - 1)).mp (hprev 0)).2 hP ha
  have hproduce : ∀ k ≤ m + 2, ∀ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPLHomeomorphOn g P (D k) → g a = z k →
      ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → E,
        IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (C k) ∧
        (∀ x ∈ P, G (x, 0) = g x) ∧ G '' (P ×ˢ ({1} : Set ℝ)) = D (k + 1) ∧
        G (a, 1) = z (k + 1) ∧ G '' ({a} ×ˢ Icc (0 : ℝ) 1) = C k ∩ L.space := by
    intro k hk g hg hga
    obtain ⟨G, hG, hG0, hG1, hGa, hGaxis⟩ :=
      exists_isPLHomeomorphOn_circleCell_prism_marked K L hK hLK hL e he hinterior
        hP ha (↑k : Fin (m + 3)) hg hga
    refine ⟨G, hG, hG0, ?_, ?_, hGaxis⟩
    · simpa only [D, C, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, inter_comm] using hG1
    · simpa only [z, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        dualFaceCrossing_comm] using hGa
  have hfar : ∀ i k, i + 1 < k → k ≤ m + 1 → Disjoint (C i) (C k) := by
    intro i k hik hk
    apply disjoint_left.mpr
    intro x hxi hxk
    have hne : (↑i : Fin (m + 3)) ≠ (↑k : Fin (m + 3)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [hcast i (by omega), hcast k (by omega)] at hv
      omega
    have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
      (hLK (e (↑i : Fin (m + 3))).property) (hLK (e (↑k : Fin (m + 3))).property)
      ⟨x, hxi, hxk⟩
    have hadj := (he (↑i : Fin (m + 3)) (↑k : Fin (m + 3))).mpr ⟨e.injective.ne hne, hcomp⟩
    have hlt : (↑i : Fin (m + 3)) < (↑k : Fin (m + 3)) := by
      change (↑i : Fin (m + 3)).val < (↑k : Fin (m + 3)).val
      rw [hcast i (by omega), hcast k (by omega)]
      omega
    rw [SimpleGraph.cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hlt,
      Fin.sub_val_of_le hlt.le, hcast i (by omega), hcast k (by omega)] at hadj
    omega
  have hfinal : (⋃ k ≤ m + 1, C k) ∩ C (m + 2) = D 0 ∪ D (m + 2) := by
    have hzero : (0 : Fin (m + 3)) - 1 = ↑(m + 2) := by
      apply Fin.ext
      simp only [Fin.val_sub, Fin.val_zero, Fin.val_one, Fin.val_natCast]
      congr 1
    have hlast : (↑(m + 2) : Fin (m + 3)) - 1 = ↑(m + 1) := by
      apply Fin.ext
      rw [Fin.sub_val_of_le]
      · rw [hcast (m + 2) (by omega), hcast (m + 1) (by omega)]
        simp
      · change (1 : Fin (m + 3)).val ≤ _
        rw [Fin.val_one, hcast (m + 2) (by omega)]
        omega
    have hD0 : D 0 = C 0 ∩ C (m + 2) := by simp only [D, C, Nat.cast_zero, hzero]
    have hDlast : D (m + 2) = C (m + 2) ∩ C (m + 1) := by
      change C (m + 2) ∩ (derivedNeighborhoodCell K (e (↑(m + 2) - 1)).val).space = _
      rw [hlast]
    rw [hD0, hDlast]
    apply Subset.antisymm
    · rintro x ⟨hx, hlastx⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hlt : (↑i : Fin (m + 3)) < (↑(m + 2) : Fin (m + 3)) := by
        change (↑i : Fin (m + 3)).val < (↑(m + 2) : Fin (m + 3)).val
        rw [hcast i (by omega), hcast (m + 2) (by omega)]
        omega
      have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
        (hLK (e (↑i : Fin (m + 3))).property)
        (hLK (e (↑(m + 2) : Fin (m + 3))).property) ⟨x, hxi, hlastx⟩
      have hadj := (he (↑i : Fin (m + 3)) (↑(m + 2) : Fin (m + 3))).mpr
        ⟨e.injective.ne (ne_of_lt hlt), hcomp⟩
      rw [SimpleGraph.cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hlt,
        Fin.sub_val_of_le hlt.le, hcast i (by omega), hcast (m + 2) (by omega)] at hadj
      have hiend : i = 0 ∨ i = m + 1 := by omega
      rcases hiend with rfl | rfl
      · exact Or.inl ⟨hxi, hlastx⟩
      · exact Or.inr ⟨hlastx, hxi⟩
    · rintro x (hx | hx)
      · exact ⟨mem_iUnion₂.mpr ⟨0, Nat.zero_le _, hx.1⟩, hx.2⟩
      · exact ⟨mem_iUnion₂.mpr ⟨m + 1, le_rfl, hx.2⟩, hx.1⟩
  have hclose : (↑(m + 3) : Fin (m + 3)) = 0 := by ext; simp
  obtain ⟨φ, hφ, hclosed, haxis⟩ := exists_cylindricalDiagram_of_prism_cycle_marked
    hP.isPolyhedron (interior_subset ha) (show IsPLHomeomorphOn g P (D 0) from hg) hga
    (m + 1) hproduce
    (fun k _ => by
      simp only [D, C, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, inter_comm])
    hfar hfinal
    (by simp only [D, C, show m + 1 + 2 = m + 3 by omega, hclose, Nat.cast_zero])
    (by simp only [z, show m + 1 + 2 = m + 3 by omega, hclose, Nat.cast_zero])
  have hcover : (⋃ k ≤ m + 2, C k) = (derivedNeighborhood K L).space := by
    rw [← iUnion_derivedNeighborhoodCell_space K L hLK]
    ext x
    constructor
    · intro hx
      obtain ⟨k, _, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨(e (↑k : Fin (m + 3))).val, (e _).property, hx⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, hi⟩ := e.surjective ⟨s, hs⟩
      refine mem_iUnion₂.mpr ⟨i.val, by omega, ?_⟩
      simpa only [C, Fin.cast_val_eq_self, hi] using hxs
  refine ⟨φ, hcover ▸ hφ, hclosed, ?_⟩
  rw [haxis, ← iUnion₂_inter, hcover,
    inter_eq_right.mpr (subcomplex_space_subset_derivedNeighborhood hLK)]

open Classical in
theorem exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends_marked
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space)
    (hinterior : ∀ s ∈ L.faces, s ∉ (boundaryComplex 3 K).faces)
    (hor : IsOrientable 3 K)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P) :
    ∃ φ : EuclideanSpace ℝ (Fin 2) × ℝ → E,
      IsCylindricalDiagram φ P (derivedNeighborhood K L).space ∧
      (∀ x ∈ P, φ (x, 0) = φ (x, 1)) ∧ φ '' ({a} ×ˢ Icc (0 : ℝ) 1) = L.space := by
  let _ : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  obtain ⟨φ, hφ, hclosed, haxis⟩ :=
    exists_cylindricalDiagram_derivedNeighborhood_circle_marked K L hK hLK hL hconn
      hinterior hP ha
  obtain ⟨horN, -⟩ := exists_cylindricalDiagram_isOrientable_derivedNeighborhood_circle
    K L hK hLK hL hconn hor
  have hPball : IsPLBall 2 P := by simpa using hP.isPLBall ⟨a, ha⟩
  obtain ⟨g, hg, hends, hga⟩ := hφ.exists_endMap_id_preserving_axis_of_isOrientable
    hP hPball (derivedNeighborhood K L) (hK.derivedNeighborhood L) horN ha hclosed
  exact ⟨g, hg, hends, hga.trans haxis⟩

end DifferentialGeometry.Topology.PiecewiseLinear
