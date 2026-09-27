/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphFaceArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutIntersections
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.nontrivial
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {n : ℕ} {S B : Set M} (hS : IsPLCellOn (n + 1) S B) : S.Nontrivial := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hS
  exact (IsPLBall.nontrivial ⟨r, hr⟩).image_of_injOn hu.injOn

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

private theorem subsingleton_split_inter_triangle
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦') :
    (section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' s.1).Subsingleton := by
  by_cases hes : Section34Incident e.1 s.1
  · obtain ⟨p, hp⟩ := exists_singleton_section34GraphSplitCell_inter_residualTriangle
      hsub hmap s e hes
    rw [hp]
    exact subsingleton_singleton
  · rw [inter_comm, section34GraphResidualCell_inter_split_eq_empty_of_not_incident
      hsub hmap s.2.1 e hes]
    exact subsingleton_empty

private theorem subsingleton_split_inter_distinct_tetrahedra
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦') (hst : s ≠ t) :
    (section34GraphSplitCell 𝒦 𝒦' e ∩
      (section34GraphResidualCell 𝒦 𝒦' s.1 ∩
        section34GraphResidualCell 𝒦 𝒦' t.1)).Subsingleton := by
  classical
  rw [section34GraphResidualCell_inter hsub hmap s.2.1 t.2.1]
  have hne : s.1 ∩ t.1 ≠ s.1 := by
    intro h
    have hst' : s.1 ⊆ t.1 := h ▸ (Finset.inter_subset_right : s.1 ∩ t.1 ⊆ t.1)
    exact hst (Subtype.ext (Finset.eq_of_subset_of_card_le hst' (by rw [s.2.2, t.2.2])))
  have hcard : (s.1 ∩ t.1).card ≤ 3 := by
    have := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩)
    have := s.2.2
    omega
  rcases (s.1 ∩ t.1).eq_empty_or_nonempty with hem | hnon
  · simp only [hem, section34GraphResidualCell, simplexBody, Finset.coe_empty,
      convexHull_empty, image_empty, empty_sdiff, closure_empty, inter_empty]
    exact subsingleton_empty
  · have hi := 𝒦.complex.down_closed s.2.1 Finset.inter_subset_left hnon
    by_cases hc : (s.1 ∩ t.1).card = 3
    · exact subsingleton_split_inter_triangle hsub hmap ⟨s.1 ∩ t.1, hi, hc⟩ e
    · rw [section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap hi (by omega),
        inter_empty]
      exact subsingleton_empty

theorem section34GraphCutFamily_subset_strict_on_arcs
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map) :
    let src := section34GraphCutFamily 𝒦 𝒦'
    (∀ a l, src (.faceArc a) ⊆ src l →
      (.faceArc a : Section34CutLabelOf 𝒦 𝒦') = l ∨ 1 < section34Dim l) ∧
    ∀ i l, src (.edgeArc i) ⊆ src l →
      (.edgeArc i : Section34CutLabelOf 𝒦 𝒦') = l ∨ 1 < section34Dim l := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  let E := section34GraphSplitCell 𝒦 𝒦'
  let R := section34GraphResidualCell 𝒦 𝒦'
  let A := fun a : Section34ArcIndex 𝒦 𝒦' => C a.1.2 ∩ R a.1.1.1
  let I := fun i : Section34EdgeArcIndex 𝒦 𝒦' => R i.1.1.1 ∩ E i.1.2
  have hA : ∀ a, (A a).Nontrivial := by
    intro a
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphVertexCell_inter_residualTriangle
      hsub hmap a.1.1 a.1.2 a.2
    exact hB.nontrivial
  have hI : ∀ i, (I i).Nontrivial := by
    intro i
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphSplitCell_inter_residualTetrahedron
      hsub hmap i.1.1 i.1.2 i.2
    simpa only [I, R, E, inter_comm] using hB.nontrivial
  have hAE : ∀ a e, ¬ A a ⊆ E e := by
    intro a e h
    exact (hA a).not_subsingleton ((subsingleton_split_inter_triangle hsub hmap a.1.1 e).anti
      (subset_inter h inter_subset_right))
  have hIR : ∀ i (s : Section34SimplexIndex 𝒦 3), ¬ I i ⊆ R s.1 := by
    intro i s h
    exact (hI i).not_subsingleton ((subsingleton_split_inter_triangle hsub hmap s i.1.2).anti
      (subset_inter inter_subset_right h))
  have hAA : ∀ a b, A a ⊆ A b → a = b := by
    intro a b h
    obtain ⟨x, hx⟩ := (hA a).nonempty
    have hs : a.1.1 = b.1.1 := by
      by_contra hs
      exact disjoint_left.mp (pairwiseDisjoint_section34GraphResidualTriangle hsub hmap hs)
        hx.2 (h hx).2
    have hw : a.1.2 = b.1.2 := by
      by_contra hw
      obtain ⟨e, -, he⟩ := exists_section34GraphSplitCell_of_vertex_inter_nonempty
        hsub hmap a.1.2 b.1.2 hw ⟨x, hx.1, (h hx).1⟩
      exact hAE a e (fun y hy => he.symm.subset ⟨hy.1, (h hy).1⟩)
    exact Subtype.ext (Prod.ext hs hw)
  have hII : ∀ i j, I i ⊆ I j → i = j := by
    intro i j h
    obtain ⟨x, hx⟩ := (hI i).nonempty
    have he : i.1.2 = j.1.2 := by
      by_contra he
      exact disjoint_left.mp (pairwise_disjoint_section34GraphSplitCell 𝒦 𝒦' he)
        hx.2 (h hx).2
    have ht : i.1.1 = j.1.1 := by
      by_contra ht
      exact (hI i).not_subsingleton
        ((subsingleton_split_inter_distinct_tetrahedra hsub hmap i.1.1 j.1.1 i.1.2 ht).anti
          (fun y hy => ⟨hy.2, hy.1, (h hy).1⟩))
    exact Subtype.ext (Prod.ext ht he)
  constructor
  · intro a l h
    cases l with
    | faceArc b => exact Or.inl (congrArg Section34Label.faceArc (hAA a b h))
    | edgeArc i => exact (hAE a i.1.2 (h.trans inter_subset_right)).elim
    | markedPoint p => exact (hAE a p.1.2 (h.trans inter_subset_left)).elim
    | _ => exact Or.inr (by simp only [section34Dim]; omega)
  · intro i l h
    cases l with
    | faceArc a => exact (hIR i a.1.1 (h.trans inter_subset_right)).elim
    | edgeArc j => exact Or.inl (congrArg Section34Label.edgeArc (hII i j h))
    | markedPoint p => exact (hIR i p.1.1 (h.trans inter_subset_right)).elim
    | _ => exact Or.inr (by simp only [section34Dim]; omega)

end DifferentialGeometry.Topology.PiecewiseLinear
