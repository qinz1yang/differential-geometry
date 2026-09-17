import DifferentialGeometry.Topology.Manifold.AmbientCornerRounding
import DifferentialGeometry.Topology.Manifold.SectorRoundingFrontier
import DifferentialGeometry.Topology.SphereSeparation.ReconstructionRegions

open Set Metric

namespace DifferentialGeometry.Topology.SphereSeparation.SphereSides

theorem closure_compactSide_smoothAbsQuadrantSet
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    {S T : Set X} (d : SphereSides S) (d' : SphereSides T)
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ closure d.compactSide ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target)
    (hT : T = (S \ e.source) ∪ e.symm '' (e.target ∩
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2})) :
    closure d'.compactSide = e.smoothAbsQuadrantSet (closure d.compactSide) ε := by
  let C := e.smoothAbsQuadrantSet (closure d.compactSide) ε
  have hC : IsCompact C :=
    e.isCompact_smoothAbsQuadrantSet hε hraw hstrip d.isCompact_closure_compactSide
  have hreg : closure (interior C) = C :=
    e.closure_interior_smoothAbsQuadrantSet hε hraw hstrip
      (by rw [d.interior_closure_compactSide])
  have hfrontA : frontier (closure d.compactSide) = S := by
    rw [frontier, closure_closure, d.interior_closure_compactSide,
      ← d.isOpen_compactSide.frontier_eq, d.frontier_compactSide]
  have hfront : frontier C = T := by
    rw [e.frontier_smoothAbsQuadrantSet hε hraw hstrip, hfrontA, hT]
  have hne : C.Nonempty := by
    obtain ⟨H, _, _⟩ := e.exists_homeomorph_smoothAbs_quadrant
      d.isCompact_closure_compactSide hε hraw hstrip
    obtain ⟨x, hx⟩ := d.compactSide_nonempty
    exact ⟨(H ⟨x, subset_closure hx⟩).val, (H ⟨x, subset_closure hx⟩).property⟩
  have hne' : (interior C).Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    rw [hz, closure_empty] at hreg
    exact hne.ne_empty hreg.symm
  have hi : interior C = d'.compactSide := by
    apply d'.eq_compactSide_of_frontier_subset isOpen_interior hne'
      (by rwa [hreg])
    · rw [← hfront]
      exact disjoint_interior_frontier
    · rw [← hfront]
      exact frontier_interior_subset
  rw [← hi, hreg]

theorem closure_compactSide_smoothAbs_reflex
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    {S T : Set X} (d : SphereSides S) (d' : SphereSides T)
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ closure d.compactSide ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0)
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target)
    (hT : T = (S \ e.source) ∪ e.symm '' (e.target ∩
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2})) :
    closure d'.compactSide = (closure d.compactSide \ e.source) ∪ e.symm ''
      (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)}) := by
  have himg : e.symm.IsImage {p : P × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0}
      (closure d.compactSide) := fun p hp => hraw p hp
  have hext := himg.interior.compl
  rw [d.interior_closure_compactSide, ← closure_compl] at hext
  have hmodel : {p : P × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0}ᶜ =
      univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by ext p; simp
  rw [hmodel, closure_prod_eq, closure_prod_eq, closure_univ, closure_Ioi] at hext
  have hquad : ∀ p ∈ e.target, e.symm p ∈ d.compactSideᶜ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
    intro p hp
    simpa only [mem_prod, mem_univ, true_and, mem_Ici, Prod.le_def] using hext hp
  obtain ⟨H, _, _, _, _, _, _, hHquad, hHreflex⟩ := e.exists_homeomorph_smoothAbs_corner hε hstrip
  have hsmall : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ e.target := by
    intro p hp
    apply hstrip
    refine ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hp.1, abs_of_nonneg hp.2.1, max_le_iff]
    constructor <;> linarith [hp.1, hp.2.1, hp.2.2]
  have hfront : frontier (H '' closure d.compactSide) = T := by
    have hfrontB : frontier (closure d.compactSide) = S := by
      rw [frontier, closure_closure, d.interior_closure_compactSide,
        ← d.isOpen_compactSide.frontier_eq, d.frontier_compactSide]
    have hfrontA : frontier d.compactSideᶜ = S := by rw [frontier_compl, d.frontier_compactSide]
    rw [← H.image_frontier, hfrontB, ← hfrontA, H.image_frontier, hHquad _ hquad,
      e.frontier_smoothAbsQuadrantSet hε hquad hsmall, hfrontA, ← hT]
  have hreg : closure (interior (H '' closure d.compactSide)) = H '' closure d.compactSide := by
    rw [← H.image_interior, ← H.image_closure, d.interior_closure_compactSide]
  have hi : interior (H '' closure d.compactSide) = d'.compactSide := by
    apply d'.eq_compactSide_of_frontier_subset isOpen_interior
    · rw [← H.image_interior, d.interior_closure_compactSide]
      exact d.compactSide_nonempty.image H
    · rw [hreg]
      exact d.isCompact_closure_compactSide.image H.continuous
    · rw [← hfront]
      exact disjoint_interior_frontier
    · rw [← hfront]
      exact frontier_interior_subset
  rw [← hi, hreg, hHreflex _ hraw]


end DifferentialGeometry.Topology.SphereSeparation.SphereSides
