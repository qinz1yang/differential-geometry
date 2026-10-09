/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcPair
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_rectangle_map_ends
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {D₀ D₁ : Set E} (hD₀K : D₀ ⊆ (boundaryComplex 2 K).space)
    (hD₁ : IsPLBall 1 D₁) (hD₁K : D₁ ⊆ (boundaryComplex 2 K).space)
    (hdis : Disjoint D₀ D₁) {g : ℝ → E} (hg : IsPLHomeomorphOn g (Icc a b) D₀) :
    ∃ G : ℝ × ℝ → E, IsPLHomeomorphOn G (Icc a b ×ˢ Icc c d) K.space ∧
      (∀ x ∈ Icc a b, G (x, c) = g x) ∧ G '' (Icc a b ×ˢ {d}) = D₁ := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  have hP := isPLBall_Icc hab
  have hprod := isPLBall_two_prod hP (isPLBall_Icc hcd)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 2 R.space := hRspace.symm ▸ hprod
  have hboundary : (boundaryComplex 2 R).space =
      Icc a b ×ˢ {c, d} ∪ {a, b} ×ˢ Icc c d := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) R hR.isCombinatorialManifoldWithBoundary,
      hRspace, frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc hcd.le,
      frontier_Icc hab.le, isClosed_Icc.closure_eq]
  have hleft : Icc a b ×ˢ {c} ⊆ (boundaryComplex 2 R).space := by
    rw [hboundary]
    exact fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩
  have hright : Icc a b ×ˢ {d} ⊆ (boundaryComplex 2 R).space := by
    rw [hboundary]
    exact fun _ hx => Or.inl ⟨hx.1, Or.inr hx.2⟩
  have hends : Disjoint (Icc a b ×ˢ {c}) (Icc a b ×ˢ {d}) :=
    disjoint_left.mpr fun _ hx hy => hcd.ne (hx.2.symm.trans hy.2)
  have hg' := (hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const c).trans hg
  obtain ⟨G, hG, hGg, hGd⟩ := exists_isPLHomeomorphOn_map_arc_pair_of_boundaryComplex R K hR hK
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const c)) hleft
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const d)) hright
    hends hD₁ hD₁K hdis hg' hD₀K
  rw [hRspace] at hG
  exact ⟨G, hG, fun x hx => hGg ⟨hx, rfl⟩, hGd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
