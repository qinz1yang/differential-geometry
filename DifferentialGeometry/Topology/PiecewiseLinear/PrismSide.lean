/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLHomeomorphOn.image_prism_side
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 2 L.space)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces] {a b : ℝ} (hab : a < b)
    {g : E × ℝ → F} (hg : IsPLHomeomorphOn g (L.space ×ˢ Icc a b) K.space) :
    g '' ((boundaryComplex 2 L).space ×ˢ Icc a b) =
      closure ((boundaryComplex 3 K).space \
        (g '' (L.space ×ˢ {a}) ∪ g '' (L.space ×ˢ {b}))) := by
  classical
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hprod : IsPLBall 3 (L.space ×ˢ Icc a b) :=
    isPLBall_three_prod hL (isPLBall_Icc hab)
  obtain ⟨R, hfin, hspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hfin.to_subtype
  let _ : Finite (boundaryComplex 2 L).faces := (boundaryComplex_faces_finite 2 L).to_subtype
  have hR : IsPLBall 3 R.space := hspace.symm ▸ hprod
  have hmap : IsPLHomeomorphOn g R.space K.space := hspace.symm ▸ hg
  have hboundary := boundaryComplex_space_prism L hL hab R hspace
  have htarget : (boundaryComplex 3 R).space \ (L.space ×ˢ {a} ∪ L.space ×ˢ {b}) =
      (boundaryComplex 2 L).space ×ˢ Ioo a b := by
    rw [hboundary]
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨hz, hzend⟩
      rcases hz with ⟨hxL, ht⟩ | ⟨hxJ, ht⟩
      · rcases ht with rfl | rfl
        · exact (hzend (Or.inl ⟨hxL, rfl⟩)).elim
        · exact (hzend (Or.inr ⟨hxL, rfl⟩)).elim
      · have hxL : x ∈ L.space := boundaryComplex_space_subset 2 L hxJ
        have hta : t ≠ a := fun h => hzend (Or.inl ⟨hxL, h⟩)
        have htb : t ≠ b := fun h => hzend (Or.inr ⟨hxL, h⟩)
        exact ⟨hxJ, lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
    · rintro ⟨hxJ, ht⟩
      refine ⟨Or.inr ⟨hxJ, ht.1.le, ht.2.le⟩, ?_⟩
      rintro (⟨_, hta⟩ | ⟨_, htb⟩)
      · exact ht.1.ne hta.symm
      · exact ht.2.ne htb
  have hends : L.space ×ˢ {a} ∪ L.space ×ˢ {b} ⊆ (boundaryComplex 3 R).space := by
    rw [hboundary]
    rintro z (⟨hzL, hza⟩ | ⟨hzL, hzb⟩)
    · exact Or.inl ⟨hzL, Or.inl hza⟩
    · exact Or.inl ⟨hzL, Or.inr hzb⟩
  have hBsub := boundaryComplex_space_subset 3 R
  have hBmap : g '' (boundaryComplex 3 R).space = (boundaryComplex 3 K).space :=
    (boundaryComplex_space_of_isPLHomeomorphOn R K
      hR.isCombinatorialManifoldWithBoundary hmap).symm
  calc
    _ = g '' closure ((boundaryComplex 3 R).space \
        (L.space ×ˢ {a} ∪ L.space ×ˢ {b})) := by
      rw [htarget, closure_prod_eq,
        (isPolyhedron_space (boundaryComplex 2 L)).isClosed.closure_eq, closure_Ioo hab.ne]
    _ = closure (g '' ((boundaryComplex 3 R).space \
        (L.space ×ˢ {a} ∪ L.space ×ˢ {b}))) :=
      hmap.image_closure hR.isPolyhedron.isCompact (sdiff_subset.trans hBsub)
    _ = _ := by
      rw [(hmap.bijOn.injOn.mono hBsub).image_sdiff_subset hends, hBmap, image_union]

end DifferentialGeometry.Topology.PiecewiseLinear
