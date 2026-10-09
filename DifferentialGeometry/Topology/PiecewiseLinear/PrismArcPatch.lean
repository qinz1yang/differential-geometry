/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_prism_ends_union_arc
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {A : Set E} (hA : IsPLBall 1 A) (hAK : A ⊆ (boundaryComplex 2 K).space)
    {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (K.space ×ˢ {a, b} ∪ A ×ˢ Icc a b) := by
  classical
  have hprod := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let B := boundaryComplex 3 R
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 R).to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  have hB : IsCombinatorialManifoldWithBoundary 2 B :=
    (isPLSphere_boundaryComplex_space_of_isPLBall R
        hR).isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  have hboundary : B.space = K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b :=
    boundaryComplex_space_prism K hK hab R hRspace
  have hAspace : A ⊆ K.space := hAK.trans (boundaryComplex_space_subset 2 K)
  have hbottom : IsPLBall 2 (K.space ×ˢ {a}) :=
    hK.of_isPLHomeomorphOn ((isPolyhedron_space K).isPLHomeomorphOn_prod_const a)
  have htop : IsPLBall 2 (K.space ×ˢ {b}) :=
    hK.of_isPLHomeomorphOn ((isPolyhedron_space K).isPLHomeomorphOn_prod_const b)
  have hband : IsPLBall 2 (A ×ˢ Icc a b) := isPLBall_two_prod hA (isPLBall_Icc hab)
  have hbottomB : K.space ×ˢ {a} ⊆ B.space := by
    rw [hboundary]
    exact fun x hx => Or.inl ⟨hx.1, Or.inl hx.2⟩
  have htopB : K.space ×ˢ {b} ⊆ B.space := by
    rw [hboundary]
    exact fun x hx => Or.inl ⟨hx.1, Or.inr hx.2⟩
  have hbandB : A ×ˢ Icc a b ⊆ B.space := by
    rw [hboundary]
    exact fun x hx => Or.inr ⟨hAK hx.1, hx.2⟩
  have hinter (t : ℝ) (ht : t ∈ Icc a b) :
      (K.space ×ˢ {t}) ∩ (A ×ˢ Icc a b) = A ×ˢ {t} := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hy.1, hx.2⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hAspace hx, hxt⟩, hx, hxt.symm ▸ ht⟩
  have hbottomI : IsPLBall 1 ((K.space ×ˢ {a}) ∩ (A ×ˢ Icc a b)) := by
    rw [hinter a ⟨le_rfl, hab.le⟩]
    exact hA.of_isPLHomeomorphOn (hA.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hfirst := hB.isPLBall_union_of_inter_isPLBall_one hbottom hband hbottomB hbandB hbottomI
  have hmeet : ((K.space ×ˢ {a}) ∪ A ×ˢ Icc a b) ∩ (K.space ×ˢ {b}) = A ×ˢ {b} := by
    ext x
    constructor
    · rintro ⟨hx | hx, hy⟩
      · exact (hab.ne (hx.2.symm.trans hy.2)).elim
      · exact ⟨hx.1, hy.2⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨Or.inr ⟨hx, hxt.symm ▸ ⟨hab.le, le_rfl⟩⟩, hAspace hx, hxt⟩
  have hsecondI : IsPLBall 1 (((K.space ×ˢ {a}) ∪ A ×ˢ Icc a b) ∩ (K.space ×ˢ {b})) := by
    rw [hmeet]
    exact hA.of_isPLHomeomorphOn (hA.isPolyhedron.isPLHomeomorphOn_prod_const b)
  have h := hB.isPLBall_union_of_inter_isPLBall_one hfirst htop
    (union_subset hbottomB hbandB) htopB hsecondI
  have heq : ((K.space ×ˢ {a}) ∪ A ×ˢ Icc a b) ∪ (K.space ×ˢ {b}) =
      K.space ×ˢ {a, b} ∪ A ×ˢ Icc a b := by
    ext x
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc]
    tauto
  rwa [heq] at h

end DifferentialGeometry.Topology.PiecewiseLinear
