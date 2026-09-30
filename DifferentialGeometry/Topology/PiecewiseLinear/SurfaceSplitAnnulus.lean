/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPLSphere.isPathConnected_one {S : Set E} (hS : IsPLSphere 1 S) :
    IsPathConnected S := by
  obtain ⟨f, hf⟩ := hS
  have hpath := ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩).image'
    (hf.isPiecewiseAffineOn.continuousOn.comp continuous_stdTriangleLoop.continuousOn
      fun t ht => stdTriangleLoop_image.subset ⟨t, ht, rfl⟩)
  have himage : (f ∘ stdTriangleLoop) '' Icc (0 : ℝ) 1 = S := by
    rw [image_comp, stdTriangleLoop_image, hf.image_eq]
  exact himage ▸ hpath

open Classical in
theorem IsPLSphere.isPathConnected_sdiff_union_of_disjoint_isPLBall_two
    {S D₀ D₁ : Set E} (hS : IsPLSphere 2 S)
    (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ S)
    (hD₁ : IsPLBall 2 D₁) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁) :
    IsPathConnected (S \ (D₀ ∪ D₁)) := by
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  let _ : DecidableEq ((Fin 3 → ℝ) × ℝ) := Classical.decEq _
  let P : Set (Fin 3 → ℝ) := Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
  have hP : IsPLBall 2 P := isPLBall_stdSimplex 2
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hprod : IsPLBall 3 (L.space ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hL (isPLBall_Icc zero_lt_one)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  let S' : Set ((Fin 3 → ℝ) × ℝ) := (boundaryComplex 3 R).space
  let D₀' : Set ((Fin 3 → ℝ) × ℝ) := L.space ×ˢ {(0 : ℝ)}
  let D₁' : Set ((Fin 3 → ℝ) × ℝ) := L.space ×ˢ {(1 : ℝ)}
  have hboundary : S' =
      L.space ×ˢ {(0 : ℝ), 1} ∪ (boundaryComplex 2 L).space ×ˢ Icc 0 1 := by
    exact boundaryComplex_space_prism L hL zero_lt_one R hRspace
  have hS' : IsPLSphere 2 S' := isPLSphere_boundaryComplex_space_of_isPLBall R hR
  have hD₀' : IsPLBall 2 D₀' :=
    hL.of_isPLHomeomorphOn (hL.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hD₁' : IsPLBall 2 D₁' :=
    hL.of_isPLHomeomorphOn (hL.isPolyhedron.isPLHomeomorphOn_prod_const 1)
  have hD₀'S : D₀' ⊆ S' := by
    rw [hboundary]
    rintro ⟨x, t⟩ ⟨hxL, ht⟩
    have ht : t = 0 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hxL, Or.inl rfl⟩
  have hD₁'S : D₁' ⊆ S' := by
    rw [hboundary]
    rintro ⟨x, t⟩ ⟨hxL, ht⟩
    have ht : t = 1 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hxL, Or.inr rfl⟩
  have hdis' : Disjoint D₀' D₁' := by
    apply disjoint_left.mpr
    rintro ⟨x, t⟩ ⟨-, ht0⟩ ⟨-, ht1⟩
    have ht0 : t = 0 := by simpa only [mem_singleton_iff] using ht0
    have ht1 : t = 1 := by simpa only [mem_singleton_iff] using ht1
    norm_num [ht0] at ht1
  obtain ⟨q, hq⟩ := hD₀
  obtain ⟨r, hr⟩ := hD₀'
  have hD₀ball : IsPLBall 2 D₀ := ⟨q, hq⟩
  let g := r ∘ Function.invFunOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hg : IsPLHomeomorphOn g D₀ D₀' := hq.symm.trans hr
  obtain ⟨G, hG, hGD₀, hGD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    hS hS' hD₀ball hD₀S hD₁ hD₁S hdis hD₁' hD₁'S hdis' hg hD₀'S
  have hGD₀image : G '' D₀ = D₀' := hGD₀.image_eq.trans hg.image_eq
  have hGpair : G '' (D₀ ∪ D₁) = D₀' ∪ D₁' := by
    rw [image_union, hGD₀image, hGD₁]
  have htarget : S' \ (D₀' ∪ D₁') =
      (boundaryComplex 2 L).space ×ˢ Ioo (0 : ℝ) 1 := by
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
        have ht0 : t ≠ 0 := fun ht0 => hzend (Or.inl ⟨hxL, ht0⟩)
        have ht1 : t ≠ 1 := fun ht1 => hzend (Or.inr ⟨hxL, ht1⟩)
        exact ⟨hxJ, lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    · rintro ⟨hxJ, ht⟩
      have hxL : x ∈ L.space := boundaryComplex_space_subset 2 L hxJ
      refine ⟨Or.inr ⟨hxJ, ht.1.le, ht.2.le⟩, ?_⟩
      rintro (⟨-, ht0⟩ | ⟨-, ht1⟩)
      · exact ht.1.ne ht0.symm
      · exact ht.2.ne ht1
  have htargetPath : IsPathConnected (S' \ (D₀' ∪ D₁')) := by
    rw [htarget]
    exact (isPLSphere_boundaryComplex_space_of_isPLBall L hL).isPathConnected_one.prod
      ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩)
  have hpairSub : D₀ ∪ D₁ ⊆ S := union_subset hD₀S hD₁S
  have himage : G '' (S \ (D₀ ∪ D₁)) = S' \ (D₀' ∪ D₁') := by
    rw [hG.bijOn.injOn.image_sdiff_subset hpairSub, hG.image_eq, hGpair]
  have hinvImage : Function.invFunOn G S '' (S' \ (D₀' ∪ D₁')) =
      S \ (D₀ ∪ D₁) := by
    rw [← himage, image_image]
    have hleft : EqOn (Function.invFunOn G S ∘ G) id (S \ (D₀ ∪ D₁)) :=
      fun x hx => hG.bijOn.invOn_invFunOn.1 hx.1
    exact hleft.image_eq.trans (image_id _)
  rw [← hinvImage]
  exact htargetPath.image' (hG.symm.isPiecewiseAffineOn.continuousOn.mono sdiff_subset)

end DifferentialGeometry.Topology.PiecewiseLinear
