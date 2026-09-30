/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCapRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Segment

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLHomeomorphOn_lineMap_Icc_segment {p a : F} (hpa : p ≠ a) :
    IsPLHomeomorphOn (AffineMap.lineMap (k := ℝ) p a) (Icc 0 1) (segment ℝ p a) := by
  have hbij : BijOn (AffineMap.lineMap (k := ℝ) p a) (Icc 0 1) (segment ℝ p a) := by
    rw [segment_eq_image_lineMap]
    exact (AffineMap.lineMap_injective ℝ hpa).injOn.bijOn_image
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    ((isPiecewiseAffineOn_of_affine (AffineMap.lineMap p a) isOpen_univ).mono_of_isPolyhedron
      isHPolytope_Icc.isPolyhedron (subset_univ _)) hbij

end Segment

section Model

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem boundaryComplex_space_eq_frontier_of_isPLBall_two [DecidableEq Plane]
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    (boundaryComplex 2 K).space = frontier K.space := by
  obtain ⟨k, hk⟩ := hK
  rw [← hk.image_stdSimplexBoundary_eq_boundaryComplex (m := 1) K rfl,
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) hk]

theorem frontier_union_eq_of_inter_eq_segment {K L : Set Plane} (hK : IsPLBall 2 K)
    (hL : IsPLBall 2 L) (hKL : IsPLBall 2 (K ∪ L)) {p a : Plane} (hpa : p ≠ a)
    (hinter : K ∩ L = segment ℝ p a) (hsK : segment ℝ p a ⊆ frontier K)
    (hsL : segment ℝ p a ⊆ frontier L) :
    frontier (K ∪ L) = (frontier K ∪ frontier L) \ (segment ℝ p a \ {p, a}) := by
  have hσ := isPLHomeomorphOn_lineMap_Icc_segment hpa
  have hσ0 : AffineMap.lineMap (k := ℝ) p a (0 : ℝ) = p := AffineMap.lineMap_apply_zero p a
  have hσ1 : AffineMap.lineMap (k := ℝ) p a (1 : ℝ) = a := AffineMap.lineMap_apply_one p a
  obtain ⟨δK, hδK, hδK0, hδK1, hmK, -⟩ :=
    hK.isPLSphere_frontier.exists_isPLHomeomorphOn_closure_sdiff hσ hsK
  obtain ⟨δL, hδL, hδL0, hδL1, hmL, -⟩ :=
    hL.isPLSphere_frontier.exists_isPLHomeomorphOn_closure_sdiff hσ hsL
  rw [hσ0] at hδK0 hδL0
  rw [hσ1] at hδK1 hδL1
  rw [hσ0, hσ1] at hmK hmL
  set AK := closure (frontier K \ segment ℝ p a) with hAK
  set AL := closure (frontier L \ segment ℝ p a) with hAL
  have hKc : IsClosed K := hK.isPolyhedron.isClosed
  have hLc : IsClosed L := hL.isPolyhedron.isClosed
  have hAKK : AK ⊆ K := closure_minimal (sdiff_subset.trans hKc.frontier_subset) hKc
  have hALL : AL ⊆ L := closure_minimal (sdiff_subset.trans hLc.frontier_subset) hLc
  have hAKfr : AK ⊆ frontier K := closure_minimal sdiff_subset isClosed_frontier
  have hALfr : AL ⊆ frontier L := closure_minimal sdiff_subset isClosed_frontier
  have hAKL : AK ∩ L ⊆ {p, a} := by
    rintro x ⟨hxA, hxL⟩
    have hxs : x ∈ segment ℝ p a := hinter ▸ ⟨hAKK hxA, hxL⟩
    exact hmK.subset ⟨hxs, hxA⟩
  have hmeet : AK ∩ AL = {δK 0, δK 1} := by
    rw [hδK0, hδK1]
    apply Subset.antisymm
    · exact fun x hx => hAKL ⟨hx.1, hALL hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨(hmK.symm.subset (mem_insert _ _)).2, (hmL.symm.subset (mem_insert _ _)).2⟩
      · exact ⟨(hmK.symm.subset (mem_insert_of_mem _ (mem_singleton _))).2,
          (hmL.symm.subset (mem_insert_of_mem _ (mem_singleton _))).2⟩
  have hcirc : IsPLSphere 1 (AK ∪ AL) :=
    isPLSphere_one_union_of_isPLHomeomorphOn_Icc hδK hδL (hδL0.trans hδK0.symm)
      (hδL1.trans hδK1.symm) hmeet
  have hoff : ∀ {M N : Set Plane}, IsClosed N → ∀ x ∈ frontier M, x ∉ N →
      x ∈ frontier (M ∪ N) := by
    intro M N hNc x hx hxN
    rw [frontier_eq_closure_inter_closure] at hx ⊢
    refine ⟨closure_mono subset_union_left hx.1, ?_⟩
    have hmem : (Nᶜ : Set Plane) ∈ nhds x := hNc.isOpen_compl.mem_nhds hxN
    have hx2 := mem_closure_iff_nhds.mp hx.2
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨y, hyU, hyM⟩ := hx2 (U ∩ Nᶜ) (Filter.inter_mem hU hmem)
    exact ⟨y, hyU.1, fun hy => hy.elim hyM hyU.2⟩
  have hsubK : AK ⊆ frontier (K ∪ L) := by
    have hopen : frontier K \ segment ℝ p a ⊆ frontier (K ∪ L) := by
      rintro x ⟨hxfr, hxs⟩
      refine hoff hLc x hxfr fun hxL => hxs ?_
      exact hinter ▸ ⟨hKc.frontier_subset hxfr, hxL⟩
    exact closure_minimal hopen isClosed_frontier
  have hsubL : AL ⊆ frontier (K ∪ L) := by
    have hopen : frontier L \ segment ℝ p a ⊆ frontier (K ∪ L) := by
      rintro x ⟨hxfr, hxs⟩
      rw [union_comm]
      refine hoff hKc x hxfr fun hxK => hxs ?_
      exact hinter ▸ ⟨hxK, hLc.frontier_subset hxfr⟩
    exact closure_minimal hopen isClosed_frontier
  have hfreq : AK ∪ AL = frontier (K ∪ L) :=
    eq_of_subset_of_isPLSphere_one hcirc hKL.isPLSphere_frontier (union_subset hsubK hsubL)
  rw [← hfreq]
  have hpaK : ({p, a} : Set Plane) ⊆ AK := fun x hx => (hmK.symm.subset hx).2
  apply Subset.antisymm
  · rintro x (hx | hx)
    · refine ⟨Or.inl (hAKfr hx), fun h => h.2 (hmK.subset ⟨h.1, hx⟩)⟩
    · refine ⟨Or.inr (hALfr hx), fun h => h.2 (hmL.subset ⟨h.1, hx⟩)⟩
  · rintro x ⟨hx | hx, hxs⟩
    · by_cases hxseg : x ∈ segment ℝ p a
      · exact Or.inl (hpaK (by_contra fun h => hxs ⟨hxseg, h⟩))
      · exact Or.inl (subset_closure ⟨hx, hxseg⟩)
    · by_cases hxseg : x ∈ segment ℝ p a
      · exact Or.inl (hpaK (by_contra fun h => hxs ⟨hxseg, h⟩))
      · exact Or.inr (subset_closure ⟨hx, hxseg⟩)

end Model

section Gluing

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_union_of_inter_eq_arc {Δ Z α : Set F}
    {q r : (Fin 3 → ℝ) → F} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Z) {γ : ℝ → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) α) (hΔZ : Δ ∩ Z = α)
    (hαΔ : α ⊆ q '' stdSimplexBoundary 2) (hαZ : α ⊆ r '' stdSimplexBoundary 2) :
    ∃ q' : (Fin 3 → ℝ) → F, IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Δ ∪ Z) ∧
      q' '' stdSimplexBoundary 2 =
        (q '' stdSimplexBoundary 2 ∪ r '' stdSimplexBoundary 2) \ (α \ {γ 0, γ 1}) := by
  classical
  obtain ⟨K, L, hKfin, hLfin, hK, hL, hKL, p, a, hpa, hinter, hbK, hbL⟩ :=
    exists_isPLBall_pair_with_segment_inter
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hKfr := boundaryComplex_space_eq_frontier_of_isPLBall_two K hK
  have hLfr := boundaryComplex_space_eq_frontier_of_isPLBall_two L hL
  have hone : (0 : ℝ) < 1 := one_pos
  have hσ := isPLHomeomorphOn_lineMap_Icc_segment hpa
  set g := AffineMap.lineMap (k := ℝ) p a ∘ Function.invFunOn γ (Icc 0 1) with hgdef
  have hg : IsPLHomeomorphOn g α (segment ℝ p a) := hγ.symm.trans hσ
  have hα : IsPLBall 1 α := (isPLBall_Icc hone).of_isPLHomeomorphOn hγ
  have hΔ : IsPLBall 2 Δ := ⟨q, hq⟩
  have hZ : IsPLBall 2 Z := ⟨r, hr⟩
  obtain ⟨KΔ, hKΔfin, hKΔ⟩ := hΔ.isPolyhedron.exists_simplicialComplex
  obtain ⟨KZ, hKZfin, hKZ⟩ := hZ.isPolyhedron.exists_simplicialComplex
  let _ : Finite KΔ.faces := hKΔfin.to_subtype
  let _ : Finite KZ.faces := hKZfin.to_subtype
  have hΔbd : q '' stdSimplexBoundary 2 = (boundaryComplex 2 KΔ).space :=
    hq.image_stdSimplexBoundary_eq_boundaryComplex (m := 1) KΔ hKΔ
  have hZbd : r '' stdSimplexBoundary 2 = (boundaryComplex 2 KZ).space :=
    hr.image_stdSimplexBoundary_eq_boundaryComplex (m := 1) KZ hKZ
  obtain ⟨G₁, hG₁, hG₁g⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient KΔ K
    (hKΔ.symm ▸ hΔ) hK hα (hΔbd ▸ hαΔ) hg (by convert hbK)
  obtain ⟨G₂, hG₂, hG₂g⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient KZ L
    (hKZ.symm ▸ hZ) hL hα (hZbd ▸ hαZ) hg (by convert hbL)
  rw [hKΔ] at hG₁
  rw [hKZ] at hG₂
  have hfg : EqOn G₁ G₂ (Δ ∩ Z) := by
    rw [hΔZ]
    exact hG₁g.trans hG₂g.symm
  have hmeet : G₁ '' (Δ ∩ Z) = K.space ∩ L.space := by
    rw [hΔZ, hG₁g.image_eq, hg.image_eq, hinter]
  have hG := hG₁.piecewise hG₂ hΔ.isPolyhedron hZ.isPolyhedron hfg hmeet
  set G := Δ.piecewise G₁ G₂ with hGdef
  have hGΔ : EqOn G G₁ Δ := Δ.piecewise_eqOn G₁ G₂
  have hGZ : EqOn G G₂ Z := by
    intro x hx
    by_cases hxΔ : x ∈ Δ
    · rw [hGΔ hxΔ]
      exact hfg ⟨hxΔ, hx⟩
    · exact Δ.piecewise_eqOn_compl G₁ G₂ hxΔ
  obtain ⟨t, ht⟩ := hKL
  set H := Function.invFunOn G (Δ ∪ Z) with hHdef
  have hH : IsPLHomeomorphOn H (K.space ∪ L.space) (Δ ∪ Z) := hG.symm
  have hHG : ∀ X ⊆ Δ ∪ Z, H '' (G '' X) = X := by
    intro X hX
    rw [← image_comp]
    refine (image_congr fun y hy => ?_).trans (image_id X)
    exact hG.bijOn.invOn_invFunOn.1 (hX hy)
  have hΔsub : Δ ⊆ Δ ∪ Z := subset_union_left
  have hZsub : Z ⊆ Δ ∪ Z := subset_union_right
  have hqbd : q '' stdSimplexBoundary 2 ⊆ Δ := by
    rw [← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hrbd : r '' stdSimplexBoundary 2 ⊆ Z := by
    rw [← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hfrK : G '' (q '' stdSimplexBoundary 2) = frontier K.space := by
    rw [(hGΔ.mono hqbd).image_eq, ← image_comp,
      IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) (hq.trans hG₁)]
  have hfrL : G '' (r '' stdSimplexBoundary 2) = frontier L.space := by
    rw [(hGZ.mono hrbd).image_eq, ← image_comp,
      IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) (hr.trans hG₂)]
  have hαsub : α ⊆ Δ := hΔZ ▸ inter_subset_left
  have hγends : {γ 0, γ 1} ⊆ α := by
    rintro x (rfl | rfl)
    · exact hγ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    · exact hγ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hgγ : ∀ x ∈ Icc (0 : ℝ) 1, g (γ x) = AffineMap.lineMap (k := ℝ) p a x := by
    intro x hx
    simp only [hgdef, Function.comp_apply]
    rw [hγ.bijOn.invOn_invFunOn.1 hx]
  have hseg : G '' (α \ {γ 0, γ 1}) = segment ℝ p a \ {p, a} := by
    rw [(hG.bijOn.injOn.mono (hαsub.trans hΔsub)).image_sdiff_subset hγends,
      (hGΔ.mono hαsub).image_eq, (hGΔ.mono (hγends.trans hαsub)).image_eq,
      hG₁g.image_eq, (hG₁g.mono hγends).image_eq, hg.image_eq, image_pair,
      hgγ 0 ⟨le_rfl, zero_le_one⟩, hgγ 1 ⟨zero_le_one, le_rfl⟩, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one]
  have hsK : segment ℝ p a ⊆ frontier K.space := hKfr ▸ hbK
  have hsL : segment ℝ p a ⊆ frontier L.space := hLfr ▸ hbL
  have hfrT := frontier_union_eq_of_inter_eq_segment hK hL ⟨t, ht⟩ hpa hinter hsK hsL
  refine ⟨H ∘ t, ht.trans hH, ?_⟩
  have hU : q '' stdSimplexBoundary 2 ∪ r '' stdSimplexBoundary 2 ⊆ Δ ∪ Z :=
    union_subset (hqbd.trans hΔsub) (hrbd.trans hZsub)
  have hsub : α \ {γ 0, γ 1} ⊆ q '' stdSimplexBoundary 2 ∪ r '' stdSimplexBoundary 2 :=
    sdiff_subset.trans (hαΔ.trans subset_union_left)
  rw [image_comp, IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) ht, hfrT, ← hfrK, ← hfrL,
    ← hseg, ← image_union, ← (hG.bijOn.injOn.mono hU).image_sdiff_subset hsub]
  exact hHG _ (sdiff_subset.trans hU)

end Gluing

end DifferentialGeometry.Topology.PiecewiseLinear
