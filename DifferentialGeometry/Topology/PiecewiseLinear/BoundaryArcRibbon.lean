/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import Mathlib.Topology.MetricSpace.Thickening

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_isPLHomeomorphOn_square_map_boundary_arc
    {B β : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (hβ : IsPLBall 1 β) (hβbd : β ⊆ q '' stdSimplexBoundary 2) :
    ∃ f : ℝ × ℝ → E,
      IsPLHomeomorphOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) B ∧
      f '' (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) = β := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  let _ : DecidableEq E := Classical.decEq _
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hQ : IsPLBall 2 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_two_prod hI hI
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hQ
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hB
  have hbottom : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 2 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) K hK.isCombinatorialManifoldWithBoundary, hKspace,
      frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
    exact fun z hz => Or.inl ⟨hz.1, Or.inl hz.2⟩
  have hβL : β ⊆ (boundaryComplex 2 L).space :=
    hβbd.trans (hq.image_stdSimplexBoundary_eq_boundaryComplex L hLspace).subset
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hβ
  have hg : IsPLHomeomorphOn (γ ∘ Prod.fst) (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) β :=
    (hI.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).trans hγ
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient
    K L hK hL (hI.of_isPLHomeomorphOn
      (hI.isPolyhedron.isPLHomeomorphOn_prod_const 0)) hbottom hg hβL
  rw [hKspace, hLspace] at hf
  exact ⟨f, hf, hfg.image_eq.trans hg.image_eq⟩

theorem IsPLHomeomorphOn.exists_isPLBall_neighborhood_boundary_arc
    {B β U : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (hβ : IsPLBall 1 β) (hβbd : β ⊆ q '' stdSimplexBoundary 2)
    (hU : IsOpen U) (hβU : β ⊆ U) :
    ∃ D : Set E, IsPLBall 2 D ∧ D ⊆ B ∩ U ∧ β ⊆ D ∧ D ∈ 𝓝ˢ[B] β := by
  obtain ⟨f, hf, hfβ⟩ := exists_isPLHomeomorphOn_square_map_boundary_arc hq hβ hβbd
  obtain ⟨V, hV, hpre⟩ := continuousOn_iff'.mp hf.isPiecewiseAffineOn.continuousOn U hU
  have hbottomV : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact (hpre.subset ⟨hβU (hfβ.subset ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩),
      hx, by norm_num⟩).1
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_Icc.prod isCompact_singleton).exists_cthickening_subset_open hV hbottomV
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := half_pos (lt_min hδ zero_lt_one)
  have hεδ : ε ≤ δ := (half_le_self (le_of_lt (lt_min hδ zero_lt_one))).trans (min_le_left δ 1)
  have hε1 : ε ≤ 1 :=
    (half_le_self (le_of_lt (lt_min hδ zero_lt_one))).trans (min_le_right δ 1)
  let R : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε
  have hRQ : R ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl hε1)
  have hR : IsPLBall 2 R :=
    isPLBall_two_prod (isPLBall_Icc zero_lt_one) (isPLBall_Icc hε)
  have hRβ : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ R :=
    fun z hz => ⟨hz.1, (show z.2 = 0 from hz.2).symm ▸ ⟨le_rfl, hε.le⟩⟩
  have hRU : f '' R ⊆ U := by
    rintro y ⟨⟨x, t⟩, hx, rfl⟩
    have hxtV : (x, t) ∈ V := by
      apply hδV
      apply Metric.mem_cthickening_of_dist_le (x, t) (x, 0) δ
        (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) ⟨hx.1, rfl⟩
      rw [dist_prod_same_left, Real.dist_eq, sub_zero, abs_of_nonneg hx.2.1]
      exact hx.2.2.trans hεδ
    exact (hpre.symm.subset ⟨hxtV, hRQ hx⟩).1
  let v := Function.invFunOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hv : IsPLHomeomorphOn v B (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := hf.symm
  have hO : IsOpen {z : ℝ × ℝ | z.2 < ε} := isOpen_lt continuous_snd continuous_const
  obtain ⟨W, hW, hWpre⟩ := continuousOn_iff'.mp hv.isPiecewiseAffineOn.continuousOn _ hO
  have hβW : β ⊆ W := by
    intro y hy
    obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hfβ.symm.subset hy
    have ht0 : t = 0 := ht
    subst t
    have hinv : v (f (x, 0)) = (x, 0) := hf.bijOn.invOn_invFunOn.1 ⟨hx, by norm_num⟩
    exact (hWpre.subset ⟨by change (v (f (x, 0))).2 < ε; rw [hinv]; exact hε,
      hf.bijOn.mapsTo ⟨hx, by norm_num⟩⟩).1
  refine ⟨f '' R, hR.of_isPLHomeomorphOn (hf.restrict hR.isPolyhedron hRQ),
    fun y hy => ⟨hf.image_eq.subset ((image_mono hRQ) hy), hRU hy⟩,
    hfβ.symm.subset.trans (image_mono hRβ), mem_nhdsSetWithin.mpr ⟨W, hW, hβW, ?_⟩⟩
  rintro y ⟨hyW, hyB⟩
  have hvy := hv.bijOn.mapsTo hyB
  have hlt : (v y).2 < ε := (hWpre.symm.subset ⟨hyW, hyB⟩).1
  exact ⟨v y, ⟨hvy.1, hvy.2.1, hlt.le⟩, hf.bijOn.invOn_invFunOn.2 hyB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
