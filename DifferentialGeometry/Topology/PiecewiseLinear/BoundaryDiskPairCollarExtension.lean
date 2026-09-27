/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskCollarExtension

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk_with_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hF : IsPLSphere 2 (boundaryComplex 3 K).space)
    {B β P W : Set E} (hB : IsClosed B)
    (hBF : B ∩ (boundaryComplex 3 K).space = β) (hP : IsPLBall 2 P)
    (hPnhds : P ∈ 𝓝ˢ[(boundaryComplex 3 K).space] β)
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc (0 : ℝ) 1) W)
    (hWK : W ⊆ K.space) (hbottom : ∀ x ∈ P, ρ (x, 0) = x)
    (hWF : W ∩ (boundaryComplex 3 K).space = P)
    (hWB : W ∩ B = ρ '' (β ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (ε : ℝ) (W' : Set E) (σ : E × ℝ → E),
      0 < ε ∧ ε ≤ 1 ∧ IsPolyhedron W' ∧ W' ⊆ K.space ∧
      W' ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space ∧
      IsPLHomeomorphOn σ ((boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) ε) W' ∧
      EqOn σ ρ (P ×ˢ Icc (0 : ℝ) ε) ∧
      (∀ x ∈ (boundaryComplex 3 K).space, σ (x, 0) = x) ∧
      W' ∩ (boundaryComplex 3 K).space = (boundaryComplex 3 K).space ∧
      W' ∩ B = σ '' (β ×ˢ Icc (0 : ℝ) ε) := by
  classical
  let F := (boundaryComplex 3 K).space
  obtain ⟨W₀, σ, -, hW₀K, -, hσ, hσρ, hbase, -, -⟩ :=
    hK.exists_collar_eqOn_boundary_disk K hF hP zero_lt_one hρ hWK hbottom hWF
  have hβF : β ⊆ F := hBF.symm.subset.trans inter_subset_right
  obtain ⟨U, hU, hβU, hUP⟩ := mem_nhdsSetWithin.mp hPnhds
  have hβP : β ⊆ P := fun x hx => hUP ⟨hβU hx, hβF hx⟩
  let Q := closure (F \ P)
  have hQF : Q ⊆ F := closure_minimal sdiff_subset hF.isPolyhedron.isClosed
  have hQ : IsCompact Q := hF.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure hQF
  have hQβ : Disjoint Q β := by
    apply disjoint_left.mpr
    intro x hxQ hxβ
    obtain ⟨y, hy, hyU⟩ := ((mem_closure_iff_frequently.mp hxQ).and_eventually
      (hU.mem_nhds (hβU hxβ))).exists
    exact hy.2 (hUP ⟨hyU, hy.1⟩)
  have hQB : Disjoint Q B := by
    apply disjoint_left.mpr
    intro x hxQ hxB
    exact disjoint_left.mp hQβ hxQ (hBF.subset ⟨hxB, hQF hxQ⟩)
  obtain ⟨O, hO, hOeq⟩ := continuousOn_iff'.mp hσ.isPiecewiseAffineOn.continuousOn
    Bᶜ hB.isOpen_compl
  have hQO : Q ×ˢ {(0 : ℝ)} ⊆ O := by
    rintro q ⟨hqQ, hq0⟩
    have hq0' : q.2 = 0 := hq0
    have hqdom : q ∈ F ×ˢ Icc (0 : ℝ) 1 := by
      exact ⟨hQF hqQ, by rw [hq0']; exact ⟨le_rfl, zero_le_one⟩⟩
    have hqB : σ q ∉ B := by
      have heq : q = (q.1, 0) := Prod.ext rfl hq0'
      rw [heq, hbase q.1 (hQF hqQ)]
      exact fun hx => disjoint_left.mp hQB hqQ hx
    exact (hOeq.subset ⟨hqB, hqdom⟩).1
  obtain ⟨U₀, V₀, -, hV₀, hQU₀, h0V₀, hUV⟩ :=
    generalized_tube_lemma hQ isCompact_singleton hO hQO
  obtain ⟨r, hr, hrV₀⟩ := Metric.isOpen_iff.mp hV₀ 0 (h0V₀ (mem_singleton 0))
  let ε := min 1 (r / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hr)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have havoid : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) ε, σ (x, t) ∉ B := by
    intro x hx t ht
    have htV : t ∈ V₀ := hrV₀ (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (half_lt_self hr))
    have hmem : (x, t) ∈ O ∩ (F ×ˢ Icc (0 : ℝ) 1) :=
      ⟨hUV ⟨hQU₀ hx, htV⟩, hQF hx, ht.1, ht.2.trans hε1⟩
    exact (hOeq.symm.subset hmem).1
  have hdom : F ×ˢ Icc (0 : ℝ) ε ⊆ F ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl hε1)
  have hdompoly := hF.isPolyhedron.prod (isPLBall_Icc hε).isPolyhedron
  let W' := σ '' (F ×ˢ Icc (0 : ℝ) ε)
  have hσ' : IsPLHomeomorphOn σ (F ×ˢ Icc (0 : ℝ) ε) W' := hσ.restrict hdompoly hdom
  have hW' : IsPolyhedron W' :=
    hdompoly.image_of_isPiecewiseAffineOn hσ'.isPiecewiseAffineOn hσ'.bijOn.injOn
  have hW'K : W' ⊆ K.space := ((image_mono hdom).trans hσ.image_eq.subset).trans hW₀K
  have hfix : EqOn σ ρ (P ×ˢ Icc (0 : ℝ) ε) :=
    hσρ.mono (prod_mono Subset.rfl (Icc_subset_Icc le_rfl hε1))
  have htrace : W' ∩ F = F := by
    apply Subset.antisymm inter_subset_right
    intro x hx
    exact ⟨⟨(x, 0), ⟨hx, le_rfl, hε.le⟩, hbase x hx⟩, hx⟩
  have hpair : W' ∩ B = σ '' (β ×ˢ Icc (0 : ℝ) ε) := by
    apply Subset.antisymm
    · rintro x ⟨⟨q, hq, rfl⟩, hxB⟩
      have hqP : q.1 ∈ P := by
        by_contra hnP
        exact havoid q.1 (subset_closure ⟨hq.1, hnP⟩) q.2 hq.2 hxB
      have hqρ : q ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hqP, hq.2.1, hq.2.2.trans hε1⟩
      have hρB : ρ q ∈ B := (hσρ hqρ) ▸ hxB
      obtain ⟨z, hz, hzq⟩ := hWB.subset ⟨hρ.bijOn.mapsTo hqρ, hρB⟩
      have heq : z = q := hρ.bijOn.injOn ⟨hβP hz.1, hz.2⟩ hqρ hzq
      exact ⟨q, ⟨heq ▸ hz.1, hq.2⟩, rfl⟩
    · rintro x ⟨q, hq, rfl⟩
      refine ⟨⟨q, ⟨hβF hq.1, hq.2⟩, rfl⟩, ?_⟩
      rw [hfix ⟨hβP hq.1, hq.2⟩]
      exact (hWB.symm.subset ⟨q, ⟨hq.1, hq.2.1, hq.2.2.trans hε1⟩, rfl⟩).2
  exact ⟨ε, W', σ, hε, hε1, hW', hW'K,
    hσ'.mem_nhdsSetWithin_boundaryComplex K hK hε hW'K hbase,
    hσ', hfix, hbase, htrace, hpair⟩

end DifferentialGeometry.Topology.PiecewiseLinear
