/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem annulus_mem_nhdsSetWithin
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) {J W : Set E} (hJ : IsPLSphere 1 J)
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hWS : W ⊆ S.space) : W ∈ 𝓝ˢ[S.space] J := by
  obtain ⟨A, R, _, hRfin, _, _, hAspace, _, _, _, hAR, hAS⟩ :=
    hS.exists_annulus_complement S hJ (by norm_num : (-1 : ℝ) < 1) hρ hWS
  let _ : Finite R.faces := hRfin.to_subtype
  have htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by rwa [hAspace] at hAR
  have hcover : W ∪ R.space = S.space := by rwa [hAspace] at hAS
  have hJavoid : J ⊆ R.spaceᶜ := by
    intro x hx hxR
    have hxW : x ∈ W := by
      rw [← hzero x hx]
      exact hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
    obtain ⟨y, hy, hyx⟩ := htrace.subset ⟨hxW, hxR⟩
    have hyP : y ∈ J ×ˢ Icc (-1 : ℝ) 1 := by
      refine ⟨hy.1, ?_⟩
      rcases hy.2 with h | h <;> rw [h] <;> norm_num
    have heq := hρ.bijOn.injOn hyP ⟨hx, by norm_num⟩ (hyx.trans (hzero x hx).symm)
    have ht : y.2 = 0 := congrArg Prod.snd heq
    have hbad : (0 : ℝ) ∈ ({-1, 1} : Set ℝ) := ht ▸ hy.2
    norm_num at hbad
  refine mem_nhdsSetWithin.mpr ⟨R.spaceᶜ, (isPolyhedron_space R).isClosed.isOpen_compl,
    hJavoid, ?_⟩
  exact fun x hx => (hcover.symm.subset hx.2).resolve_right hx.1

open Classical in
theorem IsCombinatorialManifold.exists_compression_neighborhood_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (N W D₀ D₁ : Set E) (f : (Fin 3 → ℝ) × ℝ → E)
      (ρ : E × ℝ → E) (r₀ r₁ : (Fin 3 → ℝ) → E),
      IsPLBall 3 N ∧ N ⊆ U ∧ D ⊆ N ∧ D \ S.space ⊆ interior N ∧
      D ∩ frontier N = r '' stdSimplexBoundary 2 ∧ N ∈ 𝓝ˢ[S.space ∪ D] D ∧
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) ∧
      S.space ∩ N = W ∧ W = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧
      IsPolyhedron W ∧ W ∈ 𝓝ˢ[S.space] (r '' stdSimplexBoundary 2) ∧
      IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧
      (∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-1 : ℝ) 1, ρ (r x, t) = f (x, t)) ∧
      IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧ Disjoint D₀ D₁ ∧
      frontier N = W ∪ D₀ ∪ D₁ ∧
      W ∩ D₀ = r₀ '' stdSimplexBoundary 2 ∧ W ∩ D₁ = r₁ '' stdSimplexBoundary 2 ∧
      r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) ∧
      r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) := by
  obtain ⟨N, f, hf, hNU, hzero, hwall, _⟩ :=
    hS.exists_centered_prism_neighborhood_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨W, D₀, D₁, ρ, r₀, r₁, hN, hDN, hinside, hproper, hW,
    hWpoly, hρ, hρzero, hcompatible, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hf.exists_wall_and_caps_of_centered_prism hr hzero hdim
  have hwall' : S.space ∩ N = W := hwall.trans hW.symm
  have hWS : W ⊆ S.space := hwall'.symm.subset.trans inter_subset_left
  have hWN : W ⊆ N := hwall'.symm.subset.trans inter_subset_right
  have hWnear := annulus_mem_nhdsSetWithin S hS hr.isPLSphere_image_stdSimplexBoundary
    hρ hρzero hWS
  have hinside' : D \ S.space ⊆ interior N := by
    rintro x ⟨hxD, hxS⟩
    exact hinside ⟨hxD, fun hxJ => hxS (hmeet.symm.subset hxJ).2⟩
  have hNnear : N ∈ 𝓝ˢ[S.space ∪ D] D := by
    obtain ⟨O, hO, hJO, hOS⟩ := mem_nhdsSetWithin.mp hWnear
    refine mem_nhdsSetWithin.mpr ⟨O ∪ interior N, hO.union isOpen_interior, ?_, ?_⟩
    · intro x hxD
      by_cases hxS : x ∈ S.space
      · exact Or.inl (hJO (hmeet.subset ⟨hxD, hxS⟩))
      · exact Or.inr (hinside' ⟨hxD, hxS⟩)
    · rintro x ⟨hxO | hxN, hxS | hxD⟩
      · exact hWN (hOS ⟨hxO, hxS⟩)
      · exact hDN hxD
      · exact interior_subset hxN
      · exact hDN hxD
  exact ⟨N, W, D₀, D₁, f, ρ, r₀, r₁, hN, hNU, hDN, hinside', hproper, hNnear,
    hf, hzero, hwall', hW, hWpoly, hWnear, hρ, hρzero, hcompatible,
    hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
