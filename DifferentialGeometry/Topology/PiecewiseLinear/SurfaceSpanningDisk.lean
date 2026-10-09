/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_disk_pair_of_spanning_disk_of_bicollar
    {S D W : Set E} (hS : IsClosed S) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S = r '' stdSimplexBoundary 2) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W)
    (hfix : ∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hWS : W ⊆ S) (hWnhds : W ∈ 𝓝ˢ[S] (r '' stdSimplexBoundary 2)) :
    ∃ (D₀ D₁ : Set E) (q₀ q₁ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      D ⊆ D₀ \ q₀ '' stdSimplexBoundary 2 ∧ D ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧
      D₀ ∩ D₁ = D ∧
      D₀ = D ∪ ρ '' ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 0) ∧
      D₁ = D ∪ ρ '' ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) ∧
      q₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) ∧
      q₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) ∧
      D₀ ∪ D₁ = D ∪ W ∧ D₀ ∪ D₁ ∈ 𝓝ˢ[S ∪ D] D := by
  let J := r '' stdSimplexBoundary 2
  have hJW : J ⊆ W := fun x hx => by
    rw [← hfix x hx]
    exact hρ.bijOn.mapsTo ⟨hx, by norm_num, by norm_num⟩
  have hWD : W ∩ D = J := Subset.antisymm
    (fun _ hx => hmeet.subset ⟨hx.2, hWS hx.1⟩)
    (fun _ hx => ⟨hJW hx, (hmeet.symm.subset hx).1⟩)
  obtain ⟨q₁, q₀, hq₁, hq₀, hpair, hunion, hbd₁, hbd₀, hdis₁, hdis₀⟩ :=
    exists_disk_pair_of_boundary_bicollar hr rfl hρ hfix hWD
  let D₀ := D ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
  let D₁ := D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) 1)
  have hnhds : D ∪ W ∈ 𝓝ˢ[S ∪ D] D := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
    refine mem_nhdsSetWithin.mpr ⟨O ∪ Sᶜ, hO.union hS.isOpen_compl, ?_, ?_⟩
    · intro x hxD
      by_cases hxS : x ∈ S
      · exact Or.inl (hJO (hmeet.subset ⟨hxD, hxS⟩))
      · exact Or.inr hxS
    · rintro x ⟨hxO | hxS, hxS' | hxD⟩
      · exact Or.inr (hOW ⟨hxO, hxS'⟩)
      · exact Or.inl hxD
      · exact (hxS hxS').elim
      · exact Or.inl hxD
  refine ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, ?_, ?_, ?_, rfl, rfl, hbd₀, hbd₁, ?_, ?_⟩
  · exact fun _ hx => ⟨Or.inl hx, fun h => disjoint_left.mp hdis₀ hx h⟩
  · exact fun _ hx => ⟨Or.inl hx, fun h => disjoint_left.mp hdis₁ hx h⟩
  · exact (inter_comm D₀ D₁).trans hpair
  · exact (union_comm D₀ D₁).trans hunion
  · rw [(union_comm D₀ D₁).trans hunion]
    exact hnhds

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_disk_pair_of_spanning_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (D₁ D₂ : Set E) (q₁ q₂ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      D ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧ D ⊆ D₂ \ q₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = D ∧ D₁ ⊆ D ∪ (K.space ∩ U) ∧ D₂ ⊆ D ∪ (K.space ∩ U) ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[K.space ∪ D] D := by
  let J := r '' stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJK : J ⊆ K.space := hmeet.symm.subset.trans inter_subset_right
  obtain ⟨W, ρ, -, hWK, hWU, hWnhds, hρ, hfix⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd hU
  obtain ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, hD₁, hD₂, hpair, -, -, -, -, hunion, hnhds⟩ :=
    exists_disk_pair_of_spanning_disk_of_bicollar (isPolyhedron_space K).isClosed
      hr hmeet hρ hfix (hWK.trans sdiff_subset) hWnhds
  have hWKU : W ⊆ K.space ∩ U := fun _ hx => ⟨(hWK hx).1, hWU hx⟩
  have hpairSub : D₁ ∪ D₂ ⊆ D ∪ (K.space ∩ U) :=
    hunion.subset.trans (union_subset_union Subset.rfl hWKU)
  exact ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, hD₁, hD₂, hpair,
    subset_union_left.trans hpairSub, subset_union_right.trans hpairSub, hnhds⟩

theorem IsCombinatorialManifold.exists_disk_pair_of_spanning_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (D₁ D₂ : Set E) (q₁ q₂ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      D ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧ D ⊆ D₂ \ q₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = D ∧ D₁ ⊆ D ∪ (K.space ∩ U) ∧ D₂ ⊆ D ∪ (K.space ∩ U) ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[K.space ∪ D] D := by
  classical
  have hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 K).space := by
    apply disjoint_left.mpr
    intro x _ hxB
    obtain ⟨s, hs, _⟩ := (boundaryComplex 2 K).mem_space_iff.mp hxB
    rw [hK.boundaryComplex_faces_eq_empty K] at hs
    exact hs.elim
  exact hK.isCombinatorialManifoldWithBoundary.exists_disk_pair_of_spanning_disk
    K hor hr hmeet hBd hU

end DifferentialGeometry.Topology.PiecewiseLinear
