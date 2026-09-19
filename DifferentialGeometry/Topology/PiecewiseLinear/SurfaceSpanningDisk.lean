/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryBicollar

/-!
# Enlarging spanning disks along orientable surfaces
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_disk_pair_of_spanning_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (D₁ D₂ : Set E) (q₁ q₂ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (stdSimplex ℝ (Fin 3)) D₂ ∧
      D ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧ D ⊆ D₂ \ q₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = D ∧ D₁ ⊆ D ∪ (K.space ∩ U) ∧ D₂ ⊆ D ∪ (K.space ∩ U) ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[K.space ∪ D] D := by
  classical
  let J := r '' stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJK : J ⊆ K.space := hmeet.symm.subset.trans inter_subset_right
  obtain ⟨W, ρ, _, hWK, hWU, hWnhds, hρ, hfix⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd hU
  have hJW : J ⊆ W := fun x hx => by
    rw [← hfix x hx]
    exact hρ.bijOn.mapsTo ⟨hx, by norm_num, by norm_num⟩
  have hWD : W ∩ D = J := by
    apply Subset.antisymm
    · exact fun _ hx => hmeet.subset ⟨hx.2, (hWK hx.1).1⟩
    · exact fun _ hx => ⟨hJW hx, (hmeet.symm.subset hx).1⟩
  obtain ⟨q₁, q₂, hq₁, hq₂, hpair, hunion, _, _, hdis₁, hdis₂⟩ :=
    exists_disk_pair_of_boundary_bicollar hr rfl hρ hfix hWD
  let D₁ := D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) 1)
  let D₂ := D ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
  have hWKU : W ⊆ K.space ∩ U := fun _ hx => ⟨(hWK hx).1, hWU hx⟩
  have hD₁ : D₁ ⊆ D ∪ (K.space ∩ U) := by
    apply union_subset subset_union_left
    exact ((image_mono (prod_mono Subset.rfl
      (Icc_subset_Icc (by norm_num) le_rfl))).trans hρ.image_eq.subset).trans
        (hWKU.trans subset_union_right)
  have hD₂ : D₂ ⊆ D ∪ (K.space ∩ U) := by
    apply union_subset subset_union_left
    exact ((image_mono (prod_mono Subset.rfl
      (Icc_subset_Icc le_rfl (by norm_num)))).trans hρ.image_eq.subset).trans
        (hWKU.trans subset_union_right)
  have hnhds : D ∪ W ∈ 𝓝ˢ[K.space ∪ D] D := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
    refine mem_nhdsSetWithin.mpr
      ⟨O ∪ K.spaceᶜ, hO.union (isPolyhedron_space K).isClosed.isOpen_compl, ?_, ?_⟩
    · intro x hxD
      by_cases hxK : x ∈ K.space
      · exact Or.inl (hJO (hmeet.subset ⟨hxD, hxK⟩))
      · exact Or.inr hxK
    · rintro x ⟨hxO | hxK, hxS | hxD⟩
      · exact Or.inr (hOW ⟨hxO, hxS⟩)
      · exact Or.inl hxD
      · exact (hxK hxS).elim
      · exact Or.inl hxD
  refine ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, ?_, ?_, hpair, hD₁, hD₂, ?_⟩
  · exact fun _ hx => ⟨Or.inl hx, fun h => disjoint_left.mp hdis₁ hx h⟩
  · exact fun _ hx => ⟨Or.inl hx, fun h => disjoint_left.mp hdis₂ hx h⟩
  · rwa [hunion]

theorem IsCombinatorialManifold.exists_disk_pair_of_spanning_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (D₁ D₂ : Set E) (q₁ q₂ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (stdSimplex ℝ (Fin 3)) D₂ ∧
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
