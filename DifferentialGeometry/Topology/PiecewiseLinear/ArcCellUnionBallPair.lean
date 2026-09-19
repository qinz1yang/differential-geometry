/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellNormalizationInduction

/-!
# Ball pairs from trimmed unions of interior arc cells
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBallPair_trimmedArcCellUnion_of_interior
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hinterior : ∀ j, 1 ≤ j → j ≤ 2 * n - 1 →
      arcChainFace v j ∉ (boundaryComplex 3 K).faces)
    (hnpos : 0 < n) (hn : Module.finrank ℝ E = 3) :
    IsPLBallPair 2 1 (trimmedArcCellUnion K v (2 * n - 1))
      (trimmedArcCellUnion K v (2 * n - 1) ∩ (arcComplexIn K v n).space) := by
  obtain ⟨p₁, p₂, z, y₁, y₂, L₁, L₂, L₀, L, hfin₁, hfin₂, hfin₀, hL₁, hL₂, hL₀,
    hS₁, hS₂, hS₀, hD₁, hD₂, hy₁, hy₁D, hy₂, hy₂D, hmeet, hI₁, hI₂, hI₀,
    hpair₁, hpair₂, hpair₀, hpair, hfin, hL, hS, hcone, harc, hy₁L, hy₂L, hL₂sub⟩ :=
    exists_cutModel_data (E := E) hn
  obtain ⟨Φ, hΦ, hΦarc, hΦD, hΦz, hΦy⟩ :=
    exists_normalized_trimmedArcCellUnion_of_cutModel hK hvert hedge hinj hinterior hnpos hn
      hfin₁ hfin₂ hfin₀ hfin hL₁ hL₂ hL₀ hL hS₁ hS₂ hS₀ hS hD₁ hD₂ hy₁ hy₁D hy₂ hy₂D
      hmeet hcone harc hy₁L hy₂L hL₂sub (k := 2 * n - 1) (by omega) (by omega)
  have hsub : trimmedArcCellUnion K v (2 * n - 1) ∩ (arcComplexIn K v n).space ⊆
      trimmedArcCellUnion K v (2 * n - 1) := inter_subset_left
  have hinv := (hΦ.bijOn.invOn_invFunOn.1.mono hsub).image_image
  refine hpair₁.of_isPLHomeomorphOn hΦ.symm ?_
  rw [← hΦarc, hinv]

open Classical in
theorem IsCombinatorialManifold.isPLBallPair_trimmedArcCellUnion
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hnpos : 0 < n) (hn : Module.finrank ℝ E = 3) :
    IsPLBallPair 2 1 (trimmedArcCellUnion K v (2 * n - 1))
      (trimmedArcCellUnion K v (2 * n - 1) ∩ (arcComplexIn K v n).space) := by
  apply hK.isCombinatorialManifoldWithBoundary.isPLBallPair_trimmedArcCellUnion_of_interior
    hvert hedge hinj
  · intro j hj0 hjn
    rw [hK.boundaryComplex_faces_eq_empty]
    intro h
    exact h
  · exact hnpos
  · exact hn

end DifferentialGeometry.Topology.PiecewiseLinear
