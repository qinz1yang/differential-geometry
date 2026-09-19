/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellUnion
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairRelativeGluing

/-!
# Normalized finite unions of interior cells along a simplicial arc
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_normalized_trimmedArcCellUnion_one_of_interior [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (h1B : arcChainFace v 1 ∉ (boundaryComplex 3 K).faces)
    (hnpos : 0 < n) (hn : Module.finrank ℝ E = 3) :
    ∃ (p z y : E) (L L₀ : Geometry.SimplicialComplex ℝ E) (G : E → E),
      L.faces.Finite ∧ L₀.faces.Finite ∧
      IsConeBase p L ∧ IsConeBase z L₀ ∧
      IsPLSphere 2 L.space ∧ IsPLSphere 1 L₀.space ∧
      coneSet z L₀.space ⊆ L.space ∧
      y ∈ closure (L.space \ coneSet z L₀.space) \ coneSet z L₀.space ∧
      IsPLHomeomorphOn G (trimmedArcCellUnion K v 1) (coneSet p L.space) ∧
      G '' (trimmedArcCellUnion K v 1 ∩ (arcComplexIn K v n).space) =
        coneSet p {z, y} ∧
      G '' coneSet (arcCellCrossing v 1) (arcCellInterfaceBase K v 1).space =
        coneSet z L₀.space ∧
      G (arcCellCrossing v 1) = z ∧ G (arcCellCrossing v 0) = y := by
  obtain ⟨p₁, p₂, z, y₁, y₂, L₁, L₂, L₀, L, hfin₁, hfin₂, hfin₀, hL₁, hL₂, hL₀,
    hS₁, hS₂, hS₀, hD₁, hD₂, hy₁, hy₁D, hy₂, hy₂D, hmeet, hI₁, hI₂, hI₀,
    hpair₁, hpair₂, hpair₀, hpair, hfin, hL, hS, hcone, harc, hy₁L, hy₂L, hL₂sub⟩ :=
    exists_cutModel_data (E := E) hn
  have _ : Finite (arcCellBase K v 1).faces := (arcCellBase_faces_finite v 1).to_subtype
  have _ : Finite (arcCellInterfaceBase K v 1).faces :=
    (arcCellInterfaceBase_faces_finite v 1).to_subtype
  have _ : Finite L₁.faces := hfin₁.to_subtype
  have _ : Finite L₀.faces := hfin₀.to_subtype
  have htwo : 2 ≤ 2 * n := by omega
  have hLc := isConeBase_arcCellBase (K := K) hvert hedge (j := 1) (by omega)
  have hSph := hK.isPLSphere_arcCellBase_of_interior hvert hedge (j := 1) (by omega) h1B
  have hLd := isConeBase_arcCellInterfaceBase (K := K) hvert hedge hinj (j := 1) htwo
  have hSd := hK.isPLSphere_arcCellInterfaceBase_of_interior_left
    hvert hedge hinj (j := 1) htwo h1B
  have hDS := arcCellInterface_subset_arcCellBase_left
    (K := K) hvert hedge hinj (j := 1) htwo
  have hzS : arcCellCrossing v 1 ∈ (arcCellBase K v 1).space :=
    hDS (apex_mem_coneSet _ _)
  have hyS : arcCellCrossing v 0 ∈ (arcCellBase K v 1).space :=
    arcCellInterface_subset_arcCellBase_right (K := K) hvert hedge hinj (j := 0)
      (by omega) (apex_mem_coneSet _ _)
  have hX : ({arcCellCrossing v 1, arcCellCrossing v 0} : Set E) ⊆
      (arcCellBase K v 1).space := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · simpa [hx] using hzS
    · simpa [Set.mem_singleton_iff.mp hx] using hyS
  have hDball : IsPLBall 2
      (coneSet (arcCellCrossing v 1) (arcCellInterfaceBase K v 1).space) := by
    rw [← coneComplex_space_eq_coneSet hLd]
    exact hLd.isPLBall_of_isPLSphere hSd
  obtain ⟨f₀, hf₀⟩ := hSd.exists_isPLHomeomorphOn (F := E) hS₀
  obtain ⟨g, hg, -, hgz, -⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hLd
      (subset_refl (arcCellInterfaceBase K v 1).space) hL₀ hf₀ hf₀.image_eq
  have hySrc := previous_arcCellCrossing_mem_closure_diff_interface
    (K := K) hvert hedge hinj (j := 1) (by omega) htwo
  have hyTgt : y₁ ∈ closure (L₁.space \ coneSet z L₀.space) \ coneSet z L₀.space :=
    ⟨subset_closure ⟨hy₁, hy₁D⟩, hy₁D⟩
  have hgX :
      g '' (({arcCellCrossing v 1, arcCellCrossing v 0} : Set E) ∩
        coneSet (arcCellCrossing v 1) (arcCellInterfaceBase K v 1).space) =
        ({z, y₁} : Set E) ∩ coneSet z L₀.space := by
    rw [pair_inter_coneSet (previous_arcCellCrossing_not_mem_interface
      (K := K) hvert hedge hinj (j := 1) (by omega) htwo),
      pair_inter_coneSet hy₁D, Set.image_singleton, hgz]
  obtain ⟨G, hG, hGeq, hGapex, hGX, hGbase, hGy⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hLc hX hSph hL₁ hS₁ hDball hDS hD₁
      hg hySrc hyTgt
      (pair_eq_inter_coneSet_union (previous_arcCellCrossing_not_mem_interface
        (K := K) hvert hedge hinj (j := 1) (by omega) htwo))
      (pair_eq_inter_coneSet_union hy₁D) hgX
  have hBcell : trimmedArcCellUnion K v 1 =
      (derivedNeighborhoodCell K (arcChainFace v 1)).space := by
    simpa [trimmedArcCellUnion_zero] using trimmedArcCellUnion_succ K v 0
  have hB : trimmedArcCellUnion K v 1 =
      coneSet (arcCellApex v 1) (arcCellBase K v 1).space := by
    rw [hBcell, derivedNeighborhoodCell_arcChainFace_space_eq_coneSet
      (K := K) hvert hedge (j := 1) (by omega)]
  have hA : trimmedArcCellUnion K v 1 ∩ (arcComplexIn K v n).space =
      coneSet (arcCellApex v 1) {arcCellCrossing v 1, arcCellCrossing v 0} := by
    rw [hBcell, derivedNeighborhoodCell_arcChainFace_inter_arcComplexIn_space_eq
      (K := K) hvert hedge hinj (j := 1) (by omega) htwo, Set.pair_comm]
  refine ⟨p₁, z, y₁, L₁, L₀, G, hfin₁, hfin₀, hL₁, hL₀, hS₁, hS₀, hD₁, hyTgt, ?_,
    ?_, ?_, ?_, hGy⟩
  · rwa [hB]
  · rwa [hA]
  · exact hGeq.image_eq.trans hg.image_eq
  · exact (hGeq (apex_mem_coneSet _ _)).trans hgz

open Classical in
theorem exists_normalized_trimmedArcCellUnion_one [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hnpos : 0 < n) (hn : Module.finrank ℝ E = 3) :
    ∃ (p z y : E) (L L₀ : Geometry.SimplicialComplex ℝ E) (G : E → E),
      L.faces.Finite ∧ L₀.faces.Finite ∧
      IsConeBase p L ∧ IsConeBase z L₀ ∧
      IsPLSphere 2 L.space ∧ IsPLSphere 1 L₀.space ∧
      coneSet z L₀.space ⊆ L.space ∧
      y ∈ closure (L.space \ coneSet z L₀.space) \ coneSet z L₀.space ∧
      IsPLHomeomorphOn G (trimmedArcCellUnion K v 1) (coneSet p L.space) ∧
      G '' (trimmedArcCellUnion K v 1 ∩ (arcComplexIn K v n).space) =
        coneSet p {z, y} ∧
      G '' coneSet (arcCellCrossing v 1) (arcCellInterfaceBase K v 1).space =
        coneSet z L₀.space ∧
      G (arcCellCrossing v 1) = z ∧ G (arcCellCrossing v 0) = y := by
  apply exists_normalized_trimmedArcCellUnion_one_of_interior
    hK.isCombinatorialManifoldWithBoundary hvert hedge hinj
  · rw [hK.boundaryComplex_faces_eq_empty]
    intro h
    exact h
  · exact hnpos
  · exact hn

end DifferentialGeometry.Topology.PiecewiseLinear
