/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellNeighborhoodModel

/-!
# A supported perturbation of trivalent dual-cell piercing neighborhoods
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_trivalent_graphDualCell_supported_perturbation_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J C : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (A B : Fin 3 → Set (Fin 5 → ℝ)) (U : Set (Fin 5 → ℝ))
        (δ : ℝ) (p : Fin 5 → ℝ) (h : (Fin 5 → ℝ) ≃ₜ (Fin 5 → ℝ)),
      K.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifold 3 K ∧
      L.faces ⊆ K.faces ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      (∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w)) ∧
      U = Metric.thickening 1 K.space ∧
      (∀ i,
        IsPLSphere 1 (J i) ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        A i ⊆ U ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space)) ∧
      Pairwise (fun i j => Disjoint (J i) (J j)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      0 < δ ∧ p ∈ J 0 ∧
      IsPLHomeomorphOn h univ univ ∧ h p ≠ p ∧
      EqOn h id (Metric.ball p (δ / 4))ᶜ ∧ (∀ x, dist (h x) x < δ) ∧
      (∀ i, h '' A i ⊆ U) ∧
      Pairwise (fun i j => Disjoint (h '' A i) (h '' A j)) ∧
      Pairwise (fun i j => Disjoint (h '' B i) (h '' B j)) ∧
      (∀ i, ∃ O : Set (Fin 5 → ℝ),
        IsOpen O ∧ h '' J i ⊆ O ∧
        h '' B i ⊆ O ∩ h '' K.space ∧ O ∩ h '' K.space ⊆ h '' A i) ∧
      ∀ i,
        HasImageDerivedNeighborhoodSurfaceTraces K h (A i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space) ∧
        HasImageDerivedNeighborhoodSurfaceTraces K h (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, v, w, J, C, f, A, B, U, δ, hKfin, hLfin, hK, hLK, hcard,
    hwinj, hvw, hneighbors, hU, hdata, hpairJ, hpairA, hpairB, hδ, hstable⟩ :=
    exists_trivalent_graphDualCell_piercing_neighborhood_stability_model
  obtain ⟨p, hp⟩ := (hdata 0).1.nonempty
  obtain ⟨h, hh, hmove, hfix, hclose⟩ :=
    exists_isPLHomeomorphOn_moves_point_dist_lt (p := p) hδ
  obtain ⟨himage, hpairHA, hpairHB⟩ :=
    hstable (fun _ => h) (fun _ x _ => hclose x)
  have hAB (i : Fin 3) :
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space) := by
    rcases hdata i with ⟨-, -, -, -, -, -, -, hi⟩
    exact hi
  refine ⟨K, L, v, w, J, C, f, A, B, U, δ, p, h, hKfin, hLfin, hK, hLK,
    hcard, hwinj, hvw, hneighbors, hU, hdata, hpairJ, hpairA, hpairB, hδ, hp,
    hh, hmove, hfix, hclose, himage, hpairHA, hpairHB, ?_, ?_⟩
  · intro i
    exact (hAB i).exists_image_open_nesting h
  · intro i
    exact ⟨(hAB i).1.hasImageDerivedNeighborhoodSurfaceTraces h,
      (hAB i).2.1.hasImageDerivedNeighborhoodSurfaceTraces h⟩

open Classical in
theorem exists_trivalent_graphDualCell_relative_supported_perturbation_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J C : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (A B : Fin 3 → Set (Fin 5 → ℝ)) (U : Set (Fin 5 → ℝ))
        (δ r : ℝ) (p : Fin 5 → ℝ) (h : (Fin 5 → ℝ) ≃ₜ (Fin 5 → ℝ)),
      K.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifold 3 K ∧
      L.faces ⊆ K.faces ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      (∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w)) ∧
      U = Metric.thickening 1 K.space ∧
      (∀ i,
        IsPLSphere 1 (J i) ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        A i ⊆ U ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space)) ∧
      Pairwise (fun i j => Disjoint (J i) (J j)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      0 < δ ∧ p ∈ J 0 ∧ p ∉ L.space ∧ 0 < r ∧
      Metric.ball p r ⊆ U \ L.space ∧
      IsPLHomeomorphOn h univ univ ∧ h p ≠ p ∧
      EqOn h id (Metric.ball p r)ᶜ ∧ EqOn h id L.space ∧ EqOn h id Uᶜ ∧
      (∀ x, dist (h x) x < δ) ∧
      (∀ i, h '' A i ⊆ U) ∧
      Pairwise (fun i j => Disjoint (h '' A i) (h '' A j)) ∧
      Pairwise (fun i j => Disjoint (h '' B i) (h '' B j)) ∧
      (∀ i, ∃ O : Set (Fin 5 → ℝ),
        IsOpen O ∧ h '' J i ⊆ O ∧
        h '' B i ⊆ O ∩ h '' K.space ∧ O ∩ h '' K.space ⊆ h '' A i) ∧
      ∀ i,
        HasImageDerivedNeighborhoodSurfaceTraces K h (A i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space) ∧
        HasImageDerivedNeighborhoodSurfaceTraces K h (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, v, w, hKfin, hLfin, hK, hLK, hcard, hwinj, hvw, hneighbors⟩ :=
    exists_trivalent_graph_subcomplex_model
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let U := Metric.thickening 1 K.space
  have hKU : K.space ⊆ U := Metric.self_subset_thickening zero_lt_one K.space
  have hedge (i : Fin 3) : {v, w i} ∈ L.faces :=
    (hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩
  have hDU (i : Fin 3) :
      (splittingDisk K {v, w i} (hLK (hedge i))).space ⊆ U :=
    (hK.splittingDisk_subset_boundary_graphDualCell K L hLK hcard (hvw i) (hedge i)).trans
      ((boundaryComplex_space_subset 3 (graphDualCell K L (w i))).trans
        ((graphDualCell_space_subset K L (w i)).trans
          ((derivedNeighborhood_space_subset K L).trans hKU)))
  obtain ⟨J, C, f, A, B, hdata, hpairJ, hpairA, hpairB⟩ :=
    hK.exists_piercings_with_pairwise_disjoint_nested_common_neighborhoods K L hLK hcard w
      hwinj hvw hneighbors Metric.isOpen_thickening hDU
  have hAU (i : Fin 3) : A i ⊆ U := by
    rcases hdata i with ⟨-, -, -, -, -, -, -, -, h, -⟩
    exact h
  have hAB (i : Fin 3) :
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space) := by
    rcases hdata i with ⟨-, -, -, -, -, -, -, -, -, h⟩
    exact h
  obtain ⟨δ, hδ, hstable⟩ :=
    exists_perturbation_radius_of_pairwise_disjoint_nested_common_neighborhoods
      K A B J
        (fun _ => (boundaryComplex 3 (graphDualCell K L v)).space)
        (fun i => f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)
      Metric.isOpen_thickening hAB hAU hpairA
  let c := ({v, w 0} : Finset (Fin 5 → ℝ)).centroid ℝ id
  obtain ⟨p, hpJ, hpc⟩ := ((hdata 0).1.isConnected_sdiff_singleton_one c).nonempty
  have hcard0 : ∀ t ∈ L.faces, t.card ≤ ({v, w 0} : Finset (Fin 5 → ℝ)).card := by
    intro t ht
    calc
      t.card ≤ 2 := hcard t ht
      _ = ({v, w 0} : Finset (Fin 5 → ℝ)).card := (Finset.card_pair (hvw 0)).symm
  have hpL : p ∉ L.space := by
    intro hpL
    have hpCentroid :
        p ∈ ({({v, w 0} : Finset (Fin 5 → ℝ)).centroid ℝ id} : Set (Fin 5 → ℝ)) := by
      rw [← splittingDisk_space_inter K L hLK (hedge 0) hcard0]
      exact ⟨(hdata 0).2.1 hpJ, hpL⟩
    exact hpc (by simpa [c] using hpCentroid)
  have hpU : p ∈ U := hDU 0 ((hdata 0).2.1 hpJ)
  obtain ⟨r, hr, hrU, h, hh, hmove, hfix, hfixL, hfixU, hclose⟩ :=
    exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn
      (F := L.space) (U := U) (isPolyhedron_space L).isClosed Metric.isOpen_thickening
      hpU hpL hδ
  obtain ⟨himage, hpairHA, hpairHB⟩ :=
    hstable (fun _ => h) (fun _ x _ => hclose x)
  have hdata' (i : Fin 3) :
      IsPLSphere 1 (J i) ∧
      IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
      C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
      IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
      A i ⊆ U ∧
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space) := by
    rcases hdata i with ⟨hJ, -, -, hf, hCsub, hfixf, hCball, hinter, hAiU, hAiAB⟩
    exact ⟨hJ, hf, hCsub, hfixf, hCball, hinter, hAiU, hAiAB⟩
  refine ⟨K, L, v, w, J, C, f, A, B, U, δ, r, p, h, hKfin, hLfin, hK, hLK,
    hcard, hwinj, hvw, hneighbors, rfl, hdata', hpairJ, hpairA, hpairB, hδ,
    hpJ, hpL, hr, hrU, hh, hmove, hfix, hfixL, hfixU, hclose,
    himage, hpairHA, hpairHB, ?_, ?_⟩
  · intro i
    exact (hAB i).exists_image_open_nesting h
  · intro i
    exact ⟨(hAB i).1.hasImageDerivedNeighborhoodSurfaceTraces h,
      (hAB i).2.1.hasImageDerivedNeighborhoodSurfaceTraces h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
