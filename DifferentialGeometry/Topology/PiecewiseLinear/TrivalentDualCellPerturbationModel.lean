/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellNeighborhoodModel

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
      IsPLSphere 3 K.space ∧ L.faces ⊆ K.faces ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
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
  obtain ⟨K, L, v, w, hKfin, hLfin, hK, hKsphere, hLK, hcard, hwinj, hvw,
    hneighbors⟩ :=
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
  refine ⟨K, L, v, w, J, C, f, A, B, U, δ, r, p, h, hKfin, hLfin, hK, hKsphere,
    hLK, hcard, hwinj, hvw, hneighbors, rfl, hdata', hpairJ, hpairA, hpairB, hδ,
    hpJ, hpL, hr, hrU, hh, hmove, hfix, hfixL, hfixU, hclose,
    himage, hpairHA, hpairHB, ?_, ?_⟩
  · intro i
    exact (hAB i).exists_image_open_nesting h
  · intro i
    exact ⟨(hAB i).1.hasImageDerivedNeighborhoodSurfaceTraces h,
      (hAB i).2.1.hasImageDerivedNeighborhoodSurfaceTraces h⟩

open Classical in
theorem exists_trivalent_graphDualCell_carrier_supported_perturbation_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (hKfin : K.faces.Finite) (hLfin : L.faces.Finite)
        (hK : IsCombinatorialManifold 3 K)
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J C : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (A B : Fin 3 → Set (Fin 5 → ℝ)) (U : Set (Fin 5 → ℝ)) (δ : ℝ),
      IsPLSphere 3 K.space ∧ L.faces ⊆ K.faces ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧
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
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ 0 < δ ∧
      (let _ : Finite K.faces := hKfin.to_subtype
       let _ : Finite L.faces := hLfin.to_subtype
       let _ := combinatorialChartedSpace K hK
       let _ := combinatorialChartedSpace_hasGroupoid K hK
       ∃ (p : K.space) (S : Set K.space) (h : K.space ≃ₜ K.space)
          (g : (Fin 5 → ℝ) → Fin 5 → ℝ),
        (p : Fin 5 → ℝ) ∈ J 0 ∧ (p : Fin 5 → ℝ) ∉ L.space ∧
        IsCompact S ∧
        S ⊆ (Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' (U \ L.space) ∧
        IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h p ≠ p ∧
        EqOn h id Sᶜ ∧
        EqOn h id ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' L.space) ∧
        EqOn h id ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' U)ᶜ ∧
        (∀ x, dist (h x) x < δ) ∧
        (∀ x (hx : x ∈ K.space), g x = (h ⟨x, hx⟩ : K.space)) ∧
        EqOn g id K.spaceᶜ ∧ Function.Bijective g ∧ g '' K.space = K.space ∧
        g p ≠ p ∧ EqOn g id L.space ∧ EqOn g id Uᶜ ∧
        (∀ x, dist (g x) x < δ) ∧
        (∀ i, g '' A i ⊆ U) ∧
        Pairwise (fun i j => Disjoint (g '' A i) (g '' A j)) ∧
        Pairwise (fun i j => Disjoint (g '' B i) (g '' B j)) ∧
        ∀ i, ∃ O : Set K.space,
          IsOpen O ∧
          h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' J i) ⊆ O ∧
          h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' B i) ⊆ O ∧
          O ⊆ h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' A i)) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, v, w, J, C, f, A, B, U, δ, r, p, k,
    hKfin, hLfin, hK, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU,
    hdata, hpairJ, hpairA, hpairB, hδ, hpJ, hpL, hr, hrU,
    hk, hkmove, hkfix, hkfixL, hkfixU, hkclose, hkAU, hkpairA, hkpairB,
    hkopen, hktrace⟩ :=
    exists_trivalent_graphDualCell_relative_supported_perturbation_model
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hJK (i : Fin 3) : J i ⊆ K.space := by
    rcases hdata i with ⟨-, -, -, -, -, -, -, hAB⟩
    rcases hAB.1 with ⟨R, M, P₀, P₁, -, -, -, -, hRK, hMJ, -, -, hP₀R, -, hMP₀, -,
      -, -, -, -⟩
    rw [← hMJ, ← hRK.space_eq]
    exact space_mono_of_faces_subset (hMP₀.trans hP₀R)
  have hpK : p ∈ K.space := hJK 0 hpJ
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
  let F : Set K.space := (Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' L.space
  let V : Set K.space := (Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' U
  let pK : K.space := ⟨p, hpK⟩
  have hF : IsClosed F :=
    (isPolyhedron_space L).isClosed.preimage continuous_subtype_val
  have hV : IsOpen V := by
    change IsOpen ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' U)
    rw [hU]
    exact Metric.isOpen_thickening.preimage continuous_subtype_val
  have hpU : p ∈ U := (hrU (Metric.mem_ball_self hr)).1
  have hpV : pK ∈ V := hpU
  have hpF : pK ∉ F := hpL
  obtain ⟨S, h, hS, hSVF, hh, hhi, hhmove, hhfix, hhfixF, hhfixV, hhclose⟩ :=
    exists_isPL_homeomorph_moves_point_dist_lt_eqOn
      (n := 3) (by norm_num) hF hV hpV hpF hδ
  let g : (Fin 5 → ℝ) → Fin 5 → ℝ := fun x =>
    if hx : x ∈ K.space then (h ⟨x, hx⟩ : K.space) else x
  have hgK (x : Fin 5 → ℝ) (hx : x ∈ K.space) :
      g x = (h ⟨x, hx⟩ : K.space) := by
    simp [g, hx]
  have hgOff : EqOn g id K.spaceᶜ := by
    intro x hx
    have hxK : x ∉ K.space := hx
    simp [g, hxK]
  have hgmem (x : Fin 5 → ℝ) : g x ∈ K.space ↔ x ∈ K.space := by
    by_cases hx : x ∈ K.space
    · simp [g, hx, (h ⟨x, hx⟩).property]
    · simp [g, hx]
  have hginj : Function.Injective g := by
    intro x y hxy
    by_cases hx : x ∈ K.space
    · have hy : y ∈ K.space := (hgmem y).mp (hxy ▸ (hgmem x).mpr hx)
      rw [hgK x hx, hgK y hy] at hxy
      exact congrArg Subtype.val (h.injective (Subtype.ext hxy))
    · have hy : y ∉ K.space := by
        intro hy
        exact hx ((hgmem x).mp (hxy.symm ▸ (hgmem y).mpr hy))
      simpa [g, hx, hy] using hxy
  have hgsurj : Function.Surjective g := by
    intro y
    by_cases hy : y ∈ K.space
    · let x := h.symm ⟨y, hy⟩
      refine ⟨(x : Fin 5 → ℝ), ?_⟩
      rw [hgK x x.property]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩)
    · exact ⟨y, by simp [g, hy]⟩
  have hgimageK : g '' K.space = K.space := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hgmem x).mpr hx
    · intro y hy
      let x := h.symm ⟨y, hy⟩
      refine ⟨(x : Fin 5 → ℝ), x.property, ?_⟩
      rw [hgK x x.property]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩)
  have hgmove : g p ≠ p := by
    intro hgp
    apply hhmove
    apply Subtype.ext
    simpa [pK, hgK p hpK] using hgp
  have hgfixL : EqOn g id L.space := by
    intro x hx
    have hxK : x ∈ K.space := space_mono_of_faces_subset hLK hx
    rw [hgK x hxK]
    exact congrArg Subtype.val (hhfixF hx)
  have hKU : K.space ⊆ U := by
    rw [hU]
    exact Metric.self_subset_thickening zero_lt_one K.space
  have hgfixU : EqOn g id Uᶜ := by
    intro x hx
    apply hgOff
    exact fun hxK => hx (hKU hxK)
  have hgclose : ∀ x, dist (g x) x < δ := by
    intro x
    by_cases hx : x ∈ K.space
    · rw [hgK x hx]
      simpa only [Subtype.dist_eq] using hhclose ⟨x, hx⟩
    · simpa [g, hx] using hδ
  have hgAU : ∀ i, g '' A i ⊆ U := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxK : x ∈ K.space := by
      rcases hdata i with ⟨-, -, -, -, -, -, -, hAB⟩
      exact hAB.1.subset_ambient hx
    exact hKU ((hgmem x).mpr hxK)
  have hgpair (D : Fin 3 → Set (Fin 5 → ℝ))
      (hD : Pairwise fun i j => Disjoint (D i) (D j)) :
      Pairwise fun i j => Disjoint (g '' D i) (g '' D j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := hginj (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hD hij) hx (hxz ▸ hz)
  have hnested : ∀ i, ∃ O : Set K.space,
      IsOpen O ∧
      h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' J i) ⊆ O ∧
      h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' B i) ⊆ O ∧
      O ⊆ h '' ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' A i) := by
    intro i
    rcases hdata i with ⟨-, -, -, -, -, -, -, hAB⟩
    obtain ⟨O, hO, hJO, hBO, hOA⟩ := hAB.2.2
    let O' : Set K.space := (Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' O
    refine ⟨h '' O', h.isOpenMap O' (hO.preimage continuous_subtype_val),
      image_mono ?_, image_mono ?_, image_mono ?_⟩
    · intro x hx
      exact hJO hx
    · intro x hx
      exact (hBO hx).1
    · intro x hx
      exact hOA ⟨hx, x.property⟩
  refine ⟨K, L, hKfin, hLfin, hK, v, w, J, C, f, A, B, U, δ,
    hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hdata,
    hpairJ, hpairA, hpairB, hδ, ?_⟩
  exact ⟨pK, S, h, g, hpJ, hpL, hS, hSVF, hh, hhi, hhmove, hhfix,
    hhfixF, hhfixV, hhclose, hgK, hgOff, ⟨hginj, hgsurj⟩, hgimageK,
    hgmove, hgfixL, hgfixU, hgclose, hgAU, hgpair A hpairA, hgpair B hpairB, hnested⟩

end DifferentialGeometry.Topology.PiecewiseLinear
