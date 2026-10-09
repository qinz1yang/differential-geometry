/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteHomeomorphTower
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellSolidTorusNeighborhoods

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_trivalent_graphDualCell_locallyFinite_modification_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (hKfin : K.faces.Finite) (hLfin : L.faces.Finite)
        (hK : IsCombinatorialManifold 3 K)
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (p : K.space) (h : K.space ≃ₜ K.space)
        (K₀ K₁ : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (q' : (Fin 5 → ℝ) → Fin 5 → ℝ)
        (U : Set (Fin 5 → ℝ)) (A₀ B₀ A B : Fin 3 → Set (Fin 5 → ℝ)),
      IsPLSphere 3 K.space ∧ L.faces ⊆ K.faces ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      (∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w)) ∧
      U = Metric.thickening 1 K.space ∧
      (∀ i, A₀ i ⊆ U) ∧ (∀ i, A i ⊆ U) ∧
      (∀ i, IsPLSphere 1 (J i) ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A₀ i) (B₀ i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space)) ∧
      Pairwise (fun i j => Disjoint (A₀ i) (A₀ j)) ∧
      Pairwise (fun i j => Disjoint (B₀ i) (B₀ j)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (p : Fin 5 → ℝ) ∈ J 0 ∧ (p : Fin 5 → ℝ) ∉ L.space ∧
      (let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
       let _ : Finite K.faces := hKfin.to_subtype
       let _ : Finite L.faces := hLfin.to_subtype
       let _ := combinatorialChartedSpace K hK
       let _ := combinatorialChartedSpace_hasGroupoid K hK
       let _ : Nonempty K.space := ⟨p⟩
       let T := combinatorialPLPieceIn K hK p
       let q := Function.invFunOn T.map T.complex.space ∘
         (h : K.space → K.space) ∘ T.map
       IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h p ≠ p ∧
       EqOn h id ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' L.space) ∧
       IsSubdivision K₀ K ∧ K₀.faces.Finite ∧
       IsSubdivision K₁ K ∧ K₁.faces.Finite ∧
       IsGlueIso K₀ K₁ q q' ∧ EqOn (simplicialMap K₀ q) q K.space ∧
       (∀ i,
         IsNestedCommonAnnularDerivedNeighborhood K₀ (A i) (B i) (J i)
           (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
             (graphDualCell K L v)).space
           (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
             (graphDualCell K L (w i))).space) ∧
         A i ⊆ A₀ i ∧ B i ⊆ B₀ i ∧
         IsNestedCommonAnnularDerivedNeighborhood K₁
           (simplicialMap K₀ q '' A i) (simplicialMap K₀ q '' B i)
           (simplicialMap K₀ q '' J i)
           (simplicialMap K₀ q ''
             (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
               (graphDualCell K L v)).space)
           (simplicialMap K₀ q ''
             (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
               (graphDualCell K L (w i))).space))) ∧
       Pairwise (fun i j => Disjoint
         (simplicialMap K₀ q '' A i) (simplicialMap K₀ q '' A j)) ∧
       Pairwise (fun i j => Disjoint
         (simplicialMap K₀ q '' B i) (simplicialMap K₀ q '' B j)) ∧
       (∀ i, IsParametrizedSolidTorusTransport (simplicialMap K₀ q) (B i)) ∧
        ∃ (P : PLPiece 3 K.space Set.univ)
            (S : PLHomeomorphIncrementSystem
            (LocallyFinitePieceTower.prependEmpty (LocallyFinitePieceTower.ofPiece P))),
         S.step 0 = h ∧
         S.toCompatibleTower.stage 1 = h ∧
         IsPL 3 3 S.toCompatibleTower.limitHomeomorph ∧
         S.toCompatibleTower.limitHomeomorph p ≠ p ∧
         EqOn S.toCompatibleTower.limitHomeomorph id
           ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' L.space) ∧
         (∀ C : Set K.space, IsCompact C →
           ∀ᶠ i in atTop,
             EqOn S.toCompatibleTower.limitHomeomorph (S.toCompatibleTower.stage i) C)) := by
  obtain ⟨K, L, hKfin, hLfin, hK, v, w, J, f, p, h, K₀, K₁, q', U,
    A₀, B₀, A, B, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hAU,
    hfamily, hpairA₀, hpairB₀, hpairA, hpairB, hpJ, hpL, hdata⟩ :=
    exists_trivalent_graphDualCell_compatible_solid_torus_neighborhood_model
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
  let _ : Nonempty K.space := ⟨p⟩
  let T := combinatorialPLPieceIn K hK p
  let q := Function.invFunOn T.map T.complex.space ∘
    (h : K.space → K.space) ∘ T.map
  change IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h p ≠ p ∧
    EqOn h id ((Subtype.val : K.space → Fin 5 → ℝ) ⁻¹' L.space) ∧
    IsSubdivision K₀ K ∧ K₀.faces.Finite ∧ IsSubdivision K₁ K ∧ K₁.faces.Finite ∧
    IsGlueIso K₀ K₁ q q' ∧ EqOn (simplicialMap K₀ q) q K.space ∧
    (∀ i,
      IsNestedCommonAnnularDerivedNeighborhood K₀ (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space) ∧
      A i ⊆ A₀ i ∧ B i ⊆ B₀ i ∧
      IsNestedCommonAnnularDerivedNeighborhood K₁
        (simplicialMap K₀ q '' A i) (simplicialMap K₀ q '' B i)
        (simplicialMap K₀ q '' J i)
        (simplicialMap K₀ q '' (boundaryComplex 3 (graphDualCell K L v)).space)
        (simplicialMap K₀ q ''
          (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space))) ∧
    Pairwise (fun i j => Disjoint
      (simplicialMap K₀ q '' A i) (simplicialMap K₀ q '' A j)) ∧
    Pairwise (fun i j => Disjoint
      (simplicialMap K₀ q '' B i) (simplicialMap K₀ q '' B j)) ∧
    (∀ i, IsParametrizedSolidTorusTransport (simplicialMap K₀ q) (B i)) at hdata
  obtain ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    htransport, hpairA', hpairB', hsolid⟩ := hdata
  obtain ⟨P⟩ := T.exists_pLPiece
  let S := PLHomeomorphIncrementSystem.single P h hh
  have hlimit : (S.toCompatibleTower.limitHomeomorph : K.space → K.space) = h :=
    PLHomeomorphIncrementSystem.limitHomeomorph_single_eq P h hh
  refine ⟨K, L, hKfin, hLfin, hK, v, w, J, f, p, h, K₀, K₁, q', U,
    A₀, B₀, A, B, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hAU,
    hfamily, hpairA₀, hpairB₀, hpairA, hpairB, hpJ, hpL, hh, hh', hmove, hfixL,
    hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple, htransport, hpairA', hpairB',
    hsolid, P, S, rfl, ?_, S.toCompatibleTower.isPL_limitHomeomorph, ?_, ?_, ?_⟩
  · ext x
    rfl
  · rw [hlimit]
    exact hmove
  · intro x hx
    rw [hlimit]
    exact hfixL hx
  · intro C hC
    exact S.toCompatibleTower.eventually_eqOn_limitHomeomorph_of_isCompact hC

end DifferentialGeometry.Topology.PiecewiseLinear
