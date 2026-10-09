/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleSolidTorusTransport
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellTransportedNeighborhoods

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_trivalent_graphDualCell_compatible_solid_torus_neighborhood_model :
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
      (∀ i, A₀ i ⊆ U) ∧
      (∀ i, A i ⊆ U) ∧
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
       ∀ i, IsParametrizedSolidTorusTransport (simplicialMap K₀ q) (B i)) := by
  obtain ⟨K, L, hKfin, hLfin, hK, v, w, J, f, p, h, K₀, K₁, q', U,
    A₀, B₀, A, B, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hAU,
    hfamily, hpairA₀, hpairB₀, hpairA, hpairB, hpJ, hpL, hdata⟩ :=
    exists_trivalent_graphDualCell_compatible_nested_neighborhood_model
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
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
      (simplicialMap K₀ q '' B i) (simplicialMap K₀ q '' B j)) at hdata
  obtain ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    htransport, hpairA', hpairB'⟩ := hdata
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  have hK₀ : IsCombinatorialManifoldWithBoundary 3 K₀ :=
    (hK.of_isSubdivision hK₀K).isCombinatorialManifoldWithBoundary
  have hK₁ : IsCombinatorialManifoldWithBoundary 3 K₁ :=
    (hK.of_isSubdivision hK₁K).isCombinatorialManifoldWithBoundary
  have horK : IsOrientable 3 K := isOrientable_of_isPLSphere hKsphere
  have horK₀ : IsOrientable 3 K₀ :=
    horK.subdivision hK.isCombinatorialManifoldWithBoundary hK₀K
  have horK₁ : IsOrientable 3 K₁ :=
    horK.subdivision hK.isCombinatorialManifoldWithBoundary hK₁K
  have hsolid (i : Fin 3) :
      IsParametrizedSolidTorusTransport (simplicialMap K₀ q) (B i) := by
    have hJ' : IsPLSphere 1 (simplicialMap K₀ q '' J i) :=
      (hfamily i).1.of_isPLHomeomorphOn
        (hglue.isPLHomeomorphOn.restrict (hfamily i).1.isPolyhedron
          (htransport i).1.1.circle_subset_ambient)
    exact (htransport i).1.2.1.isParametrizedSolidTorusTransport
      (htransport i).2.2.2.2.1 hK₀ horK₀ hK₁ horK₁ (hfamily i).1 hJ'
  refine ⟨K, L, hKfin, hLfin, hK, v, w, J, f, p, h, K₀, K₁, q', U,
    A₀, B₀, A, B, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hAU,
    hfamily, hpairA₀, hpairB₀, hpairA, hpairB, hpJ, hpL, ?_⟩
  exact ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    htransport, hpairA', hpairB', hsolid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
