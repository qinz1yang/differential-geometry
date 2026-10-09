/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleNeighborhoodTransport
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellCompatibleTriangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_trivalent_graphDualCell_compatible_nested_neighborhood_model :
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
         (simplicialMap K₀ q '' B i) (simplicialMap K₀ q '' B j))) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, hKfin, hLfin, hK, v, w, J, f, A₀, B₀, U, p, h, K₀, K₁,
    q', D, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hfamily,
    hcentralSphere,
    hbranchSphere,
    hpairA₀, hpairB₀, hpJ, hpL, htri⟩ :=
    exists_trivalent_graphDualCell_compatible_triangulation_model
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
    (∀ t, (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀
      (trivalentPiercingSet K L v w J f A₀ B₀ t)).space =
        trivalentPiercingSet K L v w J f A₀ B₀ t) ∧
    ∀ t, (D t).faces ⊆ K₁.faces ∧
      IsGlueIso
        (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀
          (trivalentPiercingSet K L v w J f A₀ B₀ t))
        (D t) q q' ∧
      (D t).space = q '' trivalentPiercingSet K L v w J f A₀ B₀ t at htri
  obtain ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    -, -⟩ := htri
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  have hgeometry (i : Fin 3) :
      J i ⊆ K₀.space ∧
      (boundaryComplex 3 (graphDualCell K L v)).space ⊆ K₀.space ∧
      f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space ⊆ K₀.space ∧
      J i ⊆ (boundaryComplex 3 (graphDualCell K L v)).space ∧
      J i ⊆ f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space := by
    obtain ⟨R, M, P₀, P₁, -, -, -, -, hRK, hMJ, hP₀space, hP₁space,
      hP₀R, hP₁R, hMP₀, hMP₁, -⟩ := (hfamily i).2.1
    have hS₀K : (boundaryComplex 3 (graphDualCell K L v)).space ⊆ K.space := by
      rw [← hP₀space, ← hRK.space_eq]
      exact space_mono_of_faces_subset hP₀R
    have hS₁K : f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space ⊆ K.space := by
      rw [← hP₁space, ← hRK.space_eq]
      exact space_mono_of_faces_subset hP₁R
    have hJS₀ : J i ⊆ (boundaryComplex 3 (graphDualCell K L v)).space := by
      rw [← hMJ, ← hP₀space]
      exact space_mono_of_faces_subset hMP₀
    have hJS₁ : J i ⊆ f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space := by
      rw [← hMJ, ← hP₁space]
      exact space_mono_of_faces_subset hMP₁
    rw [hK₀K.space_eq]
    exact ⟨hJS₀.trans hS₀K, hS₀K, hS₁K, hJS₀, hJS₁⟩
  choose O hOopen hJO hOKA₀ using fun i =>
    mem_nhdsSetWithin.mp (hfamily i).2.1.mem_nhdsSetWithin
  choose V hVopen hJV hVKB₀ using fun i =>
    mem_nhdsSetWithin.mp (hfamily i).2.2.1.mem_nhdsSetWithin
  choose A B hAB using fun i =>
    hglue.exists_nested_common_annular_derivedNeighborhood_transport
      (hfamily i).1 hcentralSphere (hbranchSphere i)
      (hgeometry i).1 (hgeometry i).2.1 (hgeometry i).2.2.1
      (hgeometry i).2.2.2.1 (hgeometry i).2.2.2.2
      (hOopen i) (hJO i) (hVopen i) (hJV i)
  have hAold (i : Fin 3) : A i ⊆ A₀ i := by
    intro x hx
    apply hOKA₀ i
    exact ⟨(hAB i).2.1 hx, hK₀K.space_eq.subset ((hAB i).1.1.subset_ambient hx)⟩
  have hBold (i : Fin 3) : B i ⊆ B₀ i := by
    intro x hx
    apply hVKB₀ i
    exact ⟨(hAB i).2.2.1 hx, hK₀K.space_eq.subset ((hAB i).1.2.1.subset_ambient hx)⟩
  have hAU (i : Fin 3) : A i ⊆ U := (hAold i).trans (hA₀U i)
  have hpairA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    exact (hpairA₀ hij).mono (hAold i) (hAold j)
  have hpairB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    exact (hpairB₀ hij).mono (hBold i) (hBold j)
  have hpairImage (C : Fin 3 → Set (Fin 5 → ℝ))
      (hC : ∀ i, C i ⊆ K₀.space)
      (hpairC : Pairwise fun i j => Disjoint (C i) (C j)) :
      Pairwise fun i j => Disjoint
        (simplicialMap K₀ q '' C i) (simplicialMap K₀ q '' C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := hglue.bijOn_left.injOn (hC i hx) (hC j hz) (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hpairC hij) hx (hxz ▸ hz)
  have hpairA' := hpairImage A (fun i => (hAB i).1.1.subset_ambient) hpairA
  have hpairB' := hpairImage B (fun i => (hAB i).1.2.1.subset_ambient) hpairB
  refine ⟨K, L, hKfin, hLfin, hK, v, w, J, f, p, h, K₀, K₁, q', U,
    A₀, B₀, A, B, hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hA₀U, hAU,
    hfamily,
    hpairA₀, hpairB₀, hpairA, hpairB,
    hpJ, hpL, ?_⟩
  exact ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    fun i => ⟨(hAB i).1, hAold i, hBold i, (hAB i).2.2.2⟩, hpairA', hpairB'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
