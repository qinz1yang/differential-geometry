/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldHomeomorphTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialPiece
import DifferentialGeometry.Topology.PiecewiseLinear.TrivalentDualCellPerturbationModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

inductive TrivalentPiercingSetIndex
  | graph
  | circle (i : Fin 3)
  | centralSurface
  | branchSurface (i : Fin 3)
  | outerNeighborhood (i : Fin 3)
  | innerNeighborhood (i : Fin 3)
  deriving DecidableEq, Fintype

open Classical in
noncomputable def trivalentPiercingSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (v : E) (w : Fin 3 → E)
    (J : Fin 3 → Set E) (f : Fin 3 → E → E) (A B : Fin 3 → Set E) :
    TrivalentPiercingSetIndex → Set E
  | .graph => L.space
  | .circle i => J i
  | .centralSurface => (boundaryComplex 3 (graphDualCell K L v)).space
  | .branchSurface i => f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space
  | .outerNeighborhood i => A i
  | .innerNeighborhood i => B i

open Classical in
theorem isPolyhedron_trivalentPiercingSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (v : E) (w : Fin 3 → E)
    (J : Fin 3 → Set E) (f : Fin 3 → E → E) (A B : Fin 3 → Set E)
    (hdata : ∀ i,
      IsPLSphere 1 (J i) ∧
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)) :
    ∀ t, IsPolyhedron (trivalentPiercingSet K L v w J f A B t) := by
  intro t
  cases t with
  | graph =>
      simp only [trivalentPiercingSet]
      exact isPolyhedron_space L
  | circle i =>
      simp only [trivalentPiercingSet]
      exact (hdata i).1.isPolyhedron
  | centralSurface =>
      obtain ⟨R, M, P₀, P₁, hRfin, hMfin, hP₀fin, hP₁fin, hRK, hMJ,
        hP₀space, hP₁space, hP₀R, hP₁R, hMP₀, hMP₁, hA, hAn, hA₀, hA₁,
        hH₀, hH₁⟩ := (hdata 0).2.1
      let _ : Finite P₀.faces := hP₀fin.to_subtype
      simp only [trivalentPiercingSet]
      rw [← hP₀space]
      exact isPolyhedron_space P₀
  | branchSurface i =>
      obtain ⟨R, M, P₀, P₁, hRfin, hMfin, hP₀fin, hP₁fin, hRK, hMJ,
        hP₀space, hP₁space, hP₀R, hP₁R, hMP₀, hMP₁, hA, hAn, hA₀, hA₁,
        hH₀, hH₁⟩ := (hdata i).2.1
      let _ : Finite P₁.faces := hP₁fin.to_subtype
      simp only [trivalentPiercingSet]
      rw [← hP₁space]
      exact isPolyhedron_space P₁
  | outerNeighborhood i =>
      simp only [trivalentPiercingSet]
      exact (hdata i).2.1.isPolyhedron
  | innerNeighborhood i =>
      simp only [trivalentPiercingSet]
      exact (hdata i).2.2.1.isPolyhedron

open Classical in
theorem trivalentPiercingSet_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (v : E) (w : Fin 3 → E) (J : Fin 3 → Set E) (f : Fin 3 → E → E)
    (A B : Fin 3 → Set E)
    (hdata : ∀ i,
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)) :
    ∀ t, trivalentPiercingSet K L v w J f A B t ⊆ K.space := by
  intro t
  cases t with
  | graph =>
      simp only [trivalentPiercingSet]
      exact space_mono_of_faces_subset hLK
  | circle i =>
      obtain ⟨R, M, P₀, P₁, hRfin, hMfin, hP₀fin, hP₁fin, hRK, hMJ,
        hP₀space, hP₁space, hP₀R, hP₁R, hMP₀, hMP₁, hA, hAn, hA₀, hA₁,
        hH₀, hH₁⟩ := (hdata i).1
      simp only [trivalentPiercingSet]
      rw [← hMJ, ← hRK.space_eq]
      exact space_mono_of_faces_subset (hMP₀.trans hP₀R)
  | centralSurface =>
      obtain ⟨R, M, P₀, P₁, hRfin, hMfin, hP₀fin, hP₁fin, hRK, hMJ,
        hP₀space, hP₁space, hP₀R, hP₁R, hMP₀, hMP₁, hA, hAn, hA₀, hA₁,
        hH₀, hH₁⟩ := (hdata 0).1
      simp only [trivalentPiercingSet]
      rw [← hP₀space, ← hRK.space_eq]
      exact space_mono_of_faces_subset hP₀R
  | branchSurface i =>
      obtain ⟨R, M, P₀, P₁, hRfin, hMfin, hP₀fin, hP₁fin, hRK, hMJ,
        hP₀space, hP₁space, hP₀R, hP₁R, hMP₀, hMP₁, hA, hAn, hA₀, hA₁,
        hH₀, hH₁⟩ := (hdata i).1
      simp only [trivalentPiercingSet]
      rw [← hP₁space, ← hRK.space_eq]
      exact space_mono_of_faces_subset hP₁R
  | outerNeighborhood i =>
      simp only [trivalentPiercingSet]
      exact (hdata i).1.subset_ambient
  | innerNeighborhood i =>
      simp only [trivalentPiercingSet]
      exact (hdata i).2.1.subset_ambient

open Classical in
theorem exists_trivalent_graphDualCell_compatible_triangulation_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (hKfin : K.faces.Finite) (hLfin : L.faces.Finite)
        (hK : IsCombinatorialManifold 3 K)
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (A B : Fin 3 → Set (Fin 5 → ℝ)) (U : Set (Fin 5 → ℝ))
        (p : K.space) (h : K.space ≃ₜ K.space)
        (K₀ K₁ : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (q' : (Fin 5 → ℝ) → Fin 5 → ℝ)
        (D : TrivalentPiercingSetIndex → Geometry.SimplicialComplex ℝ (Fin 5 → ℝ)),
      IsPLSphere 3 K.space ∧ L.faces ⊆ K.faces ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      (∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w)) ∧
      U = Metric.thickening 1 K.space ∧
      (∀ i, A i ⊆ U) ∧
      (∀ i,
        IsPLSphere 1 (J i) ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space)) ∧
      IsPLSphere 2 (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
        (graphDualCell K L v)).space ∧
      (∀ i, IsPLSphere 2
        (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
          (graphDualCell K L (w i))).space)) ∧
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
       IsGlueIso K₀ K₁ q q' ∧
       EqOn (simplicialMap K₀ q) q K.space ∧
       (∀ t, (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀
         (trivalentPiercingSet K L v w J f A B t)).space =
           trivalentPiercingSet K L v w J f A B t) ∧
       ∀ t, (D t).faces ⊆ K₁.faces ∧
         IsGlueIso
           (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀
             (trivalentPiercingSet K L v w J f A B t))
           (D t) q q' ∧
         (D t).space = q '' trivalentPiercingSet K L v w J f A B t) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, hKfin, hLfin, hK, v, w, J, C, f, A, B, U, δ,
    hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hdata,
    hpairJ, hpairA, hpairB, hδ, hpert⟩ :=
    exists_trivalent_graphDualCell_carrier_supported_perturbation_model
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
  obtain ⟨p, S, h, g, hpJ, hpL, hS, hSF, hh, hh', hmove, hfix, hfixL, hfixU,
    hclose, hgK, hgOff, hgbij, hgimage, hgmove, hgfixL, hgfixU, hgclose,
    hgA, hgpairA, hgpairB, hnested⟩ := hpert
  have hfamily (i : Fin 3) :
      IsPLSphere 1 (J i) ∧
      IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
        (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
          (graphDualCell K L v)).space
        (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
          (graphDualCell K L (w i))).space) := by
    rcases hdata i with ⟨hJ, hf, hCsub, hfixf, hCball, hinter, hAU, hAB⟩
    exact ⟨hJ, hAB⟩
  have hAU (i : Fin 3) : A i ⊆ U := by
    rcases hdata i with ⟨-, -, -, -, -, -, hi, -⟩
    exact hi
  have hedge (i : Fin 3) : {v, w i} ∈ L.faces :=
    (hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩
  have hv : {v} ∈ L.faces :=
    L.down_closed (hedge 0) (by simp) (Finset.singleton_nonempty v)
  have hcentralSphere : IsPLSphere 2 (boundaryComplex 3 (graphDualCell K L v)).space := by
    let _ : Finite (graphDualCell K L v).faces :=
      (graphDualCell_faces_finite K L v).to_subtype
    exact isPLSphere_boundaryComplex_space_of_isPLBall _
      (hK.isPLBall_graphDualCell K L hLK hcard hv)
  have hbranchSphere (i : Fin 3) :
      IsPLSphere 2 (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space) := by
    let _ : Finite (graphDualCell K L (w i)).faces :=
      (graphDualCell_faces_finite K L (w i)).to_subtype
    have hw : {w i} ∈ L.faces :=
      L.down_closed (hedge i) (by simp) (Finset.singleton_nonempty (w i))
    have hball : IsPLBall 3 (graphDualCell K L (w i)).space :=
      hK.isPLBall_graphDualCell K L hLK hcard hw
    have hf := (hdata i).2.1
    exact (isPLSphere_boundaryComplex_space_of_isPLBall _ hball).of_isPLHomeomorphOn
      (hf.restrict (isPolyhedron_space (boundaryComplex 3 (graphDualCell K L (w i))))
        (boundaryComplex_space_subset 3 (graphDualCell K L (w i))))
  let T := combinatorialPLPieceIn K hK p
  obtain ⟨K₀, K₁, q', D, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue, hsimple,
    hsource, htarget⟩ :=
    T.exists_compatible_isGlueIso_of_homeomorph h hh
      (trivalentPiercingSet K L v w J f A B)
      (isPolyhedron_trivalentPiercingSet K L v w J f A B hfamily)
      (trivalentPiercingSet_subset K L hLK v w J f A B fun i => (hfamily i).2)
  refine ⟨K, L, hKfin, hLfin, hK, v, w, J, f, A, B, U, p, h, K₀, K₁, q', D,
    hKsphere, hLK, hcard, hwinj, hvw, hneighbors, hU, hAU, hfamily, hcentralSphere,
    hbranchSphere,
    hpairA, hpairB, hpJ, hpL, ?_⟩
  exact ⟨hh, hh', hmove, hfixL, hK₀K, hK₀fin, hK₁K, hK₁fin, hglue,
    hsimple, hsource, htarget⟩

end DifferentialGeometry.Topology.PiecewiseLinear
