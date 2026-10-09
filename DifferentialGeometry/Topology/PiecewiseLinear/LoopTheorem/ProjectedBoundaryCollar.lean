/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifoldTopology
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedCellInDouble

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_bicollar_glued₂_space_in_double
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (p : K.space) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    IsPolyhedralManifoldWithBoundary (n := 3) 3 C ∧
    IsPolyhedralManifold (n := 3) 2 (frontier C) ∧
    Topology.IsTwoSided (frontier C) ∧
    ∀ U : Set (double 3 K).space, U ∈ 𝓝ˢ (frontier C) →
      ∃ (T : PLPiece 3 (double 3 K).space (frontier C)) (W : Set (double 3 K).space)
        (B : PLPieceIn ((EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ) 3 (double 3 K).space W)
        (ρ : (frontier C) × Icc (-1 : ℝ) 1 ≃ₜ W),
        W ⊆ U ∧ W ∈ 𝓝ˢ (frontier C) ∧
        B.complex.space = T.piece.complex.space ×ˢ Icc (-1 : ℝ) 1 ∧
        (∀ (x : T.piece.complex.space) (t : Icc (-1 : ℝ) 1),
          (ρ (⟨T.piece.map x, T.piece.bijOn.mapsTo x.property⟩, t) : (double 3 K).space) =
            B.map (x, t)) ∧
        ∀ x : frontier C, (ρ (x, ⟨0, by norm_num⟩) : (double 3 K).space) = x := by
  classical
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L :=
    isCombinatorialManifold_double_succ_succ K hK
  let _ := combinatorialChartedSpace L hL
  let _ := combinatorialChartedSpace_hasGroupoid L hL
  let R := boundaryRelSubdivision 3 K
  let A := glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id
  let _ : Finite R.faces := (boundaryRelSubdivision_faces_finite 3 K).to_subtype
  let _ : Finite L.faces := (gluedComplex_faces_finite R K
    (isGlueIso_id (PiecewiseLinear.boundaryComplex 3 K)) (boundaryComplex_faces_subset 3 K)
      (boundaryComplex_full_boundaryRelSubdivision 3 K)).to_subtype
  let _ : Finite A.faces :=
    (glued₂_faces_finite K (PiecewiseLinear.boundaryComplex 3 K) id).to_subtype
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : L.space → E × E × ℝ) ⁻¹' (ι '' K.space)
  have hι : IsPLHomeomorphOn ι K.space A.space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
      (glueSnd E E) (fun _ _ _ _ => rfl)
  have hA : IsCombinatorialManifoldWithBoundary 3 A := hK.of_isPLHomeomorphOn hι
  let _ : DecidableEq (E × E × ℝ) := Classical.decEq _
  have hAL : A.faces ⊆ L.faces := fun _ hs => Or.inr hs
  have hAK : A.space ⊆ L.space := space_mono_of_faces_subset hAL
  let q : L.space := ⟨ι p, hAK (hι.bijOn.mapsTo p.property)⟩
  let P := combinatorialPLPieceIn L hL q
  have hPval (x : E × E × ℝ) (hx : x ∈ L.space) : (P.map x : E × E × ℝ) = x := by
    simp only [P, combinatorialPLPieceIn, dite_eq_left hx]
  have himage : P.map '' A.space = C := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (P.map z : E × E × ℝ) ∈ ι '' K.space
      rw [hPval z (hAK hz), hι.image_eq]
      exact hz
    · intro hx
      have hxA : (x : E × E × ℝ) ∈ A.space := hι.image_eq.subset hx
      exact ⟨x, hxA, Subtype.ext (hPval x x.property)⟩
  let PA := P.restrict A hAL
  have hC : IsPolyhedralManifoldWithBoundary (n := 3) 3 C := by
    rw [← himage]
    exact isPolyhedralManifoldWithBoundary_of_pieceIn PA hA
  have hBd : IsPolyhedralManifold (n := 3) 2 (frontier C) := by
    have hfront : frontier C = P.map '' (PiecewiseLinear.boundaryComplex 3 A).space := by
      rw [← himage]
      exact PA.frontier_eq_image_boundaryComplex hA
    rw [hfront]
    let PB := P.restrict (PiecewiseLinear.boundaryComplex 3 A)
      ((boundaryComplex_faces_subset 3 A).trans hAL)
    apply isPolyhedralManifold_of_pieceIn PB
    simpa only [PB, PLPieceIn.restrict_complex] using isCombinatorialManifold_boundaryComplex A hA
  have htwo : Topology.IsTwoSided (frontier C) := hC.isTwoSided_frontier
  exact ⟨hC, hBd, htwo, fun U hU => hBd.exists_bicollar htwo hU⟩

namespace NormalSystem

open Classical in
theorem exists_boundary_bicollar_in_double (S : NormalSystem E) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    IsPolyhedralManifoldWithBoundary (n := 3) 3 C ∧
    IsPolyhedralManifold (n := 3) 2 (frontier C) ∧
    Topology.IsTwoSided (frontier C) ∧
    ∀ U : Set (double 3 K).space, U ∈ 𝓝ˢ (frontier C) →
      ∃ (T : PLPiece 3 (double 3 K).space (frontier C)) (W : Set (double 3 K).space)
        (B : PLPieceIn ((EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ) 3 (double 3 K).space W)
        (ρ : (frontier C) × Icc (-1 : ℝ) 1 ≃ₜ W),
        W ⊆ U ∧ W ∈ 𝓝ˢ (frontier C) ∧
        B.complex.space = T.piece.complex.space ×ˢ Icc (-1 : ℝ) 1 ∧
        (∀ (x : T.piece.complex.space) (t : Icc (-1 : ℝ) 1),
          (ρ (⟨T.piece.map x, T.piece.bijOn.mapsTo x.property⟩, t) : (double 3 K).space) =
            B.map (x, t)) ∧
        ∀ x : frontier C, (ρ (x, ⟨0, by norm_num⟩) : (double 3 K).space) = x := by
  classical
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  apply exists_bicollar_glued₂_space_in_double K S.isManifold
  exact ⟨S.basepoint, boundaryComplex_space_subset 3 K
    (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex S.basepoint.property)⟩

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
