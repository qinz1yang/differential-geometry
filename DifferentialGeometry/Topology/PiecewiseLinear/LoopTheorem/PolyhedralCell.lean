/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]

theorem PLPieceIn.exists_nonsingular_two_cell_of_isPLBall
    {Y : Set X} (T : PLPieceIn E 3 X Y) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hD : D ⊆ T.complex.space) :
    ∃ A : SingularTwoCell X, A.IsNonsingular ∧ A '' A.domain = T.map '' D ∧
      Set.range A.boundary = T.map '' (r '' stdSimplexBoundary 2) := by
  classical
  obtain ⟨V, hV, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  have hP : IsPLBall 2 (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isPLBall_convexHull_of_affineIndependent V hV hcard
  obtain ⟨p, hp⟩ := hP
  let P := convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 2)))
  let f := r ∘ Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hf : IsPLHomeomorphOn f P D := hp.symm.trans hr
  have hfK : MapsTo f P T.complex.space := fun x hx => hD (hf.bijOn.mapsTo hx)
  let A : SingularTwoCell X :=
    { domain := P
      isPLBall_domain := ⟨p, hp⟩
      toFun := T.map ∘ f
      isPLOn := T.isPLOn_comp hf.isPiecewiseAffineOn hfK }
  refine ⟨A, T.bijOn.injOn.comp hf.bijOn.injOn hfK, ?_, ?_⟩
  · change (T.map ∘ f) '' P = T.map '' D
    rw [image_comp, hf.image_eq]
  · have hfront : p '' stdSimplexBoundary 2 = frontier P :=
      IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier (n := 1) hp
    change Set.range ((T.map ∘ f) ∘ (Subtype.val : frontier P → _)) = _
    rw [range_comp, Subtype.range_coe, ← hfront, image_image, image_image]
    apply Set.EqOn.image_eq
    intro x hx
    change T.map (r (Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (p x))) = T.map (r x)
    rw [hp.bijOn.invOn_invFunOn.1 hx.1]

theorem exists_nonsingular_two_cell_of_isPLBall_in_combinatorial_manifold
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hD : D ⊆ K.space) :
    letI := combinatorialChartedSpace K hK
    ∃ A : SingularTwoCell K.space, A.IsNonsingular ∧
      Subtype.val '' (A '' A.domain) = D ∧
      Set.range (fun x => (A.boundary x : E)) = r '' stdSimplexBoundary 2 := by
  classical
  let _ := combinatorialChartedSpace K hK
  obtain ⟨p, hp⟩ := (show IsPLBall 2 D from ⟨r, hr⟩).nonempty
  let T := combinatorialPLPieceIn K hK ⟨p, hD hp⟩
  have hval (x : E) (hx : x ∈ K.space) : (T.map x : E) = x := by
    simp only [T, combinatorialPLPieceIn, dite_eq_left hx]
  have himage (S : Set E) (hS : S ⊆ K.space) : Subtype.val '' (T.map '' S) = S := by
    rw [image_image]
    have h : EqOn ((Subtype.val : K.space → E) ∘ T.map) id S :=
      fun x hx => hval x (hS hx)
    exact h.image_eq.trans (image_id S)
  obtain ⟨A, hA, hAD, hboundary⟩ := T.exists_nonsingular_two_cell_of_isPLBall hr hD
  refine ⟨A, hA, ?_, ?_⟩
  · rw [hAD]
    exact himage D hD
  · change Set.range ((Subtype.val : K.space → E) ∘ A.boundary) = _
    rw [range_comp, hboundary]
    apply himage
    rintro _ ⟨x, hx, rfl⟩
    exact hD (hr.bijOn.mapsTo hx.1)

end DifferentialGeometry.Topology.PiecewiseLinear
