import DifferentialGeometry.Topology.Homology.SquareFundamentalChain
import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne
import DifferentialGeometry.Topology.Homology.SphereHurewicz

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralConstSimplex_face (n : ℕ) (x : X) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralConstSimplex (n + 1) x) =
      integralConstSimplex n x := by
  apply (integralSingularSimplexEquiv n X).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (integralConstSimplex (n + 1) x)) t = x
  rw [integralConstSimplex, TopCat.toSSetObjEquiv_δ_apply]
  rfl

theorem integralConstChain_two_boundary (x : X) :
    (integralSingularChains X).d 2 1 (integralConstChain 2 x) = integralConstChain 1 x := by
  have h := integralSimplexChain_boundary_two (X := X) (integralConstSimplex 2 x)
  simp only [integralConstChain] at h ⊢
  rw [h, integralConstSimplex_face, integralConstSimplex_face, integralConstSimplex_face]
  abel

theorem integralConstChain_one_boundary (x : X) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralConstChain 1 x :=
  ⟨integralConstChain 2 x, integralConstChain_two_boundary x⟩

theorem integralPathChain_refl_eq_constChain (x : X) :
    integralPathChain (Path.refl x) = integralConstChain 1 x := by
  have h : integralPathSimplex (Path.refl x) = integralConstSimplex 1 x := by
    apply (integralSingularSimplexEquiv 1 X).injective
    apply ContinuousMap.ext
    intro t
    rw [integralPathSimplex_apply]
    rfl
  rw [integralPathChain, integralConstChain, h]

theorem stdSimplex_one_le_one (t : stdSimplex ℝ (Fin 2)) : (t.val 1 : ℝ) ≤ 1 := by
  have hsum : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
  have h0 : (0 : ℝ) ≤ t.val 0 := t.property.1 0
  linarith

theorem squareAffineMap_one_apply_coe (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) :
    (squareAffineMap 1 ![P, Q] t i : ℝ) =
      (1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ) := by
  have ht : t.val 0 = 1 - t.val 1 := by
    have h : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
    linarith
  fin_cases i <;>
    (rw [squareAffineMap_apply_coe, Fin.sum_univ_two, ht]
     simp)

theorem squareAffineMap_one_eq_squarePoint (P Q : Square) (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![P, Q] t =
      squarePoint
        ⟨(1 - t.val 1) * (P 0 : ℝ) + t.val 1 * (Q 0 : ℝ), by
          have hP := (P 0).property
          have hQ := (Q 0).property
          have ht1 := stdSimplex_one_le_one t
          have ht0 := t.property.1 1
          exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1],
            by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩
        ⟨(1 - t.val 1) * (P 1 : ℝ) + t.val 1 * (Q 1 : ℝ), by
          have hP := (P 1).property
          have hQ := (Q 1).property
          have ht1 := stdSimplex_one_le_one t
          have ht0 := t.property.1 1
          exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1],
            by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩ := by
  funext i
  apply Subtype.ext
  rw [squareAffineMap_one_apply_coe P Q t i]
  fin_cases i <;> rfl

theorem integralSimplexImageGen_squareSegment (f : C(Square, X)) (P Q : Square)
    (σ : integralSingularSimplex 1 X)
    (h : ∀ t : stdSimplex ℝ (Fin 2), f (squareAffineMap 1 ![P, Q] t) =
      (integralSingularSimplexEquiv 1 X σ) t) :
    singularSimplexImageGen 1 f (squareAffineSimplex 1 ![P, Q]) = σ := by
  apply (integralSingularSimplexEquiv 1 X).injective
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.comp_apply]
  exact h t

theorem integralPathChain_squareSegment (f : C(Square, X)) (P Q : Square)
    (σ : integralSingularSimplex 1 X)
    (h : ∀ t : stdSimplex ℝ (Fin 2), f (squareAffineMap 1 ![P, Q] t) =
      (integralSingularSimplexEquiv 1 X σ) t) :
    integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1 ![P, Q])) =
      integralSimplexChain 1 σ := by
  rw [integralSimplexImageGen_squareSegment f P Q σ h]

theorem singularChainImageGen_squareFundamentalChain_boundary (f : C(Square, X)) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 f squareFundamentalChain) =
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareEast, squareNorthEast])) -
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareNorth, squareNorthEast])) +
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareOrigin, squareEast])) -
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareOrigin, squareNorth])) := by
  rw [singularChainImageGen_d_eq, squareFundamentalChain_boundary]
  simp only [map_sub, map_add, singularChainImageGen_simplex, squareSegmentChain]
  abel

def reverseSquareParam : C(Square, unitInterval) where
  toFun z := ⟨(z 0 : ℝ) * (1 - (z 1 : ℝ)), by
    have h0 := (z 0).property
    have h1 := (z 1).property
    exact ⟨by nlinarith [h0.1, h1.1, h1.2], by nlinarith [h0.2, h1.1, h1.2]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_apply 0)).mul
      (continuous_const.sub (continuous_subtype_val.comp (continuous_apply 1)))

def concatSquareParam : C(Square, unitInterval) where
  toFun z := ⟨(z 0 : ℝ) * (1 + (z 1 : ℝ)) / 2, by
    have h0 := (z 0).property
    have h1 := (z 1).property
    have hz1 : (1 : ℝ) + z 1 ≤ 2 := by linarith [h1.2]
    have hmul : (z 0 : ℝ) * (1 + (z 1 : ℝ)) ≤ 1 * 2 :=
      mul_le_mul h0.2 hz1 (by linarith [h1.1]) (by linarith [h0.1])
    exact ⟨by nlinarith [h0.1, h1.1], by linarith⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_subtype_val.comp (continuous_apply 0)).mul
      (continuous_const.add (continuous_subtype_val.comp (continuous_apply 1)))).div_const 2)

def pathReverseSquare {a b : X} (p : Path a b) : C(Square, X) :=
  p.toContinuousMap.comp reverseSquareParam

def pathConcatSquare {a b c : X} (p : Path a b) (q : Path b c) : C(Square, X) :=
  (p.trans q).toContinuousMap.comp concatSquareParam

theorem reverseSquareParam_apply (z : Square) :
    reverseSquareParam z = ⟨(z 0 : ℝ) * (1 - (z 1 : ℝ)), by
      have h0 := (z 0).property
      have h1 := (z 1).property
      exact ⟨by nlinarith [h0.1, h1.1, h1.2], by nlinarith [h0.2, h1.1, h1.2]⟩⟩ := rfl

theorem pathReverseSquare_apply {a b : X} (p : Path a b) (z : Square) :
    pathReverseSquare p z = p (reverseSquareParam z) := rfl

theorem pathConcatSquare_apply {a b c : X} (p : Path a b) (q : Path b c) (z : Square) :
    pathConcatSquare p q z = (p.trans q) (concatSquareParam z) := rfl

theorem reverseSquareParam_squarePoint_zero (s : unitInterval) :
    reverseSquareParam (squarePoint s 0) = s := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem reverseSquareParam_squarePoint_one (s : unitInterval) :
    reverseSquareParam (squarePoint s 1) = 0 := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem reverseSquareParam_squarePoint_left (s : unitInterval) :
    reverseSquareParam (squarePoint 0 s) = 0 := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem reverseSquareParam_squarePoint_right (s : unitInterval) :
    reverseSquareParam (squarePoint 1 s) = ⟨1 - (s : ℝ), by
      have h := s.2
      exact ⟨by linarith [h.2], by linarith [h.1]⟩⟩ := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem concatSquareParam_squarePoint_bottom (s : unitInterval) :
    concatSquareParam (squarePoint s 0) = ⟨(s : ℝ) / 2, by
      have h := s.2
      exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩ := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem concatSquareParam_squarePoint_top (s : unitInterval) :
    concatSquareParam (squarePoint s 1) = s := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem concatSquareParam_squarePoint_left (s : unitInterval) :
    concatSquareParam (squarePoint 0 s) = 0 := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

theorem concatSquareParam_squarePoint_right (s : unitInterval) :
    concatSquareParam (squarePoint 1 s) = ⟨(1 + (s : ℝ)) / 2, by
      have h := s.2
      exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩ := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

def squareInterpCoord (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) : unitInterval :=
  ⟨(1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ), by
    have hP := (P i).property
    have hQ := (Q i).property
    have ht1 := stdSimplex_one_le_one t
    have ht0 := t.property.1 1
    exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1], by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩

theorem squareInterpCoord_apply_coe (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) :
    (squareInterpCoord P Q t i : ℝ) =
      (1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ) := rfl

theorem squareAffineMap_one_eq_squarePoint_coord (P Q : Square) (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![P, Q] t =
      squarePoint (squareInterpCoord P Q t 0) (squareInterpCoord P Q t 1) := by
  rw [squareAffineMap_one_eq_squarePoint]
  rfl

theorem pathReverseSquare_bottom {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint s 0) = p s := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_zero]

theorem pathReverseSquare_top {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint s 1) = p 0 := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_one]

theorem pathReverseSquare_left {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint 0 s) = p 0 := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_left]

theorem pathReverseSquare_right {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint 1 s) = p.symm s := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_right]
  rfl

theorem pathConcatSquare_bottom {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint s 0) = p s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_bottom, Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    push_cast
    ring
  · exfalso
    apply h
    push_cast
    linarith [s.2.2]

theorem pathConcatSquare_top {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint s 1) = (p.trans q) s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_top]

theorem pathConcatSquare_left {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint 0 s) = p 0 := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_left, Path.trans_apply]
  rw [dif_pos (by norm_num)]
  congr 1
  apply Subtype.ext
  push_cast
  ring

theorem pathConcatSquare_right {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint 1 s) = q s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_right, Path.trans_apply]
  split_ifs with h
  · have hs : (s : ℝ) = 0 := by linarith [s.2.1, h]
    have hs' : s = 0 := Subtype.ext hs
    subst hs'
    refine (congrArg p ?_).trans (p.target.trans q.source.symm)
    apply Subtype.ext
    push_cast
    ring
  · congr 1
    apply Subtype.ext
    push_cast
    ring

theorem stdSimplexHomeomorphUnitInterval_coe (t : stdSimplex ℝ (Fin 2)) :
    ((stdSimplexHomeomorphUnitInterval t : unitInterval) : ℝ) = t.val 1 := rfl

theorem squareInterpCoord_origin_east_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareEast t 0 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareEast, squarePoint_zero,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

theorem squareInterpCoord_origin_east_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareEast t 1 = 0 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareEast, squarePoint_one]
  push_cast
  ring

theorem squareInterpCoord_east_northEast_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareEast squareNorthEast t 0 = 1 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareEast, squareNorthEast, squarePoint_zero,
    ]
  push_cast
  ring

theorem squareInterpCoord_east_northEast_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareEast squareNorthEast t 1 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareEast, squareNorthEast, squarePoint_one,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

theorem squareInterpCoord_north_northEast_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareNorth squareNorthEast t 0 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareNorth, squareNorthEast, squarePoint_zero,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

theorem squareInterpCoord_north_northEast_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareNorth squareNorthEast t 1 = 1 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareNorth, squareNorthEast, squarePoint_one]
  push_cast
  ring

theorem squareInterpCoord_origin_north_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareNorth t 0 = 0 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareNorth, squarePoint_zero]
  push_cast
  ring

theorem squareInterpCoord_origin_north_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareNorth t 1 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareNorth, squarePoint_one,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

theorem pathReverseSquare_edge_bottom {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareOrigin, squareEast] t) =
        p (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_east_zero,
    squareInterpCoord_origin_east_one]
  exact pathReverseSquare_bottom p _

theorem pathReverseSquare_edge_right {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareEast, squareNorthEast] t) =
        p.symm (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_east_northEast_zero,
    squareInterpCoord_east_northEast_one]
  exact pathReverseSquare_right p _

theorem pathReverseSquare_edge_top {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareNorth, squareNorthEast] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_north_northEast_zero,
    squareInterpCoord_north_northEast_one]
  exact (pathReverseSquare_top p _).trans (Path.source p)

theorem pathReverseSquare_edge_left {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareOrigin, squareNorth] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_north_zero,
    squareInterpCoord_origin_north_one]
  exact (pathReverseSquare_left p _).trans (Path.source p)

theorem pathConcatSquare_edge_bottom {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareOrigin, squareEast] t) =
        p (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_east_zero,
    squareInterpCoord_origin_east_one]
  exact pathConcatSquare_bottom p q _

theorem pathConcatSquare_edge_right {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareEast, squareNorthEast] t) =
        q (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_east_northEast_zero,
    squareInterpCoord_east_northEast_one]
  exact pathConcatSquare_right p q _

theorem pathConcatSquare_edge_top {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareNorth, squareNorthEast] t) =
        (p.trans q) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_north_northEast_zero,
    squareInterpCoord_north_northEast_one]
  exact pathConcatSquare_top p q _

theorem pathConcatSquare_edge_left {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareOrigin, squareNorth] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_north_zero,
    squareInterpCoord_origin_north_one]
  exact (pathConcatSquare_left p q _).trans (Path.source p)

theorem pathReverseSquare_boundary {a b : X} (p : Path a b) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 (pathReverseSquare p)
      squareFundamentalChain) =
      integralPathChain p.symm - integralConstChain 1 a +
        integralPathChain p - integralConstChain 1 a := by
  have h₁ := integralPathChain_squareSegment (pathReverseSquare p) squareEast squareNorthEast
    (integralPathSimplex p.symm) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathReverseSquare_edge_right p t)
  have h₂ := integralPathChain_squareSegment (pathReverseSquare p) squareNorth squareNorthEast
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathReverseSquare_edge_top p t)
  have h₃ := integralPathChain_squareSegment (pathReverseSquare p) squareOrigin squareEast
    (integralPathSimplex p) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathReverseSquare_edge_bottom p t)
  have h₄ := integralPathChain_squareSegment (pathReverseSquare p) squareOrigin squareNorth
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathReverseSquare_edge_left p t)
  rw [singularChainImageGen_squareFundamentalChain_boundary, h₁, h₂, h₃, h₄]
  rfl

theorem pathConcatSquare_boundary {a b c : X} (p : Path a b) (q : Path b c) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 (pathConcatSquare p q)
      squareFundamentalChain) =
      integralPathChain q - integralPathChain (p.trans q) +
        integralPathChain p - integralConstChain 1 a := by
  have h₁ := integralPathChain_squareSegment (pathConcatSquare p q) squareEast squareNorthEast
    (integralPathSimplex q) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_right p q t)
  have h₂ := integralPathChain_squareSegment (pathConcatSquare p q) squareNorth squareNorthEast
    (integralPathSimplex (p.trans q)) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_top p q t)
  have h₃ := integralPathChain_squareSegment (pathConcatSquare p q) squareOrigin squareEast
    (integralPathSimplex p) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_bottom p q t)
  have h₄ := integralPathChain_squareSegment (pathConcatSquare p q) squareOrigin squareNorth
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathConcatSquare_edge_left p q t)
  rw [singularChainImageGen_squareFundamentalChain_boundary, h₁, h₂, h₃, h₄]
  rfl

theorem exists_integralPathChain_trans_sub_mem_range {a b c : X} (p : Path a b) (q : Path b c) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralPathChain (p.trans q) -
        integralPathChain p - integralPathChain q := by
  refine ⟨-(singularChainImageGen 2 (pathConcatSquare p q) squareFundamentalChain) -
    integralConstChain 2 a, ?_⟩
  rw [map_sub, map_neg, pathConcatSquare_boundary p q, integralConstChain_two_boundary]
  abel

theorem exists_integralPathChain_add_symm_mem_range {a b : X} (p : Path a b) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralPathChain p + integralPathChain p.symm := by
  refine ⟨singularChainImageGen 2 (pathReverseSquare p) squareFundamentalChain +
    (2 : ℤ) • integralConstChain 2 a, ?_⟩
  rw [map_add, map_zsmul, pathReverseSquare_boundary p, integralConstChain_two_boundary]
  abel

theorem integralSingularCycleClass_add (n : ℕ) (z w : integralSingularCycles n X) :
    integralSingularCycleClass n X (z + w) =
      integralSingularCycleClass n X z + integralSingularCycleClass n X w := by
  rw [integralSingularCycleClass, integralSingularCycleClass, integralSingularCycleClass]
  rw [show Submodule.Quotient.mk (z + w) = Submodule.Quotient.mk z + Submodule.Quotient.mk w
    from map_add (Submodule.mkQ _) z w]
  exact map_add _ _ _

theorem integralSingularCycleClass_zsmul (n : ℕ) (k : ℤ) (z : integralSingularCycles n X) :
    integralSingularCycleClass n X (k • z) = k • integralSingularCycleClass n X z := by
  rw [integralSingularCycleClass, integralSingularCycleClass]
  rw [show Submodule.Quotient.mk (k • z) = k • Submodule.Quotient.mk z
    from map_zsmul (Submodule.mkQ _) k z]
  exact map_zsmul _ k _

theorem integralSingularCycleClass_eq_of_sub_mem_range (n : ℕ) (z w : integralSingularCycles n X)
    (h : ((z : (integralSingularChains X).X (n + 1)) -
        (w : (integralSingularChains X).X (n + 1))) ∈
      LinearMap.range ((integralSingularChains X).d (n + 2) (n + 1)).hom) :
    integralSingularCycleClass n X z = integralSingularCycleClass n X w := by
  obtain ⟨c, hc⟩ := h
  have hzw : z - w = integralSingularBoundaryToCycles n X c := by
    apply Subtype.ext
    change ((z : (integralSingularChains X).X (n + 1)) -
      (w : (integralSingularChains X).X (n + 1))) = (integralSingularBoundaryToCycles n X c :
        (integralSingularChains X).X (n + 1))
    rw [integralSingularBoundaryToCycles_coe]
    exact hc.symm
  have hz : z = w + integralSingularBoundaryToCycles n X c := by
    rw [← hzw]
    abel
  rw [hz, integralSingularCycleClass_add, integralSingularCycleClass_boundary, add_zero]

theorem integralPathChain_cycle {x : X} (γ : Path x x) :
    (integralSingularChains X).d 1 0 (integralPathChain γ) = 0 := by
  rw [integralPathChain_boundary, sub_self]

def integralPathLoopClass {x : X} (γ : Path x x) : integralSingularHomology 1 X :=
  integralSingularCycleClass 0 X ⟨integralPathChain γ, integralPathChain_cycle γ⟩

theorem integralPathLoopClass_trans {x : X} (γ δ : Path x x) :
    integralPathLoopClass (γ.trans δ) =
      integralPathLoopClass γ + integralPathLoopClass δ := by
  obtain ⟨w, hw⟩ := exists_integralPathChain_trans_sub_mem_range γ δ
  have hdiff : (integralSingularChains X).d 2 1 w = integralPathChain (γ.trans δ) -
      (integralPathChain γ + integralPathChain δ) := by
    rw [hw]
    abel
  have hsum : (integralSingularChains X).d 1 0
      (integralPathChain γ + integralPathChain δ) = 0 := by
    rw [map_add, integralPathChain_cycle, integralPathChain_cycle, add_zero]
  have hkey := integralSingularCycleClass_eq_of_sub_mem_range 0
    ⟨integralPathChain (γ.trans δ), integralPathChain_cycle (γ.trans δ)⟩
    ⟨integralPathChain γ + integralPathChain δ, hsum⟩ ⟨w, hdiff⟩
  have hz : (⟨integralPathChain γ + integralPathChain δ, hsum⟩ : integralSingularCycles 0 X) =
      (⟨integralPathChain γ, integralPathChain_cycle γ⟩ : integralSingularCycles 0 X) +
        ⟨integralPathChain δ, integralPathChain_cycle δ⟩ := Subtype.ext rfl
  rw [hz, integralSingularCycleClass_add] at hkey
  exact hkey

def simplexSourceVertex (σ : integralSingularSimplex 1 X) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)

def simplexTargetVertex (σ : integralSingularSimplex 1 X) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)

theorem integralVertexChain_eq_zero_simplex (x : X) :
    integralVertexChain x = integralSimplexChain 0 (TopCat.toSSetObj₀Equiv.symm x) := by
  unfold integralVertexChain
  rfl

def integralSourceVertexMap :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 0 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 0) ℕ
    (fun σ => integralVertexChain (simplexSourceVertex σ))

def integralTargetVertexMap :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 0 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 0) ℕ
    (fun σ => integralVertexChain (simplexTargetVertex σ))

theorem integralSourceVertexMap_simplex (σ : integralSingularSimplex 1 X) :
    integralSourceVertexMap (integralSimplexChain 1 σ) =
      integralVertexChain (simplexSourceVertex σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

theorem integralTargetVertexMap_simplex (σ : integralSingularSimplex 1 X) :
    integralTargetVertexMap (integralSimplexChain 1 σ) =
      integralVertexChain (simplexTargetVertex σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

theorem integralTargetVertexMap_sub_sourceVertexMap :
    integralTargetVertexMap - integralSourceVertexMap =
      ((integralSingularChains X).d 1 0).hom := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.sub_apply, integralTargetVertexMap_simplex,
    integralSourceVertexMap_simplex, integralSimplexChain_boundary_one,
    integralSimplexChain_zero_vertex, integralSimplexChain_zero_vertex]
  simp only [simplexTargetVertex, simplexSourceVertex]

def integralReversedPathCone [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 1) ℕ
    (fun σ => integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm)

theorem integralReversedPathCone_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    integralReversedPathCone x (integralSimplexChain 0 σ) =
      integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

def pathLoopOfSimplex [PathConnectedSpace X] (x : X) (σ : integralSingularSimplex 1 X) :
    Path x x :=
  (PathConnectedSpace.somePath x (simplexSourceVertex σ)).trans
    ((integralSimplexPath σ).trans (PathConnectedSpace.somePath x (simplexTargetVertex σ)).symm)

noncomputable def integralPathConeNullHomology [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) : (integralSingularChains X).X 2 :=
  Classical.choose (exists_integralPathChain_add_symm_mem_range
    (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)))

theorem integralPathConeNullHomology_spec [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    (integralSingularChains X).d 2 1 (integralPathConeNullHomology x σ) =
      integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)) +
        integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm :=
  Classical.choose_spec (exists_integralPathChain_add_symm_mem_range
    (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)))

def integralPathConeNullHomotopy [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 2 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 2) ℕ
    (fun σ => integralPathConeNullHomology x σ)

theorem integralPathConeNullHomotopy_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    integralPathConeNullHomotopy x (integralSimplexChain 0 σ) =
      integralPathConeNullHomology x σ := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

theorem integralPathCone_equation [PathConnectedSpace X] (x : X) :
    ((integralSingularChains X).d 2 1).hom.comp (integralPathConeNullHomotopy x) =
      integralVertexPathCone x + integralReversedPathCone x := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply, integralPathConeNullHomotopy_simplex,
    integralPathConeNullHomology_spec, LinearMap.add_apply, integralVertexPathCone_simplex,
    integralReversedPathCone_simplex]

def integralPathLoopChainMap [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 1) ℕ
    (fun σ => integralPathChain (pathLoopOfSimplex x σ))

theorem integralPathLoopChainMap_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 1 X) :
    integralPathLoopChainMap x (integralSimplexChain 1 σ) =
      integralPathChain (pathLoopOfSimplex x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

theorem integralSourceVertexMap_eq_targetVertexMap_of_cycle [PathConnectedSpace X]
    (z : integralSingularCycles 0 X) :
    integralSourceVertexMap (z : (integralSingularChains X).X 1) =
      integralTargetVertexMap (z : (integralSingularChains X).X 1) := by
  have h := LinearMap.congr_fun integralTargetVertexMap_sub_sourceVertexMap
    (z : (integralSingularChains X).X 1)
  rw [LinearMap.sub_apply] at h
  have hz : (integralSingularChains X).d 1 0 (z : (integralSingularChains X).X 1) = 0 := z.property
  rw [hz, sub_eq_zero] at h
  exact h.symm

def HurewiczOneLoopGeneration [PathConnectedSpace X] (x : X) : Prop :=
  ∀ y : integralSingularHomology 1 X,
    y ∈ Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ))

def HurewiczOneVertexPairing [PathConnectedSpace X] (x : X) : Prop :=
  ∀ z : integralSingularCycles 0 X,
    ((z : (integralSingularChains X).X 1) -
      integralPathLoopChainMap x (z : (integralSingularChains X).X 1)) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom

def HurewiczOneMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) (a b : HomotopyGroup (Fin 1) X x),
    sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b

def HurewiczOneKernel (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) (a : HomotopyGroup (Fin 1) X x),
    sphereHurewicz 0 x c a = 0 → a ∈ commutator (HomotopyGroup (Fin 1) X x)

theorem hurewiczOneLoopGeneration_punit (x : PUnit.{u + 1}) : HurewiczOneLoopGeneration x := by
  have hsub : Subsingleton (integralSingularHomology 1 (PUnit.{u + 1})) :=
    integralSingularHomology_subsingleton_of_contractible (X := PUnit.{u + 1}) 1 (by omega)
  intro y
  rw [@Subsingleton.elim _ hsub y 0]
  exact Submodule.zero_mem _

noncomputable def abelianization_equiv_of_surjective_ker_eq_commutator {G : Type*} [Group G]
    {A : Type*} [CommGroup A] (f : G →* A) (hsurj : Function.Surjective f)
    (hker : f.ker = commutator G) : Abelianization G ≃* A :=
  QuotientGroup.liftEquiv (commutator G) hsurj hker.symm

def hurewiczSphereMonoidHom (x : X)
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b) :
    HomotopyGroup (Fin 1) X x →* Multiplicative (integralSingularHomology 1 X) where
  toFun a := Multiplicative.ofAdd (sphereHurewicz 0 x c a)
  map_one' := by rw [sphereHurewicz_one]; rfl
  map_mul' a b := by rw [hmul]; rfl

theorem abelianizationHomotopyGroupOne_equiv_of_hurewiczOne [PathConnectedSpace X] (x : X)
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b)
    (hsurj : Function.Surjective (sphereHurewicz 0 x c))
    (hker : ∀ a : HomotopyGroup (Fin 1) X x, sphereHurewicz 0 x c a = 0 →
      a ∈ commutator (HomotopyGroup (Fin 1) X x)) :
    Nonempty (Abelianization (HomotopyGroup (Fin 1) X x) ≃*
      Multiplicative (integralSingularHomology 1 X)) := by
  refine ⟨abelianization_equiv_of_surjective_ker_eq_commutator
    (hurewiczSphereMonoidHom x c hmul) ?_ ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := hsurj (Multiplicative.toAdd y)
    exact ⟨a, by simpa [hurewiczSphereMonoidHom] using congrArg Multiplicative.ofAdd ha⟩
  · refine le_antisymm ?_ (Abelianization.commutator_subset_ker _)
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact hker a (by simpa [hurewiczSphereMonoidHom] using ha)


end DifferentialGeometry.Topology
