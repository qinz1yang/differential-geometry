import DifferentialGeometry.Geometry.Curvature.DimensionThree.UhlReaction3
import Mathlib.Tactic.Positivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Dim3Reaction

open scoped BigOperators

def ricciFromSectional3 (K12 K13 K23 : Real) (i j : Fin 3) : Real :=
  if i = j then
    if i = 0 then K12 + K13 else if i = 1 then K12 + K23 else K13 + K23
  else 0

theorem ricciFromSectional3_symm (K12 K13 K23 : Real) (i j : Fin 3) :
    ricciFromSectional3 K12 K13 K23 i j =
      ricciFromSectional3 K12 K13 K23 j i := by
  fin_cases i <;> fin_cases j <;> simp [ricciFromSectional3]

def bivectorCoordinate3 (a b : Fin 3) (v w : Fin 3 → Real) : Real :=
  v a * w b - v b * w a

def curvatureTensorEval3
    (A : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (v w z u : Fin 3 → Real) : Real :=
  ∑ a, ∑ b, ∑ c, ∑ d, v a * w b * z c * u d * A a b c d

def curvatureOperatorQuadraticEval3 {n : Nat}
    (A : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) : Real :=
  ∑ i, ∑ j, c i * c j * curvatureTensorEval3 A (v i) (w i) (w j) (v j)

theorem curvatureTensorEval3_rm (K12 K13 K23 : Real)
    (v w z u : Fin 3 → Real) :
    curvatureTensorEval3 (rm (ricciFromSectional3 K12 K13 K23)) v w z u =
      K12 * bivectorCoordinate3 0 1 v w * bivectorCoordinate3 0 1 u z +
      K13 * bivectorCoordinate3 0 2 v w * bivectorCoordinate3 0 2 u z +
      K23 * bivectorCoordinate3 1 2 v w * bivectorCoordinate3 1 2 u z := by
  unfold curvatureTensorEval3 rm ricciFromSectional3 sc kd bivectorCoordinate3
  simp [Fin.sum_univ_three]
  ring

private theorem weighted_sum_square {n : Nat}
    (c a : Fin n → Real) (K : Real) :
    (∑ i, ∑ j, c i * c j * (K * a i * a j)) =
      K * (∑ i, c i * a i) ^ 2 := by
  rw [sq, Fintype.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem curvatureOperatorQuadraticEval3_rm {n : Nat}
    (K12 K13 K23 : Real) (c : Fin n → Real)
    (v w : Fin n → Fin 3 → Real) :
    curvatureOperatorQuadraticEval3
        (rm (ricciFromSectional3 K12 K13 K23)) c v w =
      K12 * (∑ i, c i * bivectorCoordinate3 0 1 (v i) (w i)) ^ 2 +
      K13 * (∑ i, c i * bivectorCoordinate3 0 2 (v i) (w i)) ^ 2 +
      K23 * (∑ i, c i * bivectorCoordinate3 1 2 (v i) (w i)) ^ 2 := by
  unfold curvatureOperatorQuadraticEval3
  simp_rw [curvatureTensorEval3_rm, mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j,
      c i * c j * (K12 * bivectorCoordinate3 0 1 (v i) (w i) *
        bivectorCoordinate3 0 1 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 0 1 (v i) (w i)) K12]
  rw [show (∑ i, ∑ j,
      c i * c j * (K13 * bivectorCoordinate3 0 2 (v i) (w i) *
        bivectorCoordinate3 0 2 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 0 2 (v i) (w i)) K13]
  rw [show (∑ i, ∑ j,
      c i * c j * (K23 * bivectorCoordinate3 1 2 (v i) (w i) *
        bivectorCoordinate3 1 2 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 1 2 (v i) (w i)) K23]

theorem curvatureOperatorQuadraticEval3_rm_nonneg {n : Nat}
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) :
    0 ≤ curvatureOperatorQuadraticEval3
      (rm (ricciFromSectional3 K12 K13 K23)) c v w := by
  rw [curvatureOperatorQuadraticEval3_rm]
  positivity

def sectionalReaction12 (K12 K13 K23 : Real) : Real :=
  2 * (K12 ^ 2 + K13 * K23)

def sectionalReaction13 (K12 K13 K23 : Real) : Real :=
  2 * (K13 ^ 2 + K12 * K23)

def sectionalReaction23 (K12 K13 K23 : Real) : Real :=
  2 * (K23 ^ 2 + K12 * K13)

def curvatureTensorReaction3 (K12 K13 K23 : Real)
    (a b c d : Fin 3) : Real :=
  -2 * Bsharp (ricciFromSectional3 K12 K13 K23) a b c d

theorem curvatureTensorReaction3_eq_rm (K12 K13 K23 : Real)
    (a b c d : Fin 3) :
    curvatureTensorReaction3 K12 K13 K23 a b c d =
      rm (ricciFromSectional3
        (sectionalReaction12 K12 K13 K23)
        (sectionalReaction13 K12 K13 K23)
        (sectionalReaction23 K12 K13 K23)) a b c d := by
  let R := ricciFromSectional3 K12 K13 K23
  have hsym : ∀ i j, R i j = R j i := by
    exact ricciFromSectional3_symm K12 K13 K23
  rw [curvatureTensorReaction3, bsharp_eq_knC hsym]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [knC, cc_closed hsym, R, rm, ricciFromSectional3,
      sectionalReaction12, sectionalReaction13, sectionalReaction23, sc, Rsq, normSq, kd,
      Fin.sum_univ_three] <;> ring

theorem sectionalReaction12_nonneg (K12 K13 K23 : Real)
    (h13 : 0 ≤ K13) (h23 : 0 ≤ K23) :
    0 ≤ sectionalReaction12 K12 K13 K23 := by
  unfold sectionalReaction12
  positivity

theorem sectionalReaction13_nonneg (K12 K13 K23 : Real)
    (h12 : 0 ≤ K12) (h23 : 0 ≤ K23) :
    0 ≤ sectionalReaction13 K12 K13 K23 := by
  unfold sectionalReaction13
  positivity

theorem sectionalReaction23_nonneg (K12 K13 K23 : Real)
    (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) :
    0 ≤ sectionalReaction23 K12 K13 K23 := by
  unfold sectionalReaction23
  positivity

theorem curvatureOperatorQuadraticEval3_reaction {n : Nat}
    (K12 K13 K23 : Real) (c : Fin n → Real)
    (v w : Fin n → Fin 3 → Real) :
    curvatureOperatorQuadraticEval3 (curvatureTensorReaction3 K12 K13 K23) c v w =
      sectionalReaction12 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 0 1 (v i) (w i)) ^ 2 +
        sectionalReaction13 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 0 2 (v i) (w i)) ^ 2 +
        sectionalReaction23 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 1 2 (v i) (w i)) ^ 2 := by
  have hreaction : curvatureTensorReaction3 K12 K13 K23 =
      rm (ricciFromSectional3
        (sectionalReaction12 K12 K13 K23)
        (sectionalReaction13 K12 K13 K23)
        (sectionalReaction23 K12 K13 K23)) := by
    funext a b c d
    exact curvatureTensorReaction3_eq_rm K12 K13 K23 a b c d
  rw [hreaction, curvatureOperatorQuadraticEval3_rm]

theorem curvatureOperatorQuadraticEval3_reaction_nonneg {n : Nat}
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) :
    0 ≤ curvatureOperatorQuadraticEval3
      (curvatureTensorReaction3 K12 K13 K23) c v w := by
  rw [curvatureOperatorQuadraticEval3_reaction]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (sectionalReaction12_nonneg K12 K13 K23 h13 h23) (sq_nonneg _))
      (mul_nonneg (sectionalReaction13_nonneg K12 K13 K23 h12 h23) (sq_nonneg _)))
    (mul_nonneg (sectionalReaction23_nonneg K12 K13 K23 h12 h13) (sq_nonneg _))

end DifferentialGeometry.Dim3Reaction
