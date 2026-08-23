import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Region
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
import DifferentialGeometry.Analysis.Convex.SupportFunction
import DifferentialGeometry.Analysis.Calculus.RightDerivative
import DifferentialGeometry.Analysis.InnerProductSpace.MatrixEuclidean
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Dim3Reaction
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators NNReal
open scoped Matrix.Norms.Frobenius

def hamiltonIveyMatrixReaction (A : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  2 • (A * A + A.adjugate)

def hamiltonIveyMatrixReactionEuclidean
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  matrixToEuclidean (hamiltonIveyMatrixReaction (euclideanToMatrix A))

private lemma diagProduct_erase (l1 l2 l3 : ℝ) (i : Fin 3) :
    (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase i, ![l1, l2, l3] j) =
      (if i = 0 then l2 * l3 else if i = 1 then l1 * l3 else l1 * l2) := by
  fin_cases i
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3), ![l1, l2, l3] j) = l2 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3) = ({1, 2} : Finset (Fin 3)) := by
      ext j; fin_cases j <;> simp
    rw [hset]; simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3), ![l1, l2, l3] j) = l1 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3) = ({0, 2} : Finset (Fin 3)) := by
      ext j; fin_cases j <;> simp
    rw [hset]; simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3), ![l1, l2, l3] j) = l1 * l2
    have hset : (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3) = ({0, 1} : Finset (Fin 3)) := by
      ext j; fin_cases j <;> simp
    rw [hset]; simp

theorem hamiltonIveyMatrixReaction_diagonal
    (l1 l2 l3 : Real) :
    hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3]) =
      Matrix.diagonal ![2 * (l1 ^ 2 + l2 * l3), 2 * (l2 ^ 2 + l1 * l3), 2 * (l3 ^ 2 + l1 * l2)] := by
  classical
  unfold hamiltonIveyMatrixReaction
  rw [Matrix.adjugate_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply] <;>
    simp [diagProduct_erase, Fin.reduceEq, ↓reduceIte] <;> ring

private lemma small_order_ge
    (a b a' b' : Real) (hab : b ≤ a)
    (h0 : a = b → a' = b') :
    ∃ ε : Real, 0 < ε ∧ ∀ t : Real, t ∈ Set.Icc 0 ε →
      b + t * b' ≤ a + t * a' := by
  by_cases hab' : a = b
  · subst a
    rw [h0 rfl]
    refine ⟨1, by norm_num, ?_⟩
    intro t ht
    exact le_rfl
  · have hgt : b < a := lt_of_le_of_ne hab (Ne.symm hab')
    by_cases hle : a' ≤ b'
    · let eps : Real := (a - b) / (b' - a' + 1)
      refine ⟨eps, ?_, ?_⟩
      · dsimp [eps]
        have hden : 0 < b' - a' + 1 := by nlinarith
        exact div_pos (sub_pos.mpr hgt) hden
      · intro t ht
        have hb' : b - a ≤ t * (a' - b') := by
          have htl : t ≤ (a - b) / (b' - a' + 1) := by
            dsimp [eps] at ht
            exact ht.2
          have hden : 0 < b' - a' + 1 := by nlinarith
          have h1 : t * (b' - a' + 1) ≤ a - b := by
            rw [le_div_iff₀ hden] at htl
            exact htl
          nlinarith
        nlinarith [hb']
    · refine ⟨1, by norm_num, ?_⟩
      intro t ht
      have hle' : b' ≤ a' := le_of_lt (lt_of_not_ge hle)
      have hcoef : 0 ≤ t := ht.1
      nlinarith

private lemma reactionDiag_order0_ge2 (l1 l2 l3 : Real) :
    l1 = l3 → 2 * (l1 ^ 2 + l2 * l3) = 2 * (l3 ^ 2 + l1 * l2) := by
  intro h
  rw [h]
  ring

private lemma reactionDiag_order1_ge2 (l1 l2 l3 : Real) :
    l2 = l3 → 2 * (l2 ^ 2 + l1 * l3) = 2 * (l3 ^ 2 + l1 * l2) := by
  intro h
  rw [h]

private lemma reactionDiag_minEig (l1 l2 l3 : Real) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t : Real, t ∈ Set.Icc 0 ε →
      minimumRayleighQuotient3 (Matrix.diagonal
        ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
          l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
          l3 + t * (2 * (l3 ^ 2 + l1 * l2))]) =
        l3 + t * (2 * (l3 ^ 2 + l1 * l2)) := by
  obtain ⟨ε1, hε1, h1⟩ := small_order_ge l1 l3
    (2 * (l1 ^ 2 + l2 * l3)) (2 * (l3 ^ 2 + l1 * l2))
    (le_trans h32 h21) (reactionDiag_order0_ge2 l1 l2 l3)
  obtain ⟨ε2, hε2, h2⟩ := small_order_ge l2 l3
    (2 * (l2 ^ 2 + l1 * l3)) (2 * (l3 ^ 2 + l1 * l2))
    h32 (reactionDiag_order1_ge2 l1 l2 l3)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro t ht
  have ht1 : t ∈ Set.Icc 0 ε1 := ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht2 : t ∈ Set.Icc 0 ε2 := ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  let d : Fin 3 → Real := fun i =>
    if i = 0 then l1 + t * (2 * (l1 ^ 2 + l2 * l3))
    else if i = 1 then l2 + t * (2 * (l2 ^ 2 + l1 * l3))
    else l3 + t * (2 * (l3 ^ 2 + l1 * l2))
  have hd : Matrix.diagonal ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
      l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
      l3 + t * (2 * (l3 ^ 2 + l1 * l2))] = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, d]
  have hge : ∀ i : Fin 3, l3 + t * (2 * (l3 ^ 2 + l1 * l2)) ≤ d i := by
    intro i
    fin_cases i
    · dsimp [d]
      exact h1 t ht1
    · dsimp [d]
      exact h2 t ht2
    · dsimp [d]
      exact le_rfl
  have hle : minimumRayleighQuotient3 (Matrix.diagonal d) ≤
      l3 + t * (2 * (l3 ^ 2 + l1 * l2)) := by
    simpa [d] using (minimumRayleighQuotient3_diagonal_le d (2 : Fin 3))
  have hge' : l3 + t * (2 * (l3 ^ 2 + l1 * l2)) ≤
      minimumRayleighQuotient3 (Matrix.diagonal d) :=
    minimumRayleighQuotient3_diagonal_ge d hge
  rw [hd]
  exact le_antisymm hle hge'

private lemma hasDerivAt_barrier_comp
    (K τ X X' : Real) (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 < X) :
    HasDerivAt (fun t : Real =>
      hamiltonIveyBarrier K (τ + t) (X + t * X'))
      ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * X' +
        X * (2 * K / (1 + 2 * K * τ))) 0 := by
  have hdenpos : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have hKτ' : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hinnerX : HasDerivAt (fun t : Real => (X + t * X') / K) (X' / K) 0 := by
    have hlin : HasDerivAt (fun t : Real => X + t * X') X' 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        ((hasDerivAt_id 0).mul_const X').const_add X
    simpa [div_eq_mul_inv] using hlin.div_const K
  have hlogX : HasDerivAt (fun t : Real => Real.log ((X + t * X') / K))
      (X' / X) 0 := by
    have hlog := hinnerX.log (by
      rw [show (X + 0 * X') / K = X / K by ring]
      exact div_ne_zero hX.ne' hK.ne')
    exact hlog.congr_deriv (by
      field_simp [hX.ne', hK.ne']
      ring)
  have hinnerτ : HasDerivAt (fun t : Real => 1 + 2 * K * (τ + t)) (2 * K) 0 := by
    have hlin : HasDerivAt (fun t : Real => (2 * K) * (τ + t)) (2 * K) 0 := by
      simpa using (((hasDerivAt_id 0).const_add τ).const_mul (2 * K))
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hlin.const_add 1
  have hlogτ : HasDerivAt (fun t : Real => Real.log (1 + 2 * K * (τ + t)))
      (2 * K / (1 + 2 * K * τ)) 0 := by
    have hlog := hinnerτ.log (ne_of_gt (by simpa using hdenpos))
    exact hlog.congr_deriv (by ring)
  have hsum : HasDerivAt (fun t : Real =>
      Real.log ((X + t * X') / K) + Real.log (1 + 2 * K * (τ + t)) - 3)
      (X' / X + 2 * K / (1 + 2 * K * τ)) 0 := by
    simpa using (hlogX.add hlogτ).sub_const 3
  have hlin2 : HasDerivAt (fun t : Real => X + t * X') X' 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id 0).mul_const X').const_add X
  have hB : HasDerivAt (fun t : Real =>
      (X + t * X') * (Real.log ((X + t * X') / K) + Real.log (1 + 2 * K * (τ + t)) - 3))
      (X' * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 3) +
        X * (X' / X + 2 * K / (1 + 2 * K * τ))) 0 := by
    simpa using hlin2.mul hsum
  unfold hamiltonIveyBarrier
  exact hB.congr_deriv (by
    field_simp [hX.ne', hdenpos.ne']
    ring_nf)

private lemma reactionSum3_nonneg (l1 l2 l3 : Real) :
    0 ≤ 2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2) := by
  have hsq : 0 ≤ (l1 + l2) ^ 2 + (l1 + l3) ^ 2 + (l2 + l3) ^ 2 := by positivity
  nlinarith

private lemma reactionSum3_ge_sq (l1 l2 l3 : Real) :
    4 * ((l1 + l2 + l3) ^ 2) / 3 ≤
      2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2) := by
  have hnorm : 2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2) =
      (l1 + l2) ^ 2 + (l1 + l3) ^ 2 + (l2 + l3) ^ 2 := by ring
  rw [hnorm]
  have hsq : 0 ≤ ((l1 + l2) - (l1 + l3)) ^ 2 + ((l1 + l2) - (l2 + l3)) ^ 2 +
      ((l1 + l3) - (l2 + l3)) ^ 2 := by positivity
  nlinarith

theorem hamiltonIveyMatrixReaction_orthogonal_conj
    (O A : Matrix (Fin 3) (Fin 3) Real)
    (hO : O * O.transpose = 1) :
    hamiltonIveyMatrixReaction (O * A * O.transpose) =
      O * hamiltonIveyMatrixReaction A * O.transpose := by
  classical
  unfold hamiltonIveyMatrixReaction
  have hOinv : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  have hsq : (O * A * O.transpose) * (O * A * O.transpose) =
      O * (A * A) * O.transpose := by
    calc
      (O * A * O.transpose) * (O * A * O.transpose)
          = O * A * (O.transpose * O) * A * O.transpose := by
            simp only [Matrix.mul_assoc]
      _ = O * A * A * O.transpose := by
            rw [hOinv]
            simp
      _ = O * (A * A) * O.transpose := by
            simp only [Matrix.mul_assoc]
  have hadj := adjugate_orthogonal_conj O A hO
  rw [hsq, hadj]
  calc
    2 • (O * (A * A) * O.transpose + O * A.adjugate * O.transpose)
        = 2 • ((O * (A * A) + O * A.adjugate) * O.transpose) := by
          rw [← Matrix.add_mul]
    _ = 2 • (O * (A * A + A.adjugate) * O.transpose) := by
          rw [← Matrix.mul_add]
    _ = O * (2 • (A * A + A.adjugate)) * O.transpose := by
          rw [← Matrix.smul_mul]
          rw [Matrix.mul_smul]

private lemma lip {K tau t : Real} (hK : 0 < K) (htau : 0 <= tau) (ht : 0 <= t) :
    scalarSectionalLowerBarrier3 K (tau + t) <= scalarSectionalLowerBarrier3 K tau + 12 * K ^ 2 * t := by
  unfold scalarSectionalLowerBarrier3
  have hmain : 3 * K / (1 + 4 * K * tau) - 3 * K / (1 + 4 * K * (tau + t)) <= 12 * K ^ 2 * t := by
    have hden1 : 0 < 1 + 4 * K * tau := by positivity
    have hden2 : 0 < 1 + 4 * K * (tau + t) := by positivity
    have hsum : 3 * K / (1 + 4 * K * tau) - 3 * K / (1 + 4 * K * (tau + t)) =
        3 * K * (4 * K * t) / ((1 + 4 * K * tau) * (1 + 4 * K * (tau + t))) := by
      field_simp [hden1.ne', hden2.ne']
      ring
    rw [hsum]
    have hdenle : 1 <= (1 + 4 * K * tau) * (1 + 4 * K * (tau + t)) := by
      have h1 : 1 <= 1 + 4 * K * tau := by nlinarith
      have h2 : 1 <= 1 + 4 * K * (tau + t) := by nlinarith
      nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
    have habpos : 0 < (1 + 4 * K * tau) * (1 + 4 * K * (tau + t)) := by positivity
    have h12 : 0 <= 12 * K ^ 2 * t := by positivity
    have hfac : 3 * K * (4 * K * t) = 12 * K ^ 2 * t := by ring
    rw [hfac]
    rw [div_le_iff₀ habpos]
    nlinarith [hdenle]
  have hconv1 : -3 * K / (1 + 4 * K * (tau + t)) = -(3 * K / (1 + 4 * K * (tau + t))) := by ring
  have hconv2 : -3 * K / (1 + 4 * K * tau) = -(3 * K / (1 + 4 * K * tau)) := by ring
  rw [hconv1, hconv2]
  linarith [hmain]

private lemma concave {K tau t : Real} (hK : 0 < K) (htau : 0 <= tau) (ht : 0 <= t) :
    scalarSectionalLowerBarrier3 K (tau + t) <= scalarSectionalLowerBarrier3 K tau + (12 * K ^ 2 / (1 + 4 * K * tau) ^ 2) * t := by
  unfold scalarSectionalLowerBarrier3
  have hmain : 3 * K / (1 + 4 * K * tau) - 3 * K / (1 + 4 * K * (tau + t)) <=
      (12 * K ^ 2 / (1 + 4 * K * tau) ^ 2) * t := by
    have hden1 : 0 < 1 + 4 * K * tau := by positivity
    have hden2 : 0 < 1 + 4 * K * (tau + t) := by positivity
    have hsum : 3 * K / (1 + 4 * K * tau) - 3 * K / (1 + 4 * K * (tau + t)) =
        3 * K * (4 * K * t) / ((1 + 4 * K * tau) * (1 + 4 * K * (tau + t))) := by
      field_simp [hden1.ne', hden2.ne']
      ring
    rw [hsum]
    have hab : (1 + 4 * K * tau) * (1 + 4 * K * (tau + t)) >= (1 + 4 * K * tau) ^ 2 := by
      have h2 : 1 + 4 * K * tau <= 1 + 4 * K * (tau + t) := by nlinarith
      have hpos : 0 <= 1 + 4 * K * tau := by positivity
      nlinarith [mul_le_mul hpos h2 (by positivity) (by positivity)]
    have hdenprod : 0 < (1 + 4 * K * tau) * (1 + 4 * K * (tau + t)) := by positivity
    have hnum : 12 * K ^ 2 * t / ((1 + 4 * K * tau) * (1 + 4 * K * (tau + t))) <=
        12 * K ^ 2 * t / (1 + 4 * K * tau) ^ 2 := by
      have hpos2 : 0 < (1 + 4 * K * tau) ^ 2 := by positivity
      have h12 : 0 <= 12 * K ^ 2 * t := by positivity
      exact div_le_div_of_nonneg_left h12 hpos2 hab
    have hfac : 3 * K * (4 * K * t) = 12 * K ^ 2 * t := by ring
    rw [hfac]
    have hnum' : 12 * K ^ 2 * t / ((1 + 4 * K * tau) * (1 + 4 * K * (tau + t))) <=
        (12 * K ^ 2 / (1 + 4 * K * tau) ^ 2) * t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnum
    exact hnum'
  have hconv1 : -3 * K / (1 + 4 * K * (tau + t)) = -(3 * K / (1 + 4 * K * (tau + t))) := by ring
  have hconv2 : -3 * K / (1 + 4 * K * tau) = -(3 * K / (1 + 4 * K * tau)) := by ring
  rw [hconv1, hconv2]
  linarith [hmain]


private lemma scalarBarrier_ineq_small
    {K tau : Real} (hK : 0 < K) (htau : 0 <= tau)
    (S S' : Real) (hSb : scalarSectionalLowerBarrier3 K tau <= S) (hS' : 0 <= S') (hS'ge : 4 * S ^ 2 / 3 <= S') :
    ∃ eps : Real, 0 < eps ∧ ∀ t : Real, t ∈ Set.Icc 0 eps →
      scalarSectionalLowerBarrier3 K (tau + t) <= S + t * S' := by
  by_cases hS : S = scalarSectionalLowerBarrier3 K tau
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht
    have hconc := concave (K := K) (tau := tau) (t := t) hK htau ht.1
    have hrel : 4 * (scalarSectionalLowerBarrier3 K tau) ^ 2 / 3 = 12 * K ^ 2 / (1 + 4 * K * tau) ^ 2 := by
      unfold scalarSectionalLowerBarrier3
      field_simp
      ring
    have hS'ge' : 4 * (scalarSectionalLowerBarrier3 K tau) ^ 2 / 3 <= S' := by
      simpa [hS] using hS'ge
    have hSb' : 12 * K ^ 2 / (1 + 4 * K * tau) ^ 2 <= S' := by
      simpa [hrel] using hS'ge'
    have hsc : scalarSectionalLowerBarrier3 K tau + (12 * K ^ 2 / (1 + 4 * K * tau) ^ 2) * t <= S + t * S' := by
      rw [hS]
      have ht' : 0 <= t := ht.1
      have hmul : (12 * K ^ 2 / (1 + 4 * K * tau) ^ 2) * t <= S' * t :=
        mul_le_mul_of_nonneg_right hSb' ht'
      nlinarith
    exact le_trans hconc hsc
  · have hgt : scalarSectionalLowerBarrier3 K tau < S := lt_of_le_of_ne hSb (Ne.symm hS)
    let eps : Real := (S - scalarSectionalLowerBarrier3 K tau) / (12 * K ^ 2)
    refine ⟨eps, ?_, ?_⟩
    · dsimp [eps]
      have hKsq : 0 < 12 * K ^ 2 := by positivity
      exact div_pos (sub_pos.mpr hgt) hKsq
    · intro t ht
      have htl : t <= (S - scalarSectionalLowerBarrier3 K tau) / (12 * K ^ 2) := by
        dsimp [eps] at ht
        exact ht.2
      have hKsq : 0 < 12 * K ^ 2 := by positivity
      have hlip := lip (K := K) (tau := tau) (t := t) hK htau ht.1
      have hmain : scalarSectionalLowerBarrier3 K tau + 12 * K ^ 2 * t <= S := by
        have h1 : t * (12 * K ^ 2) <= S - scalarSectionalLowerBarrier3 K tau := by
          rw [le_div_iff₀ hKsq] at htl
          nlinarith
        nlinarith
      have hle : scalarSectionalLowerBarrier3 K (tau + t) <= S := le_trans hlip hmain
      exact le_trans hle (by nlinarith [mul_nonneg ht.1 hS'])

private lemma barrier_g_continuousAt
    (K tau X X' S S' : ℝ) (hK : 0 < K) (htau : 0 ≤ tau) :
    ContinuousAt (fun t : ℝ => S + t * S' - hamiltonIveyBarrier K (tau + t) (X + t * X')) 0 := by
  have hcontB : ContinuousAt (fun t : ℝ => hamiltonIveyBarrier K (tau + t) (X + t * X')) 0 := by
    have hfun : (fun t : ℝ => hamiltonIveyBarrier K (tau + t) (X + t * X')) =
        fun t : ℝ => (X + t * X') * Real.log (X + t * X') +
          (X + t * X') * (Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K) := by
      funext t
      exact hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := tau + t) (X := X + t * X') hK
    rw [hfun]
    have hx : ContinuousAt (fun t : ℝ => X + t * X') 0 := by fun_prop
    have h1 : ContinuousAt (fun t : ℝ => (X + t * X') * Real.log (X + t * X')) 0 :=
      Real.continuous_mul_log.continuousAt.comp hx
    have hlog : ContinuousAt (fun t : ℝ => Real.log (1 + 2 * K * (tau + t))) 0 := by
      have hlin' : ContinuousAt (fun t : ℝ => 1 + 2 * K * (tau + t)) 0 := by fun_prop
      exact hlin'.log (ne_of_gt (by
        have hpos : 0 < 1 + 2 * K * (tau + 0) := by
          have hKtau : 0 ≤ 2 * K * tau := by
            have hKtau' : 0 ≤ K * tau := mul_nonneg hK.le htau
            nlinarith
          nlinarith
        simpa using hpos))
    have h2 : ContinuousAt (fun t : ℝ =>
        (X + t * X') * (Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K)) 0 := by
      have hc : ContinuousAt (fun t : ℝ =>
          Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K) 0 := by
        exact (hlog.sub_const 3).sub_const (Real.log K)
      exact hx.mul hc
    exact h1.add h2
  have hlin2 : ContinuousAt (fun t : ℝ => S + t * S') 0 := by fun_prop
  exact hlin2.sub hcontB

private lemma barrier_ineq_small
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (l1 l2 l3 : ℝ) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hB : hamiltonIveyBarrier K tau (-l3) ≤ l1 + l2 + l3) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      hamiltonIveyBarrier K (tau + t) (-(l3 + t * (2 * (l3 ^ 2 + l1 * l2)))) ≤
        (l1 + l2 + l3) + t * (2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2)) := by
  let X : ℝ := -l3
  let X' : ℝ := -(2 * (l3 ^ 2 + l1 * l2))
  let S : ℝ := l1 + l2 + l3
  let S' : ℝ := 2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2)
  let g : ℝ → ℝ := fun t => S + t * S' - hamiltonIveyBarrier K (tau + t) (X + t * X')
  have hX : 0 < X := by dsimp [X]; linarith
  have hg0 : g 0 = S - hamiltonIveyBarrier K tau X := by
    dsimp [g, X]
    ring_nf
  have hg0ge : 0 ≤ g 0 := by
    rw [hg0]
    dsimp [S, X]
    linarith [hB]
  by_cases hg0pos : 0 < g 0
  · have hg_cont : ContinuousAt g 0 := by
      dsimp [g]
      exact barrier_g_continuousAt K tau X X' S S' hK htau
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t :=
      DifferentialGeometry.eventually_pos_of_continuousAt_pos g hg_cont hg0pos
    have hev_nhds : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioi 0 → 0 < g t :=
      eventually_nhdsWithin_iff.mp hev
    rcases Metric.eventually_nhds_iff.mp hev_nhds with ⟨eps, heps, hball⟩
    let eps' : ℝ := eps / 2
    refine ⟨eps', half_pos heps, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hbar0 : hamiltonIveyBarrier K tau X ≤ S := by
        dsimp [S, X]
        exact hB
      simpa [X, X', S, S'] using hbar0
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htle : t ≤ eps / 2 := by simpa [eps'] using ht.2
      have htlt : t < eps := by
        have hhalf : eps / 2 < eps := half_lt_self heps
        nlinarith [htle]
      have hdist : dist t 0 < eps := by
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
        exact htlt
      have hgt : 0 < g t := hball hdist htpos
      have hB' : hamiltonIveyBarrier K (tau + t) (X + t * X') ≤ S + t * S' := by
        dsimp [g] at hgt
        nlinarith
      dsimp [X, X', S, S'] at hB' ⊢
      ring_nf at hB' ⊢
      exact hB'
  · have hg0eq : g 0 = 0 := by
      rw [hg0]
      have hle : S - hamiltonIveyBarrier K tau X ≤ 0 := by
        dsimp [S, X]
        have hnot : ¬ 0 < S - hamiltonIveyBarrier K tau X := by
          simpa [hg0] using hg0pos
        linarith
      exact le_antisymm hle (by simpa [hg0] using hg0ge)
    have hboundary : hamiltonIveyBarrier K tau (-l3) = l1 + l2 + l3 := by
      have hg0eq' : S - hamiltonIveyBarrier K tau X = 0 := by
        simpa [g, X] using hg0eq
      have hle2 : l1 + l2 + l3 ≤ hamiltonIveyBarrier K tau (-l3) := by
        dsimp [S, X] at hg0eq'
        linarith
      exact le_antisymm hB hle2
    have hψ : 0 < S' - (Real.log (X / K) + Real.log (1 + 2 * K * tau) - 2) * X' -
        X * (2 * K / (1 + 2 * K * tau)) := by
      have hden : 0 < 1 + 2 * K * tau := by
        have hKtau : 0 ≤ 2 * K * tau := by
          have hKtau' : 0 ≤ K * tau := mul_nonneg hK.le htau
          nlinarith
        nlinarith
      have hmain := hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
        (l1 := l1) (l2 := l2) (l3 := l3) (K := K) (τ := tau)
        h21 h32 hl3 hK hden hboundary
      simpa [S', X, X', reactionSectionalSum3, reactionPinchHeight3,
        DifferentialGeometry.Dim3Reaction.sectionalReaction12,
        DifferentialGeometry.Dim3Reaction.sectionalReaction13,
        DifferentialGeometry.Dim3Reaction.sectionalReaction23] using hmain
    have hg_deriv : HasDerivAt g (S' - (Real.log (X / K) + Real.log (1 + 2 * K * tau) - 2) * X' -
        X * (2 * K / (1 + 2 * K * tau))) 0 := by
      have hBderiv := hasDerivAt_barrier_comp (K := K) (τ := tau) (X := X) (X' := X') hK htau hX
      have hlin : HasDerivAt (fun t : ℝ => S + t * S') S' 0 := by
        simpa using ((hasDerivAt_id 0).mul_const S').const_add S
      have hd : HasDerivAt (fun t : ℝ => hamiltonIveyBarrier K (tau + t) (X + t * X'))
          ((Real.log (X / K) + Real.log (1 + 2 * K * tau) - 2) * X' +
            X * (2 * K / (1 + 2 * K * tau))) 0 := hBderiv
      have hg' : HasDerivAt (fun t : ℝ => S + t * S' - hamiltonIveyBarrier K (tau + t) (X + t * X'))
          (S' - ((Real.log (X / K) + Real.log (1 + 2 * K * tau) - 2) * X' +
            X * (2 * K / (1 + 2 * K * tau)))) 0 := hlin.sub hd
      have hg'' : HasDerivAt (fun t : ℝ => S + t * S' - hamiltonIveyBarrier K (tau + t) (X + t * X'))
          (S' - (Real.log (X / K) + Real.log (1 + 2 * K * tau) - 2) * X' -
            X * (2 * K / (1 + 2 * K * tau))) 0 := by
        convert hg' using 1
        ring_nf
      simpa [g] using hg''
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t :=
      DifferentialGeometry.eventually_pos_of_hasDerivAt_pos g _ hψ hg0eq hg_deriv
    have hev_nhds : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioi 0 → 0 < g t :=
      eventually_nhdsWithin_iff.mp hev
    rcases Metric.eventually_nhds_iff.mp hev_nhds with ⟨eps, heps, hball⟩
    let eps' : ℝ := eps / 2
    refine ⟨eps', half_pos heps, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hbar0 : hamiltonIveyBarrier K tau X ≤ S := by
        dsimp [S, X]
        exact hB
      simpa [X, X', S, S'] using hbar0
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htle : t ≤ eps / 2 := by simpa [eps'] using ht.2
      have htlt : t < eps := by
        have hhalf : eps / 2 < eps := half_lt_self heps
        nlinarith [htle]
      have hdist : dist t 0 < eps := by
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
        exact htlt
      have hgt : 0 < g t := hball hdist htpos
      have hB' : hamiltonIveyBarrier K (tau + t) (X + t * X') ≤ S + t * S' := by
        dsimp [g] at hgt
        nlinarith
      dsimp [X, X', S, S'] at hB' ⊢
      ring_nf at hB' ⊢
      exact hB'


private lemma reactionDiagonal_trace (l1 l2 l3 : ℝ) :
    (hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3])).trace =
      reactionSectionalSum3 l1 l2 l3 := by
  rw [hamiltonIveyMatrixReaction_diagonal]
  unfold reactionSectionalSum3
  simp [DifferentialGeometry.Dim3Reaction.sectionalReaction12,
    DifferentialGeometry.Dim3Reaction.sectionalReaction13,
    DifferentialGeometry.Dim3Reaction.sectionalReaction23, Fin.sum_univ_three]

private lemma diagonal_add_smul_reaction
    (l1 l2 l3 t : ℝ) :
    Matrix.diagonal ![l1, l2, l3] +
        t • hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3]) =
      Matrix.diagonal ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
        l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
        l3 + t * (2 * (l3 ^ 2 + l1 * l2))] := by
  rw [hamiltonIveyMatrixReaction_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private lemma continuousAt_hamiltonIveyBarrier_comp_nonneg
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (f : ℝ → ℝ) (hf : ContinuousAt f 0) :
    ContinuousAt (fun t : ℝ => hamiltonIveyBarrier K (tau + t) (max (f t) 0)) 0 := by
  have hdenpos : 0 < 1 + 2 * K * tau := by
    have hKtau : 0 ≤ 2 * K * tau := by
      have hKtau' : 0 ≤ K * tau := mul_nonneg hK.le htau
      nlinarith
    nlinarith
  have hX : ContinuousAt (fun t : ℝ => max (f t) 0) 0 := hf.max continuousAt_const
  have hfun : (fun t : ℝ => hamiltonIveyBarrier K (tau + t) (max (f t) 0)) =
      fun t : ℝ => (max (f t) 0) * Real.log (max (f t) 0) +
        (max (f t) 0) * (Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K) := by
    funext t
    exact hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := tau + t) (X := max (f t) 0) hK
  rw [hfun]
  have h1 : ContinuousAt (fun t : ℝ => (max (f t) 0) * Real.log (max (f t) 0)) 0 :=
    Real.continuous_mul_log.continuousAt.comp hX
  have hlog : ContinuousAt (fun t : ℝ => Real.log (1 + 2 * K * (tau + t))) 0 := by
    have hlin' : ContinuousAt (fun t : ℝ => 1 + 2 * K * (tau + t)) 0 := by fun_prop
    exact hlin'.log (ne_of_gt (by
      have hpos : 0 < 1 + 2 * K * (tau + 0) := by
        have hKtau : 0 ≤ 2 * K * tau := by
          have hKtau' : 0 ≤ K * tau := mul_nonneg hK.le htau
          nlinarith
        nlinarith
      simpa using hpos))
  have h2 : ContinuousAt (fun t : ℝ =>
      (max (f t) 0) * (Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K)) 0 := by
    have hc : ContinuousAt (fun t : ℝ =>
        Real.log (1 + 2 * K * (tau + t)) - 3 - Real.log K) 0 := by
      exact (hlog.sub_const 3).sub_const (Real.log K)
    exact hX.mul hc
  exact h1.add h2

lemma zero_mem_hamiltonIveyConvexMatrixRegion
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau) :
    (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ hamiltonIveyConvexMatrixRegion K tau := by
  rw [hamiltonIveyConvexMatrixRegion]
  refine ⟨by simp, ?_⟩
  · unfold hamiltonIveyConvexBarrier
    rw [minimumRayleighQuotient3_zero, neg_zero, max_self]
    have hscalar : scalarSectionalLowerBarrier3 K tau ≤ 0 := by
      unfold scalarSectionalLowerBarrier3
      have hden : 0 < 1 + 4 * K * tau := by
        have hKtau : 0 ≤ 4 * K * tau := by
          have hKtau' : 0 ≤ K * tau := mul_nonneg hK.le htau
          nlinarith
        nlinarith
      have hnonpos : -3 * K ≤ 0 := by nlinarith
      exact div_nonpos_of_nonpos_of_nonneg hnonpos hden.le
    have hbar0 : hamiltonIveyBarrier K tau 0 = 0 := by
      unfold hamiltonIveyBarrier
      ring
    rw [hbar0]
    simp [Matrix.trace_zero, hscalar]

private theorem hamiltonIveyConvexMatrixRegion_reaction_small_time_diagonal
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (l1 l2 l3 : ℝ) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2)
    (hAmem : Matrix.diagonal ![l1, l2, l3] ∈ hamiltonIveyConvexMatrixRegion K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      Matrix.diagonal ![l1, l2, l3] +
        t • hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3]) ∈
        hamiltonIveyConvexMatrixRegion K (tau + t) := by
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![l1, l2, l3]
  let S : ℝ := l1 + l2 + l3
  let S' : ℝ := reactionSectionalSum3 l1 l2 l3
  let X : ℝ := max (-l3) 0
  have hS'eq : S' = 2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2) := by
    dsimp [S', reactionSectionalSum3]
    simp [DifferentialGeometry.Dim3Reaction.sectionalReaction12,
      DifferentialGeometry.Dim3Reaction.sectionalReaction13,
      DifferentialGeometry.Dim3Reaction.sectionalReaction23]
  have hmin0 : minimumRayleighQuotient3 D = l3 := by
    dsimp [D]
    exact minimumRayleighQuotient3_diagonal_eq_last l1 l2 l3 h21 h32
  have hbar : hamiltonIveyConvexBarrier K tau X ≤ S := by
    dsimp [S, X]
    have h := hAmem.2
    simpa [D, hmin0, Fin.sum_univ_three] using h
  have hSbar : scalarSectionalLowerBarrier3 K tau ≤ S := by
    have hle := (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K tau X).trans hbar
    exact hle
  have hS'nonneg : 0 ≤ S' := by
    rw [hS'eq]
    exact reactionSum3_nonneg l1 l2 l3
  have hS'ge : 4 * S ^ 2 / 3 ≤ S' := by
    rw [hS'eq]
    dsimp [S]
    exact reactionSum3_ge_sq l1 l2 l3
  by_cases hl3 : l3 < 0
  · have hXeq : X = -l3 := by
      dsimp [X]
      exact max_eq_left (neg_nonneg.mpr hl3.le)
    have hB : hamiltonIveyBarrier K tau (-l3) ≤ S := by
      have hle := hbar
      unfold hamiltonIveyConvexBarrier at hle
      rw [hXeq] at hle
      exact (max_le_iff.mp hle).2
    rcases barrier_ineq_small hK htau l1 l2 l3 h21 h32 hl3 hB with ⟨ε1, hε1, hbar1⟩
    rcases scalarBarrier_ineq_small hK htau S S' hSbar hS'nonneg hS'ge with ⟨ε2, hε2, hscalar1⟩
    rcases reactionDiag_minEig l1 l2 l3 h21 h32 with ⟨ε3, hε3, hm1⟩
    have hm_cont : ContinuousAt
        (fun t : ℝ => minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) 0 :=
      (continuous_minimumRayleighQuotient3_comp
        (by fun_prop : Continuous (fun t : ℝ => D + t • hamiltonIveyMatrixReaction D))).continuousAt
    have hmneg_ev : ∀ᶠ t : ℝ in 𝓝[>] 0,
        minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D) < 0 := by
      have hev := eventually_neg_of_continuousAt_neg
        (fun t : ℝ => minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) hm_cont
        (by simpa [hmin0] using hl3)
      exact hev
    rcases exists_pos_Ioo_of_eventually_nhdsWithin
      (fun t : ℝ => minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D) < 0) hmneg_ev with
      ⟨ε4, hε4, hmneg1⟩
    let eps : ℝ := min (min ε1 ε2) (min ε3 (ε4 / 2))
    refine ⟨eps, ?_, ?_⟩
    · dsimp [eps]
      positivity
    · intro t ht
      by_cases ht0 : t = 0
      · subst t
        have hmem0 : D ∈ hamiltonIveyConvexMatrixRegion K tau := by
          simpa [D] using hAmem
        simpa [D] using hmem0
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        have ht1 : t ∈ Set.Icc 0 ε1 := ⟨ht.1, le_trans ht.2 (by dsimp [eps]; exact le_trans (min_le_left _ _) (min_le_left _ _))⟩
        have ht2 : t ∈ Set.Icc 0 ε2 := ⟨ht.1, le_trans ht.2 (by dsimp [eps]; exact le_trans (min_le_left _ _) (min_le_right _ _))⟩
        have ht3 : t ∈ Set.Icc 0 ε3 := ⟨ht.1, le_trans ht.2 (by dsimp [eps]; exact le_trans (min_le_right _ _) (min_le_left _ _))⟩
        have ht4 : t < ε4 := by
          have htle : t ≤ ε4 / 2 := le_trans ht.2 (by dsimp [eps]; exact le_trans (min_le_right _ _) (min_le_right _ _))
          exact lt_of_le_of_lt htle (half_lt_self hε4)
        have hdiag : D + t • hamiltonIveyMatrixReaction D =
            Matrix.diagonal ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
              l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
              l3 + t * (2 * (l3 ^ 2 + l1 * l2))] := by
          dsimp [D]
          exact diagonal_add_smul_reaction l1 l2 l3 t
        have htrD : D.trace = l1 + l2 + l3 := by
          dsimp [D]
          simp [Fin.sum_univ_three]
        have htr : (D + t • hamiltonIveyMatrixReaction D).trace = S + t * S' := by
          rw [Matrix.trace_add, Matrix.trace_smul]
          have htrQ : (hamiltonIveyMatrixReaction D).trace = S' := by
            dsimp [D, S']
            exact reactionDiagonal_trace l1 l2 l3
          dsimp [S]
          rw [htrD, htrQ]
        have hm_eq : minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D) =
            l3 + t * (2 * (l3 ^ 2 + l1 * l2)) := by
          rw [hdiag]
          exact hm1 t ht3
        have hbar_t : hamiltonIveyBarrier K (tau + t) (-(l3 + t * (2 * (l3 ^ 2 + l1 * l2)))) ≤ S + t * S' := by
          have h := hbar1 t ht1
          rw [← hS'eq] at h
          simpa [S] using h
        have hscalar_t : scalarSectionalLowerBarrier3 K (tau + t) ≤ S + t * S' :=
          hscalar1 t ht2
        have hbarrier_le : hamiltonIveyBarrier K (tau + t)
            (max (-minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) 0) ≤ S + t * S' := by
          have hmneg_t : minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D) < 0 :=
            hmneg1 t ⟨htpos, ht4⟩
          rw [max_eq_left (neg_nonneg.mpr hmneg_t.le), hm_eq]
          exact hbar_t
        have hmem' : D + t • hamiltonIveyMatrixReaction D ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
          rw [hamiltonIveyConvexMatrixRegion]
          refine ⟨?_, ?_⟩
          · rw [hdiag]
            exact Matrix.isHermitian_diagonal (fun i : Fin 3 =>
              ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
                l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
                l3 + t * (2 * (l3 ^ 2 + l1 * l2))] i)
          · unfold hamiltonIveyConvexBarrier
            rw [htr]
            exact max_le hscalar_t hbarrier_le
        simpa [D] using hmem'
  · have hl3ge : 0 ≤ l3 := le_of_not_gt hl3
    have hXeq : X = 0 := by
      dsimp [X]
      rw [max_eq_right (neg_nonpos.mpr hl3ge)]
    have hSge0 : 0 ≤ S := by
      have hle := hbar
      unfold hamiltonIveyConvexBarrier at hle
      rw [hXeq] at hle
      have hb0 : hamiltonIveyBarrier K tau 0 = 0 := by
        unfold hamiltonIveyBarrier
        ring
      rw [hb0] at hle
      exact (max_le_iff.mp hle).2
    by_cases hS0 : S = 0
    · have hl1 : l1 = 0 := by
        dsimp [S] at hS0
        nlinarith [h21, h32, hl3ge]
      have hl2 : l2 = 0 := by
        dsimp [S] at hS0
        nlinarith [h21, h32, hl3ge]
      have hl30 : l3 = 0 := by
        dsimp [S] at hS0
        nlinarith [h21, h32, hl3ge]
      refine ⟨1, by norm_num, ?_⟩
      intro t ht
      have hD0 : D = 0 := by
        dsimp [D]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> simp [hl1, hl2, hl30]
      have hmem0 : (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ hamiltonIveyConvexMatrixRegion K (tau + t) :=
        zero_mem_hamiltonIveyConvexMatrixRegion hK (by linarith [ht.1, htau])
      have hQ0 : hamiltonIveyMatrixReaction D = 0 := by
        rw [hD0]
        simp [hamiltonIveyMatrixReaction]
      have hsum0 : D + t • hamiltonIveyMatrixReaction D = 0 := by
        rw [hD0]
        simp [hamiltonIveyMatrixReaction]
      simpa [D, hsum0] using hmem0
    · have hSpos : 0 < S := lt_of_le_of_ne hSge0 (Ne.symm hS0)
      have hm_cont : ContinuousAt
          (fun t : ℝ => minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) 0 :=
        (continuous_minimumRayleighQuotient3_comp
          (by fun_prop : Continuous (fun t : ℝ => D + t • hamiltonIveyMatrixReaction D))).continuousAt
      let g : ℝ → ℝ := fun t => hamiltonIveyBarrier K (tau + t)
        (max (-minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) 0)
      have hg_cont : ContinuousAt g 0 := by
        dsimp [g]
        exact continuousAt_hamiltonIveyBarrier_comp_nonneg hK htau
          (fun t : ℝ => -minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) hm_cont.neg
      have hg0 : g 0 = 0 := by
        dsimp [g]
        have hm0' : minimumRayleighQuotient3 (D + 0 • hamiltonIveyMatrixReaction D) = l3 := by
          simpa [D] using hmin0
        have hbar0 : hamiltonIveyBarrier K tau 0 = 0 := by
          unfold hamiltonIveyBarrier
          ring
        convert hbar0 using 1
        · have hle' : -minimumRayleighQuotient3 D ≤ 0 := by
            rw [hmin0]
            exact neg_nonpos.mpr hl3ge
          have hmax' : max (-minimumRayleighQuotient3 D) 0 = 0 := max_eq_right hle'
          simp [hmax']
      have hg_ev : ∀ᶠ t : ℝ in 𝓝[>] 0, g t ≤ S / 2 := by
        have hlt : g 0 < S / 2 := by
          rw [hg0]
          linarith
        exact eventually_le_of_continuousAt_lt g hg_cont (S / 2) hlt
      rcases exists_pos_Ioo_of_eventually_nhdsWithin
        (fun t : ℝ => g t ≤ S / 2) hg_ev with ⟨ε5, hε5, hg5⟩
      rcases scalarBarrier_ineq_small hK htau S S' hSbar hS'nonneg hS'ge with ⟨ε2, hε2, hscalar1⟩
      let eps : ℝ := min ε2 (ε5 / 2)
      refine ⟨eps, ?_, ?_⟩
      · dsimp [eps]
        positivity
      · intro t ht
        by_cases ht0 : t = 0
        · subst t
          have hmem0 : D ∈ hamiltonIveyConvexMatrixRegion K tau := by
            simpa [D] using hAmem
          simpa [D] using hmem0
        · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have ht2 : t ∈ Set.Icc 0 ε2 := ⟨ht.1, le_trans ht.2 (by dsimp [eps]; exact min_le_left _ _)⟩
          have ht5 : t < ε5 := by
            have htle : t ≤ ε5 / 2 := le_trans ht.2 (by dsimp [eps]; exact min_le_right _ _)
            exact lt_of_le_of_lt htle (half_lt_self hε5)
          have hdiag : D + t • hamiltonIveyMatrixReaction D =
              Matrix.diagonal ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
                l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
                l3 + t * (2 * (l3 ^ 2 + l1 * l2))] := by
            dsimp [D]
            exact diagonal_add_smul_reaction l1 l2 l3 t
          have htrD : D.trace = l1 + l2 + l3 := by
            dsimp [D]
            simp [Fin.sum_univ_three]
          have htr : (D + t • hamiltonIveyMatrixReaction D).trace = S + t * S' := by
            rw [Matrix.trace_add, Matrix.trace_smul]
            have htrQ : (hamiltonIveyMatrixReaction D).trace = S' := by
              dsimp [D, S']
              exact reactionDiagonal_trace l1 l2 l3
            dsimp [S]
            rw [htrD, htrQ]
          have hscalar_t : scalarSectionalLowerBarrier3 K (tau + t) ≤ S + t * S' :=
            hscalar1 t ht2
          have hbarrier_le : hamiltonIveyBarrier K (tau + t)
              (max (-minimumRayleighQuotient3 (D + t • hamiltonIveyMatrixReaction D)) 0) ≤ S + t * S' := by
            have hg_t : g t ≤ S / 2 := hg5 t ⟨htpos, ht5⟩
            have hS'nonneg_t : 0 ≤ t * S' := mul_nonneg ht.1 hS'nonneg
            dsimp [g] at hg_t
            nlinarith
          have hmem' : D + t • hamiltonIveyMatrixReaction D ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
            rw [hamiltonIveyConvexMatrixRegion]
            refine ⟨?_, ?_⟩
            · rw [hdiag]
              exact Matrix.isHermitian_diagonal (fun i : Fin 3 =>
                ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
                  l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
                  l3 + t * (2 * (l3 ^ 2 + l1 * l2))] i)
            · unfold hamiltonIveyConvexBarrier
              rw [htr]
              exact max_le hscalar_t hbarrier_le
          simpa [D] using hmem'

theorem hamiltonIveyConvexMatrixRegion_reaction_small_time
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : Matrix (Fin 3) (Fin 3) Real)
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegion K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
  have hA : A.IsHermitian := hAmem.1
  rcases hermitian_orthogonal_diagonalization hA with ⟨O, hOorth, hdiag⟩
  let d0 : ℝ := hA.eigenvalues₀ 0
  let d1 : ℝ := hA.eigenvalues₀ 1
  let d2 : ℝ := hA.eigenvalues₀ 2
  let D : Matrix (Fin 3) (Fin 3) Real := Matrix.diagonal ![d0, d1, d2]
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  have hdiag' : O.transpose * A * O = Matrix.diagonal ![d0, d1, d2] := by
    dsimp [d0, d1, d2]
    rw [← diagonal_eigenvalues_tuple hA]
    exact hdiag
  have hDmem : D ∈ hamiltonIveyConvexMatrixRegion K tau := by
    have hconv := (hamiltonIveyConvexMatrixRegion_orthogonal_conj (Q := O) hOorth2 hOorth).1 hAmem
    simpa [D, hdiag'] using hconv
  have h21 : d1 ≤ d0 := by
    dsimp [d1, d0]
    exact hA.eigenvalues₀_antitone (by decide)
  have h32 : d2 ≤ d1 := by
    dsimp [d2, d1]
    exact hA.eigenvalues₀_antitone (by decide)
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time_diagonal hK htau d0 d1 d2 h21 h32 hDmem
    with ⟨eps, heps, hDstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hDstep' : D + t • hamiltonIveyMatrixReaction D ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
    simpa [D] using hDstep t ht
  have hAconj : A = O * D * O.transpose := by
    dsimp [D]
    rw [← hdiag']
    calc
      A = ((O * O.transpose) * A) * (O * O.transpose) := by
        rw [hOorth]
        simp
      _ = O * (O.transpose * A * O) * O.transpose := by
        repeat rw [Matrix.mul_assoc]
  have hQconj : hamiltonIveyMatrixReaction A = O * hamiltonIveyMatrixReaction D * O.transpose := by
    have h := hamiltonIveyMatrixReaction_orthogonal_conj (O := O) (A := D) hOorth
    rw [← hAconj] at h
    exact h
  have hsum : A + t • hamiltonIveyMatrixReaction A =
      O * (D + t • hamiltonIveyMatrixReaction D) * O.transpose := by
    rw [hAconj]
    rw [hamiltonIveyMatrixReaction_orthogonal_conj (O := O) (A := D) hOorth]
    calc
      O * D * O.transpose + t • (O * hamiltonIveyMatrixReaction D * O.transpose)
          = (O * D + O * (t • hamiltonIveyMatrixReaction D)) * O.transpose := by
            rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul]
      _ = (O * (D + t • hamiltonIveyMatrixReaction D)) * O.transpose := by
            rw [← Matrix.mul_add]
  have hmem' : O * (D + t • hamiltonIveyMatrixReaction D) * O.transpose ∈
      hamiltonIveyConvexMatrixRegion K (tau + t) := by
    have hconv := (hamiltonIveyConvexMatrixRegion_orthogonal_conj (Q := O.transpose)
      (by simpa using hOorth) (by simpa using hOorth2)).1 hDstep'
    simpa [Matrix.transpose_transpose] using hconv
  simpa [hsum] using hmem'

theorem hamiltonIveyConvexMatrixRegionEuclidean_reaction_small_time
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReactionEuclidean A ∈
        hamiltonIveyConvexMatrixRegionEuclidean K (tau + t) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := euclideanToMatrix A
  have hMmem : M ∈ hamiltonIveyConvexMatrixRegion K tau := by
    simpa [M] using (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K tau A).1 hAmem
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time hK htau M hMmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : M + t • hamiltonIveyMatrixReaction M ∈
      hamiltonIveyConvexMatrixRegion K (tau + t) := hstep t ht
  have hsum : A + t • hamiltonIveyMatrixReactionEuclidean A =
      matrixToEuclidean (M + t • hamiltonIveyMatrixReaction M) := by
    dsimp [hamiltonIveyMatrixReactionEuclidean, M]
    ext ij
    simp [matrixToEuclidean, euclideanToMatrix]
  rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
  rw [hsum]
  rw [euclideanToMatrix_matrixToEuclidean]
  exact hstep'

private lemma hamiltonIveyBarrier_mono_time
    {K τ τ' X : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 ≤ X) (hττ' : τ ≤ τ') :
    hamiltonIveyBarrier K τ X ≤ hamiltonIveyBarrier K τ' X := by
  have hden1 : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hden2 : 0 < 1 + 2 * K * τ' := by
    have hKτ : 0 ≤ 2 * K * τ' := by
      have h1 : 0 ≤ K * τ' := mul_nonneg hK.le (le_trans hτ hττ')
      nlinarith
    nlinarith
  unfold hamiltonIveyBarrier
  by_cases hX0 : X = 0
  · subst hX0
    simp
  · have hlog : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hX0 hK.ne'
    have hlog' : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hX0 hK.ne'
    have hle : Real.log (1 + 2 * K * τ) ≤ Real.log (1 + 2 * K * τ') := by
      exact (Real.log_le_log_iff hden1 hden2).mpr (by nlinarith)
    have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_left hle hX]

theorem hamiltonIveyConvexMatrixRegion_antitone_time
    {K τ τ' : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (hττ' : τ ≤ τ') :
    hamiltonIveyConvexMatrixRegion K τ' ⊆ hamiltonIveyConvexMatrixRegion K τ := by
  intro A hA
  rw [hamiltonIveyConvexMatrixRegion] at hA ⊢
  refine ⟨hA.1, ?_⟩
  · let X : ℝ := max (-minimumRayleighQuotient3 A) 0
    have hX : 0 ≤ X := le_max_right _ _
    have hmono := hamiltonIveyBarrier_mono_time (K := K) (X := X) hK hτ hX hττ'
    have hscalar : scalarSectionalLowerBarrier3 K τ ≤ scalarSectionalLowerBarrier3 K τ' := by
      unfold scalarSectionalLowerBarrier3
      have hd1 : 0 < 1 + 4 * K * τ := by
        have hKτ : 0 ≤ 4 * K * τ := by
          have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
          nlinarith
        nlinarith
      have hd2 : 0 < 1 + 4 * K * τ' := by
        have hKτ : 0 ≤ 4 * K * τ' := by
          have h1 : 0 ≤ K * τ' := mul_nonneg hK.le (le_trans hτ hττ')
          nlinarith
        nlinarith
      have hdiv : 3 * K / (1 + 4 * K * τ') ≤ 3 * K / (1 + 4 * K * τ) := by
        rw [div_le_div_iff₀ hd2 hd1]
        nlinarith [mul_le_mul_of_nonneg_right hττ' (by positivity : 0 ≤ 12 * K * K)]
      have hconv1 : -3 * K / (1 + 4 * K * τ) = -(3 * K / (1 + 4 * K * τ)) := by ring
      have hconv2 : -3 * K / (1 + 4 * K * τ') = -(3 * K / (1 + 4 * K * τ')) := by ring
      rw [hconv1, hconv2]
      linarith
    have hconv : hamiltonIveyConvexBarrier K τ X ≤ hamiltonIveyConvexBarrier K τ' X := by
      unfold hamiltonIveyConvexBarrier
      exact max_le_max hscalar hmono
    have hmain := hA.2
    dsimp [X] at hmain hconv
    exact le_trans hconv hmain

private theorem hamiltonIveyConvexMatrixRegion_reaction_small_time_fixed
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : Matrix (Fin 3) (Fin 3) Real)
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegion K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K tau := by
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time hK htau A hAmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K (tau + t) :=
    hstep t ht
  exact hamiltonIveyConvexMatrixRegion_antitone_time (K := K) hK htau (by linarith [ht.1]) hstep'

private theorem hamiltonIveyConvexMatrixRegionEuclidean_reaction_small_time_fixed
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReactionEuclidean A ∈
        hamiltonIveyConvexMatrixRegionEuclidean K tau := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := euclideanToMatrix A
  have hMmem : M ∈ hamiltonIveyConvexMatrixRegion K tau := by
    simpa [M] using (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K tau A).1 hAmem
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time_fixed hK htau M hMmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : M + t • hamiltonIveyMatrixReaction M ∈
      hamiltonIveyConvexMatrixRegion K tau := hstep t ht
  have hsum : A + t • hamiltonIveyMatrixReactionEuclidean A =
      matrixToEuclidean (M + t • hamiltonIveyMatrixReaction M) := by
    dsimp [hamiltonIveyMatrixReactionEuclidean, M]
    ext ij
    simp [matrixToEuclidean, euclideanToMatrix]
  rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
  rw [hsum]
  rw [euclideanToMatrix_matrixToEuclidean]
  exact hstep'

theorem hamiltonIveyConvexMatrixRegionEuclidean_fiber_tangent
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K tau) :
    hamiltonIveyMatrixReactionEuclidean A ∈ posTangentConeAt
      (hamiltonIveyConvexMatrixRegionEuclidean K tau) A := by
  rcases hamiltonIveyConvexMatrixRegionEuclidean_reaction_small_time_fixed hK htau A hAmem
    with ⟨eps, heps, hstep⟩
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, A + t • hamiltonIveyMatrixReactionEuclidean A ∈
      hamiltonIveyConvexMatrixRegionEuclidean K tau := by
    rw [eventually_nhdsWithin_iff]
    apply Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr heps) heps)
    intro t ht _htpos
    exact hstep t ⟨_htpos.le, le_of_lt ht.2⟩
  have hfreq : ∃ᶠ t : ℝ in 𝓝[>] 0, A + t • hamiltonIveyMatrixReactionEuclidean A ∈
      hamiltonIveyConvexMatrixRegionEuclidean K tau := hev.frequently
  exact mem_posTangentConeAt_of_frequently_mem hfreq

def curvatureOperatorMatrixOfRicci (R : Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => rm R (bivectorIndex3 i).1 (bivectorIndex3 i).2 (bivectorIndex3 j).2 (bivectorIndex3 j).1

lemma curvatureOperatorReactionMatrix_eq_hamiltonIveyMatrixReaction
    (R : Fin 3 → Fin 3 → ℝ) (hR : ∀ i j, R i j = R j i) :
    (fun i j : Fin 3 => -2 * Bsharp R (bivectorIndex3 i).1 (bivectorIndex3 i).2
        (bivectorIndex3 j).2 (bivectorIndex3 j).1) =
      hamiltonIveyMatrixReaction (curvatureOperatorMatrixOfRicci R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsharp, Bt, rm, curvatureOperatorMatrixOfRicci, hamiltonIveyMatrixReaction, Matrix.mul_apply,
      Matrix.adjugate_apply, bivectorIndex3, kd, sc, Fin.sum_univ_three,
      Matrix.det_fin_three, Matrix.updateRow_apply,
      hR] <;> ring

private lemma euclid_norm_le_of_entry_le {D : Matrix (Fin 3) (Fin 3) ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i j, |D i j| ≤ C) : ‖matrixToEuclidean D‖ ≤ 3 * C := by
  rw [matrixToEuclidean_norm, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ 3 * C)]
  apply Real.sqrt_le_sqrt
  calc
      (∑ i, ∑ j, ‖D i j‖ ^ (2 : ℝ)) = ∑ i, ∑ j, ‖D i j‖ ^ 2 := by
        simp_rw [Real.rpow_two]
    _ = ∑ ij : Fin 3 × Fin 3, ‖D ij.1 ij.2‖ ^ 2 := by
        rw [← Finset.sum_product', Finset.univ_product_univ]
    _ ≤ ∑ ij : Fin 3 × Fin 3, C ^ 2 := by
        apply Finset.sum_le_sum
        intro ij hij
        exact pow_le_pow_left₀ (by positivity) (by simpa [abs_of_nonneg] using hD ij.1 ij.2) 2
    _ = (3 * C) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

private lemma matrix_product_entry_sub_abs_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclidean A‖ ≤ R) (hB : ‖matrixToEuclidean B‖ ≤ R)
    (p q r s : Fin 3) :
    |A p q * A r s - B p q * B r s| ≤ 2 * R * ‖matrixToEuclidean (A - B)‖ := by
  have h1 : |A p q - B p q| ≤ ‖matrixToEuclidean (A - B)‖ := by
    have h := euclid_entry_le_norm (matrixToEuclidean (A - B)) (p, q)
    simpa [matrixToEuclidean_sub] using h
  have h2 : |A r s| ≤ R := by
    have h := euclid_entry_le_norm (matrixToEuclidean A) (r, s)
    simpa using le_trans h hA
  have h3 : |B p q| ≤ R := by
    have h := euclid_entry_le_norm (matrixToEuclidean B) (p, q)
    simpa using le_trans h hB
  have h4 : |A r s - B r s| ≤ ‖matrixToEuclidean (A - B)‖ := by
    have h := euclid_entry_le_norm (matrixToEuclidean (A - B)) (r, s)
    simpa [matrixToEuclidean_sub] using h
  calc
    |A p q * A r s - B p q * B r s| ≤
        |A p q * A r s - B p q * A r s| + |B p q * A r s - B p q * B r s| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        abs_sub_le (A p q * A r s) (B p q * A r s) (B p q * B r s)
    _ = |A p q - B p q| * |A r s| + |B p q| * |A r s - B r s| := by
      rw [← sub_mul, ← mul_sub, abs_mul, abs_mul]
    _ ≤ ‖matrixToEuclidean (A - B)‖ * R + R * ‖matrixToEuclidean (A - B)‖ := by
      exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul h3 h4 (abs_nonneg _) hR)
    _ = 2 * R * ‖matrixToEuclidean (A - B)‖ := by ring

private lemma two_monomial_sub_abs_le (x1 x2 y1 y2 z1 z2 w1 w2 : ℝ) :
    |(x1 * x2 - y1 * y2) - (z1 * z2 - w1 * w2)| ≤
      |x1 * x2 - z1 * z2| + |y1 * y2 - w1 * w2| := by
  have h : (x1 * x2 - y1 * y2) - (z1 * z2 - w1 * w2) =
      (x1 * x2 - z1 * z2) - (y1 * y2 - w1 * w2) := by ring
  rw [h]
  simpa [sub_zero, abs_neg, abs_sub_comm] using
    (abs_sub_le (x1 * x2 - z1 * z2) (0 : ℝ) (y1 * y2 - w1 * w2))

private lemma two_monomial_sub_abs_le' (x1 x2 y1 y2 z1 z2 w1 w2 : ℝ) :
    |-(x1 * x2) + y1 * y2 - (-(z1 * z2) + w1 * w2)| ≤
      |x1 * x2 - z1 * z2| + |y1 * y2 - w1 * w2| := by
  have h : -(x1 * x2) + y1 * y2 - (-(z1 * z2) + w1 * w2) =
      (y1 * y2 - x1 * x2) - (w1 * w2 - z1 * z2) := by ring
  rw [h]
  simpa [add_comm] using two_monomial_sub_abs_le y1 y2 x1 x2 w1 w2 z1 z2

private lemma matrix_adjugate_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclidean A‖ ≤ R) (hB : ‖matrixToEuclidean B‖ ≤ R) :
    ‖matrixToEuclidean (A.adjugate - B.adjugate)‖ ≤
      12 * R * ‖matrixToEuclidean (A - B)‖ := by
  have hnorm : ‖matrixToEuclidean (A.adjugate - B.adjugate)‖ ≤
      3 * (4 * R * ‖matrixToEuclidean (A - B)‖) := by
    apply euclid_norm_le_of_entry_le
    · positivity
    · intro i j
      simp_rw [Matrix.adjugate_fin_three]
      fin_cases i <;> fin_cases j <;> simp
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 1 2 2
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 2 2 1
        have h := two_monomial_sub_abs_le (A 1 1) (A 2 2) (A 1 2) (A 2 1)
          (B 1 1) (B 2 2) (B 1 2) (B 2 1)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 2 2 1
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 1 2 2
        have h := two_monomial_sub_abs_le' (A 0 1) (A 2 2) (A 0 2) (A 2 1)
          (B 0 1) (B 2 2) (B 0 2) (B 2 1)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 1 1 2
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 2 1 1
        have h := two_monomial_sub_abs_le (A 0 1) (A 1 2) (A 0 2) (A 1 1)
          (B 0 1) (B 1 2) (B 0 2) (B 1 1)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 2 2 0
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 0 2 2
        have h := two_monomial_sub_abs_le' (A 1 0) (A 2 2) (A 1 2) (A 2 0)
          (B 1 0) (B 2 2) (B 1 2) (B 2 0)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 0 2 2
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 2 2 0
        have h := two_monomial_sub_abs_le (A 0 0) (A 2 2) (A 0 2) (A 2 0)
          (B 0 0) (B 2 2) (B 0 2) (B 2 0)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 2 1 0
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 0 1 2
        have h := two_monomial_sub_abs_le' (A 0 0) (A 1 2) (A 0 2) (A 1 0)
          (B 0 0) (B 1 2) (B 0 2) (B 1 0)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 0 2 1
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 1 1 2 0
        have h := two_monomial_sub_abs_le (A 1 0) (A 2 1) (A 1 1) (A 2 0)
          (B 1 0) (B 2 1) (B 1 1) (B 2 0)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 1 2 0
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 0 2 1
        have h := two_monomial_sub_abs_le' (A 0 0) (A 2 1) (A 0 1) (A 2 0)
          (B 0 0) (B 2 1) (B 0 1) (B 2 0)
        nlinarith
      · have h1 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 0 1 1
        have h2 := matrix_product_entry_sub_abs_le A B R hR hA hB 0 1 1 0
        have h := two_monomial_sub_abs_le (A 0 0) (A 1 1) (A 0 1) (A 1 0)
          (B 0 0) (B 1 1) (B 0 1) (B 1 0)
        nlinarith
  nlinarith [hnorm]

private lemma matrix_square_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ)
    (hA : ‖matrixToEuclidean A‖ ≤ R) (hB : ‖matrixToEuclidean B‖ ≤ R) :
    ‖matrixToEuclidean (A * A - B * B)‖ ≤ 2 * R * ‖matrixToEuclidean (A - B)‖ := by
  have hident : A * A - B * B = A * (A - B) + (A - B) * B := by
    ext i j
    simp [Matrix.mul_apply, sub_mul, mul_sub]
  calc
    ‖matrixToEuclidean (A * A - B * B)‖ = ‖matrixToEuclidean (A * (A - B) + (A - B) * B)‖ := by
      rw [hident]
    _ ≤ ‖matrixToEuclidean (A * (A - B))‖ + ‖matrixToEuclidean ((A - B) * B)‖ := by
      rw [matrixToEuclidean_add]
      exact norm_add_le _ _
    _ ≤ ‖matrixToEuclidean A‖ * ‖matrixToEuclidean (A - B)‖ +
        ‖matrixToEuclidean (A - B)‖ * ‖matrixToEuclidean B‖ := by
      exact add_le_add (matrixToEuclidean_mul_norm_le A (A - B))
        (matrixToEuclidean_mul_norm_le (A - B) B)
    _ ≤ R * ‖matrixToEuclidean (A - B)‖ + ‖matrixToEuclidean (A - B)‖ * R := by
      have h1 : ‖matrixToEuclidean A‖ * ‖matrixToEuclidean (A - B)‖ ≤
          R * ‖matrixToEuclidean (A - B)‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      have h2 : ‖matrixToEuclidean (A - B)‖ * ‖matrixToEuclidean B‖ ≤
          ‖matrixToEuclidean (A - B)‖ * R :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg _)
      exact add_le_add h1 h2
    _ = 2 * R * ‖matrixToEuclidean (A - B)‖ := by ring

private lemma hamiltonIveyMatrixReaction_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclidean A‖ ≤ R) (hB : ‖matrixToEuclidean B‖ ≤ R) :
    ‖matrixToEuclidean (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ ≤
      28 * R * ‖matrixToEuclidean (A - B)‖ := by
  have hsq := matrix_square_sub_norm_le A B R hA hB
  have hadj := matrix_adjugate_sub_norm_le A B R hR hA hB
  have hsum : matrixToEuclidean (A * A - B * B + (A.adjugate - B.adjugate)) =
      matrixToEuclidean (A * A - B * B) + matrixToEuclidean (A.adjugate - B.adjugate) := by
    exact matrixToEuclidean_add (A * A - B * B) (A.adjugate - B.adjugate)
  have hnorm : ‖matrixToEuclidean (A * A - B * B + (A.adjugate - B.adjugate))‖ ≤
      2 * R * ‖matrixToEuclidean (A - B)‖ + 12 * R * ‖matrixToEuclidean (A - B)‖ := by
    rw [hsum]
    exact (norm_add_le (matrixToEuclidean (A * A - B * B))
      (matrixToEuclidean (A.adjugate - B.adjugate))).trans (add_le_add hsq hadj)
  calc
    ‖matrixToEuclidean (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ = ‖
        matrixToEuclidean ((2 : ℝ) • (A * A - B * B + (A.adjugate - B.adjugate)))‖ := by
      congr 1
      ext ij
      unfold hamiltonIveyMatrixReaction
      simp only [matrixToEuclidean, WithLp.ofLp_toLp, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul]
      ring
    _ = 2 * ‖matrixToEuclidean (A * A - B * B + (A.adjugate - B.adjugate))‖ := by
      rw [matrixToEuclidean_smul (2 : ℝ)]
      rw [norm_smul]
      norm_num
    _ ≤ 2 * (2 * R * ‖matrixToEuclidean (A - B)‖ + 12 * R * ‖matrixToEuclidean (A - B)‖) := by
      exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = 28 * R * ‖matrixToEuclidean (A - B)‖ := by ring

private lemma hamiltonIveyMatrixReactionEuclidean_sub_norm_le
    (a b : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (R : ℝ) (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖hamiltonIveyMatrixReactionEuclidean a - hamiltonIveyMatrixReactionEuclidean b‖ ≤
      28 * R * ‖a - b‖ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := euclideanToMatrix a
  let B : Matrix (Fin 3) (Fin 3) ℝ := euclideanToMatrix b
  have hA : ‖matrixToEuclidean A‖ ≤ R := by
    dsimp [A]
    simpa [euclideanToMatrix_norm_eq] using ha
  have hB : ‖matrixToEuclidean B‖ ≤ R := by
    dsimp [B]
    simpa [euclideanToMatrix_norm_eq] using hb
  have hmain : ‖matrixToEuclidean (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ ≤
      28 * R * ‖matrixToEuclidean (A - B)‖ :=
    hamiltonIveyMatrixReaction_sub_norm_le A B R hR hA hB
  have hdiff : matrixToEuclidean (A - B) = a - b := by
    dsimp [A, B]
    rw [matrixToEuclidean_sub]
    rw [matrixToEuclidean_euclideanToMatrix, matrixToEuclidean_euclideanToMatrix]
  have hlhs : matrixToEuclidean (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B) =
      hamiltonIveyMatrixReactionEuclidean a - hamiltonIveyMatrixReactionEuclidean b := by
    dsimp [A, B, hamiltonIveyMatrixReactionEuclidean]
    rw [matrixToEuclidean_sub]
  rw [hlhs, hdiff] at hmain
  exact hmain

theorem hamiltonIveyMatrixReactionEuclidean_lipschitzOn_closedBall
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : NNReal, LipschitzOnWith L hamiltonIveyMatrixReactionEuclidean
      (Metric.closedBall 0 R) := by
  refine ⟨⟨28 * R, by positivity⟩, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro a ha b hb
  rw [dist_eq_norm, dist_eq_norm]
  exact hamiltonIveyMatrixReactionEuclidean_sub_norm_le a b R hR
    (mem_closedBall_zero_iff.mp ha) (mem_closedBall_zero_iff.mp hb)

noncomputable def hamiltonIveyConvexMatrixRegionSupportEuclidean (K τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) : ℝ :=
  let ν₁ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0
  let ν₂ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 1
  let ν₃ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 2
  if ν₁ < 0 then
    sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
      x = hamiltonIveyConvexBarrier K τ X * ν₁ + X * (2 * ν₁ - ν₂ - ν₃)}
  else 0

private lemma hamiltonIveyConvexBarrier_eq_scalarLower_at_feasible_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    hamiltonIveyConvexBarrier K τ (K / (1 + 4 * K * τ)) =
      scalarSectionalLowerBarrier3 K τ := by
  unfold hamiltonIveyConvexBarrier scalarSectionalLowerBarrier3
  have hden4 : 0 < 1 + 4 * K * τ := by
    have hKτ : 0 ≤ 4 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hden2 : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hXpos : 0 < K / (1 + 4 * K * τ) := div_pos hK hden4
  have hXsub : K / (1 + 4 * K * τ) ≤ K / (1 + 2 * K * τ) := by
    exact div_le_div_of_nonneg_left hK.le hden2 (by nlinarith)
  have hbar_le : hamiltonIveyBarrier K τ (K / (1 + 4 * K * τ)) ≤
      -3 * (K / (1 + 4 * K * τ)) :=
    hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion hK hden2 hXpos.le hXsub
  have hEq : -3 * (K / (1 + 4 * K * τ)) = -3 * K / (1 + 4 * K * τ) := by
    field_simp [hden4.ne']
  have hbarsc : hamiltonIveyBarrier K τ (K / (1 + 4 * K * τ)) ≤
      -3 * K / (1 + 4 * K * τ) := by
    simpa [hEq] using hbar_le
  rw [max_eq_left hbarsc]

private lemma barrier_ge_scalar (K τ X : ℝ) :
    scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyConvexBarrier K τ X := by
  unfold hamiltonIveyConvexBarrier
  exact le_max_left _ _

private lemma support_formula_le_at_feasible_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    {X : ℝ} (hXle : X ≤ K / (1 + 4 * K * τ)) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      hamiltonIveyConvexBarrier K τ (K / (1 + 4 * K * τ)) * ν 0 +
        (K / (1 + 4 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) := by
  let B : ℝ → ℝ := fun Y => hamiltonIveyConvexBarrier K τ Y
  have hBge : B (K / (1 + 4 * K * τ)) ≤ B X := by
    have hB0 : B (K / (1 + 4 * K * τ)) = scalarSectionalLowerBarrier3 K τ := by
      simpa [B] using hamiltonIveyConvexBarrier_eq_scalarLower_at_feasible_point hK hτ
    have hB : scalarSectionalLowerBarrier3 K τ ≤ B X := by
      simpa [B] using barrier_ge_scalar K τ X
    rw [hB0]
    exact hB
  have hc_nonneg : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hXle' : X - K / (1 + 4 * K * τ) ≤ 0 := by linarith
  have hmul : ν 0 * (B X - B (K / (1 + 4 * K * τ))) ≤ 0 := by
    have hneg : ν 0 ≤ 0 := hν0.le
    exact mul_nonpos_of_nonpos_of_nonneg hneg (sub_nonneg.mpr hBge)
  have hlin : (X - K / (1 + 4 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hXle' hc_nonneg
  dsimp [B] at hBge
  nlinarith

private lemma diagonal_extremal_mem_region
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {X : ℝ} (hX : K / (1 + 4 * K * τ) ≤ X) :
    Matrix.diagonal ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X] ∈
      hamiltonIveyConvexMatrixRegion K τ := by
  let D : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
  let d : Fin 3 → ℝ := ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
  have hd_antitone : Antitone d := by
    have hB : -3 * X ≤ hamiltonIveyConvexBarrier K τ X := by
      have hsc : scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyConvexBarrier K τ X :=
        barrier_ge_scalar K τ X
      have hsc_le : -3 * X ≤ scalarSectionalLowerBarrier3 K τ := by
        unfold scalarSectionalLowerBarrier3
        have hden : 0 < 1 + 4 * K * τ := by
          have hKτ : 0 ≤ 4 * K * τ := by
            have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
            nlinarith
          nlinarith
        have hX₀ : K ≤ X * (1 + 4 * K * τ) := by
          exact (div_le_iff₀ hden).mp hX
        rw [le_div_iff₀ hden]
        nlinarith
      exact hsc_le.trans hsc
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp [d]
    · dsimp [d]
      nlinarith [hB]
    · dsimp [d]
      nlinarith [hB]
    · norm_num at hij
    · simp [d]
    · simp [d]
    · norm_num at hij
    · simp [d]
    · simp [d]
  rw [hamiltonIveyConvexMatrixRegion]
  refine ⟨?_, ?_⟩
  · exact Matrix.isHermitian_diagonal d
  · have hmin : minimumRayleighQuotient3 D = -X := by
      have heig : (Matrix.isHermitian_diagonal d).eigenvalues₀ = d :=
        diagonal_eigenvalues₀_eq_of_antitone d hd_antitone
      have hmineig : minimumRayleighQuotient3 D = (Matrix.isHermitian_diagonal d).eigenvalues₀ 2 := by
        exact minimumRayleighQuotient3_eq_min_eigenvalue (hA := Matrix.isHermitian_diagonal d)
      rw [hmineig, heig]
      simp [d]
    rw [hmin]
    have htrace : D.trace = hamiltonIveyConvexBarrier K τ X := by
      dsimp [D, d]
      rw [Matrix.trace]
      simp [Matrix.diag, Fin.sum_univ_three]
      ring
    rw [htrace]
    have hX0 : 0 ≤ X := by
      have hX₀pos : 0 < K / (1 + 4 * K * τ) := by
        have hden : 0 < 1 + 4 * K * τ := by
          have hKτ : 0 ≤ 4 * K * τ := by
            have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
            nlinarith
          nlinarith
        exact div_pos hK hden
      linarith
    simp [hX0]

private lemma inner_le_support_formula_of_mem_region
    {K τ : ℝ}
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean A) ≤
      hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 A) 0) * ν 0 +
        max (-minimumRayleighQuotient3 A) 0 * (2 * ν 0 - ν 1 - ν 2) := by
  rw [hamiltonIveyConvexMatrixRegion] at hA
  rcases hA with ⟨hAh, hbar⟩
  have hle := inner_diag_le_eigen_bound hν A hAh
  have hmin : minimumRayleighQuotient3 A = hAh.eigenvalues₀ 2 :=
    minimumRayleighQuotient3_eq_min_eigenvalue (hA := hAh)
  have hle' : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean A) ≤
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-minimumRayleighQuotient3 A) 0 := by
    simpa [hmin] using hle
  have hmul : ν 0 * A.trace ≤
      ν 0 * hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 A) 0) := by
    exact mul_le_mul_of_nonpos_left hbar hν0.le
  have hmain : ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-minimumRayleighQuotient3 A) 0 ≤
      hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 A) 0) * ν 0 +
        max (-minimumRayleighQuotient3 A) 0 * (2 * ν 0 - ν 1 - ν 2) := by
    rw [mul_comm (hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 A) 0)) (ν 0)]
    nlinarith [hmul]
  exact le_trans hle' hmain


private lemma support_formula_tail_nonpos
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0)
    {X : ℝ} (hX : 0 < X)
    (hL : (ν 0 + ν 1 + ν 2) / ν 0 ≤ Real.log (X * (1 + 2 * K * τ) / K)) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤ 0 := by
  let S : ℝ := ν 0 + ν 1 + ν 2
  let L : ℝ := Real.log (X * (1 + 2 * K * τ) / K)
  have hBh : hamiltonIveyBarrier K τ X ≤ hamiltonIveyConvexBarrier K τ X :=
    hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K τ X
  have hmul : ν 0 * hamiltonIveyConvexBarrier K τ X ≤ ν 0 * hamiltonIveyBarrier K τ X :=
    mul_le_mul_of_nonpos_left hBh hν0.le
  have hden : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have harg : 0 < X * (1 + 2 * K * τ) / K := by positivity
  have hlog : Real.log (X / K) + Real.log (1 + 2 * K * τ) = L := by
    dsimp [L]
    have h1 : Real.log (X / K) = Real.log X - Real.log K :=
      Real.log_div hX.ne' hK.ne'
    have h2 : Real.log ((X * (1 + 2 * K * τ)) / K) =
        Real.log (X * (1 + 2 * K * τ)) - Real.log K :=
      Real.log_div (mul_pos hX hden).ne' hK.ne'
    have h3 : Real.log (X * (1 + 2 * K * τ)) =
        Real.log X + Real.log (1 + 2 * K * τ) :=
      Real.log_mul hX.ne' hden.ne'
    rw [h1, h2, h3]
    ring_nf
  have hbar : hamiltonIveyBarrier K τ X = X * (L - 3) := by
    unfold hamiltonIveyBarrier
    rw [hlog]
  have hmain : ν 0 * hamiltonIveyBarrier K τ X + X * (2 * ν 0 - ν 1 - ν 2) =
      X * (ν 0 * L - S) := by
    dsimp [S]
    rw [hbar]
    ring
  have hFle : hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      X * (ν 0 * L - S) := by
    rw [← hmain]
    nlinarith
  have hL' : ν 0 * L - S ≤ 0 := by
    have hm := mul_le_mul_of_nonpos_left hL hν0.le
    have hred : ν 0 * (S / ν 0) = S := mul_div_cancel₀ S (Ne.symm hν0.ne')
    dsimp [S] at hm hred ⊢
    nlinarith
  nlinarith [hFle, hL']

private lemma support_formula_bddAbove
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) :
    BddAbove {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
      x = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)} := by
  let F : ℝ → ℝ := fun X => hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let S : ℝ := ν 0 + ν 1 + ν 2
  let X₁ : ℝ := K * Real.exp (S / ν 0) / (1 + 2 * K * τ)
  have hden : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hX₁ : 0 < X₁ := by
    dsimp [X₁]
    positivity
  have htail : ∀ X, X₁ ≤ X → F X ≤ 0 := by
    intro X hX
    have hXpos : 0 < X := lt_of_lt_of_le hX₁ hX
    have harg1 : 0 < X₁ * (1 + 2 * K * τ) / K := by positivity
    have harg2 : 0 < X * (1 + 2 * K * τ) / K := by positivity
    have hmono : Real.log (X₁ * (1 + 2 * K * τ) / K) ≤
        Real.log (X * (1 + 2 * K * τ) / K) := by
      refine (Real.log_le_log_iff harg1 harg2).mpr ?_
      have hmul : X₁ * (1 + 2 * K * τ) ≤ X * (1 + 2 * K * τ) :=
        mul_le_mul_of_nonneg_right hX (by positivity : 0 ≤ (1 + 2 * K * τ))
      exact div_le_div_of_nonneg_right hmul hK.le
    have hlogX₁ : Real.log (X₁ * (1 + 2 * K * τ) / K) = S / ν 0 := by
      have hX₁eq : X₁ * (1 + 2 * K * τ) / K = Real.exp (S / ν 0) := by
        dsimp [X₁]
        field_simp [hK.ne', hden.ne']
      rw [hX₁eq]
      exact Real.log_exp (S / ν 0)
    have hL : S / ν 0 ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
      linarith
    exact support_formula_tail_nonpos hK hτ hν0 hXpos hL
  have hcont : ContinuousOn F (Set.Icc 0 X₁) := by
    dsimp [F]
    have hB : ContinuousOn (fun X : ℝ => hamiltonIveyConvexBarrier K τ X) (Set.Icc 0 X₁) :=
      (continuous_hamiltonIveyConvexBarrier hK).continuousOn
    have hBν : ContinuousOn (fun X : ℝ => hamiltonIveyConvexBarrier K τ X * ν 0)
        (Set.Icc 0 X₁) := hB.mul continuousOn_const
    have hXc : ContinuousOn (fun X : ℝ => X * (2 * ν 0 - ν 1 - ν 2))
        (Set.Icc 0 X₁) := by fun_prop
    exact hBν.add hXc
  have hbdd₁ : BddAbove (F '' Set.Icc 0 X₁) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := X₁)).bddAbove_image hcont
  rcases hbdd₁ with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  rintro x ⟨X, hX, rfl⟩
  by_cases hX₁le : X ≤ X₁
  · have hXmem : X ∈ Set.Icc 0 X₁ := ⟨hX, hX₁le⟩
    have hle : F X ≤ C := hC ⟨X, hXmem, rfl⟩
    exact le_trans hle (le_max_left _ _)
  · have hX₁le' : X₁ ≤ X := le_of_lt (lt_of_not_ge hX₁le)
    exact le_trans (htail X hX₁le') (le_max_right _ _)


private lemma support_formula_feasible_le_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    (X : ℝ) (hX₀ : K / (1 + 4 * K * τ) ≤ X) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        (matrixToEuclidean (Matrix.diagonal ν)) := by
  let l : Fin 3 → ℝ := ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal l
  let S : Set ℝ := {y | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
    B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
      y = inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B}
  have hbdd : BddAbove S := by
    have hbddF := support_formula_bddAbove hK hτ hν0
    rcases hbddF with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨B, hBmem, rfl⟩
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
      exact (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hBmem
    have hinner : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B ≤
        hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
          max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
      inner_le_support_formula_of_mem_region hν hν0 (euclideanToMatrix B) hBm
    have hF : hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
          max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤ C := by
      exact hC ⟨max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0, (le_max_right _ _), rfl⟩
    exact le_trans hinner hF
  have hDmem : D ∈ hamiltonIveyConvexMatrixRegion K τ :=
    diagonal_extremal_mem_region hK hτ hX₀
  have hDmemE : matrixToEuclidean D ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
    simpa [D, l, euclideanToMatrix_matrixToEuclidean] using hDmem
  have hinner_eq : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean D) =
      hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) := by
    have hdd := inner_diag_diag ν l
    dsimp [D, l] at hdd
    rw [hdd]
    simp [Fin.sum_univ_three]
    ring
  unfold supportFunction
  exact le_csSup hbdd ⟨matrixToEuclidean D, hDmemE, hinner_eq.symm⟩

private lemma support_formula_le_supportFunction_diag
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) (X : ℝ) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        (matrixToEuclidean (Matrix.diagonal ν)) := by
  by_cases hX₀ : K / (1 + 4 * K * τ) ≤ X
  · exact support_formula_feasible_le_supportFunction hK hτ hν hν0 X hX₀
  · have hX₀le : X ≤ K / (1 + 4 * K * τ) := le_of_not_ge hX₀
    have hFle := support_formula_le_at_feasible_point hK hτ hν hν0 hX₀le
    have hF₀le : hamiltonIveyConvexBarrier K τ (K / (1 + 4 * K * τ)) * ν 0 +
          (K / (1 + 4 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) ≤
        supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
          (matrixToEuclidean (Matrix.diagonal ν)) :=
      support_formula_feasible_le_supportFunction hK hτ hν hν0
        (K / (1 + 4 * K * τ)) le_rfl
    exact le_trans hFle hF₀le

private lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_diag_eq_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal ν)) =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        (matrixToEuclidean (Matrix.diagonal ν)) := by
  have hsymm : euclideanMatrixSymmetrization (matrixToEuclidean (Matrix.diagonal ν)) = Matrix.diagonal ν := by
    ext i j
    dsimp [euclideanMatrixSymmetrization, euclideanToMatrix]
    by_cases h : i = j
    · simp [h, matrixToEuclidean, Matrix.diagonal]
      ring
    · simp [h, matrixToEuclidean, Matrix.diagonal, Ne.symm h]
  have hν' : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ = ν := by
    have hchar : (euclideanMatrixSymmetrization (matrixToEuclidean (Matrix.diagonal ν))).charpoly =
        (Matrix.diagonal ν).charpoly := by
      rw [hsymm]
    have heig' : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ =
        (Matrix.isHermitian_diagonal ν).eigenvalues₀ :=
      eigenvalues₀_eq_of_charpoly_eq_real
        (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν)))
        (Matrix.isHermitian_diagonal ν) hchar
    have heig : (Matrix.isHermitian_diagonal ν).eigenvalues₀ = ν :=
      diagonal_eigenvalues₀_eq_of_antitone ν hν
    exact heig'.trans heig
  let Fset : Set ℝ := {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
    x = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)}
  have hdef_eq : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (Matrix.diagonal ν)) = sSup Fset := by
    unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
    rw [hν']
    dsimp
    exact (if_pos hν0).trans rfl
  have hbddF : BddAbove Fset := by
    dsimp [Fset]
    exact support_formula_bddAbove hK hτ hν0
  have hFne : Fset.Nonempty :=
    ⟨hamiltonIveyConvexBarrier K τ 0 * ν 0 + 0 * (2 * ν 0 - ν 1 - ν 2), 0, le_rfl, rfl⟩
  have hdef_le : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (Matrix.diagonal ν)) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        (matrixToEuclidean (Matrix.diagonal ν)) := by
    rw [hdef_eq]
    refine csSup_le hFne ?_
    rintro x ⟨X, hX, rfl⟩
    exact support_formula_le_supportFunction_diag hK hτ hν hν0 X
  have hsup_le : supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
      (matrixToEuclidean (Matrix.diagonal ν)) ≤
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal ν)) := by
    let S : Set ℝ := {y | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
      B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
        y = inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B}
    have hSne : S.Nonempty := by
      rcases nonempty_hamiltonIveyConvexMatrixRegionEuclidean hK hτ with ⟨B, hB⟩
      refine ⟨inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B, B, hB, rfl⟩
    have hbddS : BddAbove S := by
      have hbddF' := support_formula_bddAbove hK hτ hν0
      rcases hbddF' with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro y ⟨B, hBmem, rfl⟩
      have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
        exact (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hBmem
      have hinner : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B ≤
          hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
            max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
        inner_le_support_formula_of_mem_region hν hν0 (euclideanToMatrix B) hBm
      have hF : hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
            max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤ C := by
        exact hC ⟨max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0, (le_max_right _ _), rfl⟩
      exact le_trans hinner hF
    unfold supportFunction
    refine csSup_le hSne ?_
    rintro y ⟨B, hBmem, rfl⟩
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
      exact (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hBmem
    have hinner : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) B ≤
        hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
          max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
      inner_le_support_formula_of_mem_region hν hν0 (euclideanToMatrix B) hBm
    have hFle : hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * ν 0 +
          max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤
        hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal ν)) := by
      rw [hdef_eq]
      exact le_csSup hbddF
        ⟨max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0, (le_max_right _ _), rfl⟩
    exact le_trans hinner hFle
  exact le_antisymm hdef_le hsup_le

private lemma inner_symm_of_region_mem
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    inner ℝ v A =
      inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean (euclideanToMatrix A)) := by
  have hAm : (euclideanToMatrix A).IsHermitian := by
    have hmem : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
    rw [hamiltonIveyConvexMatrixRegion] at hmem
    exact hmem.1
  simpa [matrixToEuclidean_euclideanToMatrix] using inner_matrixToEuclidean_symm v (euclideanToMatrix A) hAm

private lemma supportFunction_rotate_diag
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) v =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) := by
  let S : Matrix (Fin 3) (Fin 3) ℝ := euclideanMatrixSymmetrization v
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  rcases hermitian_orthogonal_diagonalization (euclideanMatrixSymmetrization_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  have hdiag' : O.transpose * S * O = Matrix.diagonal nv := by
    simpa [S, nv] using hdiag
  let φ : EuclideanSpace ℝ (Fin 3 × Fin 3) → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun A => matrixToEuclidean (O.transpose * euclideanToMatrix A * O)
  have hφ_mem : ∀ A, A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ →
      φ A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
    intro A hA
    have hAm : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O) hOorth2 hOorth).1 hAm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
    dsimp [φ]
    simpa [euclideanToMatrix_matrixToEuclidean] using hconj
  have hφ_inv : ∀ B, B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ →
      ∃ A, A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ φ A = B := by
    intro B hB
    let A : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
      matrixToEuclidean (O * euclideanToMatrix B * O.transpose)
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hB
    have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
      have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
        (Q := O.transpose) (by simpa using hOorth) (by simpa using hOorth2)).1 hBm
      rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
      dsimp [A]
      simpa [euclideanToMatrix_matrixToEuclidean, Matrix.transpose_transpose] using hconj
    refine ⟨A, hA, ?_⟩
    dsimp [φ, A]
    rw [euclideanToMatrix_matrixToEuclidean]
    have hmat : O.transpose * (O * euclideanToMatrix B * O.transpose) * O = euclideanToMatrix B := by
      simp only [Matrix.mul_assoc]
      rw [hOorth2]
      simp only [Matrix.mul_one]
      rw [← Matrix.mul_assoc]
      rw [hOorth2]
      simp only [Matrix.one_mul]
    rw [hmat, matrixToEuclidean_euclideanToMatrix]
  have hinner_eq : ∀ A, A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ →
      inner ℝ v A = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) (φ A) := by
    intro A hA
    have hAm : (euclideanToMatrix A).IsHermitian := by
      have hmem : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
        (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
      rw [hamiltonIveyConvexMatrixRegion] at hmem
      exact hmem.1
    calc
      inner ℝ v A = inner ℝ (matrixToEuclidean S) (matrixToEuclidean (euclideanToMatrix A)) := by
            dsimp [S]
            exact inner_symm_of_region_mem v A hA
      _ = inner ℝ (matrixToEuclidean (O.transpose * S * O))
            (matrixToEuclidean (O.transpose * (euclideanToMatrix A) * O)) := by
            exact inner_matrixToEuclidean_orthogonal_conj S (euclideanToMatrix A) O hOorth
      _ = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) (φ A) := by
            dsimp [φ]
            rw [hdiag']
  unfold supportFunction
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨φ A, hφ_mem A hA, ?_⟩
    exact hinner_eq A hA
  · rintro ⟨B, hB, rfl⟩
    rcases hφ_inv B hB with ⟨A, hA, rfl⟩
    refine ⟨A, hA, ?_⟩
    exact (hinner_eq A hA).symm

theorem hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) v := by
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀_antitone
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hdef : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) := by
    unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
    rw [euclideanMatrixSymmetrization_diag_eigenvalues₀ nv hnv_anti]
  calc
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v
        = hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) := hdef
    _ = supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ)
          (matrixToEuclidean (Matrix.diagonal nv)) :=
          hamiltonIveyConvexMatrixRegionSupportEuclidean_diag_eq_supportFunction hK hτ hnv_anti hnv0
    _ = supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) v :=
          (supportFunction_rotate_diag v).symm

private lemma exists_rotate_diag_of_mem_region
    {K τ : ℝ}
    (v A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
      B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
      inner ℝ v A =
        inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
  rcases hermitian_orthogonal_diagonalization (euclideanMatrixSymmetrization_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let B : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclidean (O.transpose * euclideanToMatrix A * O)
  have hB : B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
    have hAm : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O) hOorth2 hOorth).1 hAm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
    dsimp [B]
    simpa [euclideanToMatrix_matrixToEuclidean] using hconj
  have hinner :
      inner ℝ v A = inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
    have hAm : (euclideanToMatrix A).IsHermitian := by
      have hmem : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
        (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
      rw [hamiltonIveyConvexMatrixRegion] at hmem
      exact hmem.1
    have hsymm : inner ℝ v A = inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean (euclideanToMatrix A)) := by
      simpa [matrixToEuclidean_euclideanToMatrix] using inner_matrixToEuclidean_symm v (euclideanToMatrix A) hAm
    have hdiagO : inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean (euclideanToMatrix A)) =
        inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
      have hconj := inner_matrixToEuclidean_orthogonal_conj (euclideanMatrixSymmetrization v) (euclideanToMatrix A) O hOorth
      dsimp [B]
      rw [hconj]
      have hdiag' : O.transpose * euclideanMatrixSymmetrization v * O =
          Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ := by
        simpa using hdiag
      rw [hdiag']
      rfl
    rw [hsymm]
    exact hdiagO
  exact ⟨B, hB, hinner⟩

private lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_rotate_diag
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
        (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) := by
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀_antitone
  unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
  rw [euclideanMatrixSymmetrization_diag_eigenvalues₀ nv hnv_anti]

private lemma inner_le_supportFunction_of_mem_region
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    inner ℝ v A ≤ hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v := by
  rcases exists_rotate_diag_of_mem_region v A hA with ⟨B, hB, hinner⟩
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀_antitone
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hBle : inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) B ≤
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) := by
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hB
    have hle1 := inner_le_support_formula_of_mem_region hnv_anti hnv0 (euclideanToMatrix B) hBm
    have hFle := support_formula_le_supportFunction_diag hK hτ hnv_anti hnv0
      (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0)
    have hdef : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) =
        supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) (matrixToEuclidean (Matrix.diagonal nv)) :=
      hamiltonIveyConvexMatrixRegionSupportEuclidean_diag_eq_supportFunction hK hτ hnv_anti hnv0
    have hle2 : hamiltonIveyConvexBarrier K τ (max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0) * nv 0 +
          max (-minimumRayleighQuotient3 (euclideanToMatrix B)) 0 * (2 * nv 0 - nv 1 - nv 2) ≤
        hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) := by
      rw [hdef]
      exact hFle
    exact le_trans hle1 hle2
  have hinner' : inner ℝ v A = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) B := by
    simpa [nv] using hinner
  rw [hamiltonIveyConvexMatrixRegionSupportEuclidean_rotate_diag]
  rw [hinner']
  exact hBle

private lemma support_formula_unbounded_of_nonneg_top
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : 0 ≤ ν 0)
    (hne : ν ≠ 0) :
    ¬ BddAbove {x : ℝ | ∃ X : ℝ, K / (1 + 4 * K * τ) ≤ X ∧
      x = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)} := by
  intro hbdd
  rcases hbdd with ⟨C, hC⟩
  have hc_nonneg : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hsum_nonneg : 0 ≤ ν 0 + (2 * ν 0 - ν 1 - ν 2) := by nlinarith
  have hsum_pos : 0 < ν 0 + (2 * ν 0 - ν 1 - ν 2) := by
    rcases lt_or_eq_of_le hsum_nonneg with hlt | heq
    · exact hlt
    · exfalso
      apply hne
      funext i
      fin_cases i
      · change ν 0 = 0
        nlinarith [hν0, heq, hν (by decide : (0 : Fin 3) ≤ 1), hν (by decide : (0 : Fin 3) ≤ 2)]
      · change ν 1 = 0
        have hν0eq : ν 0 = 0 := by
          change ν 0 = 0
          nlinarith [hν0, heq, hν (by decide : (0 : Fin 3) ≤ 1), hν (by decide : (0 : Fin 3) ≤ 2)]
        nlinarith [hν0eq, heq, hν (by decide : (0 : Fin 3) ≤ 1), hν (by decide : (1 : Fin 3) ≤ 2)]
      · change ν 2 = 0
        have hν0eq : ν 0 = 0 := by
          change ν 0 = 0
          nlinarith [hν0, heq, hν (by decide : (0 : Fin 3) ≤ 1), hν (by decide : (0 : Fin 3) ≤ 2)]
        have hν1eq : ν 1 = 0 := by
          change ν 1 = 0
          nlinarith [hν0eq, heq, hν (by decide : (0 : Fin 3) ≤ 1), hν (by decide : (1 : Fin 3) ≤ 2)]
        nlinarith [hν0eq, hν1eq, hν (by decide : (1 : Fin 3) ≤ 2)]
  let X₀ : ℝ := K / (1 + 4 * K * τ)
  let X₁ : ℝ := K * Real.exp 4 / (1 + 2 * K * τ)
  let X : ℝ := max X₀ (max X₁ (C / (ν 0 + (2 * ν 0 - ν 1 - ν 2)) + 1))
  have hX₀le : X₀ ≤ X := le_max_left _ _
  have hX₁le : X₁ ≤ X := le_trans (le_max_left _ _) (le_max_right _ _)
  have hX₁pos : 0 < X₁ := by
    dsimp [X₁]
    have hden : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    positivity
  have hXpos : 0 < X := lt_of_lt_of_le hX₁pos hX₁le
  have hB : X ≤ hamiltonIveyConvexBarrier K τ X := by
    have hBh : X ≤ hamiltonIveyBarrier K τ X := by
      have hden : 0 < 1 + 2 * K * τ := by
        have hKτ : 0 ≤ 2 * K * τ := by
          have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
          nlinarith
        nlinarith
      have hL : 4 ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
        have harg1 : 0 < X₁ * (1 + 2 * K * τ) / K := by positivity
        have harg2 : 0 < X * (1 + 2 * K * τ) / K := by positivity
        have hmono : Real.log (X₁ * (1 + 2 * K * τ) / K) ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
          refine (Real.log_le_log_iff harg1 harg2).mpr ?_
          have hmul : X₁ * (1 + 2 * K * τ) ≤ X * (1 + 2 * K * τ) :=
            mul_le_mul_of_nonneg_right hX₁le (by positivity : 0 ≤ (1 + 2 * K * τ))
          exact div_le_div_of_nonneg_right hmul hK.le
        have hlogX₁ : Real.log (X₁ * (1 + 2 * K * τ) / K) = 4 := by
          have hX₁eq : X₁ * (1 + 2 * K * τ) / K = Real.exp 4 := by
            dsimp [X₁]
            field_simp [hK.ne', hden.ne']
          rw [hX₁eq]
          exact Real.log_exp 4
        linarith
      have hlog : Real.log (X / K) + Real.log (1 + 2 * K * τ) = Real.log (X * (1 + 2 * K * τ) / K) := by
        have h1 : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hXpos.ne' hK.ne'
        have h2 : Real.log ((X * (1 + 2 * K * τ)) / K) = Real.log (X * (1 + 2 * K * τ)) - Real.log K :=
          Real.log_div (mul_pos hXpos hden).ne' hK.ne'
        have h3 : Real.log (X * (1 + 2 * K * τ)) = Real.log X + Real.log (1 + 2 * K * τ) :=
          Real.log_mul hXpos.ne' hden.ne'
        rw [h1, h2, h3]
        ring
      unfold hamiltonIveyBarrier
      rw [hlog]
      nlinarith [hL]
    exact hBh.trans (hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K τ X)
  have hF : C < hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) := by
    have h1 : C < (ν 0 + (2 * ν 0 - ν 1 - ν 2)) * X := by
      have hXbig : C / (ν 0 + (2 * ν 0 - ν 1 - ν 2)) + 1 ≤ X := by
        dsimp [X]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      have hpos : 0 < ν 0 + (2 * ν 0 - ν 1 - ν 2) := hsum_pos
      have hlt : C / (ν 0 + (2 * ν 0 - ν 1 - ν 2)) < X := by linarith
      have hmul := mul_lt_mul_of_pos_left hlt hpos
      have hred : (ν 0 + (2 * ν 0 - ν 1 - ν 2)) * (C / (ν 0 + (2 * ν 0 - ν 1 - ν 2))) = C :=
        mul_div_cancel₀ C hpos.ne'
      nlinarith
    have hmul : (ν 0 + (2 * ν 0 - ν 1 - ν 2)) * X ≤
        hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) := by
      have h1' : ν 0 * X ≤ ν 0 * hamiltonIveyConvexBarrier K τ X :=
        mul_le_mul_of_nonneg_left hB hν0
      calc
        (ν 0 + (2 * ν 0 - ν 1 - ν 2)) * X
            = ν 0 * X + (2 * ν 0 - ν 1 - ν 2) * X := by ring
        _ ≤ ν 0 * hamiltonIveyConvexBarrier K τ X + (2 * ν 0 - ν 1 - ν 2) * X := by
              nlinarith [h1']
        _ = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) := by ring
    exact lt_of_lt_of_le h1 hmul
  have hFle : hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤ C :=
    hC ⟨X, hX₀le, rfl⟩
  linarith

private lemma exists_rotate_preimage_of_mem_region
    {K τ : ℝ}
    (v B : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hB : B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
      A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
      inner ℝ v A =
        inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
  rcases hermitian_orthogonal_diagonalization (euclideanMatrixSymmetrization_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let A : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclidean (O * euclideanToMatrix B * O.transpose)
  have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hB
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O.transpose) (by simpa using hOorth) (by simpa using hOorth2)).1 hBm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
    dsimp [A]
    simpa [euclideanToMatrix_matrixToEuclidean, Matrix.transpose_transpose] using hconj
  have hinner : inner ℝ v A =
      inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
    have hBm : euclideanToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ B).1 hB
    have hBh : (euclideanToMatrix B).IsHermitian := by
      rw [hamiltonIveyConvexMatrixRegion] at hBm
      exact hBm.1
    have hsymm : inner ℝ v A = inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean (euclideanToMatrix A)) := by
      have hAh : (euclideanToMatrix A).IsHermitian := by
        have hAm : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
          (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
        rw [hamiltonIveyConvexMatrixRegion] at hAm
        exact hAm.1
      simpa [matrixToEuclidean_euclideanToMatrix] using inner_matrixToEuclidean_symm v (euclideanToMatrix A) hAh
    have hconj := inner_matrixToEuclidean_orthogonal_conj (euclideanMatrixSymmetrization v) (euclideanToMatrix A) O hOorth
    have hdiag' : O.transpose * euclideanMatrixSymmetrization v * O =
        Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ := by
      simpa using hdiag
    calc
      inner ℝ v A = inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean (euclideanToMatrix A)) := hsymm
      _ = inner ℝ (matrixToEuclidean (O.transpose * euclideanMatrixSymmetrization v * O))
            (matrixToEuclidean (O.transpose * euclideanToMatrix A * O)) := hconj
      _ = inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀))
            (matrixToEuclidean (O.transpose * euclideanToMatrix A * O)) := by
            rw [hdiag']
            rfl
      _ = inner ℝ (matrixToEuclidean (Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀)) B := by
            dsimp [A]
            rw [euclideanToMatrix_matrixToEuclidean]
            have hmat : O.transpose * (O * euclideanToMatrix B * O.transpose) * O = euclideanToMatrix B := by
              simp only [Matrix.mul_assoc]
              rw [hOorth2]
              simp only [Matrix.mul_one]
              rw [← Matrix.mul_assoc]
              rw [hOorth2]
              simp only [Matrix.one_mul]
            rw [hmat]
            congr 1
  exact ⟨A, hA, hinner⟩

lemma mem_finiteSupportDirections_hamiltonIvey_region_iff
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) ↔
      (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 ∨ euclideanMatrixSymmetrization v = 0 := by
  constructor
  · intro hv
    by_contra h
    have hν0ge : ¬ (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 := by
      intro hneg
      exact h (Or.inl hneg)
    have hsymm_ne : euclideanMatrixSymmetrization v ≠ 0 := by
      intro hz
      exact h (Or.inr hz)
    have hν0 : 0 ≤ (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 := le_of_not_gt hν0ge
    let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
    have hnv_anti : Antitone nv := by
      dsimp [nv]
      exact (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀_antitone
    have hnv_ne : nv ≠ 0 := by
      intro hnv0
      apply hsymm_ne
      rcases hermitian_orthogonal_diagonalization (euclideanMatrixSymmetrization_isHermitian v) with ⟨O, hOorth, hdiag⟩
      have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
      have hnv0' : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ = 0 := by
        simpa [nv] using hnv0
      have hd : Matrix.diagonal (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ = 0 := by
        rw [hnv0']
        ext i j
        simp [Matrix.diagonal]
      have hdiag0 : O.transpose * euclideanMatrixSymmetrization v * O = 0 := by
        simpa [hd] using hdiag
      calc
        euclideanMatrixSymmetrization v = O * (O.transpose * euclideanMatrixSymmetrization v * O) * O.transpose := by
          simp only [Matrix.mul_assoc]
          rw [hOorth]
          simp only [Matrix.mul_one]
          rw [← Matrix.mul_assoc]
          rw [hOorth]
          simp
        _ = O * 0 * O.transpose := by rw [hdiag0]
        _ = 0 := by simp
    have hbdd_diag : BddAbove {x : ℝ | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
        B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
          x = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) B} := by
      rcases hv with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro x ⟨B, hB, rfl⟩
      rcases exists_rotate_preimage_of_mem_region v B hB with ⟨A, hA, hinner⟩
      have hinner' : inner ℝ v A = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) B := by
        simpa [nv] using hinner
      have hle : inner ℝ v A ≤ C := hC ⟨A, hA, rfl⟩
      rwa [hinner'] at hle
    have hFsubset : {x : ℝ | ∃ X : ℝ, K / (1 + 4 * K * τ) ≤ X ∧
          x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} ⊆
        {x : ℝ | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
          B ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧
            x = inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) B} := by
      rintro x ⟨X, hX₀le, rfl⟩
      let l : Fin 3 → ℝ := ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
      have hDmem : Matrix.diagonal l ∈ hamiltonIveyConvexMatrixRegion K τ :=
        diagonal_extremal_mem_region hK hτ hX₀le
      have hDmemE : matrixToEuclidean (Matrix.diagonal l) ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
        rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
        simpa [l, euclideanToMatrix_matrixToEuclidean] using hDmem
      have hinner : inner ℝ (matrixToEuclidean (Matrix.diagonal nv)) (matrixToEuclidean (Matrix.diagonal l)) =
          hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2) := by
        have hdd := inner_diag_diag nv l
        rw [hdd]
        simp [l, Fin.sum_univ_three]
        ring
      exact ⟨matrixToEuclidean (Matrix.diagonal l), hDmemE, hinner.symm⟩
    have hbddF : BddAbove {x : ℝ | ∃ X : ℝ, K / (1 + 4 * K * τ) ≤ X ∧
          x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} :=
      BddAbove.mono hFsubset hbdd_diag
    exact (support_formula_unbounded_of_nonneg_top hK hτ hnv_anti hν0 hnv_ne) hbddF
  · rintro (hv | hsymm0)
    · have hbdd : BddAbove {x : ℝ | ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
          A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = inner ℝ v A} := by
        refine ⟨hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v, ?_⟩
        rintro x ⟨A, hA, rfl⟩
        exact inner_le_supportFunction_of_mem_region hK hτ v hv A hA
      exact hbdd
    · have hbdd : BddAbove {x : ℝ | ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
          A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = inner ℝ v A} := by
        refine ⟨0, ?_⟩
        rintro x ⟨A, hA, rfl⟩
        have hAh : (euclideanToMatrix A).IsHermitian := by
          have hAm : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
            (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
          rw [hamiltonIveyConvexMatrixRegion] at hAm
          exact hAm.1
        have hz : inner ℝ v A = 0 := by
          have h := inner_matrixToEuclidean_symm v (euclideanToMatrix A) hAh
          rw [hsymm0] at h
          have hzero : inner ℝ (matrixToEuclidean 0) (matrixToEuclidean (euclideanToMatrix A)) = 0 := by
            rw [inner_matrixToEuclidean]
            simp [matrixToEuclidean]
          have hmain : inner ℝ v (matrixToEuclidean (euclideanToMatrix A)) = 0 := h.trans hzero
          simpa [matrixToEuclidean_euclideanToMatrix] using hmain
        rw [hz]
      exact hbdd

private lemma continuousOn_sSup_image_Icc
    {T Xmax : ℝ} (hX : 0 ≤ Xmax)
    (F : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax)) :
    ContinuousOn (fun τ : ℝ => sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax)) (Set.Icc 0 T) := by
  have hslab : IsCompact (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).prod (isCompact_Icc (a := (0 : ℝ)) (b := Xmax))
  have hUC : UniformContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) :=
    hslab.uniformContinuousOn_of_continuous hcont
  have hbdds : ∀ s : ℝ, s ∈ Set.Icc 0 T →
      BddAbove ((fun X : ℝ => F s X) '' Set.Icc 0 Xmax) := by
    intro s hs
    have hslice : ContinuousOn (fun X : ℝ => F s X) (Set.Icc 0 Xmax) := by
      have hmap : ContinuousOn (fun X : ℝ => (s, X)) (Set.Icc 0 Xmax) := by fun_prop
      have hsub : Set.MapsTo (fun X : ℝ => (s, X)) (Set.Icc 0 Xmax)
          (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := by
        intro X hX
        exact ⟨hs, hX⟩
      exact hcont.comp hmap hsub
    exact (isCompact_Icc (a := (0 : ℝ)) (b := Xmax)).bddAbove_image hslice
  have hne : ∀ s : ℝ, ((fun X : ℝ => F s X) '' Set.Icc 0 Xmax).Nonempty := by
    intro s
    exact ⟨F s 0, 0, ⟨le_rfl, hX⟩, rfl⟩
  intro τ₀ hτ₀
  refine Metric.continuousWithinAt_iff.mpr ?_
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hUC) (ε / 2) (by positivity) with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro τ hτ hdist
  have hmain : ∀ X : ℝ, X ∈ Set.Icc 0 Xmax → |F τ X - F τ₀ X| ≤ ε / 2 := by
    intro X hX
    have hx : (τ, X) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 Xmax := ⟨hτ, hX⟩
    have hy : (τ₀, X) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 Xmax := ⟨hτ₀, hX⟩
    have hdx : dist (τ, X) (τ₀, X) < δ := by
      have hd0 : 0 ≤ dist τ τ₀ := dist_nonneg
      rw [Prod.dist_eq]
      rw [dist_self]
      rw [max_eq_left hd0]
      exact hdist
    have hlt := hδ (τ, X) hx (τ₀, X) hy hdx
    exact le_of_lt hlt
  have hg_le : sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) ≤
      sSup ((fun X : ℝ => F τ₀ X) '' Set.Icc 0 Xmax) + ε / 2 := by
    refine csSup_le (hne τ) ?_
    rintro y ⟨X, hX, rfl⟩
    have h1 : F τ X ≤ F τ₀ X + ε / 2 := by linarith [(abs_le.mp (hmain X hX)).2]
    have h2 : F τ₀ X ≤ sSup ((fun X : ℝ => F τ₀ X) '' Set.Icc 0 Xmax) :=
      le_csSup (hbdds τ₀ hτ₀) ⟨X, hX, rfl⟩
    linarith
  have hg_ge : sSup ((fun X : ℝ => F τ₀ X) '' Set.Icc 0 Xmax) ≤
      sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) + ε / 2 := by
    refine csSup_le (hne τ₀) ?_
    rintro y ⟨X, hX, rfl⟩
    have h1 : F τ₀ X ≤ F τ X + ε / 2 := by linarith [(abs_le.mp (hmain X hX)).1]
    have h2 : F τ X ≤ sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) :=
      le_csSup (hbdds τ hτ) ⟨X, hX, rfl⟩
    linarith
  rw [dist_eq_norm]
  rw [Real.norm_eq_abs]
  rw [abs_sub_lt_iff]
  constructor <;> linarith


private lemma support_formula_continuousOn
    {K T : ℝ} (hK : 0 < K)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) :
    ContinuousOn (fun τ : ℝ => sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
      x = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)})
      (Set.Icc 0 T) := by
  let F : ℝ → ℝ → ℝ := fun τ X => hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let S : ℝ := ν 0 + ν 1 + ν 2
  let Xmax : ℝ := K * Real.exp (S / ν 0)
  have hXmax : 0 ≤ Xmax := by
    dsimp [Xmax]
    exact le_of_lt (mul_pos hK (Real.exp_pos (S / ν 0)))
  have hBcont : ContinuousOn (fun p : ℝ × ℝ => hamiltonIveyConvexBarrier K p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := by
    have hfull := continuousOn_hamiltonIveyConvexBarrier_time_nonneg (K := K) (T := T) hK
    exact hfull.mono (by
      rintro p hp
      exact ⟨hp.1, hp.2.1⟩)
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := by
    dsimp [F]
    have hBν : ContinuousOn (fun p : ℝ × ℝ => hamiltonIveyConvexBarrier K p.1 p.2 * ν 0)
        (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := hBcont.mul continuousOn_const
    have hXc : ContinuousOn (fun p : ℝ × ℝ => p.2 * (2 * ν 0 - ν 1 - ν 2))
        (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := by
      simpa [mul_comm] using (continuousOn_snd.mul (continuousOn_const (s := Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) (c := (2 * ν 0 - ν 1 - ν 2))))
    exact hBν.add hXc
  have htail0 : ∀ τ : ℝ, τ ∈ Set.Icc 0 T → ∀ X : ℝ, Xmax ≤ X → F τ X ≤ 0 := by
    intro τ hτ X hX
    have hXpos : 0 < X := lt_of_lt_of_le (by
      have hXm : 0 < Xmax := by
        dsimp [Xmax]
        exact mul_pos hK (Real.exp_pos (S / ν 0))
      exact hXm) hX
    have hL : S / ν 0 ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
      have hdenτ : 0 < 1 + 2 * K * τ := by
        have hKτ : 0 ≤ 2 * K * τ := by
          have h1' : 0 ≤ K * τ := mul_nonneg hK.le hτ.1
          nlinarith
        nlinarith
      have harg1 : 0 < X * (1 + 2 * K * τ) / K := by
        exact div_pos (mul_pos hXpos hdenτ) hK
      have harg2 : 0 < Xmax / K := by
        dsimp [Xmax]
        exact div_pos (mul_pos hK (Real.exp_pos (S / ν 0))) hK
      have hmono : Real.log (Xmax / K) ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
        refine (Real.log_le_log_iff harg2 harg1).mpr ?_
        have h1 : Xmax ≤ X * (1 + 2 * K * τ) := by
          have hτ0 : 0 ≤ 2 * K * τ := by
            have h1' : 0 ≤ K * τ := mul_nonneg hK.le hτ.1
            nlinarith
          nlinarith
        have h2 : Xmax / K ≤ X * (1 + 2 * K * τ) / K := by
          exact div_le_div_of_nonneg_right h1 hK.le
        exact h2
      have hlogXmax : Real.log (Xmax / K) = S / ν 0 := by
        have hXeq : Xmax / K = Real.exp (S / ν 0) := by
          dsimp [Xmax]
          field_simp [hK.ne']
        rw [hXeq]
        exact Real.log_exp (S / ν 0)
      linarith
    exact support_formula_tail_nonpos hK hτ.1 hν0 hXpos hL
  have hbdd0 : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      BddAbove ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) := by
    intro τ hτ
    have hslice : ContinuousOn (fun X : ℝ => F τ X) (Set.Icc 0 Xmax) := by
      have hmap : ContinuousOn (fun X : ℝ => (τ, X)) (Set.Icc 0 Xmax) := by fun_prop
      have hsub : Set.MapsTo (fun X : ℝ => (τ, X)) (Set.Icc 0 Xmax)
          (Set.Icc 0 T ×ˢ Set.Icc 0 Xmax) := by
        intro X hX
        exact ⟨hτ, hX⟩
      exact hFcont.comp hmap hsub
    exact (isCompact_Icc (a := (0 : ℝ)) (b := Xmax)).bddAbove_image hslice
  have hbddAll : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      BddAbove {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧ x = F τ X} := by
    intro τ hτ
    have hbddF := support_formula_bddAbove hK hτ.1 hν0
    simpa [F] using hbddF
  have hsup_eq : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧ x = F τ X} =
        sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) := by
    intro τ hτ
    apply le_antisymm
    · refine csSup_le ?_ ?_
      · rcases hbdd0 τ hτ with ⟨C, hC⟩
        refine ⟨F τ 0, ?_⟩
        exact ⟨0, le_rfl, rfl⟩
      · rintro x ⟨X, hX, rfl⟩
        by_cases hXle : X ≤ Xmax
        · have hXmem : X ∈ Set.Icc 0 Xmax := ⟨hX, hXle⟩
          exact le_csSup (hbdd0 τ hτ) ⟨X, hXmem, rfl⟩
        · have htail : F τ X ≤ 0 := htail0 τ hτ X (le_of_not_ge hXle)
          have h0le : 0 ≤ sSup ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) := by
            have hB0 : hamiltonIveyConvexBarrier K τ 0 = 0 := by
              unfold hamiltonIveyConvexBarrier
              have hsc : scalarSectionalLowerBarrier3 K τ ≤ 0 := by
                unfold scalarSectionalLowerBarrier3
                have hden : 0 < 1 + 4 * K * τ := by
                  have hKτ : 0 ≤ 4 * K * τ := by
                    have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ.1
                    nlinarith
                  nlinarith
                have hdiv : -3 * K / (1 + 4 * K * τ) ≤ 0 := by
                  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith : -3 * K ≤ 0) hden.le
                exact hdiv
              have hb0 : hamiltonIveyBarrier K τ 0 = 0 := by
                unfold hamiltonIveyBarrier
                simp
              rw [hb0]
              exact max_eq_right hsc
            have h0 : F τ 0 = 0 := by
              dsimp [F]
              rw [hB0]
              ring
            have hmem : 0 ∈ ((fun X : ℝ => F τ X) '' Set.Icc 0 Xmax) := by
              refine ⟨0, ⟨le_rfl, hXmax⟩, ?_⟩
              exact h0
            exact le_csSup (hbdd0 τ hτ) hmem
          linarith
    · refine csSup_le ?_ ?_
      · rcases hbddAll τ hτ with ⟨C, hC⟩
        refine ⟨F τ 0, ?_⟩
        exact ⟨0, ⟨le_rfl, hXmax⟩, rfl⟩
      · rintro x ⟨X, hX, rfl⟩
        exact le_csSup (hbddAll τ hτ) ⟨X, hX.1, rfl⟩
  have hmain := continuousOn_sSup_image_Icc (hX := hXmax) (F := F) hFcont
  exact hmain.congr (fun τ hτ => by simpa [F] using hsup_eq τ hτ)

theorem hamiltonIveyConvexMatrixRegionSupportEuclidean_continuousOn
    {K T : ℝ} (hK : 0 < K)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0) :
    ContinuousOn (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v) (Set.Icc 0 T) := by
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hmain := support_formula_continuousOn (K := K) (T := T) hK (ν := nv) hnv0
  have hdef : ∀ τ : ℝ, hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
        x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} := by
    intro τ
    unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
    dsimp [nv]
    rw [if_pos hv]
    rfl
  exact hmain.congr (fun τ hτ => hdef τ)

private lemma support_formula_min_branch
    {K τ : ℝ}
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) (X : ℝ) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) =
      min (scalarSectionalLowerBarrier3 K τ * ν 0 + X * (2 * ν 0 - ν 1 - ν 2))
        (hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)) := by
  unfold hamiltonIveyConvexBarrier
  have hν0le : ν 0 ≤ 0 := hν0.le
  have hmul : max (scalarSectionalLowerBarrier3 K τ) (hamiltonIveyBarrier K τ X) * ν 0 =
      min (scalarSectionalLowerBarrier3 K τ * ν 0) (hamiltonIveyBarrier K τ X * ν 0) := by
    by_cases h : scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyBarrier K τ X
    · rw [max_eq_right h]
      rw [min_eq_right (mul_le_mul_of_nonpos_right h hν0le)]
    · have h' : hamiltonIveyBarrier K τ X ≤ scalarSectionalLowerBarrier3 K τ := le_of_not_ge h
      rw [max_eq_left h']
      rw [min_eq_left (mul_le_mul_of_nonpos_right h' hν0le)]
  rw [hmul]
  have hdist : min (scalarSectionalLowerBarrier3 K τ * ν 0) (hamiltonIveyBarrier K τ X * ν 0) +
        X * (2 * ν 0 - ν 1 - ν 2) =
      min (scalarSectionalLowerBarrier3 K τ * ν 0 + X * (2 * ν 0 - ν 1 - ν 2))
        (hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)) := by
    let a : ℝ := scalarSectionalLowerBarrier3 K τ * ν 0
    let b : ℝ := hamiltonIveyBarrier K τ X * ν 0
    let c : ℝ := X * (2 * ν 0 - ν 1 - ν 2)
    apply le_antisymm
    · refine le_min ?_ ?_
      · exact add_le_add_left (min_le_left a b) c
      · exact add_le_add_left (min_le_right a b) c
    · by_cases h : a ≤ b
      · rw [min_eq_left h, min_eq_left (add_le_add_left h c)]
      · have h' : b ≤ a := le_of_not_ge h
        rw [min_eq_right h', min_eq_right (add_le_add_left h' c)]
  exact hdist


private lemma hamiltonIveyBarrier_at_star_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} :
    hamiltonIveyBarrier K τ (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) =
      (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * ((ν 1 + ν 2) / ν 0 - 3) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hden : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hXpos : 0 < Xs := by
    dsimp [Xs]
    positivity
  unfold hamiltonIveyBarrier
  have hXeq : Xs * (1 + 2 * K * τ) / K = Real.exp ((ν 1 + ν 2) / ν 0) := by
    dsimp [Xs]
    field_simp [hK.ne', hden.ne']
  have hlogX : Real.log (Xs * (1 + 2 * K * τ) / K) = (ν 1 + ν 2) / ν 0 := by
    rw [hXeq]
    exact Real.log_exp ((ν 1 + ν 2) / ν 0)
  have h1 : Real.log (Xs / K) = Real.log Xs - Real.log K := Real.log_div hXpos.ne' hK.ne'
  have h2 : Real.log ((Xs * (1 + 2 * K * τ)) / K) =
      Real.log (Xs * (1 + 2 * K * τ)) - Real.log K :=
    Real.log_div (mul_pos hXpos hden).ne' hK.ne'
  have h3 : Real.log (Xs * (1 + 2 * K * τ)) = Real.log Xs + Real.log (1 + 2 * K * τ) :=
    Real.log_mul hXpos.ne' hden.ne'
  have hlog : Real.log (Xs / K) + Real.log (1 + 2 * K * τ) = (ν 1 + ν 2) / ν 0 := by
    calc
      Real.log (Xs / K) + Real.log (1 + 2 * K * τ)
          = Real.log (Xs * (1 + 2 * K * τ) / K) := by
            rw [h1, h2, h3]
            ring_nf
      _ = (ν 1 + ν 2) / ν 0 := hlogX
  rw [hlog]

private lemma support_formula_at_star_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) :
    hamiltonIveyConvexBarrier K τ (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * ν 0 +
        (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) =
      min (scalarSectionalLowerBarrier3 K τ * ν 0 +
            (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2))
        (-(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)))) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hmin := support_formula_min_branch (K := K) (τ := τ) hν0 Xs
  have hbar := hamiltonIveyBarrier_at_star_point (K := K) (τ := τ) (ν := ν) hK hτ
  have hb : hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) =
      -(ν 0 * Xs) := by
    rw [hbar]
    have hcalc : Xs * ((ν 1 + ν 2) / ν 0 - 3) * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) =
        -(ν 0 * Xs) := by
      field_simp [Ne.symm hν0.ne']
      ring
    simp [Xs, hcalc]
  rw [hmin, hb]

private lemma hasDerivAt_scalarSectionalLowerBarrier3
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀) :
    HasDerivAt (fun τ : ℝ => scalarSectionalLowerBarrier3 K τ)
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2) τ₀ := by
  unfold scalarSectionalLowerBarrier3
  have hden : 0 < 1 + 4 * K * τ₀ := by
    have hKτ : 0 ≤ 4 * K * τ₀ := by
      have h1 : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀
      nlinarith
    nlinarith
  have hlin : HasDerivAt (fun τ : ℝ => 1 + 4 * K * τ) (4 * K) τ₀ := by
    have h1 : HasDerivAt (fun τ : ℝ => (4 * K) * τ) (4 * K) τ₀ := by
      simpa [mul_one] using (hasDerivAt_id τ₀).const_mul (4 * K)
    simpa [add_comm, mul_comm] using (h1.add_const 1)
  have hq : HasDerivAt (fun τ : ℝ => (-3 * K) / (1 + 4 * K * τ))
      ((0 * (1 + 4 * K * τ₀) - (-3 * K) * (4 * K)) / (1 + 4 * K * τ₀) ^ 2) τ₀ := by
    exact (hasDerivAt_const (x := τ₀) (c := (-3 * K : ℝ))).div hlin (by positivity)
  convert hq using 1
  field_simp [hden.ne']
  ring

private lemma hasDerivAt_star_point
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀)
    (t : ℝ) :
    HasDerivAt (fun τ : ℝ => K * Real.exp t / (1 + 2 * K * τ))
      (-2 * K * (K * Real.exp t / (1 + 2 * K * τ₀) ^ 2)) τ₀ := by
  have hden : 0 < 1 + 2 * K * τ₀ := by
    have hKτ : 0 ≤ 2 * K * τ₀ := by
      have h1 : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀
      nlinarith
    nlinarith
  have hlin : HasDerivAt (fun τ : ℝ => 1 + 2 * K * τ) (2 * K) τ₀ := by
    have h1 : HasDerivAt (fun τ : ℝ => (2 * K) * τ) (2 * K) τ₀ := by
      simpa [mul_one] using (hasDerivAt_id τ₀).const_mul (2 * K)
    simpa [add_comm, mul_comm] using (h1.add_const 1)
  have hq : HasDerivAt (fun τ : ℝ => (K * Real.exp t) / (1 + 2 * K * τ))
      ((0 * (1 + 2 * K * τ₀) - (K * Real.exp t) * (2 * K)) / (1 + 2 * K * τ₀) ^ 2) τ₀ := by
    exact (hasDerivAt_const (x := τ₀) (c := (K * Real.exp t : ℝ))).div hlin (by positivity)
  convert hq using 1
  field_simp [hden.ne']
  ring

private lemma hasDerivAt_candidate_A
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀)
    {ν : Fin 3 → ℝ} :
    HasDerivAt (fun τ : ℝ =>
        scalarSectionalLowerBarrier3 K τ * ν 0 +
          (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2))
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
        (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)) *
          (2 * ν 0 - ν 1 - ν 2)) τ₀ := by
  have h1 := hasDerivAt_scalarSectionalLowerBarrier3 (K := K) (τ₀ := τ₀) hK hτ₀
  have h2 := hasDerivAt_star_point (K := K) (τ₀ := τ₀) hK hτ₀ ((ν 1 + ν 2) / ν 0)
  have h1' : HasDerivAt (fun τ : ℝ => scalarSectionalLowerBarrier3 K τ * ν 0)
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0) τ₀ := h1.mul_const (ν 0)
  have h2' : HasDerivAt (fun τ : ℝ =>
      (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2))
      ((-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)) *
        (2 * ν 0 - ν 1 - ν 2)) τ₀ := h2.mul_const (2 * ν 0 - ν 1 - ν 2)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h1'.add h2'

private lemma hasDerivAt_candidate_B
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀)
    {ν : Fin 3 → ℝ} :
    HasDerivAt (fun τ : ℝ =>
        -(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ))))
      (-(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))) τ₀ := by
  have h2 := hasDerivAt_star_point (K := K) (τ₀ := τ₀) hK hτ₀ ((ν 1 + ν 2) / ν 0)
  have h2' : HasDerivAt (fun τ : ℝ => ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)))
      (ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2))) τ₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul (ν 0)
  exact h2'.neg

private lemma hasDerivAt_hamiltonIveyBarrier_x
    {K τ X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    HasDerivAt (fun Y : ℝ => hamiltonIveyBarrier K τ Y)
      (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) X := by
  have hfun : (fun Y : ℝ => hamiltonIveyBarrier K τ Y) =
      fun Y : ℝ => Y * Real.log Y + Y * (Real.log (1 + 2 * K * τ) - 3 - Real.log K) := by
    funext Y
    exact hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := τ) (X := Y) hK
  rw [hfun]
  have h1 : HasDerivAt (fun Y : ℝ => Y * Real.log Y) (Real.log X + 1) X := Real.hasDerivAt_mul_log hX.ne'
  have h2 : HasDerivAt (fun Y : ℝ => Y * (Real.log (1 + 2 * K * τ) - 3 - Real.log K))
      (Real.log (1 + 2 * K * τ) - 3 - Real.log K) X := by
    simpa [mul_comm] using ((hasDerivAt_id X).mul_const (Real.log (1 + 2 * K * τ) - 3 - Real.log K))
  have hsum := h1.add h2
  convert hsum using 1
  have hlog : Real.log X - Real.log K = Real.log (X / K) := by
    rw [Real.log_div hX.ne' hK.ne']
  linarith

private lemma deriv_hamiltonIveyBarrier_x
    {K τ X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    deriv (fun Y : ℝ => hamiltonIveyBarrier K τ Y) X =
      Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2 :=
  (hasDerivAt_hamiltonIveyBarrier_x hK hX).deriv


private lemma monotoneOn_Fh_left
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    MonotoneOn (fun X : ℝ =>
        hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2))
      (Set.Icc 0 (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ))) := by
  let Fh : ℝ → ℝ := fun X => hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hden : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hXspos : 0 < Xs := by
    dsimp [Xs]
    positivity
  have hc : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hFh_cont : ContinuousOn Fh (Set.Icc 0 Xs) := by
    dsimp [Fh]
    have hB : ContinuousOn (fun X : ℝ => hamiltonIveyBarrier K τ X) (Set.Icc 0 Xs) :=
      (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousOn
    have hBν : ContinuousOn (fun X : ℝ => hamiltonIveyBarrier K τ X * ν 0) (Set.Icc 0 Xs) :=
      hB.mul continuousOn_const
    have hXc : ContinuousOn (fun X : ℝ => X * (2 * ν 0 - ν 1 - ν 2)) (Set.Icc 0 Xs) := by
      simpa [mul_comm] using (continuousOn_id.mul (continuousOn_const (s := Set.Icc 0 Xs) (c := (2 * ν 0 - ν 1 - ν 2))))
    exact hBν.add hXc
  have hFh_diff : DifferentiableOn ℝ Fh (interior (Set.Icc 0 Xs)) := by
    intro X hX
    have hX' : X ∈ Set.Ioo 0 Xs := by simpa [interior_Icc] using hX
    have hXpos : 0 < X := hX'.1
    have hBd : HasDerivAt (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0)
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0) X :=
      (hasDerivAt_hamiltonIveyBarrier_x hK hXpos).mul_const (ν 0)
    have hXd : HasDerivAt (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))
        (2 * ν 0 - ν 1 - ν 2) X := by
      simpa [mul_comm] using ((hasDerivAt_id X).mul_const (2 * ν 0 - ν 1 - ν 2))
    exact (hBd.add hXd).differentiableAt.differentiableWithinAt
  have hFh_deriv : ∀ X : ℝ, X ∈ interior (Set.Icc 0 Xs) →
      0 ≤ deriv Fh X := by
    intro X hX
    have hX' : X ∈ Set.Ioo 0 Xs := by simpa [interior_Icc] using hX
    have hXpos : 0 < X := hX'.1
    have hXle : X ≤ Xs := le_of_lt hX'.2
    have hBd : HasDerivAt (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0)
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0) X :=
      (hasDerivAt_hamiltonIveyBarrier_x hK hXpos).mul_const (ν 0)
    have hXd : HasDerivAt (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))
        (2 * ν 0 - ν 1 - ν 2) X := by
      simpa [mul_comm] using ((hasDerivAt_id X).mul_const (2 * ν 0 - ν 1 - ν 2))
    have hlog : Real.log (X / K) + Real.log (1 + 2 * K * τ) ≤ (ν 1 + ν 2) / ν 0 := by
      have harg1 : 0 < X * (1 + 2 * K * τ) / K := by
        exact div_pos (mul_pos hXpos hden) hK
      have harg2 : 0 < Xs * (1 + 2 * K * τ) / K := by
        dsimp [Xs]
        positivity
      have hmono : Real.log (X * (1 + 2 * K * τ) / K) ≤ Real.log (Xs * (1 + 2 * K * τ) / K) := by
        refine (Real.log_le_log_iff harg1 harg2).mpr ?_
        have hmul : X * (1 + 2 * K * τ) ≤ Xs * (1 + 2 * K * τ) :=
          mul_le_mul_of_nonneg_right hXle (by positivity : 0 ≤ (1 + 2 * K * τ))
        exact div_le_div_of_nonneg_right hmul hK.le
      have hlogXs : Real.log (Xs * (1 + 2 * K * τ) / K) = (ν 1 + ν 2) / ν 0 := by
        have hXeq : Xs * (1 + 2 * K * τ) / K = Real.exp ((ν 1 + ν 2) / ν 0) := by
          dsimp [Xs]
          field_simp [hK.ne', hden.ne']
        rw [hXeq]
        exact Real.log_exp ((ν 1 + ν 2) / ν 0)
      have hlogX : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
          Real.log (X * (1 + 2 * K * τ) / K) := by
        have h1 : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hXpos.ne' hK.ne'
        have h2 : Real.log ((X * (1 + 2 * K * τ)) / K) = Real.log (X * (1 + 2 * K * τ)) - Real.log K :=
          Real.log_div (mul_pos hXpos hden).ne' hK.ne'
        have h3 : Real.log (X * (1 + 2 * K * τ)) = Real.log X + Real.log (1 + 2 * K * τ) :=
          Real.log_mul hXpos.ne' hden.ne'
        rw [h1, h2, h3]
        ring_nf
      linarith
    have hmain : 0 ≤ ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 +
        (2 * ν 0 - ν 1 - ν 2)) := by
      have hconv : (ν 1 + ν 2) / ν 0 - 2 = (2 * ν 0 - ν 1 - ν 2) / (-ν 0) := by
        field_simp [Ne.symm hν0.ne']
        ring_nf
      have hle : Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2 ≤ (2 * ν 0 - ν 1 - ν 2) / (-ν 0) := by
        rw [← hconv]
        linarith
      have hneg : 0 < -ν 0 := by linarith
      have hred : (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * (-ν 0) ≤ 2 * ν 0 - ν 1 - ν 2 := by
        have h1 : (-ν 0) * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) ≤
            2 * ν 0 - ν 1 - ν 2 := by
          calc
            (-ν 0) * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2)
                ≤ (-ν 0) * ((2 * ν 0 - ν 1 - ν 2) / (-ν 0)) :=
                  mul_le_mul_of_nonneg_left hle (le_of_lt hneg)
            _ = 2 * ν 0 - ν 1 - ν 2 := by
                  rw [mul_div_cancel₀ (2 * ν 0 - ν 1 - ν 2) (show -ν 0 ≠ 0 by positivity)]
        calc
          (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * (-ν 0)
              = (-ν 0) * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) := by ring
          _ ≤ 2 * ν 0 - ν 1 - ν 2 := h1
      have hle' : -((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0) ≤
          2 * ν 0 - ν 1 - ν 2 := by
        rw [← mul_neg]
        exact hred
      linarith
    have hBd' : deriv (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0) X =
        (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 := hBd.deriv
    have hXd' : deriv (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2)) X = 2 * ν 0 - ν 1 - ν 2 := hXd.deriv
    have hderiv : deriv Fh X =
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 + (2 * ν 0 - ν 1 - ν 2)) := by
      change deriv ((fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0) +
        (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))) X = _
      rw [deriv_add]
      · rw [hBd', hXd']
      · exact hBd.differentiableAt
      · exact hXd.differentiableAt
    rw [hderiv]
    exact hmain
  exact monotoneOn_of_deriv_nonneg (D := Set.Icc 0 Xs)
    (convex_Icc (r := (0 : ℝ)) (s := Xs)) hFh_cont hFh_diff hFh_deriv

private lemma antitoneOn_Fh_right
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    AntitoneOn (fun X : ℝ =>
        hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2))
      (Set.Ici (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ))) := by
  let Fh : ℝ → ℝ := fun X => hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hden : 0 < 1 + 2 * K * τ := by
    have hKτ : 0 ≤ 2 * K * τ := by
      have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
      nlinarith
    nlinarith
  have hXspos : 0 < Xs := by
    dsimp [Xs]
    positivity
  have hc : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hFh_cont : ContinuousOn Fh (Set.Ici Xs) := by
    dsimp [Fh]
    have hB : ContinuousOn (fun X : ℝ => hamiltonIveyBarrier K τ X) (Set.Ici Xs) :=
      (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousOn
    have hBν : ContinuousOn (fun X : ℝ => hamiltonIveyBarrier K τ X * ν 0) (Set.Ici Xs) :=
      hB.mul continuousOn_const
    have hXc : ContinuousOn (fun X : ℝ => X * (2 * ν 0 - ν 1 - ν 2)) (Set.Ici Xs) := by
      simpa [mul_comm] using (continuousOn_id.mul (continuousOn_const (s := Set.Ici Xs) (c := (2 * ν 0 - ν 1 - ν 2))))
    exact hBν.add hXc
  have hFh_diff : DifferentiableOn ℝ Fh (interior (Set.Ici Xs)) := by
    intro X hX
    have hXgt : Xs < X := by simpa [interior_Ici] using hX
    have hXpos : 0 < X := lt_of_lt_of_le hXspos (le_of_lt hXgt)
    have hBd : HasDerivAt (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0)
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0) X :=
      (hasDerivAt_hamiltonIveyBarrier_x hK hXpos).mul_const (ν 0)
    have hXd : HasDerivAt (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))
        (2 * ν 0 - ν 1 - ν 2) X := by
      simpa [mul_comm] using ((hasDerivAt_id X).mul_const (2 * ν 0 - ν 1 - ν 2))
    exact (hBd.add hXd).differentiableAt.differentiableWithinAt
  have hFh_deriv : ∀ X : ℝ, X ∈ interior (Set.Ici Xs) → deriv Fh X ≤ 0 := by
    intro X hX
    have hXgt : Xs < X := by simpa [interior_Ici] using hX
    have hXpos : 0 < X := lt_of_lt_of_le hXspos (le_of_lt hXgt)
    have hXsle : Xs ≤ X := le_of_lt hXgt
    have hBd : HasDerivAt (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0)
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0) X :=
      (hasDerivAt_hamiltonIveyBarrier_x hK hXpos).mul_const (ν 0)
    have hXd : HasDerivAt (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))
        (2 * ν 0 - ν 1 - ν 2) X := by
      simpa [mul_comm] using ((hasDerivAt_id X).mul_const (2 * ν 0 - ν 1 - ν 2))
    have hlog : (ν 1 + ν 2) / ν 0 ≤ Real.log (X / K) + Real.log (1 + 2 * K * τ) := by
      have harg1 : 0 < Xs * (1 + 2 * K * τ) / K := by
        dsimp [Xs]
        positivity
      have harg2 : 0 < X * (1 + 2 * K * τ) / K := by
        exact div_pos (mul_pos hXpos hden) hK
      have hmono : Real.log (Xs * (1 + 2 * K * τ) / K) ≤ Real.log (X * (1 + 2 * K * τ) / K) := by
        refine (Real.log_le_log_iff harg1 harg2).mpr ?_
        have hmul : Xs * (1 + 2 * K * τ) ≤ X * (1 + 2 * K * τ) :=
          mul_le_mul_of_nonneg_right hXsle (by positivity : 0 ≤ (1 + 2 * K * τ))
        exact div_le_div_of_nonneg_right hmul hK.le
      have hlogXs : Real.log (Xs * (1 + 2 * K * τ) / K) = (ν 1 + ν 2) / ν 0 := by
        have hXeq : Xs * (1 + 2 * K * τ) / K = Real.exp ((ν 1 + ν 2) / ν 0) := by
          dsimp [Xs]
          field_simp [hK.ne', hden.ne']
        rw [hXeq]
        exact Real.log_exp ((ν 1 + ν 2) / ν 0)
      have hlogX : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
          Real.log (X * (1 + 2 * K * τ) / K) := by
        have h1 : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hXpos.ne' hK.ne'
        have h2 : Real.log ((X * (1 + 2 * K * τ)) / K) = Real.log (X * (1 + 2 * K * τ)) - Real.log K :=
          Real.log_div (mul_pos hXpos hden).ne' hK.ne'
        have h3 : Real.log (X * (1 + 2 * K * τ)) = Real.log X + Real.log (1 + 2 * K * τ) :=
          Real.log_mul hXpos.ne' hden.ne'
        rw [h1, h2, h3]
        ring_nf
      linarith
    have hmain : ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 +
        (2 * ν 0 - ν 1 - ν 2)) ≤ 0 := by
      have hconv : (ν 1 + ν 2) / ν 0 - 2 = (2 * ν 0 - ν 1 - ν 2) / (-ν 0) := by
        field_simp [Ne.symm hν0.ne']
        ring_nf
      have hle : (2 * ν 0 - ν 1 - ν 2) / (-ν 0) ≤ Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2 := by
        rw [← hconv]
        linarith
      have hneg : 0 < -ν 0 := by linarith
      have hred : (2 * ν 0 - ν 1 - ν 2) ≤
          (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * (-ν 0) := by
        calc
          (2 * ν 0 - ν 1 - ν 2)
              = ((2 * ν 0 - ν 1 - ν 2) / (-ν 0)) * (-ν 0) := by
                  rw [div_mul_cancel₀ (2 * ν 0 - ν 1 - ν 2) (show -ν 0 ≠ 0 by positivity)]
          _ ≤ (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * (-ν 0) :=
                  mul_le_mul_of_nonneg_right hle (le_of_lt hneg)
      have hred' : (2 * ν 0 - ν 1 - ν 2) ≤
          -(Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 := by
        calc
          (2 * ν 0 - ν 1 - ν 2)
              ≤ (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * (-ν 0) := hred
          _ = -(Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 := by
                rw [mul_neg, neg_mul]
      linarith
    have hBd' : deriv (fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0) X =
        (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 := hBd.deriv
    have hXd' : deriv (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2)) X = 2 * ν 0 - ν 1 - ν 2 := hXd.deriv
    have hderiv : deriv Fh X =
        ((Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) * ν 0 + (2 * ν 0 - ν 1 - ν 2)) := by
      change deriv ((fun Y : ℝ => hamiltonIveyBarrier K τ Y * ν 0) +
        (fun Y : ℝ => Y * (2 * ν 0 - ν 1 - ν 2))) X = _
      rw [deriv_add]
      · rw [hBd', hXd']
      · exact hBd.differentiableAt
      · exact hXd.differentiableAt
    rw [hderiv]
    exact hmain
  exact antitoneOn_of_deriv_nonpos (D := Set.Ici Xs)
    (convex_Ici (r := Xs)) hFh_cont hFh_diff hFh_deriv

private lemma support_formula_le_candidate_star_of_le
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    {X : ℝ} (hX : 0 ≤ X)
    (hXle : X ≤ K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      hamiltonIveyConvexBarrier K τ (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * ν 0 +
        (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hc : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hmin := support_formula_min_branch (K := K) (τ := τ) hν0 X
  have hFs : scalarSectionalLowerBarrier3 K τ * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      scalarSectionalLowerBarrier3 K τ * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) := by
    dsimp [Xs]
    have hmul : X * (2 * ν 0 - ν 1 - ν 2) ≤
        (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) := by
      exact mul_le_mul_of_nonneg_right hXle hc
    linarith
  have hmono := monotoneOn_Fh_left (K := K) (τ := τ) hK hτ hν hν0
  have hFh : hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) := by
    dsimp [Xs] at hXle ⊢
    exact hmono (by exact ⟨hX, hXle⟩) (by
      have hXspos : 0 < K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ) := by
        have hden : 0 < 1 + 2 * K * τ := by
          have hKτ : 0 ≤ 2 * K * τ := by
            have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
            nlinarith
          nlinarith
        positivity
      exact ⟨le_of_lt hXspos, le_rfl⟩) hXle
  have hle_min : min (scalarSectionalLowerBarrier3 K τ * ν 0 + X * (2 * ν 0 - ν 1 - ν 2))
      (hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)) ≤
    min (scalarSectionalLowerBarrier3 K τ * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2))
      (hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2)) :=
    min_le_min hFs hFh
  have hG : hamiltonIveyConvexBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) =
      min (scalarSectionalLowerBarrier3 K τ * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2))
        (hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2)) := by
    exact support_formula_min_branch (K := K) (τ := τ) hν0 Xs
  rw [hmin, hG]
  exact hle_min

private lemma strictMonoOn_hamiltonIveyBarrier_above_E
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    StrictMonoOn (hamiltonIveyBarrier K τ)
      (Set.Ioi (K * Real.exp 2 / (1 + 2 * K * τ))) := by
  refine strictMonoOn_of_deriv_pos (D := Set.Ioi (K * Real.exp 2 / (1 + 2 * K * τ)))
    (convex_Ioi (r := (K * Real.exp 2 / (1 + 2 * K * τ)))) ?_ ?_
  · exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioi (K * Real.exp 2 / (1 + 2 * K * τ)) := by simpa [interior_Ioi] using hx
    have hden : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity) (le_of_lt hx')
    have hd : deriv (fun Y : ℝ => hamiltonIveyBarrier K τ Y) x =
        Real.log (x / K) + Real.log (1 + 2 * K * τ) - 2 := deriv_hamiltonIveyBarrier_x hK hxpos
    rw [hd]
    have hlog : 2 < Real.log (x / K) + Real.log (1 + 2 * K * τ) := by
      have harg1 : 0 < (K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K := by positivity
      have harg2 : 0 < x * (1 + 2 * K * τ) / K := by
        exact div_pos (mul_pos hxpos hden) hK
      have hmono : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) <
          Real.log (x * (1 + 2 * K * τ) / K) := by
        refine (Real.log_lt_log_iff harg1 harg2).mpr ?_
        have hmul : (K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) < x * (1 + 2 * K * τ) :=
          mul_lt_mul_of_pos_right hx' hden
        exact div_lt_div_of_pos_right hmul hK
      have hlogE : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) = 2 := by
        have hXeq : (K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K = Real.exp 2 := by
          field_simp [hK.ne', hden.ne']
        rw [hXeq]
        exact Real.log_exp 2
      have hlogX : Real.log (x / K) + Real.log (1 + 2 * K * τ) =
          Real.log (x * (1 + 2 * K * τ) / K) := by
        have h1 : Real.log (x / K) = Real.log x - Real.log K := Real.log_div hxpos.ne' hK.ne'
        have h2 : Real.log ((x * (1 + 2 * K * τ)) / K) = Real.log (x * (1 + 2 * K * τ)) - Real.log K :=
          Real.log_div (mul_pos hxpos hden).ne' hK.ne'
        have h3 : Real.log (x * (1 + 2 * K * τ)) = Real.log x + Real.log (1 + 2 * K * τ) :=
          Real.log_mul hxpos.ne' hden.ne'
        rw [h1, h2, h3]
        ring_nf
      rw [hlogX]
      linarith
    linarith

private lemma hamiltonIveyBarrier_gt_scalarLower_at_exp_four
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    scalarSectionalLowerBarrier3 K τ <
      hamiltonIveyBarrier K τ (K * Real.exp 4 / (1 + 2 * K * τ)) := by
  have hval : hamiltonIveyBarrier K τ (K * Real.exp 4 / (1 + 2 * K * τ)) =
      K * Real.exp 4 / (1 + 2 * K * τ) := by
    have hden : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    have hXpos : 0 < K * Real.exp 4 / (1 + 2 * K * τ) := by positivity
    have hlog : Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) / K) + Real.log (1 + 2 * K * τ) = 4 := by
      have hXeq : (K * Real.exp 4 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K = Real.exp 4 := by
        field_simp [hK.ne', hden.ne']
      have h1 : Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) / K) =
          Real.log (K * Real.exp 4 / (1 + 2 * K * τ)) - Real.log K :=
        Real.log_div hXpos.ne' hK.ne'
      have h2 : Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) =
          Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) * (1 + 2 * K * τ)) - Real.log K :=
        Real.log_div (mul_pos hXpos hden).ne' hK.ne'
      have h3 : Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) * (1 + 2 * K * τ)) =
          Real.log (K * Real.exp 4 / (1 + 2 * K * τ)) + Real.log (1 + 2 * K * τ) :=
        Real.log_mul hXpos.ne' hden.ne'
      calc
        Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) / K) + Real.log (1 + 2 * K * τ)
            = Real.log ((K * Real.exp 4 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) := by
              rw [h1, h2, h3]
              ring_nf
        _ = 4 := by
              rw [hXeq]
              exact Real.log_exp 4
    unfold hamiltonIveyBarrier
    rw [hlog]
    ring
  have hsc : scalarSectionalLowerBarrier3 K τ < K * Real.exp 4 / (1 + 2 * K * τ) := by
    unfold scalarSectionalLowerBarrier3
    have hden4 : 0 < 1 + 4 * K * τ := by
      have hKτ : 0 ≤ 4 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    have hden2 : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    rw [div_lt_div_iff₀ hden4 hden2]
    have hneg : -3 * K * (1 + 2 * K * τ) < 0 := by nlinarith
    have hpos : 0 < K * Real.exp 4 * (1 + 4 * K * τ) := by positivity
    linarith
  rw [hval]
  exact hsc

private lemma hamiltonIveyBarrier_lt_scalarLower_at_E
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    hamiltonIveyBarrier K τ (K * Real.exp 2 / (1 + 2 * K * τ)) < scalarSectionalLowerBarrier3 K τ := by
  have hval : hamiltonIveyBarrier K τ (K * Real.exp 2 / (1 + 2 * K * τ)) =
      -(K * Real.exp 2 / (1 + 2 * K * τ)) := by
    have hden : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    have hXpos : 0 < K * Real.exp 2 / (1 + 2 * K * τ) := by positivity
    have hlog : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) / K) + Real.log (1 + 2 * K * τ) = 2 := by
      have hXeq : (K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K = Real.exp 2 := by
        field_simp [hK.ne', hden.ne']
      have h1 : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) / K) =
          Real.log (K * Real.exp 2 / (1 + 2 * K * τ)) - Real.log K :=
        Real.log_div hXpos.ne' hK.ne'
      have h2 : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) =
          Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ)) - Real.log K :=
        Real.log_div (mul_pos hXpos hden).ne' hK.ne'
      have h3 : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ)) =
          Real.log (K * Real.exp 2 / (1 + 2 * K * τ)) + Real.log (1 + 2 * K * τ) :=
        Real.log_mul hXpos.ne' hden.ne'
      calc
        Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) / K) + Real.log (1 + 2 * K * τ)
            = Real.log ((K * Real.exp 2 / (1 + 2 * K * τ)) * (1 + 2 * K * τ) / K) := by
              rw [h1, h2, h3]
              ring_nf
        _ = 2 := by
              rw [hXeq]
              exact Real.log_exp 2
    unfold hamiltonIveyBarrier
    rw [hlog]
    ring
  have hEgt : 3 * K / (1 + 4 * K * τ) < K * Real.exp 2 / (1 + 2 * K * τ) := by
    have hden4 : 0 < 1 + 4 * K * τ := by
      have hKτ : 0 ≤ 4 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    have hden2 : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    rw [div_lt_div_iff₀ hden4 hden2]
    have hE2 : 3 < Real.exp 2 := by
      have h1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [h2]
      nlinarith
    have hKτ : 0 ≤ K * τ := mul_nonneg hK.le hτ
    have h1 : 3 * (1 + 2 * K * τ) < Real.exp 2 * (1 + 2 * K * τ) :=
      mul_lt_mul_of_pos_right hE2 hden2
    have h2 : Real.exp 2 * (1 + 2 * K * τ) ≤ Real.exp 2 * (1 + 4 * K * τ) := by
      have hle : 1 + 2 * K * τ ≤ 1 + 4 * K * τ := by nlinarith
      exact mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos 2))
    have h3 : 3 * (1 + 2 * K * τ) < Real.exp 2 * (1 + 4 * K * τ) := lt_of_lt_of_le h1 h2
    have hmul := mul_lt_mul_of_pos_left h3 hK
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hconv : -(K * Real.exp 2 / (1 + 2 * K * τ)) < -3 * K / (1 + 4 * K * τ) := by
    simpa [neg_div] using (neg_lt_neg_iff.mpr hEgt)
  rw [hval]
  unfold scalarSectionalLowerBarrier3
  exact hconv

private lemma exists_kink_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    ∃ X : ℝ, K * Real.exp 2 / (1 + 2 * K * τ) < X ∧
      hamiltonIveyBarrier K τ X = scalarSectionalLowerBarrier3 K τ := by
  let E : ℝ := K * Real.exp 2 / (1 + 2 * K * τ)
  let X₁ : ℝ := K * Real.exp 4 / (1 + 2 * K * τ)
  have hE₁ : E ≤ X₁ := by
    have hE2 : Real.exp 2 ≤ Real.exp 4 := (Real.exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 4))
    dsimp [E, X₁]
    have hden : 0 < 1 + 2 * K * τ := by
      have hKτ : 0 ≤ 2 * K * τ := by
        have h1 : 0 ≤ K * τ := mul_nonneg hK.le hτ
        nlinarith
      nlinarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE2 hK.le) hden.le
  have hcont : ContinuousOn (hamiltonIveyBarrier K τ) (Set.Icc E X₁) :=
    (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousOn.mono (by
      intro x hx
      exact Set.mem_univ x)
  have hElt : hamiltonIveyBarrier K τ E < scalarSectionalLowerBarrier3 K τ :=
    hamiltonIveyBarrier_lt_scalarLower_at_E hK hτ
  have hXgt : scalarSectionalLowerBarrier3 K τ < hamiltonIveyBarrier K τ X₁ :=
    hamiltonIveyBarrier_gt_scalarLower_at_exp_four hK hτ
  have himg : Set.Icc (hamiltonIveyBarrier K τ E) (hamiltonIveyBarrier K τ X₁) ⊆
      (hamiltonIveyBarrier K τ) '' Set.Icc E X₁ := intermediate_value_Icc hE₁ hcont
  have hmem : scalarSectionalLowerBarrier3 K τ ∈
      Set.Icc (hamiltonIveyBarrier K τ E) (hamiltonIveyBarrier K τ X₁) := ⟨hElt.le, hXgt.le⟩
  rcases himg hmem with ⟨X, hX, hEq⟩
  refine ⟨X, ?_, hEq⟩
  have hXge : E ≤ X := hX.1
  have hXne : X ≠ E := by
    intro hz
    have : hamiltonIveyBarrier K τ E = scalarSectionalLowerBarrier3 K τ := by
      simpa [hz] using hEq
    exact (ne_of_lt hElt) this
  exact lt_of_le_of_ne hXge (Ne.symm hXne)

private noncomputable def hamiltonIveyKinkPoint {K : ℝ} (hK : 0 < K) (τ : ℝ) : ℝ :=
  if hτ : 0 ≤ τ then Classical.choose (exists_kink_point hK hτ) else 0

private lemma hamiltonIveyKinkPoint_spec
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ ∧
      hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) = scalarSectionalLowerBarrier3 K τ := by
  have hdef : hamiltonIveyKinkPoint hK τ = Classical.choose (exists_kink_point hK hτ) := by
    dsimp [hamiltonIveyKinkPoint]
    simp [hτ]
  rw [hdef]
  exact Classical.choose_spec (exists_kink_point hK hτ)

private lemma hasDerivAt_hamiltonIveyBarrier_tau
    {K τ₀ X : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀) :
    HasDerivAt (fun τ : ℝ => hamiltonIveyBarrier K τ X)
      (X * (2 * K) / (1 + 2 * K * τ₀)) τ₀ := by
  have hfun : (fun τ : ℝ => hamiltonIveyBarrier K τ X) =
      fun τ : ℝ => X * Real.log X + X * (Real.log (1 + 2 * K * τ) - 3 - Real.log K) := by
    funext τ
    exact hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := τ) (X := X) hK
  rw [hfun]
  have hden : 0 < 1 + 2 * K * τ₀ := by
    have hKτ : 0 ≤ 2 * K * τ₀ := by
      have h1 : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀
      nlinarith
    nlinarith
  have hlin : HasDerivAt (fun τ : ℝ => 1 + 2 * K * τ) (2 * K) τ₀ := by
    have h1 : HasDerivAt (fun τ : ℝ => (2 * K) * τ) (2 * K) τ₀ := by
      simpa [mul_one] using (hasDerivAt_id τ₀).const_mul (2 * K)
    simpa [add_comm, mul_comm] using (h1.add_const 1)
  have hlog : HasDerivAt (fun τ : ℝ => Real.log (1 + 2 * K * τ)) ((2 * K) / (1 + 2 * K * τ₀)) τ₀ := by
    have hlog' : HasDerivAt Real.log ((1 : ℝ) / (1 + 2 * K * τ₀)) (1 + 2 * K * τ₀) := by
      simpa [one_div] using (Real.hasDerivAt_log (show 1 + 2 * K * τ₀ ≠ 0 from ne_of_gt hden))
    have hcomp := hlog'.comp τ₀ hlin
    convert hcomp using 1
    ring
  have hmul : HasDerivAt (fun τ : ℝ => X * Real.log (1 + 2 * K * τ))
      (X * ((2 * K) / (1 + 2 * K * τ₀))) τ₀ := by
    simpa [mul_comm] using hlog.const_mul X
  have hconst : HasDerivAt (fun τ : ℝ => X * Real.log X + X * (-3 - Real.log K)) 0 τ₀ := by
    simpa using (hasDerivAt_const (x := τ₀) (c := (X * Real.log X + X * (-3 - Real.log K) : ℝ)))
  have hsum := hmul.add hconst
  convert hsum using 1
  · funext τ
    dsimp
    ring_nf
  · ring

private lemma continuousAt_hamiltonIveyBarrier_tau
    {K τ₀ X : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀) :
    ContinuousAt (fun τ : ℝ => hamiltonIveyBarrier K τ X) τ₀ := by
  have hd := hasDerivAt_hamiltonIveyBarrier_tau (K := K) (τ₀ := τ₀) (X := X) hK hτ₀.le
  exact hd.continuousAt

private lemma continuousAt_scalarSectionalLowerBarrier3_tau
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀) :
    ContinuousAt (fun τ : ℝ => scalarSectionalLowerBarrier3 K τ) τ₀ := by
  have hd := hasDerivAt_scalarSectionalLowerBarrier3 (K := K) (τ₀ := τ₀) hK hτ₀.le
  exact hd.continuousAt

private lemma kink_point_above_E {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ :=
  (hamiltonIveyKinkPoint_spec hK hτ).1

private lemma kink_point_eq {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) = scalarSectionalLowerBarrier3 K τ :=
  (hamiltonIveyKinkPoint_spec hK hτ).2

private lemma kink_point_unique {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {X : ℝ} (hXgt : K * Real.exp 2 / (1 + 2 * K * τ) < X)
    (hXeq : hamiltonIveyBarrier K τ X = scalarSectionalLowerBarrier3 K τ) :
    X = hamiltonIveyKinkPoint hK τ := by
  have hmono := strictMonoOn_hamiltonIveyBarrier_above_E hK hτ
  have hX₂gt : K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ :=
    kink_point_above_E hK hτ
  by_contra hne
  have hlt : hamiltonIveyKinkPoint hK τ < X ∨ X < hamiltonIveyKinkPoint hK τ := lt_or_gt_of_ne (Ne.symm hne)
  rcases hlt with hlt | hgt
  · have hle : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) <
      hamiltonIveyBarrier K τ X := hmono hX₂gt hXgt hlt
    have hle' : scalarSectionalLowerBarrier3 K τ < scalarSectionalLowerBarrier3 K τ := by
      rw [kink_point_eq hK hτ, hXeq] at hle
      exact hle
    exact (lt_irrefl _) hle'
  · have hle : hamiltonIveyBarrier K τ X < hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) :=
      hmono hXgt hX₂gt hgt
    have hle' : scalarSectionalLowerBarrier3 K τ < scalarSectionalLowerBarrier3 K τ := by
      rw [kink_point_eq hK hτ, hXeq] at hle
      exact hle
    exact (lt_irrefl _) hle'

private lemma continuousAt_kink_point {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀) :
    ContinuousAt (fun τ : ℝ => hamiltonIveyKinkPoint hK τ) τ₀ := by
  let X : ℝ := hamiltonIveyKinkPoint hK τ₀
  have hXgt : K * Real.exp 2 / (1 + 2 * K * τ₀) < X := kink_point_above_E hK hτ₀.le
  have hXeq : hamiltonIveyBarrier K τ₀ X = scalarSectionalLowerBarrier3 K τ₀ := kink_point_eq hK hτ₀.le
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  let δ₀ : ℝ := (X - K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    have hpos : 0 < X - K * Real.exp 2 / (1 + 2 * K * τ₀) := by linarith
    linarith
  let ε' : ℝ := min ε δ₀
  have hε'pos : 0 < ε' := lt_min hε hδ₀pos
  have hXεgt : K * Real.exp 2 / (1 + 2 * K * τ₀) < X - ε' := by
    have hle : ε' ≤ δ₀ := by
      dsimp [ε']
      exact min_le_right _ _
    have hmain : X - (X - K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2 >
        K * Real.exp 2 / (1 + 2 * K * τ₀) := by
      have h2 : X - (X - K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2 =
          (X + K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2 := by ring
      rw [h2]
      linarith
    have hXεge : X - ε' ≥ X - δ₀ := by
      dsimp [ε', δ₀]
      have hle' : min ε ((X - K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2) ≤
          (X - K * Real.exp 2 / (1 + 2 * K * τ₀)) / 2 := min_le_right _ _
      linarith
    exact lt_of_lt_of_le hmain hXεge
  have hgap1 : 0 < hamiltonIveyBarrier K τ₀ (X + ε') - scalarSectionalLowerBarrier3 K τ₀ := by
    have hmono := strictMonoOn_hamiltonIveyBarrier_above_E (K := K) (τ := τ₀) hK hτ₀.le
    have hlt : hamiltonIveyBarrier K τ₀ X < hamiltonIveyBarrier K τ₀ (X + ε') :=
      hmono hXgt (by linarith : K * Real.exp 2 / (1 + 2 * K * τ₀) < X + ε')
        (by linarith : X < X + ε')
    have hmain : scalarSectionalLowerBarrier3 K τ₀ < hamiltonIveyBarrier K τ₀ (X + ε') := by
      simpa [hXeq] using hlt
    linarith
  have hgap2 : 0 < scalarSectionalLowerBarrier3 K τ₀ - hamiltonIveyBarrier K τ₀ (X - ε') := by
    have hmono := strictMonoOn_hamiltonIveyBarrier_above_E (K := K) (τ := τ₀) hK hτ₀.le
    have hlt : hamiltonIveyBarrier K τ₀ (X - ε') < hamiltonIveyBarrier K τ₀ X :=
      hmono hXεgt hXgt (by linarith : X - ε' < X)
    have hmain : hamiltonIveyBarrier K τ₀ (X - ε') < scalarSectionalLowerBarrier3 K τ₀ := by
      simpa [hXeq] using hlt
    linarith
  let η₁ : ℝ := (hamiltonIveyBarrier K τ₀ (X + ε') - scalarSectionalLowerBarrier3 K τ₀) / 4
  have hη₁pos : 0 < η₁ := by
    dsimp [η₁]
    linarith
  let η₂ : ℝ := (scalarSectionalLowerBarrier3 K τ₀ - hamiltonIveyBarrier K τ₀ (X - ε')) / 4
  have hη₂pos : 0 < η₂ := by
    dsimp [η₂]
    linarith
  let η : ℝ := min η₁ η₂
  have hηpos : 0 < η := lt_min hη₁pos hη₂pos
  have hηle1 : η ≤ η₁ := by
    dsimp [η]
    exact min_le_left _ _
  have hηle2 : η ≤ η₂ := by
    dsimp [η]
    exact min_le_right _ _
  have hs_cont : ContinuousAt (fun τ : ℝ => scalarSectionalLowerBarrier3 K τ) τ₀ :=
    continuousAt_scalarSectionalLowerBarrier3_tau hK hτ₀
  have hs_ev : ∀ᶠ τ in 𝓝 τ₀, |scalarSectionalLowerBarrier3 K τ - scalarSectionalLowerBarrier3 K τ₀| < η := by
    have h := (Metric.tendsto_nhds.mp hs_cont.tendsto) η hηpos
    simpa [dist_eq_norm] using h
  have hX_cont : ContinuousAt (fun τ : ℝ => hamiltonIveyBarrier K τ X) τ₀ :=
    continuousAt_hamiltonIveyBarrier_tau hK hτ₀
  have hX_ev : ∀ᶠ τ in 𝓝 τ₀, |hamiltonIveyBarrier K τ X - hamiltonIveyBarrier K τ₀ X| < η := by
    have h := (Metric.tendsto_nhds.mp hX_cont.tendsto) η hηpos
    simpa [dist_eq_norm] using h
  have hXp_cont : ContinuousAt (fun τ : ℝ => hamiltonIveyBarrier K τ (X + ε')) τ₀ :=
    continuousAt_hamiltonIveyBarrier_tau hK hτ₀
  have hXp_ev : ∀ᶠ τ in 𝓝 τ₀, |hamiltonIveyBarrier K τ (X + ε') - hamiltonIveyBarrier K τ₀ (X + ε')| < η := by
    have h := (Metric.tendsto_nhds.mp hXp_cont.tendsto) η hηpos
    simpa [dist_eq_norm] using h
  have hXm_cont : ContinuousAt (fun τ : ℝ => hamiltonIveyBarrier K τ (X - ε')) τ₀ :=
    continuousAt_hamiltonIveyBarrier_tau hK hτ₀
  have hXm_ev : ∀ᶠ τ in 𝓝 τ₀, |hamiltonIveyBarrier K τ (X - ε') - hamiltonIveyBarrier K τ₀ (X - ε')| < η := by
    have h := (Metric.tendsto_nhds.mp hXm_cont.tendsto) η hηpos
    simpa [dist_eq_norm] using h
  have hE_cont : ContinuousAt (fun τ : ℝ => K * Real.exp 2 / (1 + 2 * K * τ)) τ₀ := by
    have hden : 1 + 2 * K * τ₀ ≠ 0 := by
      have hpos : 0 < 1 + 2 * K * τ₀ := by
        have hKτ : 0 ≤ 2 * K * τ₀ := by
          have h1 : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀.le
          nlinarith
        nlinarith
      exact ne_of_gt hpos
    have hnum : ContinuousAt (fun τ : ℝ => K * Real.exp 2) τ₀ := continuousAt_const
    have hlin : ContinuousAt (fun τ : ℝ => 1 + 2 * K * τ) τ₀ := by fun_prop
    exact hnum.div hlin hden
  have hE_ev : ∀ᶠ τ in 𝓝 τ₀, K * Real.exp 2 / (1 + 2 * K * τ) < X - ε' := by
    have hgap : 0 < X - ε' - K * Real.exp 2 / (1 + 2 * K * τ₀) := by linarith
    have h := (Metric.tendsto_nhds.mp hE_cont.tendsto) (X - ε' - K * Real.exp 2 / (1 + 2 * K * τ₀)) hgap
    filter_upwards [h] with τ hτ
    have h1 := (abs_lt.mp hτ).2
    have h2 : K * Real.exp 2 / (1 + 2 * K * τ₀) < X - ε' := hXεgt
    linarith
  have hpos_ev : ∀ᶠ τ in 𝓝 τ₀, 0 < τ := Ioi_mem_nhds hτ₀
  filter_upwards [hs_ev, hX_ev, hXp_ev, hXm_ev, hE_ev, hpos_ev] with τ hτs hτX hτXp hτXm hτE hτpos
  have hX₂gt : K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ := kink_point_above_E hK hτpos.le
  have hX₂eq : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) = scalarSectionalLowerBarrier3 K τ := kink_point_eq hK hτpos.le
  have hmono := strictMonoOn_hamiltonIveyBarrier_above_E (K := K) (τ := τ) hK hτpos.le
  have hX₂lt : hamiltonIveyKinkPoint hK τ < X + ε' := by
    by_contra hnot
    have hge : X + ε' ≤ hamiltonIveyKinkPoint hK τ := le_of_not_gt hnot
    have hX₂gtE : K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ := hX₂gt
    have hXgtE : K * Real.exp 2 / (1 + 2 * K * τ) < X + ε' := by
      have hXgtE' : K * Real.exp 2 / (1 + 2 * K * τ) < X - ε' := hτE
      linarith
    have hle1 : hamiltonIveyBarrier K τ (X + ε') ≤ hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) :=
      hmono.monotoneOn hXgtE hX₂gtE hge
    have hstep1 : hamiltonIveyBarrier K τ (X + ε') > hamiltonIveyBarrier K τ X := by
      have hXgtE2 : K * Real.exp 2 / (1 + 2 * K * τ) < X := by linarith
      exact hmono hXgtE2 hXgtE (by linarith : X < X + ε')
    have hstep2 : hamiltonIveyBarrier K τ X > scalarSectionalLowerBarrier3 K τ₀ - η := by
      have hmain : hamiltonIveyBarrier K τ₀ X - η < hamiltonIveyBarrier K τ X := by
        have h1 : |hamiltonIveyBarrier K τ X - hamiltonIveyBarrier K τ₀ X| < η := hτX
        have h1' : -η < hamiltonIveyBarrier K τ X - hamiltonIveyBarrier K τ₀ X := (abs_lt.mp h1).1
        linarith
      have hXeq' : hamiltonIveyBarrier K τ₀ X = scalarSectionalLowerBarrier3 K τ₀ := hXeq
      linarith
    have hstep3 : hamiltonIveyBarrier K τ (X + ε') ≥ hamiltonIveyBarrier K τ₀ (X + ε') - η := by
      have h1 : |hamiltonIveyBarrier K τ (X + ε') - hamiltonIveyBarrier K τ₀ (X + ε')| < η := hτXp
      have h1' : hamiltonIveyBarrier K τ₀ (X + ε') - hamiltonIveyBarrier K τ (X + ε') < η := by
        have h1'' : -η < hamiltonIveyBarrier K τ (X + ε') - hamiltonIveyBarrier K τ₀ (X + ε') := (abs_lt.mp h1).1
        linarith
      linarith
    have hbig : scalarSectionalLowerBarrier3 K τ > scalarSectionalLowerBarrier3 K τ₀ + 3 * η := by
      have hgap : hamiltonIveyBarrier K τ₀ (X + ε') = scalarSectionalLowerBarrier3 K τ₀ + 4 * η₁ := by
        dsimp [η₁]
        ring_nf
      have h1 : hamiltonIveyBarrier K τ (X + ε') > scalarSectionalLowerBarrier3 K τ₀ + 3 * η := by
        have h1' : hamiltonIveyBarrier K τ₀ (X + ε') - hamiltonIveyBarrier K τ (X + ε') < η := by
          have h1'' : -η < hamiltonIveyBarrier K τ (X + ε') - hamiltonIveyBarrier K τ₀ (X + ε') := (abs_lt.mp hτXp).1
          linarith
        linarith
      have h2 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) ≥ hamiltonIveyBarrier K τ (X + ε') := hle1
      have h3 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) = scalarSectionalLowerBarrier3 K τ := hX₂eq
      linarith
    have hsmall : scalarSectionalLowerBarrier3 K τ < scalarSectionalLowerBarrier3 K τ₀ + η := by
      have h1 : |scalarSectionalLowerBarrier3 K τ - scalarSectionalLowerBarrier3 K τ₀| < η := hτs
      have h1' : scalarSectionalLowerBarrier3 K τ - scalarSectionalLowerBarrier3 K τ₀ < η := (abs_lt.mp h1).2
      linarith
    linarith
  have hX₂gt' : X - ε' < hamiltonIveyKinkPoint hK τ := by
    by_contra hnot
    have hle : hamiltonIveyKinkPoint hK τ ≤ X - ε' := le_of_not_gt hnot
    have hX₂gtE : K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK τ := hX₂gt
    have hXmgtE : K * Real.exp 2 / (1 + 2 * K * τ) < X - ε' := hτE
    have hle1 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) ≤ hamiltonIveyBarrier K τ (X - ε') :=
      hmono.monotoneOn hX₂gtE hXmgtE hle
    have hstep1 : hamiltonIveyBarrier K τ (X - ε') < hamiltonIveyBarrier K τ X := by
      have hXgtE2 : K * Real.exp 2 / (1 + 2 * K * τ) < X := by linarith
      exact hmono hXmgtE hXgtE2 (by linarith : X - ε' < X)
    have hstep2 : hamiltonIveyBarrier K τ X < scalarSectionalLowerBarrier3 K τ₀ + η := by
      have h1 : |hamiltonIveyBarrier K τ X - hamiltonIveyBarrier K τ₀ X| < η := hτX
      have h1' : hamiltonIveyBarrier K τ X - hamiltonIveyBarrier K τ₀ X < η := (abs_lt.mp h1).2
      have hXeq' : hamiltonIveyBarrier K τ₀ X = scalarSectionalLowerBarrier3 K τ₀ := hXeq
      linarith
    have hstep3 : hamiltonIveyBarrier K τ (X - ε') ≤ hamiltonIveyBarrier K τ₀ (X - ε') + η := by
      have h1 : |hamiltonIveyBarrier K τ (X - ε') - hamiltonIveyBarrier K τ₀ (X - ε')| < η := hτXm
      have h1' : hamiltonIveyBarrier K τ (X - ε') - hamiltonIveyBarrier K τ₀ (X - ε') < η := (abs_lt.mp h1).2
      linarith
    have hsmall : scalarSectionalLowerBarrier3 K τ < scalarSectionalLowerBarrier3 K τ₀ - 3 * η := by
      have hgap : hamiltonIveyBarrier K τ₀ (X - ε') = scalarSectionalLowerBarrier3 K τ₀ - 4 * η₂ := by
        dsimp [η₂]
        ring_nf
      have h1 : hamiltonIveyBarrier K τ (X - ε') < scalarSectionalLowerBarrier3 K τ₀ - 3 * η := by
        have h1' : hamiltonIveyBarrier K τ (X - ε') - hamiltonIveyBarrier K τ₀ (X - ε') < η := (abs_lt.mp hτXm).2
        linarith
      have h2 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) ≤ hamiltonIveyBarrier K τ (X - ε') := hle1
      have h3 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) = scalarSectionalLowerBarrier3 K τ := hX₂eq
      linarith
    have hbig : scalarSectionalLowerBarrier3 K τ₀ - η < scalarSectionalLowerBarrier3 K τ := by
      have h1 : |scalarSectionalLowerBarrier3 K τ - scalarSectionalLowerBarrier3 K τ₀| < η := hτs
      have h1' : -η < scalarSectionalLowerBarrier3 K τ - scalarSectionalLowerBarrier3 K τ₀ := (abs_lt.mp h1).1
      linarith
    linarith
  have hdist : dist (hamiltonIveyKinkPoint hK τ) X < ε := by
    have hle' : X - ε' < hamiltonIveyKinkPoint hK τ ∧ hamiltonIveyKinkPoint hK τ < X + ε' := ⟨hX₂gt', hX₂lt⟩
    have hmain : X - ε < hamiltonIveyKinkPoint hK τ ∧ hamiltonIveyKinkPoint hK τ < X + ε := by
      have hεle : ε' ≤ ε := min_le_left _ _
      constructor
      · linarith [hle'.1, hεle]
      · linarith [hle'.2, hεle]
    rw [dist_eq_norm]
    rw [Real.norm_eq_abs]
    exact abs_sub_lt_iff.mpr ⟨by linarith [hmain.2], by linarith [hmain.1]⟩
  simpa [dist_eq_norm] using hdist

private lemma hamiltonIveyBarrier_x_deriv_pos
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀) {X : ℝ}
    (hX : K * Real.exp 2 / (1 + 2 * K * τ₀) < X) :
    0 < Real.log (X / K) + Real.log (1 + 2 * K * τ₀) - 2 := by
  have hden : 0 < 1 + 2 * K * τ₀ := by
    have hKτ : 0 ≤ 2 * K * τ₀ := by
      have h1 : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀
      nlinarith
    nlinarith
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) (le_of_lt hX)
  have harg1 : 0 < (K * Real.exp 2 / (1 + 2 * K * τ₀)) * (1 + 2 * K * τ₀) / K := by positivity
  have harg2 : 0 < X * (1 + 2 * K * τ₀) / K := by
    exact div_pos (mul_pos hXpos hden) hK
  have hmono : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ₀)) * (1 + 2 * K * τ₀) / K) <
      Real.log (X * (1 + 2 * K * τ₀) / K) := by
    refine (Real.log_lt_log_iff harg1 harg2).mpr ?_
    have hmul : (K * Real.exp 2 / (1 + 2 * K * τ₀)) * (1 + 2 * K * τ₀) < X * (1 + 2 * K * τ₀) :=
      mul_lt_mul_of_pos_right hX hden
    exact div_lt_div_of_pos_right hmul hK
  have hlogE : Real.log ((K * Real.exp 2 / (1 + 2 * K * τ₀)) * (1 + 2 * K * τ₀) / K) = 2 := by
    have hXeq : (K * Real.exp 2 / (1 + 2 * K * τ₀)) * (1 + 2 * K * τ₀) / K = Real.exp 2 := by
      field_simp [hK.ne', hden.ne']
    rw [hXeq]
    exact Real.log_exp 2
  have hlogX : Real.log (X / K) + Real.log (1 + 2 * K * τ₀) =
      Real.log (X * (1 + 2 * K * τ₀) / K) := by
    have h1 : Real.log (X / K) = Real.log X - Real.log K := Real.log_div hXpos.ne' hK.ne'
    have h2 : Real.log ((X * (1 + 2 * K * τ₀)) / K) = Real.log (X * (1 + 2 * K * τ₀)) - Real.log K :=
      Real.log_div (mul_pos hXpos hden).ne' hK.ne'
    have h3 : Real.log (X * (1 + 2 * K * τ₀)) = Real.log X + Real.log (1 + 2 * K * τ₀) :=
      Real.log_mul hXpos.ne' hden.ne'
    rw [h1, h2, h3]
    ring_nf
  rw [hlogX]
  linarith

private lemma exists_hamiltonIveyBarrier_tau_deriv_eq_slope
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀) {τ : ℝ}
    (hτpos : 0 < τ) (hτne : τ ≠ τ₀) (X2τ : ℝ) :
    ∃ ξ : ℝ, ξ ∈ Set.Ioo (min τ τ₀) (max τ τ₀) ∧
      X2τ * (2 * K) / (1 + 2 * K * ξ) =
        (hamiltonIveyBarrier K τ X2τ - hamiltonIveyBarrier K τ₀ X2τ) / (τ - τ₀) := by
  let a : ℝ := min τ τ₀
  let b : ℝ := max τ τ₀
  have hab : a < b := (min_lt_max.mpr hτne)
  have hslice : ∀ t : ℝ, t ∈ Set.Icc a b →
      HasDerivAt (fun u : ℝ => hamiltonIveyBarrier K u X2τ)
        (X2τ * (2 * K) / (1 + 2 * K * t)) t := by
    intro t ht
    have hminpos : 0 < min τ τ₀ := lt_min hτpos hτ₀
    have ht0 : 0 ≤ t := by
      have hale : a ≤ t := ht.1
      dsimp [a] at hale
      linarith
    exact hasDerivAt_hamiltonIveyBarrier_tau (K := K) (τ₀ := t) (X := X2τ) hK ht0
  have hcont : ContinuousOn (fun u : ℝ => hamiltonIveyBarrier K u X2τ) (Set.Icc a b) :=
    HasDerivAt.continuousOn hslice
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => hamiltonIveyBarrier K u X2τ) (Set.Ioo a b) := by
    intro t ht
    have hmem : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact (hslice t hmem).differentiableAt.differentiableWithinAt
  rcases exists_deriv_eq_slope (fun u : ℝ => hamiltonIveyBarrier K u X2τ) hab hcont hdiff
    with ⟨ξ, hξ, hξeq⟩
  refine ⟨ξ, hξ, ?_⟩
  have hξmem : ξ ∈ Set.Icc a b := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hminpos : 0 < min τ τ₀ := lt_min hτpos hτ₀
  have hξ0 : 0 ≤ ξ := by
    have hale : a ≤ ξ := hξmem.1
    dsimp [a] at hale
    linarith
  have hderiv : deriv (fun u : ℝ => hamiltonIveyBarrier K u X2τ) ξ =
      X2τ * (2 * K) / (1 + 2 * K * ξ) :=
    (hasDerivAt_hamiltonIveyBarrier_tau (K := K) (τ₀ := ξ) (X := X2τ) hK hξ0).deriv
  rw [hderiv] at hξeq
  by_cases hle : τ ≤ τ₀
  · have hmin : min τ τ₀ = τ := min_eq_left hle
    have hmax : max τ τ₀ = τ₀ := max_eq_right hle
    have hmain : (hamiltonIveyBarrier K b X2τ - hamiltonIveyBarrier K a X2τ) / (b - a) =
        (hamiltonIveyBarrier K τ X2τ - hamiltonIveyBarrier K τ₀ X2τ) / (τ - τ₀) := by
      dsimp [a, b]
      rw [hmin, hmax]
      rw [show τ - τ₀ = -(τ₀ - τ) by ring]
      rw [show hamiltonIveyBarrier K τ X2τ - hamiltonIveyBarrier K τ₀ X2τ =
          -(hamiltonIveyBarrier K τ₀ X2τ - hamiltonIveyBarrier K τ X2τ) by ring]
      rw [neg_div_neg_eq]
    exact hξeq.trans hmain
  · have hlt : τ₀ < τ := lt_of_not_ge hle
    have hmin : min τ τ₀ = τ₀ := min_eq_right (le_of_lt hlt)
    have hmax : max τ τ₀ = τ := max_eq_left (le_of_lt hlt)
    have hmain : (hamiltonIveyBarrier K b X2τ - hamiltonIveyBarrier K a X2τ) / (b - a) =
        (hamiltonIveyBarrier K τ X2τ - hamiltonIveyBarrier K τ₀ X2τ) / (τ - τ₀) := by
      dsimp [a, b]
      rw [hmin, hmax]
    exact hξeq.trans hmain

private lemma exists_hamiltonIveyBarrier_x_deriv_eq_slope
    {K τ₀ : ℝ} (hK : 0 < K) {X X2τ : ℝ}
    (hXpos : 0 < X) (hX2pos : 0 < X2τ) (hXne : X ≠ X2τ) :
    ∃ η : ℝ, η ∈ Set.Ioo (min X X2τ) (max X X2τ) ∧
      Real.log (η / K) + Real.log (1 + 2 * K * τ₀) - 2 =
        (hamiltonIveyBarrier K τ₀ X2τ - hamiltonIveyBarrier K τ₀ X) / (X2τ - X) := by
  let a : ℝ := min X X2τ
  let b : ℝ := max X X2τ
  have hab : a < b := (min_lt_max.mpr hXne)
  have hslice : ∀ y : ℝ, y ∈ Set.Icc a b →
      HasDerivAt (fun u : ℝ => hamiltonIveyBarrier K τ₀ u)
        (Real.log (y / K) + Real.log (1 + 2 * K * τ₀) - 2) y := by
    intro y hy
    have hminpos : 0 < min X X2τ := lt_min hXpos hX2pos
    have hy0 : 0 < y := by
      have hale : a ≤ y := hy.1
      dsimp [a] at hale
      linarith
    exact hasDerivAt_hamiltonIveyBarrier_x (K := K) (τ := τ₀) (X := y) hK hy0
  have hcont : ContinuousOn (fun u : ℝ => hamiltonIveyBarrier K τ₀ u) (Set.Icc a b) :=
    HasDerivAt.continuousOn hslice
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => hamiltonIveyBarrier K τ₀ u) (Set.Ioo a b) := by
    intro y hy
    have hmem : y ∈ Set.Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    exact (hslice y hmem).differentiableAt.differentiableWithinAt
  rcases exists_deriv_eq_slope (fun u : ℝ => hamiltonIveyBarrier K τ₀ u) hab hcont hdiff
    with ⟨η, hη, hηeq⟩
  refine ⟨η, hη, ?_⟩
  have hηmem : η ∈ Set.Icc a b := ⟨le_of_lt hη.1, le_of_lt hη.2⟩
  have hminpos : 0 < min X X2τ := lt_min hXpos hX2pos
  have hη0 : 0 < η := by
    have hale : a ≤ η := hηmem.1
    dsimp [a] at hale
    linarith
  have hderiv : deriv (fun u : ℝ => hamiltonIveyBarrier K τ₀ u) η =
      Real.log (η / K) + Real.log (1 + 2 * K * τ₀) - 2 :=
    (hasDerivAt_hamiltonIveyBarrier_x (K := K) (τ := τ₀) (X := η) hK hη0).deriv
  rw [hderiv] at hηeq
  by_cases hle : X ≤ X2τ
  · have hmin : min X X2τ = X := min_eq_left hle
    have hmax : max X X2τ = X2τ := max_eq_right hle
    have hmain : (hamiltonIveyBarrier K τ₀ b - hamiltonIveyBarrier K τ₀ a) / (b - a) =
        (hamiltonIveyBarrier K τ₀ X2τ - hamiltonIveyBarrier K τ₀ X) / (X2τ - X) := by
      dsimp [a, b]
      rw [hmin, hmax]
    exact hηeq.trans hmain
  · have hlt : X2τ < X := lt_of_not_ge hle
    have hmin : min X X2τ = X2τ := min_eq_right (le_of_lt hlt)
    have hmax : max X X2τ = X := max_eq_left (le_of_lt hlt)
    have hmain : (hamiltonIveyBarrier K τ₀ b - hamiltonIveyBarrier K τ₀ a) / (b - a) =
        (hamiltonIveyBarrier K τ₀ X2τ - hamiltonIveyBarrier K τ₀ X) / (X2τ - X) := by
      dsimp [a, b]
      rw [hmin, hmax]
      rw [show X2τ - X = -(X - X2τ) by ring]
      rw [show hamiltonIveyBarrier K τ₀ X2τ - hamiltonIveyBarrier K τ₀ X =
          -(hamiltonIveyBarrier K τ₀ X - hamiltonIveyBarrier K τ₀ X2τ) by ring]
      rw [neg_div_neg_eq]
    exact hηeq.trans hmain

private lemma hasDerivAt_hamiltonIveyKinkPoint
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀) :
    HasDerivAt (fun τ : ℝ => hamiltonIveyKinkPoint hK τ)
      ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
        hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
        (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) τ₀ := by
  let X : ℝ := hamiltonIveyKinkPoint hK τ₀
  let X₂ : ℝ → ℝ := fun τ => hamiltonIveyKinkPoint hK τ
  let E₀ : ℝ := K * Real.exp 2 / (1 + 2 * K * τ₀)
  let hX : ℝ → ℝ := fun y => Real.log (y / K) + Real.log (1 + 2 * K * τ₀) - 2
  let hτfun : ℝ × ℝ → ℝ := fun p => p.2 * (2 * K) / (1 + 2 * K * p.1)
  let s : ℝ → ℝ := fun τ => scalarSectionalLowerBarrier3 K τ
  let s' : ℝ := 12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2
  have hEpos : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hXgtE : E₀ < X := by
    simpa [E₀, X] using kink_point_above_E hK hτ₀.le
  have hXpos : 0 < X := lt_of_lt_of_le hEpos (le_of_lt hXgtE)
  have hX2_cont : ContinuousAt X₂ τ₀ := by
    simpa [X₂] using continuousAt_kink_point hK hτ₀
  have hX2E : ∀ᶠ τ in 𝓝 τ₀, E₀ < X₂ τ := by
    have hgap : 0 < X - E₀ := by linarith
    have hev : ∀ᶠ τ in 𝓝 τ₀, dist (X₂ τ) X < X - E₀ :=
      (Metric.tendsto_nhds.mp hX2_cont.tendsto) (X - E₀) hgap
    filter_upwards [hev] with τ hτ
    have habs : |X₂ τ - X| < X - E₀ := by simpa [dist_eq_norm, Real.norm_eq_abs] using hτ
    have h1 : -(X - E₀) < X₂ τ - X := (abs_lt.mp habs).1
    linarith
  have hτpos_nhd : ∀ᶠ τ in 𝓝 τ₀, τ₀ / 2 < τ := Ioi_mem_nhds (half_lt_self hτ₀)
  have hXpos0 : 0 < hX X := by
    dsimp [hX]
    exact hamiltonIveyBarrier_x_deriv_pos hK hτ₀.le (by simpa [E₀] using hXgtE)
  let ξ : ℝ → ℝ := fun τ =>
    if h : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ then
      Classical.choose (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀
        (lt_of_lt_of_le (half_pos hτ₀) (le_of_lt h.1)) h.2.2 (X₂ τ))
    else τ₀
  let η : ℝ → ℝ := fun τ =>
    if h : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ ∧ X₂ τ ≠ X then
      Classical.choose (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos
        (lt_of_lt_of_le hEpos (le_of_lt h.2.1)) (Ne.symm h.2.2.2))
    else X
  have hξ_spec : ∀ τ : ℝ, τ₀ / 2 < τ → E₀ < X₂ τ → τ ≠ τ₀ →
      ξ τ ∈ Set.Ioo (min τ τ₀) (max τ τ₀) ∧
      hτfun (ξ τ, X₂ τ) =
        (hamiltonIveyBarrier K τ (X₂ τ) - hamiltonIveyBarrier K τ₀ (X₂ τ)) / (τ - τ₀) := by
    intro τ hτpos hτE hτne
    have hτ0 : 0 < τ := lt_of_lt_of_le (half_pos hτ₀) (le_of_lt hτpos)
    have hguard : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ := ⟨hτpos, hτE, hτne⟩
    have hspec := Classical.choose_spec (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀ hτ0 hτne (X₂ τ))
    have hξdef : ξ τ = Classical.choose (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀ hτ0 hτne (X₂ τ)) := by
      dsimp [ξ]
      rw [dif_pos hguard]
    rw [hξdef]
    constructor
    · exact hspec.1
    · simpa [hτfun] using hspec.2
  have hη_spec : ∀ τ : ℝ, τ₀ / 2 < τ → E₀ < X₂ τ → τ ≠ τ₀ → X₂ τ ≠ X →
      η τ ∈ Set.Ioo (min X (X₂ τ)) (max X (X₂ τ)) ∧
      hX (η τ) * (X₂ τ - X) = hamiltonIveyBarrier K τ₀ (X₂ τ) - s τ₀ := by
    intro τ hτpos hτE hτne hX2ne
    have hX2pos : 0 < X₂ τ := lt_of_lt_of_le hEpos (le_of_lt hτE)
    have hguard : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ ∧ X₂ τ ≠ X := ⟨hτpos, hτE, hτne, hX2ne⟩
    have hspec := Classical.choose_spec (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos hX2pos (Ne.symm hX2ne))
    have hηdef : η τ = Classical.choose (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos hX2pos (Ne.symm hX2ne)) := by
      dsimp [η]
      rw [dif_pos hguard]
    rw [hηdef]
    constructor
    · exact hspec.1
    · have hk : hamiltonIveyBarrier K τ₀ X = s τ₀ := by
        dsimp [s, X]
        exact kink_point_eq hK hτ₀.le
      have hXden : X₂ τ - X ≠ 0 := sub_ne_zero.mpr hX2ne
      have hmain : hX (Classical.choose (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos hX2pos (Ne.symm hX2ne))) *
            (X₂ τ - X) = hamiltonIveyBarrier K τ₀ (X₂ τ) - hamiltonIveyBarrier K τ₀ X := by
        have h : hX (Classical.choose (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos hX2pos (Ne.symm hX2ne))) =
            (hamiltonIveyBarrier K τ₀ (X₂ τ) - hamiltonIveyBarrier K τ₀ X) / (X₂ τ - X) := by
          dsimp [hX]
          exact hspec.2
        calc
          hX (Classical.choose (exists_hamiltonIveyBarrier_x_deriv_eq_slope (τ₀ := τ₀) hK hXpos hX2pos (Ne.symm hX2ne))) * (X₂ τ - X)
              = ((hamiltonIveyBarrier K τ₀ (X₂ τ) - hamiltonIveyBarrier K τ₀ X) / (X₂ τ - X)) *
                  (X₂ τ - X) := by rw [h]
          _ = hamiltonIveyBarrier K τ₀ (X₂ τ) - hamiltonIveyBarrier K τ₀ X := by
                exact div_mul_cancel₀ _ hXden
      simpa [hk, s] using hmain
  have hx_identity : ∀ τ : ℝ, τ₀ / 2 < τ → E₀ < X₂ τ → τ ≠ τ₀ →
      hamiltonIveyBarrier K τ₀ (X₂ τ) - s τ₀ = hX (η τ) * (X₂ τ - X) := by
    intro τ hτpos hτE hτne
    by_cases hX2ne : X₂ τ ≠ X
    · have hspec := hη_spec τ hτpos hτE hτne hX2ne
      exact hspec.2.symm
    · have hX2eq : X₂ τ = X := not_not.mp hX2ne
      have hηdef : η τ = X := by
        dsimp [η]
        rw [dif_neg]
        intro hg
        exact hX2ne hg.2.2.2
      rw [hX2eq, hηdef]
      have hk : hamiltonIveyBarrier K τ₀ X = s τ₀ := by
        dsimp [s, X]
        exact kink_point_eq hK hτ₀.le
      simp [hk]
  have hτ_identity : ∀ τ : ℝ, τ₀ / 2 < τ → E₀ < X₂ τ → τ ≠ τ₀ →
      s τ - hamiltonIveyBarrier K τ₀ (X₂ τ) = hτfun (ξ τ, X₂ τ) * (τ - τ₀) := by
    intro τ hτpos hτE hτne
    have hτ0 : 0 < τ := lt_of_lt_of_le (half_pos hτ₀) (le_of_lt hτpos)
    have hguard : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ := ⟨hτpos, hτE, hτne⟩
    have hspec := Classical.choose_spec (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀ hτ0 hτne (X₂ τ))
    have hξdef : ξ τ = Classical.choose (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀ hτ0 hτne (X₂ τ)) := by
      dsimp [ξ]
      rw [dif_pos hguard]
    rw [hξdef]
    have hk : hamiltonIveyBarrier K τ (X₂ τ) = s τ := by
      dsimp [s, X₂]
      exact kink_point_eq hK (le_of_lt hτ0)
    have hspec2' : hτfun (Classical.choose (exists_hamiltonIveyBarrier_tau_deriv_eq_slope hK hτ₀ hτ0 hτne (X₂ τ)), X₂ τ) =
        (hamiltonIveyBarrier K τ (X₂ τ) - hamiltonIveyBarrier K τ₀ (X₂ τ)) / (τ - τ₀) := by
      simpa [hτfun] using hspec.2
    rw [hspec2']
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hτne)]
    rw [hk]
  have hidentity : ∀ᶠ τ in 𝓝 τ₀, τ ≠ τ₀ → slope X₂ τ₀ τ =
      (slope s τ₀ τ - hτfun (ξ τ, X₂ τ)) / hX (η τ) := by
    filter_upwards [hτpos_nhd, hX2E] with τ hτpos hτE
    intro hτne
    have hx := hx_identity τ hτpos hτE hτne
    have ht := hτ_identity τ hτpos hτE hτne
    have hηpos : 0 < hX (η τ) := by
      by_cases hX2ne : X₂ τ ≠ X
      · have hspec := hη_spec τ hτpos hτE hτne hX2ne
        have hηlo : min X (X₂ τ) < η τ := hspec.1.1
        have hmin_gt : E₀ < min X (X₂ τ) := lt_min hXgtE hτE
        dsimp [hX]
        exact hamiltonIveyBarrier_x_deriv_pos hK hτ₀.le (by linarith [hmin_gt, hηlo])
      · have hX2eq : X₂ τ = X := not_not.mp hX2ne
        have hηdef : η τ = X := by
          dsimp [η]
          rw [dif_neg]
          intro hg
          exact hX2ne hg.2.2.2
        rw [hηdef]
        dsimp [hX]
        exact hamiltonIveyBarrier_x_deriv_pos hK hτ₀.le hXgtE
    have hηne : hX (η τ) ≠ 0 := ne_of_gt hηpos
    have hsum : s τ - s τ₀ = hτfun (ξ τ, X₂ τ) * (τ - τ₀) + hX (η τ) * (X₂ τ - X) := by
      calc
        s τ - s τ₀ = (s τ - hamiltonIveyBarrier K τ₀ (X₂ τ)) +
            (hamiltonIveyBarrier K τ₀ (X₂ τ) - s τ₀) := by ring
        _ = hτfun (ξ τ, X₂ τ) * (τ - τ₀) + hX (η τ) * (X₂ τ - X) := by rw [ht, hx]
    have hq : (X₂ τ - X) / (τ - τ₀) = (slope s τ₀ τ - hτfun (ξ τ, X₂ τ)) / hX (η τ) := by
      have hs_slope : slope s τ₀ τ = (s τ - s τ₀) / (τ - τ₀) := by
        rw [slope_def_field]
      have hsum2 : (s τ - s τ₀) / (τ - τ₀) =
          hτfun (ξ τ, X₂ τ) + hX (η τ) * ((X₂ τ - X) / (τ - τ₀)) := by
        rw [hsum]
        field_simp [sub_ne_zero.mpr hτne]
      have hqeq : hX (η τ) * ((X₂ τ - X) / (τ - τ₀)) = slope s τ₀ τ - hτfun (ξ τ, X₂ τ) := by
        rw [hs_slope]
        linarith [hsum2]
      rw [eq_div_iff hηne]
      rw [mul_comm]
      exact hqeq
    calc
      slope X₂ τ₀ τ = (X₂ τ - X) / (τ - τ₀) := by
        rw [slope_def_field]
      _ = (slope s τ₀ τ - hτfun (ξ τ, X₂ τ)) / hX (η τ) := hq
  have hξ_bound : ∀ τ : ℝ, |ξ τ - τ₀| ≤ |τ - τ₀| := by
    intro τ
    by_cases hg : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀
    · have hspec := hξ_spec τ hg.1 hg.2.1 hg.2.2
      have hξlo : min τ τ₀ < ξ τ := hspec.1.1
      have hξhi : ξ τ < max τ τ₀ := hspec.1.2
      by_cases hle : τ ≤ τ₀
      · have hmin : min τ τ₀ = τ := min_eq_left hle
        have hmax : max τ τ₀ = τ₀ := max_eq_right hle
        have hlo : τ < ξ τ := by simpa [hmin] using hξlo
        have hhi : ξ τ < τ₀ := by simpa [hmax] using hξhi
        rw [abs_of_neg (sub_neg.mpr hhi)]
        rw [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne hle hg.2.2))]
        linarith
      · have hgt : τ₀ < τ := lt_of_not_ge hle
        have hmin : min τ τ₀ = τ₀ := min_eq_right (le_of_lt hgt)
        have hmax : max τ τ₀ = τ := max_eq_left (le_of_lt hgt)
        have hlo : τ₀ < ξ τ := by simpa [hmin] using hξlo
        have hhi : ξ τ < τ := by simpa [hmax] using hξhi
        rw [abs_of_pos (sub_pos.mpr hlo)]
        rw [abs_of_pos (sub_pos.mpr hgt)]
        linarith
    · have hξdef : ξ τ = τ₀ := by
        dsimp [ξ]
        rw [dif_neg hg]
      rw [hξdef]
      simp
  have hη_bound : ∀ τ : ℝ, |η τ - X| ≤ |X₂ τ - X| := by
    intro τ
    by_cases hg : τ₀ / 2 < τ ∧ E₀ < X₂ τ ∧ τ ≠ τ₀ ∧ X₂ τ ≠ X
    · have hspec := hη_spec τ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
      have hηlo : min X (X₂ τ) < η τ := hspec.1.1
      have hηhi : η τ < max X (X₂ τ) := hspec.1.2
      by_cases hle : X ≤ X₂ τ
      · have hmin : min X (X₂ τ) = X := min_eq_left hle
        have hmax : max X (X₂ τ) = X₂ τ := max_eq_right hle
        have hlo : X < η τ := by simpa [hmin] using hηlo
        have hhi : η τ < X₂ τ := by simpa [hmax] using hηhi
        rw [abs_of_pos (sub_pos.mpr hlo)]
        rw [abs_of_pos (sub_pos.mpr (lt_of_lt_of_le hlo (le_of_lt hhi)))]
        linarith
      · have hgt : X₂ τ < X := lt_of_not_ge hle
        have hmin : min X (X₂ τ) = X₂ τ := min_eq_right (le_of_lt hgt)
        have hmax : max X (X₂ τ) = X := max_eq_left (le_of_lt hgt)
        have hlo : X₂ τ < η τ := by simpa [hmin] using hηlo
        have hhi : η τ < X := by simpa [hmax] using hηhi
        rw [abs_of_neg (sub_neg.mpr hhi)]
        rw [abs_of_neg (sub_neg.mpr hgt)]
        linarith
    · have hηdef : η τ = X := by
        dsimp [η]
        rw [dif_neg hg]
      rw [hηdef]
      simp
  have hτdiff_zero : Filter.Tendsto (fun τ : ℝ => |τ - τ₀|) (𝓝 τ₀) (𝓝 (0 : ℝ)) := by
    have hτ : Filter.Tendsto (fun τ : ℝ => τ - τ₀) (𝓝 τ₀) (𝓝 (0 : ℝ)) := by
      simpa using (Continuous.tendsto continuous_id τ₀).sub (tendsto_const_nhds (x := τ₀))
    simpa [Real.norm_eq_abs] using hτ.norm
  have hX₂_zero : Filter.Tendsto (fun τ : ℝ => |X₂ τ - X|) (𝓝 τ₀) (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (Metric.tendsto_nhds.mp hX2_cont.tendsto) ε hε
    filter_upwards [h] with τ hτ
    simpa [dist_eq_norm, Real.norm_eq_abs] using hτ
  have hξ_zero : Filter.Tendsto (fun τ : ℝ => |ξ τ - τ₀|) (𝓝 τ₀) (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun τ => abs_nonneg _) hξ_bound hτdiff_zero
  have hη_zero : Filter.Tendsto (fun τ : ℝ => |η τ - X|) (𝓝 τ₀) (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun τ => abs_nonneg _) hη_bound hX₂_zero
  have hξ_tendsto : Filter.Tendsto ξ (𝓝 τ₀) (𝓝 τ₀) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (Metric.tendsto_nhds.mp hξ_zero) ε hε
    filter_upwards [h] with τ hτ
    simpa [dist_eq_norm, Real.norm_eq_abs] using hτ
  have hη_tendsto : Filter.Tendsto η (𝓝 τ₀) (𝓝 X) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (Metric.tendsto_nhds.mp hη_zero) ε hε
    filter_upwards [h] with τ hτ
    simpa [dist_eq_norm, Real.norm_eq_abs] using hτ
  have hξval : ξ τ₀ = τ₀ := by simp [ξ]
  have hX₂val : X₂ τ₀ = X := rfl
  have hξ_cont : ContinuousAt ξ τ₀ := by
    change Filter.Tendsto ξ (𝓝 τ₀) (𝓝 (ξ τ₀))
    rw [hξval]
    exact hξ_tendsto
  have hX₂_cont' : ContinuousAt X₂ τ₀ := by
    change Filter.Tendsto X₂ (𝓝 τ₀) (𝓝 (X₂ τ₀))
    rw [hX₂val]
    exact hX2_cont.tendsto
  have hprod_tendsto : Filter.Tendsto (fun τ : ℝ => (ξ τ, X₂ τ)) (𝓝 τ₀) (𝓝 (τ₀, X)) := by
    have h := (ContinuousAt.prodMk hξ_cont hX₂_cont').tendsto
    simpa [hξval, hX₂val] using h
  have hτfun_cont : ContinuousAt hτfun (τ₀, X) := by
    dsimp [hτfun]
    have hden : (1 + 2 * K * τ₀ : ℝ) ≠ 0 := by
      have hpos : 0 < 1 + 2 * K * τ₀ := by
        have hKτ : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀.le
        nlinarith
      exact ne_of_gt hpos
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.2 * (2 * K) : ℝ)) (τ₀, X) := by fun_prop
    have hd : ContinuousAt (fun p : ℝ × ℝ => (1 + 2 * K * p.1 : ℝ)) (τ₀, X) := by fun_prop
    have hdinv : ContinuousAt (fun p : ℝ × ℝ => ((1 + 2 * K * p.1 : ℝ)⁻¹)) (τ₀, X) := hd.inv₀ hden
    have hmul : ContinuousAt (fun p : ℝ × ℝ => (p.2 * (2 * K) : ℝ) * (1 + 2 * K * p.1)⁻¹)
        (τ₀, X) := hc.mul hdinv
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hX_cont : ContinuousAt hX X := by
    have hXK : X / K ≠ 0 := div_ne_zero hXpos.ne' hK.ne'
    have hdiv : ContinuousAt (fun y : ℝ => y / K) X := (continuousAt_id.div₀ continuousAt_const hK.ne')
    have hlog : ContinuousAt (fun y : ℝ => Real.log (y / K)) X := hdiv.log hXK
    have hlogc : ContinuousAt (fun y : ℝ => Real.log (1 + 2 * K * τ₀)) X := by fun_prop
    have hsum : ContinuousAt (fun y : ℝ => Real.log (y / K) + Real.log (1 + 2 * K * τ₀)) X :=
      hlog.add hlogc
    have hsub : ContinuousAt (fun y : ℝ => Real.log (y / K) + Real.log (1 + 2 * K * τ₀) - 2) X :=
      hsum.sub continuousAt_const
    change ContinuousAt (fun y : ℝ => Real.log (y / K) + Real.log (1 + 2 * K * τ₀) - 2) X
    exact hsub
  have hτcomp : Filter.Tendsto (fun τ : ℝ => hτfun (ξ τ, X₂ τ)) (𝓝 τ₀) (𝓝 (hτfun (τ₀, X))) :=
    hτfun_cont.tendsto.comp hprod_tendsto
  have hXcomp : Filter.Tendsto (fun τ : ℝ => hX (η τ)) (𝓝 τ₀) (𝓝 (hX X)) :=
    hX_cont.tendsto.comp hη_tendsto
  have hs_tendsto : Filter.Tendsto (fun τ : ℝ => slope s τ₀ τ) (𝓝[≠] τ₀) (𝓝 s') :=
    (hasDerivAt_scalarSectionalLowerBarrier3 hK hτ₀.le).tendsto_slope
  have hnum : Filter.Tendsto (fun τ : ℝ => slope s τ₀ τ - hτfun (ξ τ, X₂ τ))
      (𝓝[≠] τ₀) (𝓝 (s' - hτfun (τ₀, X))) :=
    hs_tendsto.sub (hτcomp.mono_left nhdsWithin_le_nhds)
  have hden : Filter.Tendsto (fun τ : ℝ => hX (η τ)) (𝓝[≠] τ₀) (𝓝 (hX X)) :=
    hXcomp.mono_left nhdsWithin_le_nhds
  have hX_ne : hX X ≠ 0 := ne_of_gt hXpos0
  have hquot : Filter.Tendsto (fun τ : ℝ => (slope s τ₀ τ - hτfun (ξ τ, X₂ τ)) / hX (η τ))
      (𝓝[≠] τ₀) (𝓝 ((s' - hτfun (τ₀, X)) / hX X)) :=
    hnum.div hden hX_ne
  have hq_eq : (fun τ : ℝ => slope X₂ τ₀ τ) =ᶠ[𝓝[≠] τ₀]
      (fun τ : ℝ => (slope s τ₀ τ - hτfun (ξ τ, X₂ τ)) / hX (η τ)) := by
    rw [Filter.EventuallyEq]
    rw [eventually_nhdsWithin_iff]
    simpa using hidentity
  have hq : Filter.Tendsto (fun τ : ℝ => slope X₂ τ₀ τ) (𝓝[≠] τ₀)
      (𝓝 ((s' - hτfun (τ₀, X)) / hX X)) :=
    hquot.congr' hq_eq.symm
  have hmain : HasDerivAt X₂ ((s' - hτfun (τ₀, X)) / hX X) τ₀ :=
    (hasDerivAt_iff_tendsto_slope).mpr hq
  convert hmain using 1

private lemma hamiltonIveyBarrierStarPoint_fhValue
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) :
    hamiltonIveyBarrier K τ (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * ν 0 +
        (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) =
      -(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ))) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hbar := hamiltonIveyBarrier_at_star_point (K := K) (τ := τ) (ν := ν) hK hτ
  calc
    hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2)
        = (Xs * ((ν 1 + ν 2) / ν 0 - 3)) * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) := by rw [hbar]
    _ = -(ν 0 * Xs) := by
          field_simp [Ne.symm hν0.ne']
          ring

private lemma hamiltonIveyBarrierKink_fhValue
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} :
    hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) =
      scalarSectionalLowerBarrier3 K τ * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) := by
  have hk := kink_point_eq hK hτ
  rw [hk]

private lemma hamiltonIveyKinkStarValues_eq_of_crossing
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0)
    (hcross : hamiltonIveyKinkPoint hK τ =
      K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) :
    -(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ))) =
      scalarSectionalLowerBarrier3 K τ * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) := by
  have hfh2 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) =
      scalarSectionalLowerBarrier3 K τ * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) :=
    hamiltonIveyBarrierKink_fhValue hK hτ
  have hfh1 : hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK τ) * ν 0 +
        hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) =
      -(ν 0 * (hamiltonIveyKinkPoint hK τ)) := by
    have h1 := hamiltonIveyBarrierStarPoint_fhValue hK hτ hν0
    rwa [← hcross] at h1
  rw [← hcross]
  exact hfh1.symm.trans hfh2

private lemma support_formula_eq_kink_or_star
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal ν)) =
      if hamiltonIveyKinkPoint hK τ ≤
          K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ) then
        -(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)))
      else
        scalarSectionalLowerBarrier3 K τ * ν 0 +
          hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  let X₂ : ℝ := hamiltonIveyKinkPoint hK τ
  let G₁ : ℝ := -(ν 0 * Xs)
  let G₂ : ℝ := scalarSectionalLowerBarrier3 K τ * ν 0 + X₂ * (2 * ν 0 - ν 1 - ν 2)
  let F : ℝ → ℝ := fun X => hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let Fh : ℝ → ℝ := fun X => hamiltonIveyBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let Fs : ℝ → ℝ := fun X => scalarSectionalLowerBarrier3 K τ * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)
  let Fset : Set ℝ := {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧ x = F X}
  have hXspos : 0 < Xs := by
    dsimp [Xs]
    positivity
  have hX2pos : 0 ≤ X₂ := by
    have hgt : K * Real.exp 2 / (1 + 2 * K * τ) < X₂ := kink_point_above_E hK hτ
    have hEpos : 0 < K * Real.exp 2 / (1 + 2 * K * τ) := by positivity
    exact le_of_lt (lt_of_lt_of_le hEpos (le_of_lt hgt))
  have hc : 0 ≤ 2 * ν 0 - ν 1 - ν 2 := by
    have h1 : ν 1 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 1)
    have h2 : ν 2 ≤ ν 0 := hν (by decide : (0 : Fin 3) ≤ 2)
    nlinarith
  have hF_eq_min : ∀ X : ℝ, F X = min (Fs X) (Fh X) := by
    intro X
    have h := support_formula_min_branch (K := K) (τ := τ) hν0 X
    simpa [F, Fs, Fh] using h
  have hF_le_Fh : ∀ X : ℝ, F X ≤ Fh X := by
    intro X
    rw [hF_eq_min X]
    exact min_le_right _ _
  have hF_le_Fs : ∀ X : ℝ, F X ≤ Fs X := by
    intro X
    rw [hF_eq_min X]
    exact min_le_left _ _
  have hFh_Xs : Fh Xs = G₁ := by
    dsimp [Fh, G₁, Xs]
    exact hamiltonIveyBarrierStarPoint_fhValue hK hτ hν0
  have hFh_X2 : Fh X₂ = G₂ := by
    dsimp [Fh, G₂, X₂]
    exact hamiltonIveyBarrierKink_fhValue hK hτ
  have hFs_X2 : Fs X₂ = G₂ := by
    dsimp [Fs, G₂]
  have hFs_mono : MonotoneOn Fs (Set.univ : Set ℝ) := by
    intro x hx y hy hxy
    dsimp [Fs]
    have hmul : x * (2 * ν 0 - ν 1 - ν 2) ≤ y * (2 * ν 0 - ν 1 - ν 2) :=
      mul_le_mul_of_nonneg_right hxy hc
    linarith
  have hFh_left : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → y ≤ Xs → Fh x ≤ Fh y := by
    intro x y hx hxy hy
    have hmono := monotoneOn_Fh_left (K := K) (τ := τ) hK hτ hν hν0
    exact hmono ⟨hx, le_trans hxy hy⟩ ⟨le_trans hx hxy, hy⟩ hxy
  have hFh_right : ∀ {x y : ℝ}, Xs ≤ x → x ≤ y → Fh y ≤ Fh x := by
    intro x y hx hxy
    have hmono := antitoneOn_Fh_right (K := K) (τ := τ) hK hτ hν hν0
    exact hmono hx (le_trans hx hxy) hxy
  have hdef_eq : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (Matrix.diagonal ν)) = sSup Fset := by
    have hsymm : euclideanMatrixSymmetrization (matrixToEuclidean (Matrix.diagonal ν)) = Matrix.diagonal ν := by
      ext i j
      dsimp [euclideanMatrixSymmetrization, euclideanToMatrix]
      by_cases h : i = j
      · simp [h, matrixToEuclidean, Matrix.diagonal]
        ring
      · simp [h, matrixToEuclidean, Matrix.diagonal, Ne.symm h]
    have hν' : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ = ν := by
      have hchar : (euclideanMatrixSymmetrization (matrixToEuclidean (Matrix.diagonal ν))).charpoly =
          (Matrix.diagonal ν).charpoly := by
        rw [hsymm]
      have heig' : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ =
          (Matrix.isHermitian_diagonal ν).eigenvalues₀ :=
        eigenvalues₀_eq_of_charpoly_eq_real
          (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν)))
          (Matrix.isHermitian_diagonal ν) hchar
      have heig : (Matrix.isHermitian_diagonal ν).eigenvalues₀ = ν :=
        diagonal_eigenvalues₀_eq_of_antitone ν hν
      exact heig'.trans heig
    unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
    rw [hν']
    dsimp [F]
    exact (if_pos hν0).trans rfl
  have hbddF : BddAbove Fset := by
    dsimp [Fset, F]
    exact support_formula_bddAbove hK hτ hν0
  have hFne : Fset.Nonempty := by
    refine ⟨F 0, ?_⟩
    exact ⟨0, le_rfl, rfl⟩
  have hF_le_choice : ∀ X : ℝ, 0 ≤ X → F X ≤ (if X₂ ≤ Xs then G₁ else G₂) := by
    intro X hX
    by_cases h2s : X₂ ≤ Xs
    · rw [if_pos h2s]
      by_cases hXle : X ≤ Xs
      · have hmain : Fh X ≤ Fh Xs := hFh_left (x := X) (y := Xs) hX hXle le_rfl
        exact le_trans (hF_le_Fh X) (le_trans hmain hFh_Xs.le)
      · have hXsle : Xs ≤ X := le_of_not_ge hXle
        have hmain : Fh X ≤ Fh Xs := hFh_right (x := Xs) (y := X) le_rfl hXsle
        exact le_trans (hF_le_Fh X) (le_trans hmain hFh_Xs.le)
    · rw [if_neg h2s]
      by_cases hXle : X ≤ X₂
      · have hmain : Fs X ≤ Fs X₂ := hFs_mono trivial trivial hXle
        exact le_trans (hF_le_Fs X) (le_trans hmain hFs_X2.le)
      · have hX2le : X₂ ≤ X := le_of_not_ge hXle
        have hX2gtXs : Xs < X₂ := lt_of_not_ge h2s
        have hmain : Fh X ≤ Fh X₂ := hFh_right (x := X₂) (y := X) (le_of_lt hX2gtXs) hX2le
        exact le_trans (hF_le_Fh X) (le_trans hmain hFh_X2.le)
  have hsup_le : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (Matrix.diagonal ν)) ≤ (if X₂ ≤ Xs then G₁ else G₂) := by
    rw [hdef_eq]
    refine csSup_le hFne ?_
    rintro x ⟨X, hX, rfl⟩
    exact hF_le_choice X hX
  have hsup_ge : (if X₂ ≤ Xs then G₁ else G₂) ≤ hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (Matrix.diagonal ν)) := by
    by_cases h2s : X₂ ≤ Xs
    · have hX2gtE : K * Real.exp 2 / (1 + 2 * K * τ) < X₂ := kink_point_above_E hK hτ
      have hXsgtE : K * Real.exp 2 / (1 + 2 * K * τ) < Xs := by
        linarith
      have hs_le_hXs : scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyBarrier K τ Xs := by
        have hmono := (strictMonoOn_hamiltonIveyBarrier_above_E hK hτ).monotoneOn
        have hle := hmono hX2gtE hXsgtE h2s
        have hX2eq : hamiltonIveyBarrier K τ X₂ = scalarSectionalLowerBarrier3 K τ := kink_point_eq hK hτ
        dsimp [X₂] at hX2eq
        linarith
      have hG1_le_FsXs : G₁ ≤ Fs Xs := by
        have hmain : Fh Xs ≤ Fs Xs := by
          dsimp [Fs, Fh]
          have hmul : hamiltonIveyBarrier K τ Xs * ν 0 ≤ scalarSectionalLowerBarrier3 K τ * ν 0 := by
            simpa [mul_comm] using (mul_le_mul_of_nonpos_left hs_le_hXs hν0.le)
          linarith
        simpa [hFh_Xs] using hmain
      have hF_Xs : F Xs = G₁ := by
        rw [hF_eq_min Xs]
        have hle : Fh Xs ≤ Fs Xs := by
          simpa [hFh_Xs] using hG1_le_FsXs
        rw [min_eq_right hle]
        exact hFh_Xs
      have hmem : G₁ ∈ Fset := by
        refine ⟨Xs, le_of_lt hXspos, ?_⟩
        exact hF_Xs.symm
      rw [if_pos h2s]
      rw [hdef_eq]
      exact le_csSup hbddF hmem
    · have hF_X2 : F X₂ = G₂ := by
        rw [hF_eq_min X₂]
        rw [hFs_X2, hFh_X2]
        exact min_self G₂
      have hmem : G₂ ∈ Fset := by
        refine ⟨X₂, hX2pos, ?_⟩
        exact hF_X2.symm
      rw [if_neg h2s]
      rw [hdef_eq]
      exact le_csSup hbddF hmem
  exact le_antisymm hsup_le hsup_ge

private lemma hasDerivAt_of_eventually_or
    {f g₁ g₂ : ℝ → ℝ} {a x : ℝ}
    (h₁ : HasDerivAt g₁ a x) (h₂ : HasDerivAt g₂ a x)
    (hx : g₁ x = g₂ x) (hf : f x = g₁ x)
    (hchoice : ∀ᶠ y in 𝓝[≠] x, f y = g₁ y ∨ f y = g₂ y) :
    HasDerivAt f a x := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have e₁ : ∀ᶠ y in 𝓝[≠] x, dist (slope g₁ x y) a < ε :=
    (Metric.tendsto_nhds.mp h₁.tendsto_slope) ε hε
  have e₂ : ∀ᶠ y in 𝓝[≠] x, dist (slope g₂ x y) a < ε :=
    (Metric.tendsto_nhds.mp h₂.tendsto_slope) ε hε
  filter_upwards [e₁, e₂, hchoice] with y h₁' h₂' hc
  rcases hc with hfy | hfy
  · have hslope : slope f x y = slope g₁ x y := by
      rw [slope_def_field, slope_def_field]
      rw [hfy, hf]
    simpa [hslope] using h₁'
  · have hslope : slope f x y = slope g₂ x y := by
      rw [slope_def_field, slope_def_field]
      rw [hfy, hf, hx]
    simpa [hslope] using h₂'

private lemma hamiltonIveyKinkStarDerivatives_eq_of_crossing
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0)
    (hcross : hamiltonIveyKinkPoint hK τ₀ =
      K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀)) :
    (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
      ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
        hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
        (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
          (2 * ν 0 - ν 1 - ν 2)) =
      -(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2))) := by
  let X : ℝ := hamiltonIveyKinkPoint hK τ₀
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀)
  let c : ℝ := 2 * ν 0 - ν 1 - ν 2
  let a : ℝ := (ν 1 + ν 2) / ν 0
  let S : ℝ := 12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2
  have hden : (1 + 2 * K * τ₀ : ℝ) ≠ 0 := by
    have hpos : 0 < 1 + 2 * K * τ₀ := by
      have hKτ : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀.le
      nlinarith
    exact ne_of_gt hpos
  have hXpos : 0 < X := by
    have hE : K * Real.exp 2 / (1 + 2 * K * τ₀) < X := by simpa [X] using kink_point_above_E hK hτ₀.le
    have hEpos : 0 < K * Real.exp 2 / (1 + 2 * K * τ₀) := by positivity
    exact lt_of_lt_of_le hEpos (le_of_lt hE)
  have hXs' : X / K = Real.exp a / (1 + 2 * K * τ₀) := by
    change hamiltonIveyKinkPoint hK τ₀ / K = Real.exp a / (1 + 2 * K * τ₀)
    rw [hcross]
    field_simp [hden, hK.ne']
    simp [a]
  have hdenpos : 0 < 1 + 2 * K * τ₀ := by
    have hKτ : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀.le
    nlinarith
  have hlogXs : Real.log (Real.exp a / (1 + 2 * K * τ₀)) = a - Real.log (1 + 2 * K * τ₀) := by
    rw [Real.log_div (Real.exp_pos a).ne' hdenpos.ne']
    rw [Real.log_exp a]
  have hXlog : Real.log (X / K) + Real.log (1 + 2 * K * τ₀) = a := by
    rw [hXs', hlogXs]
    ring
  have hXh : Real.log (X / K) + Real.log (1 + 2 * K * τ₀) - 2 = a - 2 := by linarith
  have hνa : ν 0 * a = ν 1 + ν 2 := by
    dsimp [a]
    field_simp [Ne.symm hν0.ne']
  have hFhX : ν 0 * (a - 2) + c = 0 := by
    dsimp [c]
    linarith [hνa]
  have hc' : c = -(ν 0 * (a - 2)) := by
    linarith [hFhX]
  have hXeq : K * Real.exp ((ν 1 + ν 2) / ν 0) = X * (1 + 2 * K * τ₀) := by
    change K * Real.exp ((ν 1 + ν 2) / ν 0) = hamiltonIveyKinkPoint hK τ₀ * (1 + 2 * K * τ₀)
    rw [hcross]
    field_simp [hden, hK.ne']
  have ha_ne : a - 2 ≠ 0 := by
    intro h2
    have hν2 : (ν 1 + ν 2) / ν 0 = 2 := by linarith
    have hE : Xs = K * Real.exp 2 / (1 + 2 * K * τ₀) := by
      dsimp [Xs, a]
      rw [hν2]
    have hElt : hamiltonIveyBarrier K τ₀ (K * Real.exp 2 / (1 + 2 * K * τ₀)) <
        scalarSectionalLowerBarrier3 K τ₀ := hamiltonIveyBarrier_lt_scalarLower_at_E hK hτ₀.le
    have hXseq : hamiltonIveyBarrier K τ₀ Xs = scalarSectionalLowerBarrier3 K τ₀ := by
      simpa [X, hcross] using kink_point_eq hK hτ₀.le
    rw [hE] at hXseq
    exact (ne_of_lt hElt) hXseq
  have hmain : S * ν 0 + ((S - X * (2 * K) / (1 + 2 * K * τ₀)) / (a - 2)) * c =
      2 * K ^ 2 * ν 0 * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2 := by
    rw [hc']
    have hcalc : S * ν 0 + (S - X * (2 * K) / (1 + 2 * K * τ₀)) / (a - 2) *
        (-(ν 0 * (a - 2))) = ν 0 * (X * (2 * K) / (1 + 2 * K * τ₀)) := by
      field_simp [ha_ne]
      ring
    rw [hcalc]
    have h' : Real.exp ((ν 1 + ν 2) / ν 0) = X * (1 + 2 * K * τ₀) / K := by
      rw [← hXeq]
      field_simp [hK.ne']
    rw [h']
    field_simp [hden]
  have hfinal : (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
      ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 - X * (2 * K) / (1 + 2 * K * τ₀)) /
        (Real.log (X / K) + Real.log (1 + 2 * K * τ₀) - 2)) * c) =
      -(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2))) := by
    rw [hXh]
    calc
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
          ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 - X * (2 * K) / (1 + 2 * K * τ₀)) / (a - 2)) * c)
          = 2 * K ^ 2 * ν 0 * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2 := hmain
      _ = -(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2))) := by
            field_simp [hden]
  simpa [X, c] using hfinal

private lemma hasDerivAt_hamiltonIveyKinkBranchSupportFunction
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀)
    {ν : Fin 3 → ℝ} :
    HasDerivAt (fun τ : ℝ =>
        scalarSectionalLowerBarrier3 K τ * ν 0 +
          hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2))
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
        ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
          hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
          (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
            (2 * ν 0 - ν 1 - ν 2)) τ₀ := by
  have h1 := hasDerivAt_scalarSectionalLowerBarrier3 (K := K) (τ₀ := τ₀) hK hτ₀.le
  have h2 := hasDerivAt_hamiltonIveyKinkPoint (K := K) (τ₀ := τ₀) hK hτ₀
  have h1' : HasDerivAt (fun τ : ℝ => scalarSectionalLowerBarrier3 K τ * ν 0)
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0) τ₀ := h1.mul_const (ν 0)
  have h2' : HasDerivAt (fun τ : ℝ => hamiltonIveyKinkPoint hK τ * (2 * ν 0 - ν 1 - ν 2))
      (((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
        hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
        (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
          (2 * ν 0 - ν 1 - ν 2)) τ₀ := h2.mul_const (2 * ν 0 - ν 1 - ν 2)
  simpa [mul_assoc] using h1'.add h2'

private lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_diag_hasDerivAt
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    HasDerivAt (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
        (matrixToEuclidean (Matrix.diagonal ν)))
      (if hamiltonIveyKinkPoint hK τ₀ ≤
          K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) then
        -(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))
      else
        12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
          ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
            hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
            (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
              (2 * ν 0 - ν 1 - ν 2)) τ₀ := by
  let X₂ : ℝ → ℝ := fun τ => hamiltonIveyKinkPoint hK τ
  let Xs : ℝ → ℝ := fun τ => K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  let G₁ : ℝ → ℝ := fun τ => -(ν 0 * Xs τ)
  let G₂ : ℝ → ℝ := fun τ =>
    scalarSectionalLowerBarrier3 K τ * ν 0 + X₂ τ * (2 * ν 0 - ν 1 - ν 2)
  let supp : ℝ → ℝ := fun τ =>
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal ν))
  have hτ0_nhd : ∀ᶠ τ in 𝓝 τ₀, 0 ≤ τ := Ici_mem_nhds hτ₀
  have hsupp_eq : ∀ᶠ τ in 𝓝 τ₀, supp τ = (if X₂ τ ≤ Xs τ then G₁ τ else G₂ τ) := by
    filter_upwards [hτ0_nhd] with τ hτ
    exact support_formula_eq_kink_or_star (K := K) (τ := τ) hK hτ hν hν0
  have hX₂cont : ContinuousAt X₂ τ₀ := by
    simpa [X₂] using continuousAt_kink_point hK hτ₀
  have hXscont : ContinuousAt Xs τ₀ := by
    dsimp [Xs]
    have hden : (1 + 2 * K * τ₀ : ℝ) ≠ 0 := by
      have hpos : 0 < 1 + 2 * K * τ₀ := by
        have hKτ : 0 ≤ K * τ₀ := mul_nonneg hK.le hτ₀.le
        nlinarith
      exact ne_of_gt hpos
    have hnum : ContinuousAt (fun τ : ℝ => (K * Real.exp ((ν 1 + ν 2) / ν 0) : ℝ)) τ₀ := by fun_prop
    have hlin : ContinuousAt (fun τ : ℝ => (1 + 2 * K * τ : ℝ)) τ₀ := by fun_prop
    exact hnum.div hlin hden
  have hG₁deriv : HasDerivAt G₁
      (-(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))) τ₀ := by
    have h := hasDerivAt_candidate_B (K := K) (τ₀ := τ₀) hK hτ₀.le (ν := ν)
    simpa [G₁, Xs] using h
  have hG₂deriv : HasDerivAt G₂
      (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
        ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
          hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
          (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
            (2 * ν 0 - ν 1 - ν 2)) τ₀ := by
    have h := hasDerivAt_hamiltonIveyKinkBranchSupportFunction (K := K) (τ₀ := τ₀) hK hτ₀ (ν := ν)
    simpa [G₂, X₂] using h
  by_cases hle : X₂ τ₀ ≤ Xs τ₀
  · by_cases hlt : X₂ τ₀ < Xs τ₀
    · have hneg : X₂ τ₀ - Xs τ₀ < 0 := sub_neg.mpr hlt
      have hgap : 0 < -(X₂ τ₀ - Xs τ₀) := by linarith
      have hcont : ContinuousAt (fun τ : ℝ => X₂ τ - Xs τ) τ₀ := hX₂cont.sub hXscont
      have hev : ∀ᶠ τ in 𝓝 τ₀, dist (X₂ τ - Xs τ) (X₂ τ₀ - Xs τ₀) < -(X₂ τ₀ - Xs τ₀) :=
        (Metric.tendsto_nhds.mp hcont.tendsto) (-(X₂ τ₀ - Xs τ₀)) hgap
      have hnhd : ∀ᶠ τ in 𝓝 τ₀, supp τ = G₁ τ := by
        filter_upwards [hev, hsupp_eq] with τ hd hform
        have h1 : X₂ τ - Xs τ - (X₂ τ₀ - Xs τ₀) < -(X₂ τ₀ - Xs τ₀) :=
          (abs_lt.mp (by simpa [dist_eq_norm, Real.norm_eq_abs] using hd)).2
        have hltτ : X₂ τ < Xs τ := by linarith
        rw [hform, if_pos (le_of_lt hltτ)]
      have hmain : HasDerivAt supp
          (-(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))) τ₀ :=
        hG₁deriv.congr_of_eventuallyEq hnhd
      simpa [X₂, Xs, hle] using hmain
    · have hcross : X₂ τ₀ = Xs τ₀ := le_antisymm hle (le_of_not_gt hlt)
      have hval : G₁ τ₀ = G₂ τ₀ := by
        have h := hamiltonIveyKinkStarValues_eq_of_crossing hK hτ₀.le hν0
          (by simpa [X₂, Xs] using hcross)
        simpa [G₁, G₂] using h
      have hderiv_eq : (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
            ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
              hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
              (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
                (2 * ν 0 - ν 1 - ν 2)) =
          -(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2))) :=
        hamiltonIveyKinkStarDerivatives_eq_of_crossing hK hτ₀ hν0
          (by simpa [X₂, Xs] using hcross)
      have hchoice : ∀ᶠ τ in 𝓝[≠] τ₀, supp τ = G₁ τ ∨ supp τ = G₂ τ := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [hsupp_eq] with τ hform
        intro hτne
        by_cases h : X₂ τ ≤ Xs τ
        · left
          rw [hform, if_pos h]
        · right
          rw [hform, if_neg h]
      have hsupp₀ : supp τ₀ = G₁ τ₀ := by
        change hamiltonIveyConvexMatrixRegionSupportEuclidean K τ₀ (matrixToEuclidean (Matrix.diagonal ν)) = G₁ τ₀
        rw [support_formula_eq_kink_or_star hK hτ₀.le hν hν0]
        have hle' : hamiltonIveyKinkPoint hK τ₀ ≤ K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) := by
          simpa [X₂, Xs] using hle
        rw [if_pos hle']
      have hG₂deriv' : HasDerivAt G₂
          (-(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))) τ₀ :=
        hG₂deriv.congr_deriv hderiv_eq
      have hmain : HasDerivAt supp
          (-(ν 0 * (-2 * K * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ₀) ^ 2)))) τ₀ :=
        hasDerivAt_of_eventually_or hG₁deriv hG₂deriv' hval hsupp₀ hchoice
      simpa [X₂, Xs, hle] using hmain
  · have hgt : Xs τ₀ < X₂ τ₀ := lt_of_not_ge hle
    have hpos : 0 < X₂ τ₀ - Xs τ₀ := sub_pos.mpr hgt
    have hcont : ContinuousAt (fun τ : ℝ => X₂ τ - Xs τ) τ₀ := hX₂cont.sub hXscont
    have hev : ∀ᶠ τ in 𝓝 τ₀, dist (X₂ τ - Xs τ) (X₂ τ₀ - Xs τ₀) < X₂ τ₀ - Xs τ₀ :=
      (Metric.tendsto_nhds.mp hcont.tendsto) (X₂ τ₀ - Xs τ₀) hpos
    have hnhd : ∀ᶠ τ in 𝓝 τ₀, supp τ = G₂ τ := by
      filter_upwards [hev, hsupp_eq] with τ hd hform
      have h1 : -(X₂ τ₀ - Xs τ₀) < X₂ τ - Xs τ - (X₂ τ₀ - Xs τ₀) :=
        (abs_lt.mp (by simpa [dist_eq_norm, Real.norm_eq_abs] using hd)).1
      have hgtτ : Xs τ < X₂ τ := by linarith
      rw [hform, if_neg (not_le_of_gt hgtτ)]
    have hmain : HasDerivAt supp
        (12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * ν 0 +
          ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
            hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
            (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
              (2 * ν 0 - ν 1 - ν 2)) τ₀ :=
      hG₂deriv.congr_of_eventuallyEq hnhd
    simpa [X₂, Xs, hle] using hmain

lemma zero_mem_hamiltonIveyConvexMatrixRegionEuclidean
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
  rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
  let hM : (0 : Matrix (Fin 3) (Fin 3) ℝ).IsHermitian := by simp
  refine ⟨hM, ?_⟩
  · have hscalar : scalarSectionalLowerBarrier3 K τ ≤ 0 := by
      have hden : 0 < 1 + 4 * K * τ := by
        nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : Real) < 4) hK).le hτ]
      unfold scalarSectionalLowerBarrier3
      have hnonpos : -(3 * K) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : Real) ≤ 3) (le_of_lt hK))
      have hdiv := div_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hden)
      simpa using hdiv
    unfold hamiltonIveyConvexBarrier
    have hzero : euclideanToMatrix (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) = 0 := by
      ext i j
      simp [euclideanToMatrix]
    have hbar : hamiltonIveyBarrier K τ
        (max (-minimumRayleighQuotient3
          (euclideanToMatrix (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)))) 0) ≤ 0 := by
      rw [hzero, minimumRayleighQuotient3_zero]
      simp [hamiltonIveyBarrier]
    have ht : (euclideanToMatrix (0 : EuclideanSpace ℝ (Fin 3 × Fin 3))).trace = 0 := by
      simp [euclideanToMatrix, Matrix.trace]
    rw [ht]
    exact max_le (by simpa using hscalar) hbar

private lemma inner_zero_of_symm_zero_mem_region
    {K τ : ℝ} (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : euclideanMatrixSymmetrization v = 0)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    inner ℝ v A = 0 := by
  have hAh : (euclideanToMatrix A).IsHermitian := by
    have hAm : euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ A).1 hA
    rw [hamiltonIveyConvexMatrixRegion] at hAm
    exact hAm.1
  have h := inner_matrixToEuclidean_symm v (euclideanToMatrix A) hAh
  rw [hv] at h
  have hzero : inner ℝ (matrixToEuclidean (0 : Matrix (Fin 3) (Fin 3) ℝ))
      (matrixToEuclidean (euclideanToMatrix A)) = 0 := by
    rw [inner_matrixToEuclidean]
    simp [matrixToEuclidean]
  have hmain : inner ℝ v (matrixToEuclidean (euclideanToMatrix A)) = 0 := h.trans hzero
  rw [← matrixToEuclidean_euclideanToMatrix A]
  exact hmain

lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_zero_of_symm_zero
    {K τ : ℝ} (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : euclideanMatrixSymmetrization v = 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v = 0 := by
  unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
  have hν : ¬ (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 := by
    intro hlt
    have hzero : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 = 0 := by
      have hz : euclideanMatrixSymmetrization v = 0 := hv
      have heig : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues = 0 := by
        exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA := euclideanMatrixSymmetrization_isHermitian v)).mpr hv
      let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
      have h0 : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues (e 0) = 0 := congrFun heig (e 0)
      have hdef : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues (e 0) =
          (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ (e.symm (e 0)) := rfl
      rw [hdef, Equiv.symm_apply_apply] at h0
      exact h0
    linarith
  rw [if_neg hν]

private lemma supportFunction_eq_zero_of_symm_zero
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : euclideanMatrixSymmetrization v = 0) :
    supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) v = 0 := by
  unfold supportFunction
  have hset : {x : ℝ | ∃ q : EuclideanSpace ℝ (Fin 3 × Fin 3),
      q ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = inner ℝ v q} = {0} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨q, hq, rfl⟩
      have hz := inner_zero_of_symm_zero_mem_region v hv q hq
      simp [hz]
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      rw [hx0]
      exact ⟨0, zero_mem_hamiltonIveyConvexMatrixRegionEuclidean hK hτ, by simp⟩
  rw [hset]
  exact csSup_singleton 0

lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ)) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) v := by
  have hiff := (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ v).mp hv
  rcases hiff with hvneg | hsymm
  · exact hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction hK hτ v hvneg
  · have hz := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_zero_of_symm_zero (K := K) (τ := τ) v hsymm
    have hsup := supportFunction_eq_zero_of_symm_zero hK hτ v hsymm
    rw [hz, hsup]

private lemma finiteSupportDirections_hamiltonIvey_region_independent
    {K τ₁ τ₂ : ℝ} (hK : 0 < K) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂) :
    finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ₁) =
      finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ₂) := by
  ext v
  rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ₁,
      mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ₂]

theorem hamiltonIveyConvexMatrixRegionEuclidean_mem_iff_forall_support_le
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (p : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    p ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ↔
      ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3),
        ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) →
          inner ℝ ν p ≤ hamiltonIveyConvexMatrixRegionSupportEuclidean K τ ν := by
  constructor
  · intro hp ν hν
    have hEq := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
      hK hτ ν hν
    rw [hEq]
    exact supportFunction_le_of_mem hν hp
  · intro hle
    have hle' : ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3),
        ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) →
          inner ℝ ν p ≤ supportFunction (hamiltonIveyConvexMatrixRegionEuclidean K τ) ν := by
      intro ν hν
      have hEq := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
        hK hτ ν hν
      rw [← hEq]
      exact hle ν hν
    exact (mem_iff_support_le
      (isClosed_hamiltonIveyConvexMatrixRegionEuclidean hK)
      (nonempty_hamiltonIveyConvexMatrixRegionEuclidean hK hτ)
      (convex_hamiltonIveyConvexMatrixRegionEuclidean hK hτ)).mpr hle'

noncomputable def hamiltonIveyConvexMatrixRegionSupportDeriv (K : ℝ) (hK : 0 < K) (τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) : ℝ :=
  let ν₁ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0
  let ν₂ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 1
  let ν₃ : ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 2
  if ν₁ < 0 then
    if hamiltonIveyKinkPoint hK τ ≤ K * Real.exp ((ν₂ + ν₃) / ν₁) / (1 + 2 * K * τ) then
      -(ν₁ * (-2 * K * (K * Real.exp ((ν₂ + ν₃) / ν₁) / (1 + 2 * K * τ) ^ 2)))
    else
      12 * K ^ 2 / (1 + 4 * K * τ) ^ 2 * ν₁ +
        ((12 * K ^ 2 / (1 + 4 * K * τ) ^ 2 -
          hamiltonIveyKinkPoint hK τ * (2 * K) / (1 + 2 * K * τ)) /
          (Real.log (hamiltonIveyKinkPoint hK τ / K) + Real.log (1 + 2 * K * τ) - 2)) *
            (2 * ν₁ - ν₂ - ν₃)
  else 0

lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_hasDerivAt
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 < τ₀)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    HasDerivAt (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v)
      (hamiltonIveyConvexMatrixRegionSupportDeriv K hK τ₀ v) τ₀ := by
  let nv : Fin 3 → ℝ := (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀_antitone
  by_cases hv : nv 0 < 0
  · have hdiag := hamiltonIveyConvexMatrixRegionSupportEuclidean_diag_hasDerivAt
      (K := K) (τ₀ := τ₀) hK hτ₀ hnv_anti hv
    have hrot : ∀ τ : ℝ, hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
        hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (Matrix.diagonal nv)) := by
      intro τ
      exact hamiltonIveyConvexMatrixRegionSupportEuclidean_rotate_diag (K := K) (τ := τ) v
    have hmain : HasDerivAt (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v)
        (if hamiltonIveyKinkPoint hK τ₀ ≤ K * Real.exp ((nv 1 + nv 2) / nv 0) / (1 + 2 * K * τ₀) then
          -(nv 0 * (-2 * K * (K * Real.exp ((nv 1 + nv 2) / nv 0) / (1 + 2 * K * τ₀) ^ 2)))
        else
          12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 * nv 0 +
            ((12 * K ^ 2 / (1 + 4 * K * τ₀) ^ 2 -
              hamiltonIveyKinkPoint hK τ₀ * (2 * K) / (1 + 2 * K * τ₀)) /
              (Real.log (hamiltonIveyKinkPoint hK τ₀ / K) + Real.log (1 + 2 * K * τ₀) - 2)) *
                (2 * nv 0 - nv 1 - nv 2)) τ₀ :=
      hdiag.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun τ => hrot τ))
    have hv' : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 := by simpa [nv] using hv
    exact hmain.congr_deriv (by
      simp [hamiltonIveyConvexMatrixRegionSupportDeriv, nv, hv']
      rfl)
  · have hnot : ¬ (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 := by
      dsimp [nv] at hv
      exact hv
    have hconst : ∀ τ : ℝ, hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v = 0 := by
      intro τ
      unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
      rw [if_neg hnot]
    have hzero : HasDerivAt (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v) 0 τ₀ := by
      simpa [hconst] using (hasDerivAt_const (x := τ₀) (c := (0 : ℝ)))
    have hv' : ¬ (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0 := by simpa [nv] using hv
    exact hzero.congr_deriv (by
      simp [hamiltonIveyConvexMatrixRegionSupportDeriv, hv'])

lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_reaction_le_deriv
    {K τ₀ : ℝ} (hK : 0 < K) (hτ₀ : 0 ≤ τ₀)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (euclideanMatrixSymmetrization_isHermitian v).eigenvalues₀ 0 < 0)
    (p : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hp : p ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ₀)
    (htangent : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ₀ v = inner ℝ v p)
    (support' : ℝ)
    (hderiv : HasDerivAt (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v) support' τ₀) :
    inner ℝ (hamiltonIveyMatrixReactionEuclidean p) v ≤ support' := by
  rcases hamiltonIveyConvexMatrixRegionEuclidean_reaction_small_time hK hτ₀ p hp with ⟨ε, hε, hstep⟩
  have hmain : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      inner ℝ (hamiltonIveyMatrixReactionEuclidean p) v ≤
        (hamiltonIveyConvexMatrixRegionSupportEuclidean K (τ₀ + s) v -
          hamiltonIveyConvexMatrixRegionSupportEuclidean K τ₀ v) / s := by
    have hspos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := by
      rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall (fun s hs => hs)
    have hslt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ε :=
      (show ∀ᶠ s in 𝓝 (0 : ℝ), s < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds
    filter_upwards [hspos, hslt] with s hs hsε
    have hstep' : p + s • hamiltonIveyMatrixReactionEuclidean p ∈
        hamiltonIveyConvexMatrixRegionEuclidean K (τ₀ + s) := hstep s ⟨hs.le, hsε.le⟩
    have hle := inner_le_supportFunction_of_mem_region hK (by linarith) v hv
      (p + s • hamiltonIveyMatrixReactionEuclidean p) hstep'
    have hinner : inner ℝ v (p + s • hamiltonIveyMatrixReactionEuclidean p) =
        inner ℝ v p + s * inner ℝ v (hamiltonIveyMatrixReactionEuclidean p) := by
      rw [inner_add_right, inner_smul_right]
    have hle' : inner ℝ v p + s * inner ℝ v (hamiltonIveyMatrixReactionEuclidean p) ≤
        hamiltonIveyConvexMatrixRegionSupportEuclidean K (τ₀ + s) v := by
      rwa [hinner] at hle
    rw [← htangent] at hle'
    rw [le_div_iff₀ hs]
    have hc : inner ℝ (hamiltonIveyMatrixReactionEuclidean p) v * s ≤
        hamiltonIveyConvexMatrixRegionSupportEuclidean K (τ₀ + s) v -
          hamiltonIveyConvexMatrixRegionSupportEuclidean K τ₀ v := by
      have hc2 : inner ℝ (hamiltonIveyMatrixReactionEuclidean p) v =
          inner ℝ v (hamiltonIveyMatrixReactionEuclidean p) := real_inner_comm _ _
      rw [hc2, mul_comm]
      nlinarith [hle']
    exact hc
  have hshift : Filter.Tendsto (fun s : ℝ => τ₀ + s) (𝓝[>] (0 : ℝ)) (𝓝[≠] τ₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h : Filter.Tendsto (fun s : ℝ => τ₀ + s) (𝓝 (0 : ℝ)) (𝓝 (τ₀ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall (fun s hs => by
        have hs0 : s ≠ 0 := ne_of_gt hs
        intro h
        have h' : s + τ₀ = 0 + τ₀ := by simpa [add_comm] using h
        exact hs0 (add_right_cancel h'))
  have hquot : Filter.Tendsto (fun s : ℝ =>
      (hamiltonIveyConvexMatrixRegionSupportEuclidean K (τ₀ + s) v -
        hamiltonIveyConvexMatrixRegionSupportEuclidean K τ₀ v) / s) (𝓝[>] (0 : ℝ)) (𝓝 support') := by
    have h := hderiv.tendsto_slope.comp hshift
    convert h using 1
    funext s
    simp only [Function.comp_def]
    rw [slope_def_field]
    ring
  exact ge_of_tendsto hquot hmain

lemma hamiltonIveyMatrixReaction_isHermitian
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    (hamiltonIveyMatrixReaction A).IsHermitian := by
  unfold hamiltonIveyMatrixReaction
  have hsq : (A * A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    rw [hA]
  have hsum : (A * A + A.adjugate).IsHermitian := hsq.add hA.adjugate
  have hsum' : ((A * A + A.adjugate) + (A * A + A.adjugate)).IsHermitian := hsum.add hsum
  have h2x : 2 • (A * A + A.adjugate) = (A * A + A.adjugate) + (A * A + A.adjugate) := by
    rw [two_nsmul]
  rw [h2x]
  exact hsum'

lemma hamiltonIveyMatrixReactionEuclidean_isHermitian
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : (euclideanToMatrix A).IsHermitian) :
    (euclideanToMatrix (hamiltonIveyMatrixReactionEuclidean A)).IsHermitian := by
  dsimp [hamiltonIveyMatrixReactionEuclidean]
  rw [euclideanToMatrix_matrixToEuclidean]
  exact hamiltonIveyMatrixReaction_isHermitian hA

private lemma inner_reactionState_zero_of_symm_zero
    (ν A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hν : euclideanMatrixSymmetrization ν = 0)
    (hA : (euclideanToMatrix A).IsHermitian) :
    inner ℝ (hamiltonIveyMatrixReactionEuclidean A) ν = 0 := by
  have hAh := hamiltonIveyMatrixReactionEuclidean_isHermitian A hA
  have h := inner_matrixToEuclidean_symm ν (euclideanToMatrix (hamiltonIveyMatrixReactionEuclidean A)) hAh
  rw [hν] at h
  have hzero : inner ℝ (matrixToEuclidean (0 : Matrix (Fin 3) (Fin 3) ℝ))
      (matrixToEuclidean (euclideanToMatrix (hamiltonIveyMatrixReactionEuclidean A))) = 0 := by
    rw [inner_matrixToEuclidean]
    simp [matrixToEuclidean]
  have hmain : inner ℝ ν (matrixToEuclidean (euclideanToMatrix (hamiltonIveyMatrixReactionEuclidean A))) = 0 :=
    h.trans hzero
  rw [real_inner_comm]
  rw [← matrixToEuclidean_euclideanToMatrix (hamiltonIveyMatrixReactionEuclidean A)]
  exact hmain

lemma hamiltonIveyConvexMatrixRegionSupportDeriv_eq_zero_of_symm_zero
    {K : ℝ} (hK : 0 < K) (τ : ℝ) (ν : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hν : euclideanMatrixSymmetrization ν = 0) :
    hamiltonIveyConvexMatrixRegionSupportDeriv K hK τ ν = 0 := by
  unfold hamiltonIveyConvexMatrixRegionSupportDeriv
  have hnot : ¬ (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues₀ 0 < 0 := by
    intro hlt
    have hzero : (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues₀ 0 = 0 := by
      have heig : (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues = 0 := by
        exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA := euclideanMatrixSymmetrization_isHermitian ν)).mpr hν
      let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
      have h0 : (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues (e 0) = 0 := congrFun heig (e 0)
      have hdef : (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues (e 0) =
          (euclideanMatrixSymmetrization_isHermitian ν).eigenvalues₀ (e.symm (e 0)) := rfl
      rw [hdef, Equiv.symm_apply_apply] at h0
      exact h0
    linarith
  rw [if_neg hnot]
end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
