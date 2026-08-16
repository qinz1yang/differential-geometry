import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
import DifferentialGeometry.Analysis.Convex.SupportFunction
import DifferentialGeometry.Analysis.Calculus.RightDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckCurvatureOperatorHeatReaction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Dim3Reaction
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators NNReal
open scoped Matrix.Norms.Frobenius

def hamiltonIveyMatrixReaction (A : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  2 • (A * A + A.adjugate)

def uhlenbeckCurvatureOperatorReactionState
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  matrixToEuclid (hamiltonIveyMatrixReaction (euclidToMatrix A))

lemma matrixTransposeMul_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (O : Matrix n n ℝ) (hO : O * O.transpose = 1) :
    O.transpose * O = 1 := by
  have hdet : IsUnit O.det := by
    have h : O.det * O.transpose.det = 1 := by
      rw [← Matrix.det_mul, hO, Matrix.det_one]
    have h' : O.det * O.det = 1 := by simpa [Matrix.det_transpose] using h
    exact isUnit_iff_exists_inv.mpr ⟨O.det, by rw [h']⟩
  have h2 : O⁻¹ = O.transpose := by
    calc
      O⁻¹ = O⁻¹ * 1 := by rw [mul_one]
      _ = O⁻¹ * (O * O.transpose) := by rw [hO]
      _ = (O⁻¹ * O) * O.transpose := by rw [Matrix.mul_assoc]
      _ = 1 * O.transpose := by rw [Matrix.nonsing_inv_mul O hdet]
      _ = O.transpose := by rw [one_mul]
  calc
    O.transpose * O = O⁻¹ * O := by rw [h2]
    _ = 1 := Matrix.nonsing_inv_mul O hdet

lemma adjugate_orthogonal_conj (O A : Matrix (Fin 3) (Fin 3) ℝ)
    (hO : O * O.transpose = 1) :
    (O * A * O.transpose).adjugate = O * A.adjugate * O.transpose := by
  have hOadj : O.adjugate = O.det • O.transpose := by
    have hdet : IsUnit O.det := by
      have h : O.det * O.transpose.det = 1 := by
        rw [← Matrix.det_mul, hO, Matrix.det_one]
      have h' : O.det * O.det = 1 := by simpa [Matrix.det_transpose] using h
      exact isUnit_iff_exists_inv.mpr ⟨O.det, by rw [h']⟩
    have h4 : O⁻¹ * (O.det • 1) = O.det • O⁻¹ := by
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, mul_comm]
    have h5 : O.adjugate = O.det • O⁻¹ := by
      calc
        O.adjugate = 1 * O.adjugate := by rw [one_mul]
        _ = (O⁻¹ * O) * O.adjugate := by rw [Matrix.nonsing_inv_mul O hdet]
        _ = O⁻¹ * (O * O.adjugate) := by rw [Matrix.mul_assoc]
        _ = O⁻¹ * (O.det • 1) := by rw [Matrix.mul_adjugate O]
        _ = O.det • O⁻¹ := h4
    have h6 : O⁻¹ = O.transpose := by
      calc
        O⁻¹ = O⁻¹ * 1 := by rw [mul_one]
        _ = O⁻¹ * (O * O.transpose) := by rw [hO]
        _ = (O⁻¹ * O) * O.transpose := by rw [Matrix.mul_assoc]
        _ = 1 * O.transpose := by rw [Matrix.nonsing_inv_mul O hdet]
        _ = O.transpose := by rw [one_mul]
    rw [h6] at h5
    exact h5
  have hOt : O.transpose.adjugate = O.det • O := by
    calc
      O.transpose.adjugate = (O.adjugate).transpose := by rw [Matrix.adjugate_transpose]
      _ = (O.det • O.transpose).transpose := by rw [hOadj]
      _ = O.det • O := by simp [Matrix.transpose_smul]
  have hdt : O.det * O.det = 1 := by
    have h : (O * O.transpose).det = 1 := by rw [hO, Matrix.det_one]
    simpa [Matrix.det_mul, Matrix.det_transpose] using h
  calc
    (O * A * O.transpose).adjugate = (O * (A * O.transpose)).adjugate := by rw [Matrix.mul_assoc]
    _ = (A * O.transpose).adjugate * O.adjugate := Matrix.adjugate_mul_distrib _ _
    _ = (O.transpose.adjugate * A.adjugate) * O.adjugate := by rw [Matrix.adjugate_mul_distrib]
    _ = ((O.det • O) * A.adjugate) * (O.det • O.transpose) := by rw [hOt, hOadj]
    _ = O * A.adjugate * O.transpose := by
      have hmul : ∀ X : Matrix (Fin 3) (Fin 3) ℝ,
          ((O.det • O) * X) * (O.det • O.transpose) = (O.det * O.det) • (O * X * O.transpose) := by
        intro X
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
      rw [hmul, hdt]
      simp

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

theorem sectionalRayleigh3_diagonal
    (d : Fin 3 → Real) (x : EuclideanSpace ℝ (Fin 3)) :
    sectionalRayleigh3 (Matrix.diagonal d) x = ∑ i : Fin 3, d i * (x i) ^ 2 := by
  unfold sectionalRayleigh3
  simp only [Matrix.diagonal]
  have hdiag : ∀ i : Fin 3,
      (∑ x_2 : Fin 3, (if i = x_2 then d i else 0) * x.ofLp x_2) =
        d i * x.ofLp i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro x_2 _ hx2
      rw [if_neg (Ne.symm hx2)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h
  calc
    ∑ i : Fin 3, x i * (∑ x_2 : Fin 3, (if i = x_2 then d i else 0) * x.ofLp x_2)
        = ∑ i : Fin 3, x i * (d i * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag i]
    _ = ∑ i : Fin 3, d i * (x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem sectionalRayleighMin3_diagonal_le
    (d : Fin 3 → Real) (j : Fin 3) :
    sectionalRayleighMin3 (Matrix.diagonal d) ≤ d j := by
  let e : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun i : Fin 3 => if i = j then (1 : ℝ) else 0)
  have hsphere : e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [e]
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [show (∑ i : Fin 3, (if i = j then (1 : ℝ) else 0) ^ 2) = 1 by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ j) h]
    norm_num
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      sectionalRayleigh3 (Matrix.diagonal d) x) := by
    simpa using continuous_sectionalRayleigh3.comp
      ((continuous_const (y := Matrix.diagonal d)).prodMk continuous_id)
  have hbdd : BddBelow (sectionalRayleigh3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  unfold sectionalRayleighMin3
  have hval : sectionalRayleigh3 (Matrix.diagonal d) e = d j := by
    rw [sectionalRayleigh3_diagonal]
    dsimp [e]
    rw [show (∑ i : Fin 3, d i * (if i = j then (1 : ℝ) else 0) ^ 2) = d j by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ j) h]
  have him : d j ∈ sectionalRayleigh3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    exact hval ▸ Set.mem_image_of_mem (sectionalRayleigh3 (Matrix.diagonal d)) hsphere
  exact (csInf_le hbdd (hval ▸ him))

theorem sectionalRayleighMin3_diagonal_ge
    (d : Fin 3 → Real) {m : Real}
    (hm : ∀ i : Fin 3, m ≤ d i) :
    m ≤ sectionalRayleighMin3 (Matrix.diagonal d) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      sectionalRayleigh3 (Matrix.diagonal d) x) := by
    simpa using continuous_sectionalRayleigh3.comp
      ((continuous_const (y := Matrix.diagonal d)).prodMk continuous_id)
  have hbdd : BddBelow (sectionalRayleigh3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  have hne : (sectionalRayleigh3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty := by
    have hsphere0 : (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [show (∑ i : Fin 3, (if i = 0 then (1 : ℝ) else 0) ^ 2) = 1 by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ (0 : Fin 3)) h]
      norm_num
    exact ⟨sectionalRayleigh3 (Matrix.diagonal d)
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)),
      ⟨_, hsphere0, rfl⟩⟩
  unfold sectionalRayleighMin3
  apply le_csInf hne
  rintro y ⟨x, hx, rfl⟩
  rw [sectionalRayleigh3_diagonal]
  have hsumsq : (∑ i : Fin 3, (x i) ^ 2) = 1 := by
    have hnorm : ‖x‖ = 1 := (mem_sphere_zero_iff_norm).mp hx
    have hsq : (∑ i : Fin 3, (x i) ^ 2) = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
    rw [hsq, hnorm]
    norm_num
  calc
    m = m * (∑ i : Fin 3, (x i) ^ 2) := by rw [hsumsq, mul_one]
    _ = ∑ i : Fin 3, m * (x i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin 3, d i * (x i) ^ 2 := by
          exact Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_right (hm i) (sq_nonneg (x i)))

lemma small_order_ge
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

lemma reactionDiag_order0_ge2 (l1 l2 l3 : Real) :
    l1 = l3 → 2 * (l1 ^ 2 + l2 * l3) = 2 * (l3 ^ 2 + l1 * l2) := by
  intro h
  rw [h]
  ring

lemma reactionDiag_order1_ge2 (l1 l2 l3 : Real) :
    l2 = l3 → 2 * (l2 ^ 2 + l1 * l3) = 2 * (l3 ^ 2 + l1 * l2) := by
  intro h
  rw [h]

lemma reactionDiag_minEig (l1 l2 l3 : Real) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t : Real, t ∈ Set.Icc 0 ε →
      sectionalRayleighMin3 (Matrix.diagonal
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
  have hle : sectionalRayleighMin3 (Matrix.diagonal d) ≤
      l3 + t * (2 * (l3 ^ 2 + l1 * l2)) := by
    simpa [d] using (sectionalRayleighMin3_diagonal_le d (2 : Fin 3))
  have hge' : l3 + t * (2 * (l3 ^ 2 + l1 * l2)) ≤
      sectionalRayleighMin3 (Matrix.diagonal d) :=
    sectionalRayleighMin3_diagonal_ge d hge
  rw [hd]
  exact le_antisymm hle hge'

lemma hasDerivAt_barrier_comp
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

lemma reactionSum3_nonneg (l1 l2 l3 : Real) :
    0 ≤ 2 * (l1 ^ 2 + l2 * l3) + 2 * (l2 ^ 2 + l1 * l3) + 2 * (l3 ^ 2 + l1 * l2) := by
  have hsq : 0 ≤ (l1 + l2) ^ 2 + (l1 + l3) ^ 2 + (l2 + l3) ^ 2 := by positivity
  nlinarith

lemma reactionSum3_ge_sq (l1 l2 l3 : Real) :
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

lemma lip {K tau t : Real} (hK : 0 < K) (htau : 0 <= tau) (ht : 0 <= t) :
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

lemma concave {K tau t : Real} (hK : 0 < K) (htau : 0 <= tau) (ht : 0 <= t) :
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


lemma scalarBarrier_ineq_small
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

lemma barrier_ineq_small
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


lemma sectionalRayleighMin3_diagonal_eq_last
    (l1 l2 l3 : ℝ) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) :
    sectionalRayleighMin3 (Matrix.diagonal ![l1, l2, l3]) = l3 := by
  have hge : ∀ i : Fin 3, l3 ≤ ![l1, l2, l3] i := by
    intro i
    fin_cases i <;> simp <;> linarith
  have hle : sectionalRayleighMin3 (Matrix.diagonal ![l1, l2, l3]) ≤ l3 := by
    simpa using (sectionalRayleighMin3_diagonal_le ![l1, l2, l3] (2 : Fin 3))
  have hge' : l3 ≤ sectionalRayleighMin3 (Matrix.diagonal ![l1, l2, l3]) :=
    sectionalRayleighMin3_diagonal_ge ![l1, l2, l3] hge
  exact le_antisymm hle hge'

lemma reactionDiagonal_trace (l1 l2 l3 : ℝ) :
    (hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3])).trace =
      reactionSectionalSum3 l1 l2 l3 := by
  rw [hamiltonIveyMatrixReaction_diagonal]
  unfold reactionSectionalSum3
  simp [DifferentialGeometry.Dim3Reaction.sectionalReaction12,
    DifferentialGeometry.Dim3Reaction.sectionalReaction13,
    DifferentialGeometry.Dim3Reaction.sectionalReaction23, Fin.sum_univ_three]

lemma diagonal_add_smul_reaction
    (l1 l2 l3 t : ℝ) :
    Matrix.diagonal ![l1, l2, l3] +
        t • hamiltonIveyMatrixReaction (Matrix.diagonal ![l1, l2, l3]) =
      Matrix.diagonal ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
        l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
        l3 + t * (2 * (l3 ^ 2 + l1 * l2))] := by
  rw [hamiltonIveyMatrixReaction_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

lemma continuousAt_hamiltonIveyBarrier_comp_nonneg
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
  rw [hamiltonIveyConvexMatrixRegion_eq_violation]
  refine ⟨by simp, ?_, ?_⟩
  · exact le_max_right _ _
  · unfold hamiltonIveyConvexBarrier
    rw [sectionalRayleighMin3_zero, neg_zero, max_self]
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

theorem hamiltonIveyConvexMatrixRegion_reaction_small_time_diagonal
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
  have hmin0 : sectionalRayleighMin3 D = l3 := by
    dsimp [D]
    exact sectionalRayleighMin3_diagonal_eq_last l1 l2 l3 h21 h32
  have hAmemV : hamiltonIveyConvexMatrixRegionViolation K tau D := by
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hAmem
    simpa [D] using hAmem
  have hbar : hamiltonIveyConvexBarrier K tau X ≤ S := by
    dsimp [S, X]
    have h := hAmemV.2.2
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
        (fun t : ℝ => sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) 0 :=
      (continuous_sectionalRayleighMin3_comp
        (by fun_prop : Continuous (fun t : ℝ => D + t • hamiltonIveyMatrixReaction D))).continuousAt
    have hmneg_ev : ∀ᶠ t : ℝ in 𝓝[>] 0,
        sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D) < 0 := by
      have hev := eventually_neg_of_continuousAt_neg
        (fun t : ℝ => sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) hm_cont
        (by simpa [hmin0] using hl3)
      exact hev
    rcases exists_pos_Ioo_of_eventually_nhdsWithin
      (fun t : ℝ => sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D) < 0) hmneg_ev with
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
        have hm_eq : sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D) =
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
            (max (-sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) 0) ≤ S + t * S' := by
          have hmneg_t : sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D) < 0 :=
            hmneg1 t ⟨htpos, ht4⟩
          rw [max_eq_left (neg_nonneg.mpr hmneg_t.le), hm_eq]
          exact hbar_t
        have hmem' : D + t • hamiltonIveyMatrixReaction D ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
          rw [hamiltonIveyConvexMatrixRegion_eq_violation]
          refine ⟨?_, ?_, ?_⟩
          · rw [hdiag]
            exact Matrix.isHermitian_diagonal (fun i : Fin 3 =>
              ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
                l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
                l3 + t * (2 * (l3 ^ 2 + l1 * l2))] i)
          · exact le_max_right _ _
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
          (fun t : ℝ => sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) 0 :=
        (continuous_sectionalRayleighMin3_comp
          (by fun_prop : Continuous (fun t : ℝ => D + t • hamiltonIveyMatrixReaction D))).continuousAt
      let g : ℝ → ℝ := fun t => hamiltonIveyBarrier K (tau + t)
        (max (-sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) 0)
      have hg_cont : ContinuousAt g 0 := by
        dsimp [g]
        exact continuousAt_hamiltonIveyBarrier_comp_nonneg hK htau
          (fun t : ℝ => -sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) hm_cont.neg
      have hg0 : g 0 = 0 := by
        dsimp [g]
        have hm0' : sectionalRayleighMin3 (D + 0 • hamiltonIveyMatrixReaction D) = l3 := by
          simpa [D] using hmin0
        have hbar0 : hamiltonIveyBarrier K tau 0 = 0 := by
          unfold hamiltonIveyBarrier
          ring
        convert hbar0 using 1
        · have hle' : -sectionalRayleighMin3 D ≤ 0 := by
            rw [hmin0]
            exact neg_nonpos.mpr hl3ge
          have hmax' : max (-sectionalRayleighMin3 D) 0 = 0 := max_eq_right hle'
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
              (max (-sectionalRayleighMin3 (D + t • hamiltonIveyMatrixReaction D)) 0) ≤ S + t * S' := by
            have hg_t : g t ≤ S / 2 := hg5 t ⟨htpos, ht5⟩
            have hS'nonneg_t : 0 ≤ t * S' := mul_nonneg ht.1 hS'nonneg
            dsimp [g] at hg_t
            nlinarith
          have hmem' : D + t • hamiltonIveyMatrixReaction D ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
            rw [hamiltonIveyConvexMatrixRegion_eq_violation]
            refine ⟨?_, ?_, ?_⟩
            · rw [hdiag]
              exact Matrix.isHermitian_diagonal (fun i : Fin 3 =>
                ![l1 + t * (2 * (l1 ^ 2 + l2 * l3)),
                  l2 + t * (2 * (l2 ^ 2 + l1 * l3)),
                  l3 + t * (2 * (l3 ^ 2 + l1 * l2))] i)
            · exact le_max_right _ _
            · unfold hamiltonIveyConvexBarrier
              rw [htr]
              exact max_le hscalar_t hbarrier_le
          simpa [D] using hmem'

theorem hamiltonIveyConvexMatrixRegion_reaction_small_time
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : Matrix (Fin 3) (Fin 3) Real) (hA : A.IsHermitian)
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegion K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K (tau + t) := by
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

noncomputable def hamiltonIveyConvexMatrixSlabEuclid (K T : ℝ) :
    Set (WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ)) :=
  {q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧
    (WithLp.ofLp q).1 ∈ hamiltonIveyConvexMatrixRegionEuclid K (WithLp.ofLp q).2}

theorem hamiltonIveyConvexMatrixRegionEuclid_reaction_small_time
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclid K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • uhlenbeckCurvatureOperatorReactionState A ∈
        hamiltonIveyConvexMatrixRegionEuclid K (tau + t) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := euclidToMatrix A
  have hMmem : M ∈ hamiltonIveyConvexMatrixRegion K tau := by
    simpa [M] using (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K tau A).1 hAmem
  have hMherm : M.IsHermitian := by
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hMmem
    exact hMmem.1
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time hK htau M hMherm hMmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : M + t • hamiltonIveyMatrixReaction M ∈
      hamiltonIveyConvexMatrixRegion K (tau + t) := hstep t ht
  have hsum : A + t • uhlenbeckCurvatureOperatorReactionState A =
      matrixToEuclid (M + t • hamiltonIveyMatrixReaction M) := by
    dsimp [uhlenbeckCurvatureOperatorReactionState, M]
    ext ij
    simp [matrixToEuclid, euclidToMatrix]
  rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
  rw [hsum]
  rw [euclidToMatrix_matrixToEuclid]
  exact hstep'

theorem hamiltonIveyConvexMatrixSlabEuclid_reaction_tangent
    {K T : ℝ} (hK : 0 < K)
    {tau : ℝ} (htau : tau ∈ Set.Ico 0 T)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclid K tau) :
    WithLp.toLp 2 (uhlenbeckCurvatureOperatorReactionState A, (1 : Real)) ∈
      posTangentConeAt (hamiltonIveyConvexMatrixSlabEuclid K T) (WithLp.toLp 2 (A, tau)) := by
  let x : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) := WithLp.toLp 2 (A, tau)
  let y : WithLp 2 (EuclideanSpace ℝ (Fin 3 × Fin 3) × ℝ) :=
    WithLp.toLp 2 (uhlenbeckCurvatureOperatorReactionState A, (1 : Real))
  rcases hamiltonIveyConvexMatrixRegionEuclid_reaction_small_time hK htau.1 A hAmem
    with ⟨eps, heps, hstep⟩
  let eps' : ℝ := min eps ((T - tau) / 2)
  have hTminus : 0 < T - tau := sub_pos.mpr htau.2
  have heps' : 0 < eps' := by
    dsimp [eps']
    exact lt_min heps (half_pos hTminus)
  have htbound : ∀ᶠ t : ℝ in 𝓝[>] 0, t < eps' := by
    rw [eventually_nhdsWithin_iff]
    apply Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr heps') heps')
    intro t ht
    exact fun _ => ht.2
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • y ∈ hamiltonIveyConvexMatrixSlabEuclid K T := by
    filter_upwards [htbound, self_mem_nhdsWithin] with t ht' htpos
    have htle : t ≤ eps' := le_of_lt ht'
    have htstep : A + t • uhlenbeckCurvatureOperatorReactionState A ∈
        hamiltonIveyConvexMatrixRegionEuclid K (tau + t) :=
      hstep t ⟨htpos.le, le_trans htle (min_le_left _ _)⟩
    have htausmall : tau + t ≤ T := by
      have ht' : t ≤ (T - tau) / 2 := le_trans htle (min_le_right _ _)
      nlinarith [hTminus]
    have htau' : 0 ≤ tau + t := by linarith [htau.1, (show 0 < t from htpos)]
    have hcurve : x + t • y = WithLp.toLp 2 (A + t • uhlenbeckCurvatureOperatorReactionState A, tau + t) := by
      dsimp [x, y]
      rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
      congr 1
      ext <;> simp
    rw [hcurve]
    rw [show hamiltonIveyConvexMatrixSlabEuclid K T =
        {q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧
          (WithLp.ofLp q).1 ∈ hamiltonIveyConvexMatrixRegionEuclid K (WithLp.ofLp q).2} by rfl]
    simp [htau', htausmall, htstep]
  have hfreq : ∃ᶠ t : ℝ in 𝓝[>] 0, x + t • y ∈ hamiltonIveyConvexMatrixSlabEuclid K T :=
    hev.frequently
  exact mem_posTangentConeAt_of_frequently_mem hfreq

lemma hamiltonIveyBarrier_mono_time
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
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hA ⊢
  refine ⟨hA.1, ?_, ?_⟩
  · exact hA.2.1
  · let X : ℝ := max (-sectionalRayleighMin3 A) 0
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
    have hmain := hA.2.2
    dsimp [X] at hmain hconv
    exact le_trans hconv hmain

theorem hamiltonIveyConvexMatrixRegion_reaction_small_time_fixed
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : Matrix (Fin 3) (Fin 3) Real) (hA : A.IsHermitian)
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegion K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K tau := by
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time hK htau A hA hAmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : A + t • hamiltonIveyMatrixReaction A ∈ hamiltonIveyConvexMatrixRegion K (tau + t) :=
    hstep t ht
  exact hamiltonIveyConvexMatrixRegion_antitone_time (K := K) hK htau (by linarith [ht.1]) hstep'

theorem hamiltonIveyConvexMatrixRegionEuclid_reaction_small_time_fixed
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclid K tau) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Icc 0 eps →
      A + t • uhlenbeckCurvatureOperatorReactionState A ∈
        hamiltonIveyConvexMatrixRegionEuclid K tau := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := euclidToMatrix A
  have hMmem : M ∈ hamiltonIveyConvexMatrixRegion K tau := by
    simpa [M] using (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K tau A).1 hAmem
  have hMherm : M.IsHermitian := by
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hMmem
    exact hMmem.1
  rcases hamiltonIveyConvexMatrixRegion_reaction_small_time_fixed hK htau M hMherm hMmem
    with ⟨eps, heps, hstep⟩
  refine ⟨eps, heps, ?_⟩
  intro t ht
  have hstep' : M + t • hamiltonIveyMatrixReaction M ∈
      hamiltonIveyConvexMatrixRegion K tau := hstep t ht
  have hsum : A + t • uhlenbeckCurvatureOperatorReactionState A =
      matrixToEuclid (M + t • hamiltonIveyMatrixReaction M) := by
    dsimp [uhlenbeckCurvatureOperatorReactionState, M]
    ext ij
    simp [matrixToEuclid, euclidToMatrix]
  rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
  rw [hsum]
  rw [euclidToMatrix_matrixToEuclid]
  exact hstep'

theorem hamiltonIveyConvexMatrixRegionEuclid_fiber_tangent
    {K tau : ℝ} (hK : 0 < K) (htau : 0 ≤ tau)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hAmem : A ∈ hamiltonIveyConvexMatrixRegionEuclid K tau) :
    uhlenbeckCurvatureOperatorReactionState A ∈ posTangentConeAt
      (hamiltonIveyConvexMatrixRegionEuclid K tau) A := by
  rcases hamiltonIveyConvexMatrixRegionEuclid_reaction_small_time_fixed hK htau A hAmem
    with ⟨eps, heps, hstep⟩
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, A + t • uhlenbeckCurvatureOperatorReactionState A ∈
      hamiltonIveyConvexMatrixRegionEuclid K tau := by
    rw [eventually_nhdsWithin_iff]
    apply Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr heps) heps)
    intro t ht _htpos
    exact hstep t ⟨_htpos.le, le_of_lt ht.2⟩
  have hfreq : ∃ᶠ t : ℝ in 𝓝[>] 0, A + t • uhlenbeckCurvatureOperatorReactionState A ∈
      hamiltonIveyConvexMatrixRegionEuclid K tau := hev.frequently
  exact mem_posTangentConeAt_of_frequently_mem hfreq

def opFromR (R : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => rm R (bivectorIndex3 i).1 (bivectorIndex3 i).2 (bivectorIndex3 j).2 (bivectorIndex3 j).1

lemma curvatureOperatorReactionMatrix_eq_hamiltonIveyMatrixReaction
    (R : Fin 3 → Fin 3 → ℝ) (hR : ∀ i j, R i j = R j i) :
    (fun i j : Fin 3 => -2 * Bsharp R (bivectorIndex3 i).1 (bivectorIndex3 i).2
        (bivectorIndex3 j).2 (bivectorIndex3 j).1) =
      hamiltonIveyMatrixReaction (opFromR R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsharp, Bt, rm, opFromR, hamiltonIveyMatrixReaction, Matrix.mul_apply,
      Matrix.adjugate_apply, bivectorIndex3, kd, sc, Fin.sum_univ_three,
      Matrix.det_fin_three, Matrix.updateRow_apply,
      hR] <;> ring

lemma euclid_entry_le_norm (a : EuclideanSpace ℝ (Fin 3 × Fin 3)) (ij : Fin 3 × Fin 3) :
    |a ij| ≤ ‖a‖ := by
  simpa [abs_of_nonneg] using (PiLp.norm_apply_le a ij)

lemma matrixToEuclid_norm (A : Matrix (Fin 3) (Fin 3) ℝ) : ‖matrixToEuclid A‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold matrixToEuclid
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.sqrt_eq_rpow]
  congr 1
  rw [← Finset.sum_product']
  rw [Finset.univ_product_univ]
  apply Finset.sum_congr rfl
  intro x hx
  simp

lemma matrixToEuclid_mul_norm_le (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖matrixToEuclid (A * B)‖ ≤ ‖matrixToEuclid A‖ * ‖matrixToEuclid B‖ := by
  rw [matrixToEuclid_norm, matrixToEuclid_norm, matrixToEuclid_norm]
  exact Matrix.frobenius_norm_mul A B

lemma matrixToEuclid_sub (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToEuclid (A - B) = matrixToEuclid A - matrixToEuclid B := by
  ext ij
  rfl

lemma matrixToEuclid_add (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToEuclid (A + B) = matrixToEuclid A + matrixToEuclid B := by
  ext ij
  rfl

lemma matrixToEuclid_smul (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToEuclid (c • A) = c • matrixToEuclid A := by
  ext ij
  rfl

lemma euclid_norm_le_of_entry_le {D : Matrix (Fin 3) (Fin 3) ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i j, |D i j| ≤ C) : ‖matrixToEuclid D‖ ≤ 3 * C := by
  rw [matrixToEuclid_norm, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
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

lemma matrix_product_entry_sub_abs_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclid A‖ ≤ R) (hB : ‖matrixToEuclid B‖ ≤ R)
    (p q r s : Fin 3) :
    |A p q * A r s - B p q * B r s| ≤ 2 * R * ‖matrixToEuclid (A - B)‖ := by
  have h1 : |A p q - B p q| ≤ ‖matrixToEuclid (A - B)‖ := by
    have h := euclid_entry_le_norm (matrixToEuclid (A - B)) (p, q)
    simpa [matrixToEuclid_sub] using h
  have h2 : |A r s| ≤ R := by
    have h := euclid_entry_le_norm (matrixToEuclid A) (r, s)
    simpa using le_trans h hA
  have h3 : |B p q| ≤ R := by
    have h := euclid_entry_le_norm (matrixToEuclid B) (p, q)
    simpa using le_trans h hB
  have h4 : |A r s - B r s| ≤ ‖matrixToEuclid (A - B)‖ := by
    have h := euclid_entry_le_norm (matrixToEuclid (A - B)) (r, s)
    simpa [matrixToEuclid_sub] using h
  calc
    |A p q * A r s - B p q * B r s| ≤
        |A p q * A r s - B p q * A r s| + |B p q * A r s - B p q * B r s| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        abs_sub_le (A p q * A r s) (B p q * A r s) (B p q * B r s)
    _ = |A p q - B p q| * |A r s| + |B p q| * |A r s - B r s| := by
      rw [← sub_mul, ← mul_sub, abs_mul, abs_mul]
    _ ≤ ‖matrixToEuclid (A - B)‖ * R + R * ‖matrixToEuclid (A - B)‖ := by
      exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul h3 h4 (abs_nonneg _) hR)
    _ = 2 * R * ‖matrixToEuclid (A - B)‖ := by ring

lemma two_monomial_sub_abs_le (x1 x2 y1 y2 z1 z2 w1 w2 : ℝ) :
    |(x1 * x2 - y1 * y2) - (z1 * z2 - w1 * w2)| ≤
      |x1 * x2 - z1 * z2| + |y1 * y2 - w1 * w2| := by
  have h : (x1 * x2 - y1 * y2) - (z1 * z2 - w1 * w2) =
      (x1 * x2 - z1 * z2) - (y1 * y2 - w1 * w2) := by ring
  rw [h]
  simpa [sub_zero, abs_neg, abs_sub_comm] using
    (abs_sub_le (x1 * x2 - z1 * z2) (0 : ℝ) (y1 * y2 - w1 * w2))

lemma two_monomial_sub_abs_le' (x1 x2 y1 y2 z1 z2 w1 w2 : ℝ) :
    |-(x1 * x2) + y1 * y2 - (-(z1 * z2) + w1 * w2)| ≤
      |x1 * x2 - z1 * z2| + |y1 * y2 - w1 * w2| := by
  have h : -(x1 * x2) + y1 * y2 - (-(z1 * z2) + w1 * w2) =
      (y1 * y2 - x1 * x2) - (w1 * w2 - z1 * z2) := by ring
  rw [h]
  simpa [add_comm] using two_monomial_sub_abs_le y1 y2 x1 x2 w1 w2 z1 z2

lemma matrix_adjugate_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclid A‖ ≤ R) (hB : ‖matrixToEuclid B‖ ≤ R) :
    ‖matrixToEuclid (A.adjugate - B.adjugate)‖ ≤
      12 * R * ‖matrixToEuclid (A - B)‖ := by
  have hnorm : ‖matrixToEuclid (A.adjugate - B.adjugate)‖ ≤
      3 * (4 * R * ‖matrixToEuclid (A - B)‖) := by
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

lemma euclidToMatrix_norm_eq (a : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    ‖euclidToMatrix a‖ = ‖a‖ := by
  have h := matrixToEuclid_norm (euclidToMatrix a)
  rw [matrixToEuclid_euclidToMatrix] at h
  exact h.symm

lemma matrix_square_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ)
    (hA : ‖matrixToEuclid A‖ ≤ R) (hB : ‖matrixToEuclid B‖ ≤ R) :
    ‖matrixToEuclid (A * A - B * B)‖ ≤ 2 * R * ‖matrixToEuclid (A - B)‖ := by
  have hident : A * A - B * B = A * (A - B) + (A - B) * B := by
    ext i j
    simp [Matrix.mul_apply, sub_mul, mul_sub]
  calc
    ‖matrixToEuclid (A * A - B * B)‖ = ‖matrixToEuclid (A * (A - B) + (A - B) * B)‖ := by
      rw [hident]
    _ ≤ ‖matrixToEuclid (A * (A - B))‖ + ‖matrixToEuclid ((A - B) * B)‖ := by
      rw [matrixToEuclid_add]
      exact norm_add_le _ _
    _ ≤ ‖matrixToEuclid A‖ * ‖matrixToEuclid (A - B)‖ +
        ‖matrixToEuclid (A - B)‖ * ‖matrixToEuclid B‖ := by
      exact add_le_add (matrixToEuclid_mul_norm_le A (A - B))
        (matrixToEuclid_mul_norm_le (A - B) B)
    _ ≤ R * ‖matrixToEuclid (A - B)‖ + ‖matrixToEuclid (A - B)‖ * R := by
      have h1 : ‖matrixToEuclid A‖ * ‖matrixToEuclid (A - B)‖ ≤
          R * ‖matrixToEuclid (A - B)‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      have h2 : ‖matrixToEuclid (A - B)‖ * ‖matrixToEuclid B‖ ≤
          ‖matrixToEuclid (A - B)‖ * R :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg _)
      exact add_le_add h1 h2
    _ = 2 * R * ‖matrixToEuclid (A - B)‖ := by ring

lemma hamiltonIveyMatrixReaction_sub_norm_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ‖matrixToEuclid A‖ ≤ R) (hB : ‖matrixToEuclid B‖ ≤ R) :
    ‖matrixToEuclid (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ ≤
      28 * R * ‖matrixToEuclid (A - B)‖ := by
  have hsq := matrix_square_sub_norm_le A B R hA hB
  have hadj := matrix_adjugate_sub_norm_le A B R hR hA hB
  have hsum : matrixToEuclid (A * A - B * B + (A.adjugate - B.adjugate)) =
      matrixToEuclid (A * A - B * B) + matrixToEuclid (A.adjugate - B.adjugate) := by
    exact matrixToEuclid_add (A * A - B * B) (A.adjugate - B.adjugate)
  have hnorm : ‖matrixToEuclid (A * A - B * B + (A.adjugate - B.adjugate))‖ ≤
      2 * R * ‖matrixToEuclid (A - B)‖ + 12 * R * ‖matrixToEuclid (A - B)‖ := by
    rw [hsum]
    exact (norm_add_le (matrixToEuclid (A * A - B * B))
      (matrixToEuclid (A.adjugate - B.adjugate))).trans (add_le_add hsq hadj)
  calc
    ‖matrixToEuclid (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ = ‖
        matrixToEuclid ((2 : ℝ) • (A * A - B * B + (A.adjugate - B.adjugate)))‖ := by
      congr 1
      ext ij
      unfold hamiltonIveyMatrixReaction
      simp only [matrixToEuclid, WithLp.ofLp_toLp, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul]
      ring
    _ = 2 * ‖matrixToEuclid (A * A - B * B + (A.adjugate - B.adjugate))‖ := by
      rw [matrixToEuclid_smul (2 : ℝ)]
      rw [norm_smul]
      norm_num
    _ ≤ 2 * (2 * R * ‖matrixToEuclid (A - B)‖ + 12 * R * ‖matrixToEuclid (A - B)‖) := by
      exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = 28 * R * ‖matrixToEuclid (A - B)‖ := by ring

lemma uhlenbeckCurvatureOperatorReactionState_sub_norm_le
    (a b : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (R : ℝ) (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖uhlenbeckCurvatureOperatorReactionState a - uhlenbeckCurvatureOperatorReactionState b‖ ≤
      28 * R * ‖a - b‖ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := euclidToMatrix a
  let B : Matrix (Fin 3) (Fin 3) ℝ := euclidToMatrix b
  have hA : ‖matrixToEuclid A‖ ≤ R := by
    dsimp [A]
    simpa [euclidToMatrix_norm_eq] using ha
  have hB : ‖matrixToEuclid B‖ ≤ R := by
    dsimp [B]
    simpa [euclidToMatrix_norm_eq] using hb
  have hmain : ‖matrixToEuclid (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B)‖ ≤
      28 * R * ‖matrixToEuclid (A - B)‖ :=
    hamiltonIveyMatrixReaction_sub_norm_le A B R hR hA hB
  have hdiff : matrixToEuclid (A - B) = a - b := by
    dsimp [A, B]
    rw [matrixToEuclid_sub]
    rw [matrixToEuclid_euclidToMatrix, matrixToEuclid_euclidToMatrix]
  have hlhs : matrixToEuclid (hamiltonIveyMatrixReaction A - hamiltonIveyMatrixReaction B) =
      uhlenbeckCurvatureOperatorReactionState a - uhlenbeckCurvatureOperatorReactionState b := by
    dsimp [A, B, uhlenbeckCurvatureOperatorReactionState]
    rw [matrixToEuclid_sub]
  rw [hlhs, hdiff] at hmain
  exact hmain

theorem uhlenbeckCurvatureOperatorReactionState_lipschitzOn_closedBall
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : NNReal, LipschitzOnWith L uhlenbeckCurvatureOperatorReactionState
      (Metric.closedBall 0 R) := by
  refine ⟨⟨28 * R, by positivity⟩, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro a ha b hb
  rw [dist_eq_norm, dist_eq_norm]
  exact uhlenbeckCurvatureOperatorReactionState_sub_norm_le a b R hR
    (mem_closedBall_zero_iff.mp ha) (mem_closedBall_zero_iff.mp hb)

noncomputable def symmEuclid (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • (euclidToMatrix v + (euclidToMatrix v).transpose)

theorem symmEuclid_isHermitian (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    (symmEuclid v).IsHermitian := by
  dsimp [symmEuclid]
  unfold Matrix.IsHermitian
  ext i j
  simp [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_comm]
  ring

noncomputable def hamiltonIveyConvexMatrixRegionSupportEuclid (K τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) : ℝ :=
  let ν₁ : ℝ := (symmEuclid_isHermitian v).eigenvalues₀ 0
  let ν₂ : ℝ := (symmEuclid_isHermitian v).eigenvalues₀ 1
  let ν₃ : ℝ := (symmEuclid_isHermitian v).eigenvalues₀ 2
  if ν₁ < 0 then
    sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
      x = hamiltonIveyConvexBarrier K τ X * ν₁ + X * (2 * ν₁ - ν₂ - ν₃)}
  else 0

lemma inner_matrixToEuclid_symm
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.IsHermitian) :
    inner ℝ v (matrixToEuclid A) =
      inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid A) := by
  rw [inner_matrixToEuclid, inner_matrixToEuclid]
  dsimp [symmEuclid]
  have hAij : ∀ i j : Fin 3, A i j = A j i := by
    intro i j
    have h1 := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose] using h1.symm
  have hswap :
      (∑ ij : Fin 3 × Fin 3, v (ij.2, ij.1) * A ij.1 ij.2) =
        (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.1 ij.2) := by
    calc
      (∑ ij : Fin 3 × Fin 3, v (ij.2, ij.1) * A ij.1 ij.2)
          = (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.2 ij.1) := by
            refine Finset.sum_bij (fun ij _ => (ij.2, ij.1)) ?_ ?_ ?_ ?_
            · intro ij hij
              simp
            · intro a ha b hb h
              exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
            · intro b hb
              refine ⟨(b.2, b.1), ⟨by simp, ?_⟩⟩
              change (b.1, b.2) = b
              exact Prod.ext rfl rfl
            · intro ij hij
              rfl
        _ = (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.1 ij.2) := by
          apply Finset.sum_congr rfl
          intro ij hij
          simp [hAij ij.1 ij.2]
  calc
    (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.1 ij.2)
        = (1 / 2 : ℝ) * (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.1 ij.2) +
            (1 / 2 : ℝ) * (∑ ij : Fin 3 × Fin 3, v (ij.2, ij.1) * A ij.1 ij.2) := by
          rw [hswap]
          ring
    _ = (∑ ij : Fin 3 × Fin 3,
            (1 / 2 : ℝ) * (v (ij.1, ij.2) + v (ij.2, ij.1)) * A ij.1 ij.2) := by
          calc
            (1 / 2 : ℝ) * (∑ ij : Fin 3 × Fin 3, v (ij.1, ij.2) * A ij.1 ij.2) +
                (1 / 2 : ℝ) * (∑ ij : Fin 3 × Fin 3, v (ij.2, ij.1) * A ij.1 ij.2)
                = (∑ ij : Fin 3 × Fin 3, (1 / 2 : ℝ) * (v (ij.1, ij.2) * A ij.1 ij.2)) +
                    (∑ ij : Fin 3 × Fin 3, (1 / 2 : ℝ) * (v (ij.2, ij.1) * A ij.1 ij.2)) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
            _ = (∑ ij : Fin 3 × Fin 3,
                    (1 / 2 : ℝ) * (v (ij.1, ij.2) + v (ij.2, ij.1)) * A ij.1 ij.2) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro ij hij
                  ring

lemma sum_pair_swap_three (f : Fin 3 × Fin 3 → ℝ) :
    (∑ p : Fin 3 × Fin 3, f (p.2, p.1)) = ∑ p : Fin 3 × Fin 3, f p := by
  refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp
  · intro a ha b hb h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro b hb
    refine ⟨(b.2, b.1), ⟨by simp, ?_⟩⟩
    change (b.1, b.2) = b
    exact Prod.ext rfl rfl
  · intro p hp
    rfl

lemma matrixDot_eq_trace_transpose_mul
    (N A : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ ij : Fin 3 × Fin 3, N ij.1 ij.2 * A ij.1 ij.2) =
      Matrix.trace (N.transpose * A) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem inner_matrixToEuclid_orthogonal_conj
    (N A O : Matrix (Fin 3) (Fin 3) ℝ) (hOorth : O * O.transpose = 1) :
    inner ℝ (matrixToEuclid N) (matrixToEuclid A) =
      inner ℝ (matrixToEuclid (O.transpose * N * O))
        (matrixToEuclid (O.transpose * A * O)) := by
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  calc
    inner ℝ (matrixToEuclid N) (matrixToEuclid A)
        = (∑ ij : Fin 3 × Fin 3, N ij.1 ij.2 * A ij.1 ij.2) := by
          rw [inner_matrixToEuclid]
          change (∑ ij : Fin 3 × Fin 3, N ij.1 ij.2 * A ij.1 ij.2) =
            (∑ ij : Fin 3 × Fin 3, N ij.1 ij.2 * A ij.1 ij.2)
          rfl
    _ = Matrix.trace (N.transpose * A) :=
          matrixDot_eq_trace_transpose_mul N A
    _ = Matrix.trace (O.transpose * (N.transpose * A) * O) := by
          have hcyc := Matrix.trace_mul_cycle O.transpose (N.transpose * A) O
          rw [hOorth] at hcyc
          simpa [Matrix.one_mul] using hcyc.symm
    _ = Matrix.trace ((O.transpose * N * O).transpose * (O.transpose * A * O)) := by
          congr 1
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
          rw [show O * (O.transpose * (A * O)) = A * O by
            rw [← Matrix.mul_assoc, hOorth]
            simp]
    _ = (∑ ij : Fin 3 × Fin 3,
          (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2) :=
          (matrixDot_eq_trace_transpose_mul (O.transpose * N * O) (O.transpose * A * O)).symm
    _ = inner ℝ (matrixToEuclid (O.transpose * N * O))
          (matrixToEuclid (O.transpose * A * O)) := by
          rw [inner_matrixToEuclid]
          change (∑ ij : Fin 3 × Fin 3,
              (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2) =
            (∑ ij : Fin 3 × Fin 3,
              (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2)
          rfl

lemma sum_eigenvalues_eq_sum_eigenvalues₀
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) :
    (∑ i : Fin 3, hA.eigenvalues i) = ∑ i : Fin 3, hA.eigenvalues₀ i := by
  let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
  have hsum := Fintype.sum_equiv e.symm
    (f := fun i => hA.eigenvalues₀ (e.symm i))
    (g := fun i => hA.eigenvalues₀ i)
    (by intro i; rfl)
  simpa [e, Matrix.IsHermitian.eigenvalues] using hsum

lemma weight_sum_orth (O : Matrix (Fin 3) (Fin 3) ℝ) (hOorth2 : O.transpose * O = 1)
    (i : Fin 3) :
    (∑ j : Fin 3, (O j i) ^ 2) = 1 := by
  have hOO : (O.transpose * O) i i = 1 := by
    have h1 := congrFun (congrFun hOorth2 i) i
    simpa [Matrix.one_apply] using h1
  have hmain : (O.transpose * O) i i = ∑ j : Fin 3, (O j i) ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [hmain] at hOO
  exact hOO

lemma inner_diag_le_eigen_bound
    {ν : Fin 3 → ℝ} (hν : Antitone ν)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) :
    inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid A) ≤
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-hA.eigenvalues₀ 2) 0 := by
  rcases hermitian_orthogonal_diagonalization hA with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let a : Fin 3 → ℝ := hA.eigenvalues₀
  let d : Matrix (Fin 3) (Fin 3) ℝ := O.transpose * Matrix.diagonal ν * O
  let X : ℝ := max (-a 2) 0
  have hdiag_expand : ∀ i : Fin 3, d i i = ∑ j : Fin 3, ν j * (O j i) ^ 2 := by
    intro i
    dsimp [d]
    simp only [Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sq]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hd_le : ∀ i : Fin 3, d i i ≤ ν 0 := by
    intro i
    calc
      d i i = ∑ j : Fin 3, ν j * (O j i) ^ 2 := hdiag_expand i
      _ ≤ ν 0 * (∑ j : Fin 3, (O j i) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hν (Fin.zero_le j)) (sq_nonneg (O j i))
      _ = ν 0 := by
            rw [weight_sum_orth O hOorth2 i]
            simp
  have hd_sum : (∑ i : Fin 3, d i i) = ∑ i : Fin 3, ν i := by
    calc
      (∑ i : Fin 3, d i i) = ∑ i : Fin 3, ∑ j : Fin 3, ν j * (O j i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hdiag_expand i
      _ = ∑ j : Fin 3, ν j * (∑ i : Fin 3, (O j i) ^ 2) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = ∑ i : Fin 3, ν i := by
            apply Finset.sum_congr rfl
            intro j hj
            have hw : (∑ i : Fin 3, (O j i) ^ 2) = 1 := by
              have hOO : (O * O.transpose) j j = 1 := by
                have h1 := congrFun (congrFun hOorth j) j
                simpa [Matrix.one_apply] using h1
              have hmain : (O * O.transpose) j j = ∑ i : Fin 3, (O j i) ^ 2 := by
                simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
              rw [hmain] at hOO
              exact hOO
            rw [hw]
            ring
  have ha_ge : ∀ i : Fin 3, 0 ≤ a i + X := by
    intro i
    have hi_le : i ≤ (2 : Fin 3) := by fin_cases i <;> decide
    have ha2 : a 2 ≤ a i := hA.eigenvalues₀_antitone hi_le
    have hX : 0 ≤ a 2 + X := by
      dsimp [X]
      have hle : -a 2 ≤ max (-a 2) 0 := le_max_left _ _
      linarith
    nlinarith
  have htrace : A.trace = ∑ i : Fin 3, a i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hA]
    simpa [a] using sum_eigenvalues_eq_sum_eigenvalues₀ A hA
  have hsum : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid A) ≤
      ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
    have hconj := inner_matrixToEuclid_orthogonal_conj (Matrix.diagonal ν) A O hOorth
    rw [hconj, hdiag]
    rw [inner_matrixToEuclid]
    have hmain : (∑ ij : Fin 3 × Fin 3, d ij.1 ij.2 * (Matrix.diagonal a) ij.1 ij.2) ≤
        ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
      calc
        (∑ ij : Fin 3 × Fin 3, d ij.1 ij.2 * (Matrix.diagonal a) ij.1 ij.2)
            = (∑ i : Fin 3, d i i * a i) := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_eq_single i]
              · simp [Matrix.diagonal]
              · intro j _ hj
                simp [Matrix.diagonal, Ne.symm hj]
              · intro h
                exact absurd (Finset.mem_univ i) h
        _ = (∑ i : Fin 3, d i i * (a i + X)) - X * (∑ i : Fin 3, d i i) := by
              calc
                (∑ i : Fin 3, d i i * a i)
                    = ∑ i : Fin 3, (d i i * (a i + X) - d i i * X) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = (∑ i : Fin 3, d i i * (a i + X)) - X * (∑ i : Fin 3, d i i) := by
                      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring_nf
        _ ≤ ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
              have h1 : (∑ i : Fin 3, d i i * (a i + X)) ≤ ν 0 * (∑ i : Fin 3, (a i + X)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro i hi
                exact mul_le_mul_of_nonneg_right (hd_le i) (ha_ge i)
              rw [hd_sum]
              linarith
    simpa [d, a, hmain]
  have hX0 : 0 ≤ X := le_max_right _ _
  have hcalc : ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) =
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * X := by
    rw [htrace]
    simp [Finset.sum_add_distrib, Fin.sum_univ_three]
    ring
  simpa [X, a, hcalc] using hsum

lemma hamiltonIveyConvexBarrier_eq_scalarLower_at_feasible_point
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

lemma barrier_ge_scalar (K τ X : ℝ) :
    scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyConvexBarrier K τ X := by
  unfold hamiltonIveyConvexBarrier
  exact le_max_left _ _

lemma support_formula_le_at_feasible_point
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

lemma diagonal_extremal_mem_region
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
  rw [hamiltonIveyConvexMatrixRegion_eq_violation]
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.isHermitian_diagonal d
  · have hmin : sectionalRayleighMin3 D = -X := by
      have heig : (Matrix.isHermitian_diagonal d).eigenvalues₀ = d :=
        diagonal_eigenvalues₀_eq_of_antitone d hd_antitone
      have hmineig : sectionalRayleighMin3 D = (Matrix.isHermitian_diagonal d).eigenvalues₀ 2 := by
        exact sectionalRayleighMin3_eq_eigenvalue_min (hA := Matrix.isHermitian_diagonal d)
      rw [hmineig, heig]
      simp [d]
    rw [hmin]
    exact le_max_right _ _
  · have hmin : sectionalRayleighMin3 D = -X := by
      have heig : (Matrix.isHermitian_diagonal d).eigenvalues₀ = d :=
        diagonal_eigenvalues₀_eq_of_antitone d hd_antitone
      have hmineig : sectionalRayleighMin3 D = (Matrix.isHermitian_diagonal d).eigenvalues₀ 2 := by
        exact sectionalRayleighMin3_eq_eigenvalue_min (hA := Matrix.isHermitian_diagonal d)
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

lemma inner_diag_diag (ν l : Fin 3 → ℝ) :
    inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid (Matrix.diagonal l)) =
      ∑ i : Fin 3, ν i * l i := by
  rw [inner_matrixToEuclid]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [matrixToEuclid, Matrix.diagonal]
  · intro j _ hj
    simp [Matrix.diagonal, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma inner_le_support_formula_of_mem_region
    {K τ : ℝ}
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid A) ≤
      hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 A) 0) * ν 0 +
        max (-sectionalRayleighMin3 A) 0 * (2 * ν 0 - ν 1 - ν 2) := by
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hA
  rcases hA with ⟨hAh, hX0, hbar⟩
  have hle := inner_diag_le_eigen_bound hν A hAh
  have hmin : sectionalRayleighMin3 A = hAh.eigenvalues₀ 2 :=
    sectionalRayleighMin3_eq_eigenvalue_min (hA := hAh)
  have hle' : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid A) ≤
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-sectionalRayleighMin3 A) 0 := by
    simpa [hmin] using hle
  have hmul : ν 0 * A.trace ≤
      ν 0 * hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 A) 0) := by
    exact mul_le_mul_of_nonpos_left hbar hν0.le
  have hmain : ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-sectionalRayleighMin3 A) 0 ≤
      hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 A) 0) * ν 0 +
        max (-sectionalRayleighMin3 A) 0 * (2 * ν 0 - ν 1 - ν 2) := by
    rw [mul_comm (hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 A) 0)) (ν 0)]
    nlinarith [hmul]
  exact le_trans hle' hmain


lemma support_formula_tail_nonpos
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

lemma support_formula_bddAbove
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


lemma support_formula_feasible_le_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0)
    (X : ℝ) (hX₀ : K / (1 + 4 * K * τ) ≤ X) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
        (matrixToEuclid (Matrix.diagonal ν)) := by
  let l : Fin 3 → ℝ := ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal l
  let S : Set ℝ := {y | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
    B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
      y = inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B}
  have hbdd : BddAbove S := by
    have hbddF := support_formula_bddAbove hK hτ hν0
    rcases hbddF with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨B, hBmem, rfl⟩
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
      exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hBmem
    have hinner : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B ≤
        hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
          max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
      inner_le_support_formula_of_mem_region hν hν0 (euclidToMatrix B) hBm
    have hF : hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
          max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤ C := by
      exact hC ⟨max (-sectionalRayleighMin3 (euclidToMatrix B)) 0, (le_max_right _ _), rfl⟩
    exact le_trans hinner hF
  have hDmem : D ∈ hamiltonIveyConvexMatrixRegion K τ :=
    diagonal_extremal_mem_region hK hτ hX₀
  have hDmemE : matrixToEuclid D ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    simpa [D, l, euclidToMatrix_matrixToEuclid] using hDmem
  have hinner_eq : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) (matrixToEuclid D) =
      hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) := by
    have hdd := inner_diag_diag ν l
    dsimp [D, l] at hdd
    rw [hdd]
    simp [Fin.sum_univ_three]
    ring
  unfold supportFunction
  exact le_csSup hbdd ⟨matrixToEuclid D, hDmemE, hinner_eq.symm⟩

lemma support_formula_le_supportFunction_diag
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) (X : ℝ) :
    hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
        (matrixToEuclid (Matrix.diagonal ν)) := by
  by_cases hX₀ : K / (1 + 4 * K * τ) ≤ X
  · exact support_formula_feasible_le_supportFunction hK hτ hν hν0 X hX₀
  · have hX₀le : X ≤ K / (1 + 4 * K * τ) := le_of_not_ge hX₀
    have hFle := support_formula_le_at_feasible_point hK hτ hν hν0 hX₀le
    have hF₀le : hamiltonIveyConvexBarrier K τ (K / (1 + 4 * K * τ)) * ν 0 +
          (K / (1 + 4 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) ≤
        supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
          (matrixToEuclid (Matrix.diagonal ν)) :=
      support_formula_feasible_le_supportFunction hK hτ hν hν0
        (K / (1 + 4 * K * τ)) le_rfl
    exact le_trans hFle hF₀le

lemma hamiltonIveyConvexMatrixRegionSupportEuclid_diag_eq_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν : Antitone ν) (hν0 : ν 0 < 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal ν)) =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
        (matrixToEuclid (Matrix.diagonal ν)) := by
  have hsymm : symmEuclid (matrixToEuclid (Matrix.diagonal ν)) = Matrix.diagonal ν := by
    ext i j
    dsimp [symmEuclid, euclidToMatrix]
    by_cases h : i = j
    · simp [h, matrixToEuclid, Matrix.diagonal]
      ring
    · simp [h, matrixToEuclid, Matrix.diagonal, Ne.symm h]
  have hν' : (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν))).eigenvalues₀ = ν := by
    have hchar : (symmEuclid (matrixToEuclid (Matrix.diagonal ν))).charpoly =
        (Matrix.diagonal ν).charpoly := by
      rw [hsymm]
    have heig' : (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν))).eigenvalues₀ =
        (Matrix.isHermitian_diagonal ν).eigenvalues₀ :=
      eigenvalues₀_eq_of_charpoly_eq_real
        (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν)))
        (Matrix.isHermitian_diagonal ν) hchar
    have heig : (Matrix.isHermitian_diagonal ν).eigenvalues₀ = ν :=
      diagonal_eigenvalues₀_eq_of_antitone ν hν
    exact heig'.trans heig
  let Fset : Set ℝ := {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
    x = hamiltonIveyConvexBarrier K τ X * ν 0 + X * (2 * ν 0 - ν 1 - ν 2)}
  have hdef_eq : hamiltonIveyConvexMatrixRegionSupportEuclid K τ
      (matrixToEuclid (Matrix.diagonal ν)) = sSup Fset := by
    unfold hamiltonIveyConvexMatrixRegionSupportEuclid
    rw [hν']
    dsimp
    exact (if_pos hν0).trans rfl
  have hbddF : BddAbove Fset := by
    dsimp [Fset]
    exact support_formula_bddAbove hK hτ hν0
  have hFne : Fset.Nonempty :=
    ⟨hamiltonIveyConvexBarrier K τ 0 * ν 0 + 0 * (2 * ν 0 - ν 1 - ν 2), 0, le_rfl, rfl⟩
  have hdef_le : hamiltonIveyConvexMatrixRegionSupportEuclid K τ
      (matrixToEuclid (Matrix.diagonal ν)) ≤
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
        (matrixToEuclid (Matrix.diagonal ν)) := by
    rw [hdef_eq]
    refine csSup_le hFne ?_
    rintro x ⟨X, hX, rfl⟩
    exact support_formula_le_supportFunction_diag hK hτ hν hν0 X
  have hsup_le : supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
      (matrixToEuclid (Matrix.diagonal ν)) ≤
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal ν)) := by
    let S : Set ℝ := {y | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
      B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
        y = inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B}
    have hSne : S.Nonempty := by
      rcases nonempty_hamiltonIveyConvexMatrixRegionEuclid hK hτ with ⟨B, hB⟩
      refine ⟨inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B, B, hB, rfl⟩
    have hbddS : BddAbove S := by
      have hbddF' := support_formula_bddAbove hK hτ hν0
      rcases hbddF' with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro y ⟨B, hBmem, rfl⟩
      have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
        exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hBmem
      have hinner : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B ≤
          hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
            max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
        inner_le_support_formula_of_mem_region hν hν0 (euclidToMatrix B) hBm
      have hF : hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
            max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤ C := by
        exact hC ⟨max (-sectionalRayleighMin3 (euclidToMatrix B)) 0, (le_max_right _ _), rfl⟩
      exact le_trans hinner hF
    unfold supportFunction
    refine csSup_le hSne ?_
    rintro y ⟨B, hBmem, rfl⟩
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ := by
      exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hBmem
    have hinner : inner ℝ (matrixToEuclid (Matrix.diagonal ν)) B ≤
        hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
          max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) :=
      inner_le_support_formula_of_mem_region hν hν0 (euclidToMatrix B) hBm
    have hFle : hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * ν 0 +
          max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * ν 0 - ν 1 - ν 2) ≤
        hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal ν)) := by
      rw [hdef_eq]
      exact le_csSup hbddF
        ⟨max (-sectionalRayleighMin3 (euclidToMatrix B)) 0, (le_max_right _ _), rfl⟩
    exact le_trans hinner hFle
  exact le_antisymm hdef_le hsup_le

lemma inner_symm_of_region_mem
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    inner ℝ v A =
      inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid (euclidToMatrix A)) := by
  have hAm : (euclidToMatrix A).IsHermitian := by
    have hmem : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
    rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmem
    exact hmem.1
  simpa [matrixToEuclid_euclidToMatrix] using inner_matrixToEuclid_symm v (euclidToMatrix A) hAm

lemma supportFunction_rotate_diag
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ) v =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
        (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) := by
  let S : Matrix (Fin 3) (Fin 3) ℝ := symmEuclid v
  let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
  rcases hermitian_orthogonal_diagonalization (symmEuclid_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  have hdiag' : O.transpose * S * O = Matrix.diagonal nv := by
    simpa [S, nv] using hdiag
  -- the map A ↦ matrixToEuclid (Oᵀ (euclidToMatrix A) O) is a bijection of the region
  let φ : EuclideanSpace ℝ (Fin 3 × Fin 3) → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun A => matrixToEuclid (O.transpose * euclidToMatrix A * O)
  have hφ_mem : ∀ A, A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ →
      φ A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
    intro A hA
    have hAm : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O) hOorth2 hOorth).1 hAm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    dsimp [φ]
    simpa [euclidToMatrix_matrixToEuclid] using hconj
  have hφ_inv : ∀ B, B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ →
      ∃ A, A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ φ A = B := by
    intro B hB
    let A : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
      matrixToEuclid (O * euclidToMatrix B * O.transpose)
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hB
    have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
      have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
        (Q := O.transpose) (by simpa using hOorth) (by simpa using hOorth2)).1 hBm
      rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
      dsimp [A]
      simpa [euclidToMatrix_matrixToEuclid, Matrix.transpose_transpose] using hconj
    refine ⟨A, hA, ?_⟩
    dsimp [φ, A]
    rw [euclidToMatrix_matrixToEuclid]
    have hmat : O.transpose * (O * euclidToMatrix B * O.transpose) * O = euclidToMatrix B := by
      simp only [Matrix.mul_assoc]
      rw [hOorth2]
      simp only [Matrix.mul_one]
      rw [← Matrix.mul_assoc]
      rw [hOorth2]
      simp only [Matrix.one_mul]
    rw [hmat, matrixToEuclid_euclidToMatrix]
  -- inner v A = inner (diag nv) (φ A) for A ∈ region
  have hinner_eq : ∀ A, A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ →
      inner ℝ v A = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) (φ A) := by
    intro A hA
    have hAm : (euclidToMatrix A).IsHermitian := by
      have hmem : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
        (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
      rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmem
      exact hmem.1
    calc
      inner ℝ v A = inner ℝ (matrixToEuclid S) (matrixToEuclid (euclidToMatrix A)) := by
            dsimp [S]
            exact inner_symm_of_region_mem v A hA
      _ = inner ℝ (matrixToEuclid (O.transpose * S * O))
            (matrixToEuclid (O.transpose * (euclidToMatrix A) * O)) := by
            exact inner_matrixToEuclid_orthogonal_conj S (euclidToMatrix A) O hOorth
      _ = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) (φ A) := by
            dsimp [φ]
            rw [hdiag']
  -- supportFunction v = sSup {inner v A | A ∈ region} = sSup {inner (diag nv) B | B ∈ region}
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

lemma symmEuclid_diag_eigenvalues₀ (ν : Fin 3 → ℝ) (hν : Antitone ν) :
    (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν))).eigenvalues₀ = ν := by
  have hsymm : symmEuclid (matrixToEuclid (Matrix.diagonal ν)) = Matrix.diagonal ν := by
    ext i j
    dsimp [symmEuclid, euclidToMatrix]
    by_cases h : i = j
    · simp [h, matrixToEuclid, Matrix.diagonal]
      ring
    · simp [h, matrixToEuclid, Matrix.diagonal, Ne.symm h]
  have hchar : (symmEuclid (matrixToEuclid (Matrix.diagonal ν))).charpoly =
      (Matrix.diagonal ν).charpoly := by
    rw [hsymm]
  have heig' : (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν))).eigenvalues₀ =
      (Matrix.isHermitian_diagonal ν).eigenvalues₀ :=
    eigenvalues₀_eq_of_charpoly_eq_real
      (symmEuclid_isHermitian (matrixToEuclid (Matrix.diagonal ν)))
      (Matrix.isHermitian_diagonal ν) hchar
  have heig : (Matrix.isHermitian_diagonal ν).eigenvalues₀ = ν :=
    diagonal_eigenvalues₀_eq_of_antitone ν hν
  exact heig'.trans heig

theorem hamiltonIveyConvexMatrixRegionSupportEuclid_eq_supportFunction
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (symmEuclid_isHermitian v).eigenvalues₀ 0 < 0) :
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ v =
      supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ) v := by
  let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (symmEuclid_isHermitian v).eigenvalues₀_antitone
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hdef : hamiltonIveyConvexMatrixRegionSupportEuclid K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal nv)) := by
    unfold hamiltonIveyConvexMatrixRegionSupportEuclid
    rw [symmEuclid_diag_eigenvalues₀ nv hnv_anti]
  calc
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ v
        = hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal nv)) := hdef
    _ = supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ)
          (matrixToEuclid (Matrix.diagonal nv)) :=
          hamiltonIveyConvexMatrixRegionSupportEuclid_diag_eq_supportFunction hK hτ hnv_anti hnv0
    _ = supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ) v :=
          (supportFunction_rotate_diag v).symm

lemma exists_rotate_diag_of_mem_region
    {K τ : ℝ}
    (v A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
      B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
      inner ℝ v A =
        inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
  rcases hermitian_orthogonal_diagonalization (symmEuclid_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let B : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclid (O.transpose * euclidToMatrix A * O)
  have hB : B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
    have hAm : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O) hOorth2 hOorth).1 hAm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    dsimp [B]
    simpa [euclidToMatrix_matrixToEuclid] using hconj
  have hinner :
      inner ℝ v A = inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
    have hAm : (euclidToMatrix A).IsHermitian := by
      have hmem : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
        (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
      rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmem
      exact hmem.1
    have hsymm : inner ℝ v A = inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid (euclidToMatrix A)) := by
      simpa [matrixToEuclid_euclidToMatrix] using inner_matrixToEuclid_symm v (euclidToMatrix A) hAm
    have hdiagO : inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid (euclidToMatrix A)) =
        inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
      have hconj := inner_matrixToEuclid_orthogonal_conj (symmEuclid v) (euclidToMatrix A) O hOorth
      dsimp [B]
      rw [hconj]
      -- Oᵀ (symm v) O = diag (eigenvalues₀)
      have hdiag' : O.transpose * symmEuclid v * O =
          Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀ := by
        simpa using hdiag
      rw [hdiag']
      rfl
    rw [hsymm]
    exact hdiagO
  exact ⟨B, hB, hinner⟩

lemma hamiltonIveyConvexMatrixRegionSupportEuclid_rotate_diag
    {K τ : ℝ}
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    hamiltonIveyConvexMatrixRegionSupportEuclid K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ
        (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) := by
  let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (symmEuclid_isHermitian v).eigenvalues₀_antitone
  unfold hamiltonIveyConvexMatrixRegionSupportEuclid
  rw [symmEuclid_diag_eigenvalues₀ nv hnv_anti]

lemma inner_le_supportFunction_of_mem_region
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (symmEuclid_isHermitian v).eigenvalues₀ 0 < 0)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    inner ℝ v A ≤ hamiltonIveyConvexMatrixRegionSupportEuclid K τ v := by
  rcases exists_rotate_diag_of_mem_region v A hA with ⟨B, hB, hinner⟩
  let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
  have hnv_anti : Antitone nv := by
    dsimp [nv]
    exact (symmEuclid_isHermitian v).eigenvalues₀_antitone
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hBle : inner ℝ (matrixToEuclid (Matrix.diagonal nv)) B ≤
      hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal nv)) := by
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hB
    have hle1 := inner_le_support_formula_of_mem_region hnv_anti hnv0 (euclidToMatrix B) hBm
    have hFle := support_formula_le_supportFunction_diag hK hτ hnv_anti hnv0
      (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0)
    have hdef : hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal nv)) =
        supportFunction (hamiltonIveyConvexMatrixRegionEuclid K τ) (matrixToEuclid (Matrix.diagonal nv)) :=
      hamiltonIveyConvexMatrixRegionSupportEuclid_diag_eq_supportFunction hK hτ hnv_anti hnv0
    have hle2 : hamiltonIveyConvexBarrier K τ (max (-sectionalRayleighMin3 (euclidToMatrix B)) 0) * nv 0 +
          max (-sectionalRayleighMin3 (euclidToMatrix B)) 0 * (2 * nv 0 - nv 1 - nv 2) ≤
        hamiltonIveyConvexMatrixRegionSupportEuclid K τ (matrixToEuclid (Matrix.diagonal nv)) := by
      rw [hdef]
      exact hFle
    exact le_trans hle1 hle2
  have hinner' : inner ℝ v A = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) B := by
    simpa [nv] using hinner
  rw [hamiltonIveyConvexMatrixRegionSupportEuclid_rotate_diag]
  rw [hinner']
  exact hBle

lemma support_formula_unbounded_of_nonneg_top
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
      -- h(τ,X) = X(L − 3) ≥ X for L ≥ 4
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
      -- barrier = X·(log(X/K)+log(1+2Kτ)−3) ≥ X·(4−3) = X
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

lemma exists_rotate_preimage_of_mem_region
    {K τ : ℝ}
    (v B : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hB : B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ) :
    ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
      A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
      inner ℝ v A =
        inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
  rcases hermitian_orthogonal_diagonalization (symmEuclid_isHermitian v) with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let A : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclid (O * euclidToMatrix B * O.transpose)
  have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hB
    have hconj := (hamiltonIveyConvexMatrixRegion_orthogonal_conj
      (Q := O.transpose) (by simpa using hOorth) (by simpa using hOorth2)).1 hBm
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    dsimp [A]
    simpa [euclidToMatrix_matrixToEuclid, Matrix.transpose_transpose] using hconj
  have hinner : inner ℝ v A =
      inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
    have hBm : euclidToMatrix B ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ B).1 hB
    have hBh : (euclidToMatrix B).IsHermitian := by
      rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hBm
      exact hBm.1
    have hsymm : inner ℝ v A = inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid (euclidToMatrix A)) := by
      have hAh : (euclidToMatrix A).IsHermitian := by
        have hAm : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
          (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
        rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hAm
        exact hAm.1
      simpa [matrixToEuclid_euclidToMatrix] using inner_matrixToEuclid_symm v (euclidToMatrix A) hAh
    have hconj := inner_matrixToEuclid_orthogonal_conj (symmEuclid v) (euclidToMatrix A) O hOorth
    have hdiag' : O.transpose * symmEuclid v * O =
        Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀ := by
      simpa using hdiag
    calc
      inner ℝ v A = inner ℝ (matrixToEuclid (symmEuclid v)) (matrixToEuclid (euclidToMatrix A)) := hsymm
      _ = inner ℝ (matrixToEuclid (O.transpose * symmEuclid v * O))
            (matrixToEuclid (O.transpose * euclidToMatrix A * O)) := hconj
      _ = inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀))
            (matrixToEuclid (O.transpose * euclidToMatrix A * O)) := by
            rw [hdiag']
            rfl
      _ = inner ℝ (matrixToEuclid (Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀)) B := by
            dsimp [A]
            rw [euclidToMatrix_matrixToEuclid]
            have hmat : O.transpose * (O * euclidToMatrix B * O.transpose) * O = euclidToMatrix B := by
              simp only [Matrix.mul_assoc]
              rw [hOorth2]
              simp only [Matrix.mul_one]
              rw [← Matrix.mul_assoc]
              rw [hOorth2]
              simp only [Matrix.one_mul]
            rw [hmat, matrixToEuclid_euclidToMatrix]
  exact ⟨A, hA, hinner⟩

lemma mem_finiteSupportDirections_hamiltonIvey_region_iff
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K τ) ↔
      (symmEuclid_isHermitian v).eigenvalues₀ 0 < 0 ∨ symmEuclid v = 0 := by
  constructor
  · intro hv
    by_contra h
    have hν0ge : ¬ (symmEuclid_isHermitian v).eigenvalues₀ 0 < 0 := by
      intro hneg
      exact h (Or.inl hneg)
    have hsymm_ne : symmEuclid v ≠ 0 := by
      intro hz
      exact h (Or.inr hz)
    have hν0 : 0 ≤ (symmEuclid_isHermitian v).eigenvalues₀ 0 := le_of_not_gt hν0ge
    let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
    have hnv_anti : Antitone nv := by
      dsimp [nv]
      exact (symmEuclid_isHermitian v).eigenvalues₀_antitone
    have hnv_ne : nv ≠ 0 := by
      intro hnv0
      apply hsymm_ne
      rcases hermitian_orthogonal_diagonalization (symmEuclid_isHermitian v) with ⟨O, hOorth, hdiag⟩
      have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
      have hnv0' : (symmEuclid_isHermitian v).eigenvalues₀ = 0 := by
        simpa [nv] using hnv0
      have hd : Matrix.diagonal (symmEuclid_isHermitian v).eigenvalues₀ = 0 := by
        rw [hnv0']
        ext i j
        simp [Matrix.diagonal]
      have hdiag0 : O.transpose * symmEuclid v * O = 0 := by
        simpa [hd] using hdiag
      calc
        symmEuclid v = O * (O.transpose * symmEuclid v * O) * O.transpose := by
          simp only [Matrix.mul_assoc]
          rw [hOorth]
          simp only [Matrix.mul_one]
          rw [← Matrix.mul_assoc]
          rw [hOorth]
          simp
        _ = O * 0 * O.transpose := by rw [hdiag0]
        _ = 0 := by simp
    have hbdd_diag : BddAbove {x : ℝ | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
        B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
          x = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) B} := by
      rcases hv with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro x ⟨B, hB, rfl⟩
      rcases exists_rotate_preimage_of_mem_region v B hB with ⟨A, hA, hinner⟩
      have hinner' : inner ℝ v A = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) B := by
        simpa [nv] using hinner
      have hle : inner ℝ v A ≤ C := hC ⟨A, hA, rfl⟩
      rwa [hinner'] at hle
    have hFsubset : {x : ℝ | ∃ X : ℝ, K / (1 + 4 * K * τ) ≤ X ∧
          x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} ⊆
        {x : ℝ | ∃ B : EuclideanSpace ℝ (Fin 3 × Fin 3),
          B ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧
            x = inner ℝ (matrixToEuclid (Matrix.diagonal nv)) B} := by
      rintro x ⟨X, hX₀le, rfl⟩
      let l : Fin 3 → ℝ := ![hamiltonIveyConvexBarrier K τ X + 2 * X, -X, -X]
      have hDmem : Matrix.diagonal l ∈ hamiltonIveyConvexMatrixRegion K τ :=
        diagonal_extremal_mem_region hK hτ hX₀le
      have hDmemE : matrixToEuclid (Matrix.diagonal l) ∈ hamiltonIveyConvexMatrixRegionEuclid K τ := by
        rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
        simpa [l, euclidToMatrix_matrixToEuclid] using hDmem
      have hinner : inner ℝ (matrixToEuclid (Matrix.diagonal nv)) (matrixToEuclid (Matrix.diagonal l)) =
          hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2) := by
        have hdd := inner_diag_diag nv l
        rw [hdd]
        simp [l, Fin.sum_univ_three]
        ring
      exact ⟨matrixToEuclid (Matrix.diagonal l), hDmemE, hinner.symm⟩
    have hbddF : BddAbove {x : ℝ | ∃ X : ℝ, K / (1 + 4 * K * τ) ≤ X ∧
          x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} :=
      BddAbove.mono hFsubset hbdd_diag
    exact (support_formula_unbounded_of_nonneg_top hK hτ hnv_anti hν0 hnv_ne) hbddF
  · rintro (hv | hsymm0)
    · -- ν̃₁ < 0: finite via bound
      have hbdd : BddAbove {x : ℝ | ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
          A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ x = inner ℝ v A} := by
        refine ⟨hamiltonIveyConvexMatrixRegionSupportEuclid K τ v, ?_⟩
        rintro x ⟨A, hA, rfl⟩
        exact inner_le_supportFunction_of_mem_region hK hτ v hv A hA
      exact hbdd
    · -- symm v = 0: inner v A = 0 for all A ∈ region
      have hbdd : BddAbove {x : ℝ | ∃ A : EuclideanSpace ℝ (Fin 3 × Fin 3),
          A ∈ hamiltonIveyConvexMatrixRegionEuclid K τ ∧ x = inner ℝ v A} := by
        refine ⟨0, ?_⟩
        rintro x ⟨A, hA, rfl⟩
        have hAh : (euclidToMatrix A).IsHermitian := by
          have hAm : euclidToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ :=
            (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ A).1 hA
          rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hAm
          exact hAm.1
        have hz : inner ℝ v A = 0 := by
          have h := inner_matrixToEuclid_symm v (euclidToMatrix A) hAh
          rw [hsymm0] at h
          have hzero : inner ℝ (matrixToEuclid 0) (matrixToEuclid (euclidToMatrix A)) = 0 := by
            rw [inner_matrixToEuclid]
            simp [matrixToEuclid]
          have hmain : inner ℝ v (matrixToEuclid (euclidToMatrix A)) = 0 := h.trans hzero
          simpa [matrixToEuclid_euclidToMatrix] using hmain
        rw [hz]
      exact hbdd

lemma continuousOn_sSup_image_Icc
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


lemma support_formula_continuousOn
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
      -- log(X(1+2Kτ)/K) ≥ log(X/K) ≥ log(Xmax/K) = S/ν0
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
    -- hbddF : BddAbove {x | ∃X ≥ 0, x = barrier-formula} — the formula is F τ X
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

theorem hamiltonIveyConvexMatrixRegionSupportEuclid_continuousOn
    {K T : ℝ} (hK : 0 < K)
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hv : (symmEuclid_isHermitian v).eigenvalues₀ 0 < 0) :
    ContinuousOn (fun τ : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclid K τ v) (Set.Icc 0 T) := by
  let nv : Fin 3 → ℝ := (symmEuclid_isHermitian v).eigenvalues₀
  have hnv0 : nv 0 < 0 := by
    simpa [nv] using hv
  have hmain := support_formula_continuousOn (K := K) (T := T) hK (ν := nv) hnv0
  have hdef : ∀ τ : ℝ, hamiltonIveyConvexMatrixRegionSupportEuclid K τ v =
      sSup {x : ℝ | ∃ X : ℝ, 0 ≤ X ∧
        x = hamiltonIveyConvexBarrier K τ X * nv 0 + X * (2 * nv 0 - nv 1 - nv 2)} := by
    intro τ
    unfold hamiltonIveyConvexMatrixRegionSupportEuclid
    dsimp [nv]
    rw [if_pos hv]
    rfl
  exact hmain.congr (fun τ hτ => hdef τ)

lemma support_formula_min_branch
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


lemma hamiltonIveyBarrier_at_star_point
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

lemma support_formula_at_star_point
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {ν : Fin 3 → ℝ} (hν0 : ν 0 < 0) :
    hamiltonIveyConvexBarrier K τ (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * ν 0 +
        (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2) =
      min (scalarSectionalLowerBarrier3 K τ * ν 0 +
            (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)) * (2 * ν 0 - ν 1 - ν 2))
        (-(ν 0 * (K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)))) := by
  let Xs : ℝ := K * Real.exp ((ν 1 + ν 2) / ν 0) / (1 + 2 * K * τ)
  have hmin := support_formula_min_branch (K := K) (τ := τ) hν0 Xs
  -- hmin : B K τ Xs * ν0 + Xs*c = min (s*ν0 + Xs*c) (h-barrier*ν0 + Xs*c)
  -- and h-barrier*ν0 + Xs*c = −ν0·Xs via hamiltonIveyBarrier_at_star_point
  have hbar := hamiltonIveyBarrier_at_star_point (K := K) (τ := τ) (ν := ν) hK hτ
  have hb : hamiltonIveyBarrier K τ Xs * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) =
      -(ν 0 * Xs) := by
    rw [hbar]
    have hcalc : Xs * ((ν 1 + ν 2) / ν 0 - 3) * ν 0 + Xs * (2 * ν 0 - ν 1 - ν 2) =
        -(ν 0 * Xs) := by
      -- Xs·((ν1+ν2)/ν0 − 3)·ν0 + Xs·(2ν0−ν1−ν2) = Xs·(ν1+ν2 − 3ν0 + 2ν0 −ν1 −ν2) = −ν0Xs
      field_simp [Ne.symm hν0.ne']
      ring
    simp [Xs, hcalc]
  rw [hmin, hb]



lemma hasDerivAt_scalarSectionalLowerBarrier3
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

lemma hasDerivAt_star_point
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

lemma hasDerivAt_candidate_A
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

lemma hasDerivAt_candidate_B
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

lemma hasDerivAt_hamiltonIveyBarrier_x
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

lemma deriv_hamiltonIveyBarrier_x
    {K τ X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    deriv (fun Y : ℝ => hamiltonIveyBarrier K τ Y) X =
      Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2 :=
  (hasDerivAt_hamiltonIveyBarrier_x hK hX).deriv


lemma monotoneOn_Fh_left
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

lemma antitoneOn_Fh_right
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

lemma support_formula_le_candidate_star_of_le
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

lemma strictMonoOn_hamiltonIveyBarrier_above_E
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

lemma hamiltonIveyBarrier_gt_scalarLower_at_exp_four
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

lemma hamiltonIveyBarrier_lt_scalarLower_at_E
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

lemma exists_kink_point
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

noncomputable def hamiltonIveyKinkPoint {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) : ℝ :=
  Classical.choose (exists_kink_point hK hτ)

lemma hamiltonIveyKinkPoint_spec
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    K * Real.exp 2 / (1 + 2 * K * τ) < hamiltonIveyKinkPoint hK hτ ∧
      hamiltonIveyBarrier K τ (hamiltonIveyKinkPoint hK hτ) = scalarSectionalLowerBarrier3 K τ :=
  Classical.choose_spec (exists_kink_point hK hτ)

end DifferentialGeometry.PDE.RicciFlow

end
