import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
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

end DifferentialGeometry.PDE.RicciFlow

end
