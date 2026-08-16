import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckCurvatureOperatorHeatReaction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

def hamiltonIveyMatrixReaction (A : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  2 • (A * A + A.adjugate)

def uhlenbeckCurvatureOperatorReactionState
    (_t : Real) (A : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
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

end DifferentialGeometry.PDE.RicciFlow

end
