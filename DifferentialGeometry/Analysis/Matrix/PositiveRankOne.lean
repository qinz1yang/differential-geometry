import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


noncomputable section

open Filter
open scoped BigOperators ContDiff Topology MatrixOrder Matrix.Norms.Elementwise

namespace DifferentialGeometry.Analysis

private def coordinateVector {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℝ :=
  Pi.single i 1

private theorem sum_rank_one_pairs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsSymm) (ε : ℝ) (p q : ι) :
    (∑ i, ∑ j,
      ((ε + B i j / 4) * ((coordinateVector i : ι → ℝ) p + coordinateVector j p) *
          (coordinateVector i q + coordinateVector j q) +
        (ε - B i j / 4) * (coordinateVector i p - coordinateVector j p) *
          (coordinateVector i q - coordinateVector j q))) =
      4 * (Fintype.card ι : ℝ) * ε * (if p = q then 1 else 0) + B p q := by
  have hpair (i j : ι) :
      ((ε + B i j / 4) * ((coordinateVector i : ι → ℝ) p + coordinateVector j p) *
          (coordinateVector i q + coordinateVector j q) +
        (ε - B i j / 4) * (coordinateVector i p - coordinateVector j p) *
          (coordinateVector i q - coordinateVector j q)) =
      2 * ε * (coordinateVector i p * coordinateVector i q) +
        2 * ε * (coordinateVector j p * coordinateVector j q) +
        B i j / 2 * (coordinateVector i p * coordinateVector j q) +
        B i j / 2 * (coordinateVector j p * coordinateVector i q) := by
    ring
  simp_rw [hpair]
  simp only [Finset.sum_add_distrib]
  have hdiag : (∑ i : ι, (coordinateVector i : ι → ℝ) p * coordinateVector i q) =
      if p = q then 1 else 0 := by
    simp [coordinateVector, Pi.single_apply, mul_ite]
  have hfirst : (∑ i : ι, ∑ j : ι,
      2 * ε * ((coordinateVector i : ι → ℝ) p * coordinateVector i q)) =
      (Fintype.card ι : ℝ) * (2 * ε) * (if p = q then 1 else 0) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hdiag]
    ring
  have hsecond : (∑ i : ι, ∑ j : ι,
      2 * ε * ((coordinateVector j : ι → ℝ) p * coordinateVector j q)) =
      (Fintype.card ι : ℝ) * (2 * ε) * (if p = q then 1 else 0) := by
    simp only [← Finset.mul_sum, hdiag, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hthird : (∑ i : ι, ∑ j : ι,
      B i j / 2 * ((coordinateVector i : ι → ℝ) p * coordinateVector j q)) = B p q / 2 := by
    simp [coordinateVector, Pi.single_apply, mul_ite]
  have hfourth : (∑ i : ι, ∑ j : ι,
      B i j / 2 * ((coordinateVector j : ι → ℝ) p * coordinateVector i q)) = B q p / 2 := by
    simp [coordinateVector, Pi.single_apply, mul_ite]
  rw [hfirst, hsecond, hthird, hfourth, hB.apply p q]
  ring

private theorem exists_positive_rank_one_near_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ (v : ι ⊕ ((ι × ι) ⊕ (ι × ι)) → ι → ℝ)
      (a : ι ⊕ ((ι × ι) ⊕ (ι × ι)) → Matrix ι ι ℝ → ℝ),
      (∀ k, ContDiff ℝ ∞ (a k)) ∧
      (∀ᶠ A in 𝓝 (1 : Matrix ι ι ℝ), ∀ k, 0 < a k A) ∧
      ∀ A : Matrix ι ι ℝ, A.IsSymm →
        ∀ i j, A i j = ∑ k, a k A * v k i * v k j := by
  let ε : ℝ := (8 * ((Fintype.card ι : ℝ) + 1))⁻¹
  let d : ℝ := 1 - 4 * (Fintype.card ι : ℝ) * ε
  let v : ι ⊕ ((ι × ι) ⊕ (ι × ι)) → ι → ℝ :=
    Sum.elim (fun i ↦ coordinateVector i)
      (Sum.elim (fun ij ↦ coordinateVector ij.1 + coordinateVector ij.2)
        (fun ij ↦ coordinateVector ij.1 - coordinateVector ij.2))
  let a : ι ⊕ ((ι × ι) ⊕ (ι × ι)) → Matrix ι ι ℝ → ℝ :=
    Sum.elim (fun _ _ ↦ d)
      (Sum.elim (fun ij A ↦ ε + (A - 1) ij.1 ij.2 / 4)
        (fun ij A ↦ ε - (A - 1) ij.1 ij.2 / 4))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hd : 0 < d := by
    have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have hden : 0 < 8 * ((Fintype.card ι : ℝ) + 1) := by positivity
    dsimp [d, ε]
    apply (mul_pos_iff_of_pos_right hden).mp
    field_simp
    ring_nf
    positivity
  have ha (k) : ContDiff ℝ ∞ (a k) := by
    rcases k with i | ij
    · exact contDiff_const
    · rcases ij with ij | ij
      · exact contDiff_const.add
          (((contDiff_apply_apply ℝ ℝ ij.1 ij.2).sub contDiff_const).div_const 4)
      · exact contDiff_const.sub
          (((contDiff_apply_apply ℝ ℝ ij.1 ij.2).sub contDiff_const).div_const 4)
  have ha1 (k) : 0 < a k 1 := by
    rcases k with i | ij
    · exact hd
    · rcases ij with ij | ij <;> simpa [a] using hε
  refine ⟨v, a, ha, ?_, ?_⟩
  · rw [eventually_all]
    intro k
    exact (ha k).continuous.continuousAt.tendsto.eventually_const_lt (ha1 k)
  · intro A hA p q
    have hB : (A - 1).IsSymm := hA.sub Matrix.isSymm_one
    have hsum := sum_rank_one_pairs (A - 1) hB ε p q
    have hdiag : (∑ i : ι, d * (coordinateVector i : ι → ℝ) p * coordinateVector i q) =
        d * (if p = q then 1 else 0) := by
      simp [coordinateVector, Pi.single_apply, mul_ite]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, a, v, Sum.elim_inl,
      Sum.elim_inr, Pi.add_apply, Pi.sub_apply]
    simp only [Finset.sum_add_distrib] at hsum
    rw [hsum, hdiag]
    simp only [Matrix.sub_apply, Matrix.one_apply, d]
    ring

private theorem exists_invertible_mul_transpose_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ C : Matrix ι ι ℝ, IsUnit C.det ∧ A = C * C.transpose := by
  obtain ⟨C, hC⟩ :=
    CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hA.posSemidef.nonneg
  have hfactor : A = C * C.transpose := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hC
  refine ⟨C, ?_, hfactor⟩
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [hfactor, Matrix.det_mul, Matrix.det_transpose] at hd
  exact isUnit_of_mul_isUnit_left hd

private theorem contDiff_matrix_congruence
    {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ) :
    ContDiff ℝ ∞ (fun A : Matrix ι ι ℝ ↦ C * A * C.transpose) := by
  refine contDiff_pi.2 fun i ↦ contDiff_pi.2 fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine ContDiff.sum fun k _ ↦ ?_
  refine ContDiff.mul ?_ contDiff_const
  exact ContDiff.sum fun l _ ↦
    contDiff_const.mul (contDiff_apply_apply ℝ ℝ l k)

theorem exists_contDiff_positive_rank_one_decomposition
    {ι : Type*} [Fintype ι] {A₀ : Matrix ι ι ℝ} (hA₀ : A₀.PosDef) :
    ∃ (N : ℕ) (v : Fin N → ι → ℝ) (a : Fin N → Matrix ι ι ℝ → ℝ),
      (∀ k, ContDiff ℝ ∞ (a k)) ∧
      (∀ᶠ A in 𝓝 A₀, ∀ k, 0 < a k A) ∧
      ∀ A : Matrix ι ι ℝ, A.IsSymm →
        ∀ i j, A i j = ∑ k, a k A * v k i * v k j := by
  classical
  obtain ⟨C, hC, hfactor⟩ := exists_invertible_mul_transpose_of_posDef hA₀
  let F : Matrix ι ι ℝ → Matrix ι ι ℝ := fun A ↦ C⁻¹ * A * C⁻¹.transpose
  have hF : ContDiff ℝ ∞ F := contDiff_matrix_congruence C⁻¹
  have hF₀ : F A₀ = 1 := by
    calc
      F A₀ = (C⁻¹ * C) * (C⁻¹ * C).transpose := by
        simp only [F, hfactor, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul C hC]; simp
  have hsymm {A : Matrix ι ι ℝ} (hA : A.IsSymm) : (F A).IsSymm := by
    change (C⁻¹ * A * C⁻¹.transpose).transpose = _
    simp only [F, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
      Matrix.mul_assoc]
  have hrec (A : Matrix ι ι ℝ) : C * F A * C.transpose = A := by
    calc
      C * F A * C.transpose = (C * C⁻¹) * A * (C * C⁻¹).transpose := by
        simp only [F, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [Matrix.mul_nonsing_inv C hC]; simp
  obtain ⟨w, b, hb, hpos, hrep⟩ := exists_positive_rank_one_near_one (ι := ι)
  let κ := ι ⊕ ((ι × ι) ⊕ (ι × ι))
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let v : Fin (Fintype.card κ) → ι → ℝ := fun k ↦ C.mulVec (w (e k))
  let a : Fin (Fintype.card κ) → Matrix ι ι ℝ → ℝ := fun k A ↦ b (e k) (F A)
  refine ⟨Fintype.card κ, v, a, ?_, ?_, ?_⟩
  · intro k
    exact (hb (e k)).comp hF
  · have hnear : ∀ᶠ A in 𝓝 A₀, ∀ k, 0 < b k (F A) := by
      have ht : Tendsto F (𝓝 A₀) (𝓝 (1 : Matrix ι ι ℝ)) := by
        rw [← hF₀]
        exact hF.continuous.continuousAt.tendsto
      exact ht.eventually hpos
    filter_upwards [hnear] with A hA k
    exact hA (e k)
  · intro A hA i j
    have hdec : F A = ∑ k, b k (F A) • Matrix.vecMulVec (w k) (w k) := by
      ext p q
      simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, mul_assoc] using hrep (F A) (hsymm hA) p q
    have hentry : A i j =
        ∑ k : κ, b k (F A) * C.mulVec (w k) i * C.mulVec (w k) j := by
      calc
        A i j = (C * F A * C.transpose) i j := by rw [hrec]
        _ = _ := by
          nth_rw 1 [hdec]
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
            Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            smul_eq_mul, mul_assoc]
          rfl
    rw [hentry]
    exact (Equiv.sum_comp e (fun k : κ ↦
      b k (F A) * C.mulVec (w k) i * C.mulVec (w k) j)).symm

end DifferentialGeometry.Analysis
