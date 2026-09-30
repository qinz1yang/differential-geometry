import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Ball
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def exponentialBallBarrier (R k : ℝ) (x : V) : ℝ :=
  Real.exp (k * R ^ 2) - Real.exp (k * ‖x‖ ^ 2)

theorem contDiff_exponentialBallBarrier (R k : ℝ) :
    ContDiff ℝ ∞ (exponentialBallBarrier (d := d) R k) :=
  contDiff_const.sub ((contDiff_const.mul (contDiff_id.norm_sq ℝ)).exp)

theorem exponentialBallBarrier_nonneg {R k : ℝ} (hR : 0 ≤ R) (hk : 0 ≤ k)
    {x : V} (hx : x ∈ Metric.closedBall (0 : V) R) :
    0 ≤ exponentialBallBarrier R k x := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hk
  exact (sq_le_sq₀ (norm_nonneg x) hR).mpr (by simpa using hx)

theorem exponentialBallBarrier_nonpos {R k : ℝ} (hR : 0 ≤ R) (hk : 0 ≤ k)
    {x : V} (hx : x ∉ Metric.closedBall (0 : V) R) :
    exponentialBallBarrier R k x ≤ 0 := by
  apply sub_nonpos.mpr
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hk
  apply (sq_le_sq₀ hR (norm_nonneg x)).mpr
  exact le_of_lt (by simpa using hx)

theorem exponentialBallBarrier_eq_zero {R k : ℝ}
    {x : V} (hx : x ∈ Metric.sphere (0 : V) R) : exponentialBallBarrier R k x = 0 := by
  have he : ‖x‖ = R := by simpa using hx
  simp only [exponentialBallBarrier, he, sub_self]

theorem memW01p_exponentialBallBarrier [NeZero d] {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k) :
    DeGiorgi.MemW01p 2 (exponentialBallBarrier (d := d) R k) (Metric.ball (0 : V) R) := by
  have hp := DeGiorgi.memW01p_pos_part_of_nonpos_outside_closedBall (d := d)
    ((contDiff_exponentialBallBarrier R k).of_le (by norm_cast)) 0 hR
    (fun x hx => exponentialBallBarrier_nonpos hR.le hk hx)
  apply hp.congr
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact max_eq_left (exponentialBallBarrier_nonneg hR.le hk (Metric.ball_subset_closedBall hx))

theorem smoothGradField_exponentialBallBarrier (R k : ℝ) (x : V) (j : Fin d) :
    DeGiorgi.smoothGradField (exponentialBallBarrier R k) x j =
      -(2 * k * Real.exp (k * ‖x‖ ^ 2) * x j) := by
  have hs := ((hasFDerivAt_id x).norm_sq.const_mul k).exp
  have hb := (hasFDerivAt_const (Real.exp (k * R ^ 2)) x).sub hs
  have he := hb.fderiv
  change fderiv ℝ (exponentialBallBarrier R k) x = _ at he
  change fderiv ℝ (exponentialBallBarrier R k) x (EuclideanSpace.single j 1) = _
  rw [he]
  simp [PiLp.inner_apply]
  ring


theorem fderiv_smoothGradField_exponentialBallBarrier
    (R k : ℝ) (x : V) (i j : Fin d) :
    fderiv ℝ (fun y => DeGiorgi.smoothGradField (exponentialBallBarrier R k) y j)
      x (EuclideanSpace.single i 1) =
      -(2 * k * Real.exp (k * ‖x‖ ^ 2) *
        (2 * k * x i * x j + if i = j then 1 else 0)) := by
  have hs := ((hasFDerivAt_id x).norm_sq.const_mul k).exp
  have hp := (EuclideanSpace.proj j : V →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd := (((hs.const_mul k).const_mul 2).mul hp).neg
  have he := hd.fderiv
  change fderiv ℝ (fun y => -(2 * (k * Real.exp (k * ‖y‖ ^ 2)) * y j)) x = _ at he
  have hf : (fun y => DeGiorgi.smoothGradField (exponentialBallBarrier R k) y j) =
      fun y => -(2 * (k * Real.exp (k * ‖y‖ ^ 2)) * y j) := by
    funext y
    rw [smoothGradField_exponentialBallBarrier]
    ring
  rw [hf, he]
  simp only [neg_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, innerSL_apply_apply, smul_eq_mul]
  simp only [EuclideanSpace.coe_proj, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, PiLp.single_apply]
  by_cases hij : i = j
  · subst j
    ring
  · simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    ring

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem divergence_exponentialBallBarrier
    (R k : ℝ) (A : V → Matrix (Fin d) (Fin d) ℝ) (x : V)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (A y)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x
      (EuclideanSpace.single i 1)) =
      -(2 * k * Real.exp (k * ‖x‖ ^ 2)) *
        ((∑ i, A x i i) +
          (∑ i, ∑ j, fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1) * x j) +
          2 * k * inner ℝ x (DeGiorgi.matMulE (A x) x)) := by
  let G := DeGiorgi.smoothGradField (exponentialBallBarrier (d := d) R k)
  have hG (j : Fin d) : DifferentiableAt ℝ (fun y => G y j) x := by
    have he : (fun y => G y j) = fun y =>
        -(2 * k * Real.exp (k * ‖y‖ ^ 2) * y j) := by
      funext y
      exact smoothGradField_exponentialBallBarrier R k y j
    rw [he]
    have hE : ContDiff ℝ 1 (fun y : V => Real.exp (k * ‖y‖ ^ 2)) :=
      (contDiff_const.mul (contDiff_id.norm_sq ℝ)).exp
    have hP : ContDiff ℝ 1 (fun y : V => y j) := contDiff_piLp_apply 2
    have hc : ContDiff ℝ 1 (fun y : V => -(2 * k * Real.exp (k * ‖y‖ ^ 2) * y j)) :=
      ((contDiff_const.mul hE).mul hP).neg
    exact hc.differentiable one_ne_zero x
  have hpart (i j : Fin d) :
      fderiv ℝ (fun y => A y i j * G y j) x (EuclideanSpace.single i 1) =
        -(2 * k * Real.exp (k * ‖x‖ ^ 2)) *
          (fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1) * x j +
            A x i j * (if i = j then 1 else 0) + 2 * k * x i * A x i j * x j) := by
    have hh := ((hA i j).hasFDerivAt.mul (hG j).hasFDerivAt).fderiv
    change fderiv ℝ (fun y : V => A y i j * G y j) x = _ at hh
    rw [hh]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show G x j = _ from smoothGradField_exponentialBallBarrier R k x j]
    rw [show fderiv ℝ (fun y => G y j) x (EuclideanSpace.single i 1) = _ from
      fderiv_smoothGradField_exponentialBallBarrier R k x i j]
    ring
  have hsum (i : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.matMulE (A y) (G y) i) x (EuclideanSpace.single i 1) =
        ∑ j, fderiv ℝ (fun y => A y i j * G y j) x (EuclideanSpace.single i 1) := by
    change fderiv ℝ (fun y => ∑ j, A y i j * G y j) x (EuclideanSpace.single i 1) = _
    have hh := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((hA i j).mul (hG j)).hasFDerivAt)
    have he := hh.fderiv
    change fderiv ℝ (fun y : V => ∑ j, A y i j * G y j) x = _ at he
    rw [he]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hf : ((fun y : V => A y i j) * (fun y => G y j)) =
        (fun y => A y i j * G y j) := by funext y; rfl
    rw [hf]
  change (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (A y) (G y) i) x
    (EuclideanSpace.single i 1)) = _
  simp_rw [hsum, hpart, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib]
  have hdiag : (∑ i, ∑ j, A x i j * (if i = j then 1 else 0)) = ∑ i, A x i i := by
    simp [mul_ite]
  rw [hdiag]
  have hquad : (∑ i, ∑ j, 2 * k * x i * A x i j * x j) =
      2 * k * inner ℝ x (DeGiorgi.matMulE (A x) x) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hquad]
  ring

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis
open Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem trace_ge_ellipticity
    (B : SmoothEllipticBilinearForm d (univ : Set V)) (x : V) :
    B.lam ≤ ∑ i, B.a x i i := by
  have hi (i : Fin d) : B.lam ≤ B.a x i i := by
    have hh := B.coercive x (mem_univ x) (EuclideanSpace.single i 1)
    simpa [PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  calc
    B.lam ≤ d * B.lam := by nlinarith [B.ellipticity_pos]
    _ = ∑ _i : Fin d, B.lam := by simp
    _ ≤ _ := hs

theorem exists_exponentialBallBarrier_divergence_le_neg_one
    (B : SmoothEllipticBilinearForm d (univ : Set V)) (R : ℝ) :
    ∃ k : ℝ, 0 < k ∧ ∀ x ∈ Metric.closedBall (0 : V) R,
      (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y)
          (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x
        (EuclideanSpace.single i 1)) ≤ -1 := by
  let D (x : V) : V := WithLp.toLp 2 fun j =>
    ∑ i, fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)
  have hDc : Continuous D := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    apply continuous_pi
    intro j
    apply continuous_finsetSum
    intro i _
    exact ((B.smooth_a i j).continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn hDc.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hlam := B.ellipticity_pos
  let k := M ^ 2 / B.lam ^ 2 + B.lam⁻¹ + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hklam : 1 ≤ k * B.lam := by
    have hh : k * B.lam = M ^ 2 / B.lam + 1 + B.lam := by
      dsimp only [k]
      field_simp [B.ellipticity_pos.ne']
    rw [hh]
    have hn : 0 ≤ M ^ 2 / B.lam := by positivity
    linarith
  have hkquad : M ^ 2 / B.lam ≤ 4 * k * B.lam := by
    have he : 4 * k * B.lam - M ^ 2 / B.lam =
        3 * (M ^ 2 / B.lam) + 4 + 4 * B.lam := by
      dsimp only [k]
      field_simp [B.ellipticity_pos.ne']
      ring
    have hn : 0 ≤ 3 * (M ^ 2 / B.lam) + 4 + 4 * B.lam := by positivity
    linarith
  refine ⟨k, hk, ?_⟩
  intro x hx
  rw [divergence_exponentialBallBarrier R k B.a x
    (fun i j => (B.smooth_a i j).differentiable (by simp) x)]
  have hD : ‖D x‖ ≤ M := (hC x hx).trans (le_max_left _ _)
  have hde : (∑ i, ∑ j,
      fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1) * x j) =
        inner ℝ (D x) x := by
    rw [Finset.sum_comm]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, D,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hde]
  have hDrift : -(M * ‖x‖) ≤ inner ℝ (D x) x :=
    (neg_le_neg (mul_le_mul_of_nonneg_right hD (norm_nonneg x))).trans
      (neg_le_of_abs_le (abs_real_inner_le_norm (D x) x))
  have hYoung : 2 * M * ‖x‖ ≤ B.lam + B.lam⁻¹ * (M * ‖x‖) ^ 2 := by
    simpa only [one_pow, mul_one, one_mul, mul_assoc] using
      (two_mul_le_add_mul_sq (a := (1 : ℝ)) (b := M * ‖x‖) B.ellipticity_pos)
  have hQ := B.coercive x (mem_univ x) x
  have hQmul := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 4 * k)
  have hkbound := mul_le_mul_of_nonneg_right hkquad (sq_nonneg ‖x‖)
  have hT := trace_ge_ellipticity B x
  have hbracket : B.lam / 2 ≤ (∑ i, B.a x i i) +
      inner ℝ (D x) x + 2 * k * inner ℝ x (DeGiorgi.matMulE (B.a x) x) := by
    have he : B.lam⁻¹ * (M * ‖x‖) ^ 2 = M ^ 2 / B.lam * ‖x‖ ^ 2 := by ring
    rw [he] at hYoung
    nlinarith
  have he : 1 ≤ Real.exp (k * ‖x‖ ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hbracket
    (by positivity : 0 ≤ 2 * k * Real.exp (k * ‖x‖ ^ 2))
  have hh : 1 ≤ k * B.lam * Real.exp (k * ‖x‖ ^ 2) := by nlinarith
  nlinarith

end DifferentialGeometry.Analysis

end

end
