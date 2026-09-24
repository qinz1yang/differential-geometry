import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Gradient
import Mathlib.Tactic.LinearCombination

section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

def quadraticBallCutoff (p : V) (R : ℝ) (x : V) : ℝ := R ^ 2 - ‖x - p‖ ^ 2

theorem contDiff_quadraticBallCutoff (p : V) (R : ℝ) :
    ContDiff ℝ ∞ (quadraticBallCutoff p R) :=
  contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)

theorem fderiv_quadraticBallCutoff (p : V) (R : ℝ) (x : V) :
    fderiv ℝ (quadraticBallCutoff p R) x = (-2 : ℝ) • (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (x - p) := by
  have h := ((hasFDerivAt_id x).sub_const p).norm_sq
  have he := (h.const_sub (R ^ 2)).fderiv
  simpa only [quadraticBallCutoff, ContinuousLinearMap.comp_id, neg_smul, id_eq, two_smul] using! he

theorem fderiv_fderiv_quadraticBallCutoff (p : V) (R : ℝ) (x v w : V) :
    fderiv ℝ (fderiv ℝ (quadraticBallCutoff p R)) x v w = -2 * inner ℝ v w := by
  have he : fderiv ℝ (quadraticBallCutoff p R) =
      fun y => (-2 : ℝ) • (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (y - p) :=
    funext (fderiv_quadraticBallCutoff p R)
  rw [he]
  have h := (((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const p)).const_smul (-2 : ℝ)
  have hd : fderiv ℝ (fun y => (-2 : ℝ) • (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (y - p)) x =
      (-2 : ℝ) • (((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)).comp (ContinuousLinearMap.id ℝ V)) := by
    simpa only [Function.comp_apply, Pi.smul_apply, id_eq] using! h.fderiv
  rw [hd]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rfl

theorem scalarEllipticOperator_quadraticBallCutoff [DecidableEq ι]
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) (p : V) (R : ℝ) (x : V) :
    scalarEllipticOperator A b (quadraticBallCutoff p R) x =
      -2 * (∑ i, A x i i) - 2 * ∑ i, b x i * (x i - p i) := by
  simp only [scalarEllipticOperator, fderiv_fderiv_quadraticBallCutoff,
    fderiv_quadraticBallCutoff, smul_apply]
  simp [PiLp.inner_apply, PiLp.single_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  ring

theorem quadraticBallCutoff_nonneg {p x : V} {R : ℝ} (hR : 0 ≤ R)
    (hx : x ∈ Metric.closedBall p R) : 0 ≤ quadraticBallCutoff p R x := by
  have h := Metric.mem_closedBall.mp hx
  rw [dist_eq_norm] at h
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hR).mpr h)

theorem quadraticBallCutoff_le (p : V) (R : ℝ) (x : V) :
    quadraticBallCutoff p R x ≤ R ^ 2 := sub_le_self _ (sq_nonneg _)

theorem quadraticBallCutoff_eq_zero {p x : V} {R : ℝ}
    (hx : x ∈ Metric.sphere p R) : quadraticBallCutoff p R x = 0 := by
  have h := Metric.mem_sphere.mp hx
  rw [dist_eq_norm] at h
  simp only [quadraticBallCutoff, h, sub_self]

theorem abs_fderiv_quadraticBallCutoff_apply_le [DecidableEq ι] {p x : V} {R : ℝ}
    (hx : x ∈ Metric.closedBall p R) (i : ι) :
    |fderiv ℝ (quadraticBallCutoff p R) x (EuclideanSpace.single i 1)| ≤ 2 * R := by
  rw [fderiv_quadraticBallCutoff]
  simp only [smul_apply, smul_eq_mul]
  change |(-2 : ℝ) * inner ℝ (x - p) (EuclideanSpace.single i 1)| ≤ 2 * R
  rw [abs_mul]
  have hn : |inner ℝ (x - p) (EuclideanSpace.single i 1)| ≤ R := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [PiLp.norm_single, norm_one, mul_one, ← dist_eq_norm] using
      Metric.mem_closedBall.mp hx
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "e" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

private theorem two_mul_le_weighted_squares {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    2 * a * b ≤ δ * b ^ 2 + a ^ 2 / δ := by
  apply (mul_le_mul_iff_left₀ hδ).mp
  have hcancel : (δ * b ^ 2 + a ^ 2 / δ) * δ = δ ^ 2 * b ^ 2 + a ^ 2 := by
    field_simp [hδ.ne']
  rw [hcancel]
  nlinarith [sq_nonneg (δ * b - a)]

private theorem abs_sum_three_le (f : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    |∑ i, ∑ j, ∑ k, f i j k| ≤ ∑ i, ∑ j, ∑ k, |f i j k| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact Finset.abs_sum_le_sum_abs _ _

private theorem principal_derivative_term_le
    (g : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (DA : Fin 2 → Fin 2 → Fin 2 → ℝ) {D lam : ℝ}
    (hDA : ∀ k i j, |DA k i j| ≤ D) (hlam : 0 < lam) :
    2 * |∑ k, ∑ i, ∑ j, g k * DA k i j * H i j| ≤
      (lam / 2) * (∑ i, ∑ j, H i j ^ 2) +
        (16 * D ^ 2 / lam) * (∑ k, g k ^ 2) := by
  have hterm (k i j : Fin 2) :
      2 * |g k * DA k i j * H i j| ≤
        (lam / 4) * H i j ^ 2 + (4 * D ^ 2 / lam) * g k ^ 2 := by
    have hy := two_mul_le_weighted_squares (δ := lam / 4) (by positivity)
      (D * |g k|) |H i j|
    have hb : 2 * |g k * DA k i j * H i j| ≤ 2 * (D * |g k|) * |H i j| := by
      simp only [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hDA k i j) (abs_nonneg (g k)),
        mul_nonneg (abs_nonneg (g k)) (abs_nonneg (H i j)),
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hDA k i j) (abs_nonneg (g k)))
          (abs_nonneg (H i j))]
    apply hb.trans
    have he : (lam / 4) * |H i j| ^ 2 + (D * |g k|) ^ 2 / (lam / 4) =
        (lam / 4) * H i j ^ 2 + (4 * D ^ 2 / lam) * g k ^ 2 := by
      simp only [mul_pow, sq_abs]
      field_simp [hlam.ne']
    exact hy.trans_eq he
  calc
    _ ≤ 2 * (∑ k, ∑ i, ∑ j, |g k * DA k i j * H i j|) :=
      mul_le_mul_of_nonneg_left (abs_sum_three_le _) (by norm_num)
    _ = ∑ k, ∑ i, ∑ j, 2 * |g k * DA k i j * H i j| := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ k, ∑ i, ∑ j,
        ((lam / 4) * H i j ^ 2 + (4 * D ^ 2 / lam) * g k ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hterm k i j
    _ = _ := by simp only [Fin.sum_univ_two]; ring

private theorem drift_derivative_term_le
    (g : Fin 2 → ℝ) (Db : Fin 2 → Fin 2 → ℝ) {B : ℝ}
    (hDb : ∀ k j, |Db k j| ≤ B) :
    2 * |∑ k, ∑ j, g k * Db k j * g j| ≤ 4 * B * (∑ k, g k ^ 2) := by
  have hB : 0 ≤ B := (abs_nonneg (Db 0 0)).trans (hDb 0 0)
  have habs : |∑ k, ∑ j, g k * Db k j * g j| ≤
      ∑ k, ∑ j, |g k * Db k j * g j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    exact Finset.abs_sum_le_sum_abs _ _
  have hterm (k j : Fin 2) : 2 * |g k * Db k j * g j| ≤ B * (g k ^ 2 + g j ^ 2) := by
    have hprod := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hDb k j) (abs_nonneg (g k))) (abs_nonneg (g j))
    have hs : 2 * |g k| * |g j| ≤ g k ^ 2 + g j ^ 2 := by
      nlinarith [sq_nonneg (|g k| - |g j|), sq_abs (g k), sq_abs (g j)]
    have hsq := mul_le_mul_of_nonneg_left hs hB
    simp only [abs_mul]
    nlinarith
  calc
    _ ≤ 2 * (∑ k, ∑ j, |g k * Db k j * g j|) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = ∑ k, ∑ j, 2 * |g k * Db k j * g j| := by simp only [Finset.mul_sum]
    _ ≤ ∑ k, ∑ j, B * (g k ^ 2 + g j ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact hterm k j
    _ = _ := by simp only [Fin.sum_univ_two]; ring

private theorem forcing_gradient_term_ge (g f : Fin 2 → ℝ) :
    -(∑ k, g k ^ 2) - (∑ k, f k ^ 2) ≤ 2 * ∑ k, g k * f k := by
  have hterm (k : Fin 2) : -(g k ^ 2) - f k ^ 2 ≤ 2 * (g k * f k) := by
    nlinarith [sq_nonneg (g k + f k)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hterm k)
  simpa only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] using hs

private theorem cutoff_gradient_hessian_term_ge
    (g : Fin 2 → ℝ) (H A : Fin 2 → Fin 2 → ℝ) (dη : Fin 2 → ℝ)
    {η R Λ lam : ℝ} (hA : ∀ i j, |A i j| ≤ Λ)
    (hdη : ∀ i, |dη i| ≤ 2 * R) (hη : 0 ≤ η) (hlam : 0 < lam) :
    -(lam / 2) * η ^ 2 * (∑ j, ∑ k, H j k ^ 2) -
        (1024 * Λ ^ 2 / lam) * R ^ 2 * (∑ k, g k ^ 2) ≤
      8 * η * ∑ i, ∑ j, ∑ k, A i j * dη i * g k * H j k := by
  have hΛ : 0 ≤ Λ := (abs_nonneg (A 0 0)).trans (hA 0 0)
  have hterm (i j k : Fin 2) :
      8 * η * |A i j * dη i * g k * H j k| ≤
        (lam / 4) * η ^ 2 * H j k ^ 2 + (256 * Λ ^ 2 / lam) * R ^ 2 * g k ^ 2 := by
    have hp : |A i j * dη i * g k * H j k| ≤
        Λ * (2 * R) * |g k| * |H j k| := by
      simp only [abs_mul]
      gcongr
      · exact hA i j
      · exact hdη i
    have hb := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hη)
    have hy := two_mul_le_weighted_squares (δ := lam / 4) (by positivity)
      (8 * Λ * R * |g k|) (η * |H j k|)
    have he : (lam / 4) * (η * |H j k|) ^ 2 +
        (8 * Λ * R * |g k|) ^ 2 / (lam / 4) =
        (lam / 4) * η ^ 2 * H j k ^ 2 +
          (256 * Λ ^ 2 / lam) * R ^ 2 * g k ^ 2 := by
      simp only [mul_pow, sq_abs]
      field_simp [hlam.ne']
      ring
    rw [he] at hy
    nlinarith
  have hsum : 8 * η * |∑ i, ∑ j, ∑ k, A i j * dη i * g k * H j k| ≤
      (lam / 2) * η ^ 2 * (∑ j, ∑ k, H j k ^ 2) +
        (1024 * Λ ^ 2 / lam) * R ^ 2 * (∑ k, g k ^ 2) := by
    calc
      _ ≤ 8 * η * (∑ i, ∑ j, ∑ k, |A i j * dη i * g k * H j k|) :=
        mul_le_mul_of_nonneg_left (abs_sum_three_le _) (mul_nonneg (by norm_num) hη)
      _ = ∑ i, ∑ j, ∑ k, 8 * η * |A i j * dη i * g k * H j k| := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, ∑ k,
          ((lam / 4) * η ^ 2 * H j k ^ 2 +
            (256 * Λ ^ 2 / lam) * R ^ 2 * g k ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact hterm i j k
      _ = _ := by simp only [Fin.sum_univ_two]; ring
  have hlower := neg_abs_le (∑ i, ∑ j, ∑ k, A i j * dη i * g k * H j k)
  have hh := mul_le_mul_of_nonneg_left hlower (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hη)
  linarith


private theorem scalarEllipticOperator_gradient_sq_lower_bound
    (A : V → Matrix (Fin 2) (Fin 2) ℝ) (b : V → Fin 2 → ℝ)
    {u : V → ℝ} {x : V} (hu : ContDiffAt ℝ 3 u x)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    {lam D B : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ v : Fin 2 → ℝ, lam * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (hDA : ∀ k i j, |fderiv ℝ (fun y => A y i j) x (e k)| ≤ D)
    (hDb : ∀ k j, |fderiv ℝ (fun y => b y j) x (e k)| ≤ B) :
    (3 * lam / 2) * (∑ i, ∑ j, (fderiv ℝ (fderiv ℝ u) x (e i) (e j)) ^ 2) -
      (16 * D ^ 2 / lam + 4 * B + 1) * (∑ k, (fderiv ℝ u x (e k)) ^ 2) -
      (∑ k, (fderiv ℝ (scalarEllipticOperator A b u) x (e k)) ^ 2) ≤
      scalarEllipticOperator A b (fun y => ∑ k, (fderiv ℝ u y (e k)) ^ 2) x := by
  let g (k : Fin 2) := fderiv ℝ u x (e k)
  let H (i j : Fin 2) := fderiv ℝ (fderiv ℝ u) x (e i) (e j)
  let DA (k i j : Fin 2) := fderiv ℝ (fun y => A y i j) x (e k)
  let Db (k j : Fin 2) := fderiv ℝ (fun y => b y j) x (e k)
  let f (k : Fin 2) := fderiv ℝ (scalarEllipticOperator A b u) x (e k)
  have hgrad (i k : Fin 2) : fderiv ℝ (fun y => fderiv ℝ u y (e k)) x (e i) = H i k := by
    rw [fderiv_clm_apply ((hu.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      (differentiableAt_const (e k))]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, H]
  have hid := scalarEllipticOperator_gradient_sq A b hu hA hb
  have hcoerSum : lam * (∑ i, ∑ j, H i j ^ 2) ≤
      ∑ k, ∑ i, ∑ j, A x i j * H i k * H j k := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hcoer (fun i => H i k))
    simp only [Fin.sum_univ_two] at h ⊢
    nlinarith only [h]
  have hDAest := principal_derivative_term_le g H DA hDA hlam
  have hDbest := drift_derivative_term_le g Db hDb
  have hfest := forcing_gradient_term_ge g f
  rw [hid]
  simp only [hgrad]
  change (3 * lam / 2) * (∑ i, ∑ j, H i j ^ 2) -
    (16 * D ^ 2 / lam + 4 * B + 1) * (∑ k, g k ^ 2) - (∑ k, f k ^ 2) ≤ _
  nlinarith [le_abs_self (∑ k, ∑ i, ∑ j, g k * DA k i j * H i j),
    le_abs_self (∑ k, ∑ j, g k * Db k j * g j)]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

private theorem bernstein_differential_inequalities_combine
    {r lam eta T Q c₀ cE cEta cCross Deta G K M F LQ Leta P Cross LS : ℝ}
    (h1 : eta ^ 2 * ((3 * lam / 2) * T - c₀ * Q - G ^ 2) ≤ eta ^ 2 * LQ)
    (h2 : -(2 * eta * Deta * Q) ≤ 2 * eta * Q * Leta)
    (h3 : 0 ≤ P * Q)
    (h4 : K * r ^ 2 * (2 * lam * Q - 2 * M * F) ≤ K * r ^ 2 * LS)
    (hcross : -(lam / 2) * eta ^ 2 * T - cCross * r ^ 2 * Q ≤ Cross)
    (hscale : c₀ * eta ^ 2 * Q ≤ cE * r ^ 2 * Q)
    (hscale2 : 2 * eta * Deta * Q ≤ cEta * r ^ 2 * Q)
    (hscale3 : eta ^ 2 * G ^ 2 ≤ r ^ 4 * G ^ 2)
    (hK : 2 * lam * K = cE + cEta + cCross + 1)
    (hpositive : 0 ≤ lam * eta ^ 2 * T) :
    r ^ 2 * Q - r ^ 4 * G ^ 2 - 2 * K * r ^ 2 * M * F ≤
      eta ^ 2 * LQ + (2 * eta * Leta + 2 * P) * Q + Cross + K * r ^ 2 * LS := by
  linear_combination h1 + h2 + 2 * h3 + h4 + hcross + hscale + hscale2 + hscale3 +
    hpositive - r ^ 2 * Q * hK

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "e" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

private theorem scalarEllipticOperator_bernstein_lower_bound
    (A : V → Matrix (Fin 2) (Fin 2) ℝ) (b : V → Fin 2 → ℝ)
    {u : V → ℝ} {p x : V} {R R₀ lam Λ D B B₀ G M F : ℝ}
    (hR : 0 < R) (hRR₀ : R ≤ R₀) (hx : x ∈ Metric.closedBall p R)
    (hu : ContDiffAt ℝ 3 u x)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    (hsymm : (A x).IsSymm) (hlam : 0 < lam)
    (hcoer : ∀ v : Fin 2 → ℝ, lam * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (hAbound : ∀ i j, |A x i j| ≤ Λ)
    (hDA : ∀ k i j, |fderiv ℝ (fun y => A y i j) x (e k)| ≤ D)
    (hDb : ∀ k j, |fderiv ℝ (fun y => b y j) x (e k)| ≤ B)
    (hbBound : ∀ i, |b x i| ≤ B₀)
    (hforce : ∑ k, (fderiv ℝ (scalarEllipticOperator A b u) x (e k)) ^ 2 ≤ G ^ 2)
    (huM : |u x| ≤ M) (hLu : |scalarEllipticOperator A b u x| ≤ F) :
    let K := ((16 * D ^ 2 / lam + 4 * B + 1) * R₀ ^ 2 +
      8 * Λ + 8 * R₀ * B₀ + 1024 * Λ ^ 2 / lam + 1) / (2 * lam)
    R ^ 2 * (∑ k, (fderiv ℝ u x (e k)) ^ 2) - R ^ 4 * G ^ 2 - 2 * K * R ^ 2 * M * F ≤
      scalarEllipticOperator A b (fun y => (quadraticBallCutoff p R y) ^ 2 *
        (∑ k, (fderiv ℝ u y (e k)) ^ 2) + K * R ^ 2 * u y ^ 2) x := by
  let η := quadraticBallCutoff p R
  let Q (y : V) := ∑ k, (fderiv ℝ u y (e k)) ^ 2
  let H (i j : Fin 2) := fderiv ℝ (fderiv ℝ u) x (e i) (e j)
  let T := ∑ i, ∑ j, H i j ^ 2
  let c₀ := 16 * D ^ 2 / lam + 4 * B + 1
  let K := (c₀ * R₀ ^ 2 + 8 * Λ + 8 * R₀ * B₀ + 1024 * Λ ^ 2 / lam + 1) / (2 * lam)
  have hD : 0 ≤ D := (abs_nonneg _).trans (hDA 0 0 0)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hDb 0 0)
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (hAbound 0 0)
  have hB₀ : 0 ≤ B₀ := (abs_nonneg _).trans (hbBound 0)
  have hR₀ : 0 < R₀ := hR.trans_le hRR₀
  have hK : 0 ≤ K := by dsimp [K, c₀]; positivity
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hQ : 0 ≤ Q x := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hη : 0 ≤ η x := quadraticBallCutoff_nonneg hR.le hx
  have hηR : η x ≤ R ^ 2 := quadraticBallCutoff_le p R x
  have hηsq : η x ^ 2 ≤ R ^ 4 := by nlinarith
  have hηC : ContDiffAt ℝ 2 η x := (contDiff_quadraticBallCutoff p R).contDiffAt.of_le (by decide)
  have huC : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hQC : ContDiffAt ℝ 2 Q x := ContDiffAt.sum fun k _ =>
    ((hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).pow 2
  have hpartD (k : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e k)) x :=
    ((hu.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const (e k))
  have hpartEq (j k : Fin 2) : fderiv ℝ (fun y => fderiv ℝ u y (e k)) x (e j) = H j k := by
    rw [fderiv_clm_apply ((hu.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      (differentiableAt_const (e k))]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, H]
  have hDQ (j : Fin 2) : fderiv ℝ Q x (e j) =
      2 * ∑ k, fderiv ℝ u x (e k) * H j k := by
    dsimp only [Q]
    rw [fderiv_fun_sum (fun k _ => (hpartD k).fun_pow 2)]
    simp only [sum_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_fun_pow 2 (hpartD k)]
    simp only [Nat.add_one_sub_one, pow_one, smul_apply, smul_eq_mul, hpartEq]
    ring
  have hLQ := scalarEllipticOperator_gradient_sq_lower_bound A b hu hA hb hlam hcoer hDA hDb
  change (3 * lam / 2) * T - c₀ * Q x - _ ≤ scalarEllipticOperator A b Q x at hLQ
  have hLQ' : (3 * lam / 2) * T - c₀ * Q x - G ^ 2 ≤ scalarEllipticOperator A b Q x := by
    linarith
  have hLη : -(4 * Λ + 4 * R * B₀) ≤ scalarEllipticOperator A b η x := by
    rw [scalarEllipticOperator_quadraticBallCutoff]
    have hcoord (i : Fin 2) : |x i - p i| ≤ R := by
      have hh := PiLp.norm_apply_le (x - p) i
      have hh' : |x i - p i| ≤ ‖x - p‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hh
      exact hh'.trans (by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hx)
    have hterm (i : Fin 2) : b x i * (x i - p i) ≤ B₀ * R :=
      (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul (hbBound i) (hcoord i) (abs_nonneg _) hB₀))
    have ha0 := (le_abs_self (A x 0 0)).trans (hAbound 0 0)
    have ha1 := (le_abs_self (A x 1 1)).trans (hAbound 1 1)
    simp only [Fin.sum_univ_two]
    nlinarith [hterm 0, hterm 1]
  have hηEnergy : 0 ≤ ∑ i, ∑ j, A x i j * fderiv ℝ η x (e i) * fderiv ℝ η x (e j) :=
    (mul_nonneg hlam.le (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans (hcoer _)
  have hLuSq : 2 * lam * Q x - 2 * M * F ≤ scalarEllipticOperator A b (fun y => u y ^ 2) x := by
    rw [scalarEllipticOperator_sq A b huC]
    have hprod : -(M * F) ≤ u x * scalarEllipticOperator A b u x :=
      (neg_le_neg ((abs_mul _ _).trans_le (mul_le_mul huM hLu (abs_nonneg _)
        ((abs_nonneg _).trans huM)))).trans (neg_abs_le _)
    have he := hcoer (fun k => fderiv ℝ u x (e k))
    change lam * Q x ≤ _ at he
    nlinarith
  have hcross := cutoff_gradient_hessian_term_ge (fun k => fderiv ℝ u x (e k)) H (A x)
    (fun i => fderiv ℝ η x (e i)) hAbound
    (fun i => abs_fderiv_quadraticBallCutoff_apply_le hx i) hη hlam
  have hid : scalarEllipticOperator A b
      (fun y => η y ^ 2 * Q y + K * R ^ 2 * u y ^ 2) x =
      η x ^ 2 * scalarEllipticOperator A b Q x +
      (2 * η x * scalarEllipticOperator A b η x +
        2 * ∑ i, ∑ j, A x i j * fderiv ℝ η x (e i) * fderiv ℝ η x (e j)) * Q x +
      8 * η x * ∑ i, ∑ j, ∑ k, A x i j * fderiv ℝ η x (e i) *
        fderiv ℝ u x (e k) * H j k +
      K * R ^ 2 * scalarEllipticOperator A b (fun y => u y ^ 2) x := by
    rw [scalarEllipticOperator_add A b ((hηC.pow 2).mul hQC) (contDiffAt_const.mul (huC.pow 2)),
      scalarEllipticOperator_const_mul A b (huC.pow 2),
      scalarEllipticOperator_mul_of_isSymm A b (hηC.pow 2) hQC hsymm,
      scalarEllipticOperator_sq A b hηC]
    simp_rw [fderiv_fun_pow 2 (hηC.differentiableAt (by norm_num)), hDQ]
    simp only [Nat.add_one_sub_one, pow_one, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    simp only [Fin.sum_univ_two]
    ring
  have hmul1 := mul_le_mul_of_nonneg_left hLQ' (sq_nonneg (η x))
  have hmul2 := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2 * η x * Q x by positivity)
  have hmul3 := mul_le_mul_of_nonneg_right hηEnergy hQ
  rw [zero_mul] at hmul3
  have hmul4 := mul_le_mul_of_nonneg_left hLuSq (mul_nonneg hK (sq_nonneg R))
  have hscale : c₀ * η x ^ 2 * Q x ≤ c₀ * R₀ ^ 2 * R ^ 2 * Q x := by
    have hsq : R ^ 2 ≤ R₀ ^ 2 := (sq_le_sq₀ hR.le hR₀.le).mpr hRR₀
    calc
      _ ≤ c₀ * (R ^ 2 * R ^ 2) * Q x := by
        gcongr
        nlinarith only [hηsq]
      _ ≤ c₀ * (R₀ ^ 2 * R ^ 2) * Q x := by gcongr
      _ = _ := by ring
  have hscale2 : 2 * η x * (4 * Λ + 4 * R * B₀) * Q x ≤
      (8 * Λ + 8 * R₀ * B₀) * R ^ 2 * Q x := by
    calc
      _ ≤ 2 * R ^ 2 * (4 * Λ + 4 * R₀ * B₀) * Q x := by gcongr
      _ = _ := by ring
  have hscale3 := mul_le_mul_of_nonneg_right hηsq (sq_nonneg G)
  have hKidentity : 2 * lam * K = c₀ * R₀ ^ 2 + 8 * Λ + 8 * R₀ * B₀ + 1024 * Λ ^ 2 / lam + 1 := by
    dsimp only [K]
    field_simp
  change _ ≤ scalarEllipticOperator A b (fun y => η y ^ 2 * Q y + K * R ^ 2 * u y ^ 2) x
  rw [hid]
  change _ ≤ _ at hcross
  apply bernstein_differential_inequalities_combine hmul1 ?_ hmul3 hmul4 hcross
    hscale hscale2 hscale3 ?_ (mul_nonneg (mul_nonneg hlam.le (sq_nonneg (η x))) hT)
  · nlinarith only [hmul2]
  · nlinarith only [hKidentity]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

private theorem bernstein_interior_gradient_bound
    {R Q K M F G L : ℝ} (hR : 0 < R) (hL : L ≤ 0)
    (hlower : R ^ 2 * Q - R ^ 4 * G ^ 2 - 2 * K * R ^ 2 * M * F ≤ L) :
    Q ≤ R ^ 2 * G ^ 2 + 2 * K * M * F := by
  have hscaled : R ^ 2 * Q ≤ R ^ 2 * (R ^ 2 * G ^ 2 + 2 * K * M * F) := by
    nlinarith only [hlower, hL]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).mp hscaled

private theorem bernstein_center_bound_of_boundary_maximum
    {R Q K M F G H₀ Hmax : ℝ} (hR : 0 < R)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hcenter : R ^ 4 * Q ≤ H₀) (hmax : H₀ ≤ Hmax)
    (hboundary : Hmax ≤ K * R ^ 2 * M ^ 2) :
    Q ≤ K * M ^ 2 / R ^ 2 + 2 * K * M * F + R ^ 2 * G ^ 2 := by
  have hR4 : 0 < R ^ 4 := pow_pos hR 4
  have hbound : R ^ 4 * Q ≤ K * R ^ 2 * M ^ 2 := hcenter.trans (hmax.trans hboundary)
  have hscaled : R ^ 4 * Q ≤ R ^ 4 * (K * M ^ 2 / R ^ 2) := by
    have he : R ^ 4 * (K * M ^ 2 / R ^ 2) = K * R ^ 2 * M ^ 2 := by
      field_simp [ne_of_gt hR]
    rw [he]
    exact hbound
  have hQ := (mul_le_mul_iff_right₀ hR4).mp hscaled
  have hMF : 0 ≤ 2 * K * M * F := by positivity
  have hG : 0 ≤ R ^ 2 * G ^ 2 := by positivity
  linarith

private theorem bernstein_center_bound_of_interior_maximum
    {R η Q Q₀ K M F G L H₀ Hmax : ℝ} (hR : 0 < R)
    (hη : 0 ≤ η) (hηR : η ≤ R ^ 2) (hQ : 0 ≤ Q)
    (hL : L ≤ 0)
    (hlower : R ^ 2 * Q - R ^ 4 * G ^ 2 - 2 * K * R ^ 2 * M * F ≤ L)
    (hcenter : R ^ 4 * Q₀ ≤ H₀) (hmax : H₀ ≤ Hmax)
    (hupper : Hmax ≤ η ^ 2 * Q + K * R ^ 2 * M ^ 2) :
    Q₀ ≤ K * M ^ 2 / R ^ 2 + 2 * K * M * F + R ^ 2 * G ^ 2 := by
  have hQbound := bernstein_interior_gradient_bound hR hL hlower
  have hηsq : η ^ 2 ≤ R ^ 4 := by
    calc
      η ^ 2 ≤ (R ^ 2) ^ 2 := (sq_le_sq₀ hη (sq_nonneg R)).mpr hηR
      _ = R ^ 4 := by ring
  have hηQ : η ^ 2 * Q ≤ R ^ 4 * Q := mul_le_mul_of_nonneg_right hηsq hQ
  have hscaleQ := mul_le_mul_of_nonneg_left hQbound (le_of_lt (pow_pos hR 4))
  have he : R ^ 4 * (K * M ^ 2 / R ^ 2 + 2 * K * M * F + R ^ 2 * G ^ 2) =
      K * R ^ 2 * M ^ 2 + R ^ 4 * (R ^ 2 * G ^ 2 + 2 * K * M * F) := by
    field_simp [ne_of_gt hR]
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos hR 4)).mp
  rw [he]
  linarith

private theorem bernstein_center_gradient_sq_le_of_operator_lower_bound
    (A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
    (b : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin 2) → ℝ} (hu : ContDiffOn ℝ 3 u Ω)
    {p : EuclideanSpace ℝ (Fin 2)} {R K M F G : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hball : Metric.closedBall p R ⊆ Ω)
    (hA : ∀ x ∈ Metric.ball p R, (A x).PosDef)
    (hum : ∀ x ∈ Metric.closedBall p R, |u x| ≤ M)
    (hlower : ∀ x ∈ Metric.ball p R,
      R ^ 2 * (∑ k : Fin 2, (fderiv ℝ u x (EuclideanSpace.single k 1)) ^ 2) -
          R ^ 4 * G ^ 2 - 2 * K * R ^ 2 * M * F ≤
        scalarEllipticOperator A b (fun y =>
          (R ^ 2 - ‖y - p‖ ^ 2) ^ 2 *
            (∑ k : Fin 2, (fderiv ℝ u y (EuclideanSpace.single k 1)) ^ 2) +
          K * R ^ 2 * u y ^ 2) x) :
    (∑ k : Fin 2, (fderiv ℝ u p (EuclideanSpace.single k 1)) ^ 2) ≤
      K * M ^ 2 / R ^ 2 + 2 * K * M * F + R ^ 2 * G ^ 2 := by
  let η : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => R ^ 2 - ‖x - p‖ ^ 2
  let Q : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
    ∑ k : Fin 2, (fderiv ℝ u x (EuclideanSpace.single k 1)) ^ 2
  let H : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
    η x ^ 2 * Q x + K * R ^ 2 * u x ^ 2
  change Q p ≤ _
  change ∀ x ∈ Metric.ball p R,
    R ^ 2 * Q x - R ^ 4 * G ^ 2 - 2 * K * R ^ 2 * M * F ≤
      scalarEllipticOperator A b H x at hlower
  have hQnonneg (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ Q x :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hηsmooth : ContDiff ℝ ∞ η :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hdu : ContDiffOn ℝ 2 (fderiv ℝ u) Ω :=
    hu.fderiv_of_isOpen hΩ (by norm_num)
  have hQs : ContDiffOn ℝ 2 Q Ω := by
    apply ContDiffOn.sum
    intro k hk
    exact (hdu.clm_apply contDiffOn_const).pow 2
  have hHs : ContDiffOn ℝ 2 H Ω :=
    (((hηsmooth.of_le (by decide)).contDiffOn.pow 2).mul hQs).add
      (contDiffOn_const.mul ((hu.of_le (by norm_num)).pow 2))
  have hp : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self hR.le
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall p R).exists_isMaxOn
    ⟨p, hp⟩ (hHs.continuousOn.mono hball)
  have hcenter : R ^ 4 * Q p ≤ H p := by
    change R ^ 4 * Q p ≤ (R ^ 2 - ‖p - p‖ ^ 2) ^ 2 * Q p + K * R ^ 2 * u p ^ 2
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    have he : (R ^ 2) ^ 2 = R ^ 4 := by ring
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have hmaxp : H p ≤ H x := hmax hp
  have huSq : u x ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (abs_le.mp (hum x hx)).1 (abs_le.mp (hum x hx)).2
  have hupper : H x ≤ η x ^ 2 * Q x + K * R ^ 2 * M ^ 2 := by
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left huSq (mul_nonneg hK (sq_nonneg R)))
  by_cases hxi : x ∈ Metric.ball p R
  · have hlocal : IsLocalMax H x :=
      hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hxi)
    have hHtwo : ContDiffAt ℝ 2 H x :=
      (hHs.contDiffAt (hΩ.mem_nhds (hball hx))).of_le (by norm_cast)
    have hnonpos := scalarEllipticOperator_nonpos_of_isLocalMax A b hHtwo hlocal (hA x hxi)
    have hxnorm : ‖x - p‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hηnonneg : 0 ≤ η x :=
      sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hR.le).mpr hxnorm)
    have hηle : η x ≤ R ^ 2 := sub_le_self _ (sq_nonneg _)
    exact bernstein_center_bound_of_interior_maximum hR hηnonneg hηle (hQnonneg x)
      hnonpos (hlower x hxi) hcenter hmaxp hupper
  · have hxnorm : ‖x - p‖ = R := by
      apply le_antisymm
      · simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
      · apply le_of_not_gt
        simpa only [Metric.mem_ball, dist_eq_norm] using hxi
    have hηzero : η x = 0 := by
      change R ^ 2 - ‖x - p‖ ^ 2 = 0
      rw [hxnorm, sub_self]
    have hboundary : H x ≤ K * R ^ 2 * M ^ 2 := by
      simpa only [hηzero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] using hupper
    exact bernstein_center_bound_of_boundary_maximum hR hK hM hF hcenter hmaxp hboundary

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem sum_sq_fderiv_le_of_scalar_elliptic_bounds
    (A : V → Matrix (Fin 2) (Fin 2) ℝ) (b : V → Fin 2 → ℝ)
    {Ω : Set V} (hΩ : IsOpen Ω) {u : V → ℝ} (hu : ContDiffOn ℝ 3 u Ω)
    {p : V} {R R₀ lam Λ D B B₀ G M F : ℝ}
    (hR : 0 < R) (hRR₀ : R ≤ R₀) (hlam : 0 < lam)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hball : Metric.closedBall p R ⊆ Ω)
    (hApos : ∀ x ∈ Metric.ball p R, (A x).PosDef)
    (hA : ∀ x ∈ Metric.ball p R, ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hb : ∀ x ∈ Metric.ball p R, ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    (hcoer : ∀ x ∈ Metric.ball p R, ∀ v : Fin 2 → ℝ,
      lam * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (hAbound : ∀ x ∈ Metric.ball p R, ∀ i j, |A x i j| ≤ Λ)
    (hDA : ∀ x ∈ Metric.ball p R, ∀ k i j,
      |fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single k 1)| ≤ D)
    (hDb : ∀ x ∈ Metric.ball p R, ∀ k j,
      |fderiv ℝ (fun y => b y j) x (EuclideanSpace.single k 1)| ≤ B)
    (hbBound : ∀ x ∈ Metric.ball p R, ∀ i, |b x i| ≤ B₀)
    (hforce : ∀ x ∈ Metric.ball p R,
      ∑ k, (fderiv ℝ (scalarEllipticOperator A b u) x (EuclideanSpace.single k 1)) ^ 2 ≤ G ^ 2)
    (hum : ∀ x ∈ Metric.closedBall p R, |u x| ≤ M)
    (hLu : ∀ x ∈ Metric.ball p R, |scalarEllipticOperator A b u x| ≤ F) :
    let K := ((16 * D ^ 2 / lam + 4 * B + 1) * R₀ ^ 2 +
      8 * Λ + 8 * R₀ * B₀ + 1024 * Λ ^ 2 / lam + 1) / (2 * lam)
    (∑ k : Fin 2, (fderiv ℝ u p (EuclideanSpace.single k 1)) ^ 2) ≤
      K * M ^ 2 / R ^ 2 + 2 * K * M * F + R ^ 2 * G ^ 2 := by
  dsimp only
  apply bernstein_center_gradient_sq_le_of_operator_lower_bound A b hΩ hu hR
    (by have hR₀ := hR.trans_le hRR₀; positivity) hM hF hball hApos hum
  intro x hx
  have hxC := Metric.ball_subset_closedBall hx
  have hu3 : ContDiffAt ℝ 3 u x :=
    hu.contDiffAt (hΩ.mem_nhds (hball hxC))
  exact scalarEllipticOperator_bernstein_lower_bound A b hR hRR₀ hxC hu3
    (hA x hx) (hb x hx) (Matrix.isHermitian_iff_isSymm.mp (hApos x hx).isHermitian)
    hlam (hcoer x hx) (hAbound x hx) (hDA x hx) (hDb x hx) (hbBound x hx)
    (hforce x hx) (hum x hxC) (hLu x hx)

end DifferentialGeometry.Analysis

end

end
