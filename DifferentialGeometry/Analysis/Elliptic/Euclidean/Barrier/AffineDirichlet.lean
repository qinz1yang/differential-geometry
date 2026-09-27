import DifferentialGeometry.Analysis.Elliptic.Euclidean.Barrier.Exponential
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Supersolution
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakMaximumPrinciple
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Composition
import DifferentialGeometry.External.DeGiorgi.Localization

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis
open Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem flux_affine_add_barrier
    (a : V → Matrix (Fin d) (Fin d) ℝ) (R k σ C : ℝ) (j : Fin d) (x : V) (i : Fin d) :
    DeGiorgi.matMulE (a x) (DeGiorgi.smoothGradField
      (fun y => σ * y j + C * exponentialBallBarrier R k y) x) i =
      σ * a x i j + C * DeGiorgi.matMulE (a x)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) x) i := by
  have hj : ContDiff ℝ ∞ (fun y : V => y j) := contDiff_piLp_apply 2
  rw [DeGiorgi.smoothGradField_add (contDiff_const.mul hj)
    (contDiff_const.mul (contDiff_exponentialBallBarrier R k)),
    DeGiorgi.smoothGradField_smul, DeGiorgi.smoothGradField_smul]
  have hgj : DeGiorgi.smoothGradField (fun y : V => y j) x = EuclideanSpace.single j 1 := by
    ext l
    change fderiv ℝ (fun y : V => y j) x (EuclideanSpace.single l 1) = _
    have he := (EuclideanSpace.proj j : V →L[ℝ] ℝ).fderiv (x := x)
    rw [← EuclideanSpace.coe_proj ℝ, he]
    simp [eq_comm]
  change DeGiorgi.matMulE (a x)
    (σ • DeGiorgi.smoothGradField (fun y : V => y j) x +
      C • DeGiorgi.smoothGradField (exponentialBallBarrier R k) x) i = _
  rw [hgj]
  simp only [DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  simp [PiLp.single_apply, Finset.mul_sum, mul_left_comm, mul_comm]

theorem exists_affine_exponential_supersolutions
    (B : SmoothEllipticBilinearForm d (univ : Set V)) {R : ℝ} (hR : 0 < R)
    (A : DeGiorgi.EllipticCoeff d (Metric.ball (0 : V) R))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin d) :
    ∃ k C : ℝ, 0 < k ∧ 0 < C ∧
      DeGiorgi.MemW01p 2 (exponentialBallBarrier (d := d) R k) (Metric.ball (0 : V) R) ∧
      ∀ σ : ℝ, |σ| ≤ 1 → DeGiorgi.IsSupersolution A
        (fun x => σ * x j + C * exponentialBallBarrier R k x) := by
  obtain ⟨k, hk, hbar⟩ := exists_exponentialBallBarrier_divergence_le_neg_one B R
  let D (x : V) := ∑ i, fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)
  have hDc : Continuous D := continuous_finsetSum _ (fun i _ =>
    ((B.smooth_a i j).continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn hDc.continuousOn
  let C := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨k, C, hk, hC, memW01p_exponentialBallBarrier hR hk.le, ?_⟩
  intro σ hσ
  have hj : ContDiff ℝ ∞ (fun y : V => y j) := contDiff_piLp_apply 2
  have hU : ContDiff ℝ ∞ (fun x : V => σ * x j + C * exponentialBallBarrier R k x) :=
    (contDiff_const.mul hj).add
      (contDiff_const.mul (contDiff_exponentialBallBarrier (d := d) R k))
  apply DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos isOpen_univ
    (subset_univ _) A B.a (fun i l => (B.smooth_a i l).contDiffOn.of_le (by norm_cast)) hAB
    (hU.contDiffOn.of_le (by norm_cast))
  intro x hx
  have hflux (i : Fin d) := funext (fun y => flux_affine_add_barrier B.a R k σ C j y i)
  have hFG (i : Fin d) : DifferentiableAt ℝ
      (fun y => DeGiorgi.matMulE (B.a y)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x := by
    have hgc (l : Fin d) : ContDiff ℝ 1
        (fun y => DeGiorgi.smoothGradField (exponentialBallBarrier R k) y l) := by
      exact ((contDiff_exponentialBallBarrier R k).fderiv_right
        (by norm_cast)).clm_apply contDiff_const
    have hfc : ContDiff ℝ 1 (fun y => ∑ l, B.a y i l *
        DeGiorgi.smoothGradField (exponentialBallBarrier R k) y l) :=
      ContDiff.sum (fun l _ => ((B.smooth_a i l).of_le (by norm_cast)).mul (hgc l))
    exact hfc.differentiable one_ne_zero x
  have hder (i : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y) (DeGiorgi.smoothGradField
        (fun z => σ * z j + C * exponentialBallBarrier R k z) y) i) x
        (EuclideanSpace.single i 1) =
      σ * fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1) +
        C * fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y)
          (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x
          (EuclideanSpace.single i 1) := by
    rw [hflux i]
    have hh := (((B.smooth_a i j).differentiable (by simp) x).hasFDerivAt.const_mul σ).add
      ((hFG i).hasFDerivAt.const_mul C)
    have he := hh.fderiv
    change fderiv ℝ (fun y : V => σ * B.a y i j + C *
      DeGiorgi.matMulE (B.a y)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x = _ at he
    rw [he]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hder, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hDx : |D x| ≤ max M 0 := (hM x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)
  have hsD : σ * D x ≤ max M 0 :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le
      ((mul_le_mul hσ hDx (abs_nonneg _) (by positivity)).trans_eq (one_mul _)))
  have hb := hbar x (Metric.ball_subset_closedBall hx)
  have hCb := mul_le_mul_of_nonneg_left hb hC.le
  change σ * D x + _ ≤ 0
  dsimp only [C] at hCb
  linarith

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.exists_ae_affine_dirichlet_barrier_bound
    (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin d)
    (ht : MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R)) :
    ∃ k C : ℝ, 0 < k ∧ 0 < C ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) R),
        |u x - x j| ≤ C * exponentialBallBarrier R k x := by
  obtain ⟨k, C, hk, hC, hb0, hsuper⟩ := exists_affine_exponential_supersolutions B hR A hAB j
  have hplus : IsSupersolution A (fun x => x j + C * exponentialBallBarrier R k x) := by
    simpa only [one_mul] using hsuper 1 (by norm_num)
  have hminus : IsSupersolution A (fun x => -x j + C * exponentialBallBarrier R k x) := by
    simpa only [neg_one_mul] using hsuper (-1) (by norm_num)
  have htplus : MemH01 (fun x => u x - (x j + C * exponentialBallBarrier R k x))
      (Metric.ball (0 : V) R) := by
    apply (ht.sub (hb0.smul C)).congr
    filter_upwards with x
    ring
  have htminus : MemH01 (fun x => -u x - (-x j + C * exponentialBallBarrier R k x))
      (Metric.ball (0 : V) R) := by
    apply ((ht.smul (-1)).sub (hb0.smul C)).congr
    filter_upwards with x
    ring
  have hup := hu.1.ae_le_of_memH01_sub hd Metric.isOpen_ball Metric.isBounded_ball hplus htplus
  have hlo := (hu.2.neg_ball hR).ae_le_of_memH01_sub hd Metric.isOpen_ball
    Metric.isBounded_ball hminus htminus
  refine ⟨k, C, hk, hC, ?_⟩
  filter_upwards [hup, hlo] with x hx hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem IsSolution.exists_affine_dirichlet_barrier_bound_of_continuousOn
    (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    {A : EllipticCoeff d (Metric.ball (0 : V) R)} {u v : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin d)
    (ht : MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R))
    (hv : ContinuousOn v (Metric.ball (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v) :
    ∃ k C : ℝ, 0 < k ∧ 0 < C ∧ ∀ x ∈ Metric.ball (0 : V) R,
      |v x - x j| ≤ C * exponentialBallBarrier R k x := by
  obtain ⟨k, C, hk, hC, hb⟩ := hu.exists_ae_affine_dirichlet_barrier_bound hd hR B hAB j ht
  let F := fun x => max (|v x - x j| - C * exponentialBallBarrier R k x) 0
  have hFa : F =ᵐ[volume.restrict (Metric.ball (0 : V) R)] 0 := by
    filter_upwards [hb, huv] with x hx he
    change max (|v x - x j| - C * exponentialBallBarrier R k x) 0 = 0
    rw [← he]
    exact max_eq_right (sub_nonpos.mpr hx)
  have hj : Continuous (fun x : V => x j) := (EuclideanSpace.proj j : V →L[ℝ] ℝ).continuous
  have hFc : ContinuousOn F (Metric.ball (0 : V) R) :=
    (((hv.sub hj.continuousOn).abs).sub
      (continuousOn_const.mul (contDiff_exponentialBallBarrier R k).continuous.continuousOn)).sup
      continuousOn_const
  have hFe := Measure.eqOn_open_of_ae_eq hFa Metric.isOpen_ball hFc continuousOn_const
  refine ⟨k, C, hk, hC, ?_⟩
  intro x hx
  exact sub_nonpos.mp ((le_max_left _ _).trans (le_of_eq (hFe hx)))

end DeGiorgi

end

end

section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis

open Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_affine_exponential_supersolutions_on_subballs
    (B : SmoothEllipticBilinearForm d (univ : Set V)) (R₀ : ℝ) (j : Fin d) :
    ∃ k C : ℝ, 0 < k ∧ 0 < C ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∀ (A : DeGiorgi.EllipticCoeff d (Metric.ball (0 : V) R)),
      EqOn A.a B.a (Metric.ball (0 : V) R) →
      DeGiorgi.MemW01p 2 (exponentialBallBarrier (d := d) R k) (Metric.ball (0 : V) R) ∧
      ∀ σ : ℝ, |σ| ≤ 1 → DeGiorgi.IsSupersolution A
        (fun x => σ * x j + C * exponentialBallBarrier R k x) := by
  obtain ⟨k, hk, hbar⟩ := exists_exponentialBallBarrier_divergence_le_neg_one B R₀
  let D (x : V) := ∑ i, fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)
  have hDc : Continuous D := continuous_finsetSum _ (fun i _ =>
    ((B.smooth_a i j).continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) R₀).exists_bound_of_continuousOn hDc.continuousOn
  let C := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨k, C, hk, hC, ?_⟩
  intro R hR hRR A hAB
  refine ⟨memW01p_exponentialBallBarrier hR hk.le, ?_⟩
  intro σ hσ
  have hj : ContDiff ℝ ∞ (fun y : V => y j) := contDiff_piLp_apply 2
  have hU : ContDiff ℝ ∞ (fun x : V => σ * x j + C * exponentialBallBarrier R k x) :=
    (contDiff_const.mul hj).add
      (contDiff_const.mul (contDiff_exponentialBallBarrier (d := d) R k))
  apply DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos isOpen_univ
    (subset_univ _) A B.a (fun i l => (B.smooth_a i l).contDiffOn.of_le (by norm_cast)) hAB
    (hU.contDiffOn.of_le (by norm_cast))
  intro x hx
  have hflux (i : Fin d) := funext (fun y => flux_affine_add_barrier B.a R k σ C j y i)
  have hFG (i : Fin d) : DifferentiableAt ℝ
      (fun y => DeGiorgi.matMulE (B.a y)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x := by
    have hgc (l : Fin d) : ContDiff ℝ 1
        (fun y => DeGiorgi.smoothGradField (exponentialBallBarrier R k) y l) := by
      exact ((contDiff_exponentialBallBarrier R k).fderiv_right
        (by norm_cast)).clm_apply contDiff_const
    have hfc : ContDiff ℝ 1 (fun y => ∑ l, B.a y i l *
        DeGiorgi.smoothGradField (exponentialBallBarrier R k) y l) :=
      ContDiff.sum (fun l _ => ((B.smooth_a i l).of_le (by norm_cast)).mul (hgc l))
    exact hfc.differentiable one_ne_zero x
  have hder (i : Fin d) :
      fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y) (DeGiorgi.smoothGradField
        (fun z => σ * z j + C * exponentialBallBarrier R k z) y) i) x
        (EuclideanSpace.single i 1) =
      σ * fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1) +
        C * fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y)
          (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x
          (EuclideanSpace.single i 1) := by
    rw [hflux i]
    have hh := (((B.smooth_a i j).differentiable (by simp) x).hasFDerivAt.const_mul σ).add
      ((hFG i).hasFDerivAt.const_mul C)
    have he := hh.fderiv
    change fderiv ℝ (fun y : V => σ * B.a y i j + C *
      DeGiorgi.matMulE (B.a y)
        (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x = _ at he
    rw [he]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hder, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hxR₀ : x ∈ Metric.closedBall (0 : V) R₀ :=
    Metric.closedBall_subset_closedBall hRR (Metric.ball_subset_closedBall hx)
  have hDx : |D x| ≤ max M 0 := (hM x hxR₀).trans (le_max_left _ _)
  have hsD : σ * D x ≤ max M 0 :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le
      ((mul_le_mul hσ hDx (abs_nonneg _) (by positivity)).trans_eq (one_mul _)))
  have hb := hbar x hxR₀
  have hderRadius :
      (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y)
          (DeGiorgi.smoothGradField (exponentialBallBarrier R k) y) i) x
        (EuclideanSpace.single i 1)) =
      (∑ i, fderiv ℝ (fun y => DeGiorgi.matMulE (B.a y)
          (DeGiorgi.smoothGradField (exponentialBallBarrier R₀ k) y) i) x
        (EuclideanSpace.single i 1)) := by
    rw [divergence_exponentialBallBarrier R k B.a x
      (fun i l => (B.smooth_a i l).differentiable (by simp) x),
      divergence_exponentialBallBarrier R₀ k B.a x
        (fun i l => (B.smooth_a i l).differentiable (by simp) x)]
  rw [← hderRadius] at hb
  have hCb := mul_le_mul_of_nonneg_left hb hC.le
  change σ * D x + _ ≤ 0
  dsimp only [C] at hCb
  linarith

omit [NeZero d] in
theorem exponentialBallBarrier_le_mul_radius_sq
    {R R₀ k : ℝ} (hR : 0 ≤ R) (hRR : R ≤ R₀) (hk : 0 ≤ k) (x : V) :
    exponentialBallBarrier R k x ≤ k * Real.exp (k * R₀ ^ 2) * R ^ 2 := by
  have hR₀ : 0 ≤ R₀ := hR.trans hRR
  have ha : 0 ≤ k * R ^ 2 := mul_nonneg hk (sq_nonneg R)
  have hb : 1 ≤ Real.exp (k * ‖x‖ ^ 2) := Real.one_le_exp (by positivity)
  have hA : Real.exp (k * R ^ 2) ≤ Real.exp (k * R₀ ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hR hR₀).mpr hRR) hk)
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(k * R ^ 2)))
    (le_of_lt (Real.exp_pos (k * R ^ 2)))
  rw [← Real.exp_add] at ht
  have hmul := mul_le_mul_of_nonneg_left hA ha
  simp only [add_neg_cancel, Real.exp_zero] at ht
  dsimp only [exponentialBallBarrier]
  nlinarith only [ht, hb, hmul]

end DifferentialGeometry.Analysis

namespace DeGiorgi

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_affine_dirichlet_barrier_bound_on_subballs
    (hd : 2 ≤ d) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (R₀ : ℝ) (j : Fin d) :
    ∃ k C : ℝ, 0 < k ∧ 0 < C ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∀ (A : EllipticCoeff d (Metric.ball (0 : V) R)) (u v : V → ℝ),
      IsSolution A u → EqOn A.a B.a (Metric.ball (0 : V) R) →
      MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R) →
      ContinuousOn v (Metric.ball (0 : V) R) →
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v →
      ∀ x ∈ Metric.ball (0 : V) R,
        |v x - x j| ≤ C * exponentialBallBarrier R k x ∧
        C * exponentialBallBarrier R k x ≤ C * k * Real.exp (k * R₀ ^ 2) * R ^ 2 := by
  obtain ⟨k, C, hk, hC, hsuperAll⟩ :=
    exists_affine_exponential_supersolutions_on_subballs B R₀ j
  refine ⟨k, C, hk, hC, ?_⟩
  intro R hR hRR A u v hu hAB ht hv huv
  obtain ⟨hb0, hsuper⟩ := hsuperAll R hR hRR A hAB
  have hplus : IsSupersolution A (fun x => x j + C * exponentialBallBarrier R k x) := by
    simpa only [one_mul] using hsuper 1 (by norm_num)
  have hminus : IsSupersolution A (fun x => -x j + C * exponentialBallBarrier R k x) := by
    simpa only [neg_one_mul] using hsuper (-1) (by norm_num)
  have htplus : MemH01 (fun x => u x - (x j + C * exponentialBallBarrier R k x))
      (Metric.ball (0 : V) R) := by
    apply (ht.sub (hb0.smul C)).congr
    filter_upwards with x
    ring
  have htminus : MemH01 (fun x => -u x - (-x j + C * exponentialBallBarrier R k x))
      (Metric.ball (0 : V) R) := by
    apply ((ht.smul (-1)).sub (hb0.smul C)).congr
    filter_upwards with x
    ring
  have hup := hu.1.ae_le_of_memH01_sub hd Metric.isOpen_ball Metric.isBounded_ball hplus htplus
  have hlo := (hu.2.neg_ball hR).ae_le_of_memH01_sub hd Metric.isOpen_ball
    Metric.isBounded_ball hminus htminus
  have hb : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) R),
      |u x - x j| ≤ C * exponentialBallBarrier R k x := by
    filter_upwards [hup, hlo] with x hx hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let F := fun x => max (|v x - x j| - C * exponentialBallBarrier R k x) 0
  have hFa : F =ᵐ[volume.restrict (Metric.ball (0 : V) R)] 0 := by
    filter_upwards [hb, huv] with x hx he
    change max (|v x - x j| - C * exponentialBallBarrier R k x) 0 = 0
    rw [← he]
    exact max_eq_right (sub_nonpos.mpr hx)
  have hj : Continuous (fun x : V => x j) := (EuclideanSpace.proj j : V →L[ℝ] ℝ).continuous
  have hFc : ContinuousOn F (Metric.ball (0 : V) R) :=
    (((hv.sub hj.continuousOn).abs).sub
      (continuousOn_const.mul (contDiff_exponentialBallBarrier R k).continuous.continuousOn)).sup
      continuousOn_const
  have hFe := Measure.eqOn_open_of_ae_eq hFa Metric.isOpen_ball hFc continuousOn_const
  intro x hx
  refine ⟨sub_nonpos.mp ((le_max_left _ _).trans (le_of_eq (hFe hx))), ?_⟩
  calc
    C * exponentialBallBarrier R k x ≤
        C * (k * Real.exp (k * R₀ ^ 2) * R ^ 2) :=
      mul_le_mul_of_nonneg_left (exponentialBallBarrier_le_mul_radius_sq hR.le hRR hk.le x) hC.le
    _ = C * k * Real.exp (k * R₀ ^ 2) * R ^ 2 := by ring

end DeGiorgi

end

end
