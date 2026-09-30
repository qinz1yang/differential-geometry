import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FixedBallMovingControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.Calabi
import DifferentialGeometry.Analysis.Parabolic.Bernstein.Cutoff
import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Barrier

set_option autoImplicit false
noncomputable section

open Bundle Filter Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private def profileGradientCost : ℝ :=
  Classical.choose DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq

private theorem profileGradientCost_spec :
    0 ≤ profileGradientCost ∧ ∀ z : ℝ,
      (deriv DifferentialGeometry.Analysis.CutoffProfile.value z) ^ 2 ≤
        profileGradientCost * DifferentialGeometry.Analysis.CutoffProfile.value z :=
  Classical.choose_spec DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq

def finiteDistanceCutoffConstant (n : ℕ) : ℝ :=
  1 + (64 * profileGradientCost +
    DifferentialGeometry.Analysis.CutoffProfile.derivBound * (136 * (n : ℝ) ^ 2 + 64)) *
      Real.exp (2 * (n : ℝ) ^ 2)

theorem finiteDistanceCutoffConstant_pos (n : ℕ) :
    0 < finiteDistanceCutoffConstant n := by
  have hG := profileGradientCost_spec.1
  have hD := DifferentialGeometry.Analysis.CutoffProfile.derivBound_nonneg
  unfold finiteDistanceCutoffConstant
  positivity

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

def finiteDistanceCutoff (S : SolutionOn (I := I) (M := M) D)
    (R : ℝ) (O : M) (s : ℝ) (x : M) : ℝ :=
  DifferentialGeometry.Analysis.CutoffProfile.evalue
    (ENNReal.ofReal ((8 / R) *
        Real.exp (((Module.finrank ℝ E : ℝ) ^ 2 / R ^ 2) * s)) *
      riemannianEDistOf (I := I) (S.base.metric s) O x)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private theorem finite_parabolic_algebra
    (alpha U c q C e r P ep epp G : ℝ)
    (ha : 0 ≤ alpha) (hU : 0 ≤ U) (hc : 0 ≤ c) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (he : 0 ≤ e) (heU : e ≤ U) (hr : 0 < r)
    (hactive : 1 ≤ alpha * e * r)
    (hP : -e * (2 * c / r + q) ≤ P)
    (hep0 : ep ≤ 0) (hep : |ep| ≤ C) (hepp : |epp| ≤ C)
    (hG0 : 0 ≤ G) (hG : G ≤ alpha ^ 2 * U ^ 2) :
    ep * (alpha * P) - epp * G ≤
      C * (2 * c * alpha ^ 2 * U ^ 2 + alpha * U * q + alpha ^ 2 * U ^ 2) := by
  have he2 : e ^ 2 ≤ U ^ 2 := (sq_le_sq₀ he hU).2 heU
  have hinv : 1 / r ≤ alpha * e := (div_le_iff₀ hr).2 (by simpa [mul_assoc] using hactive)
  have hdiv : alpha * e / r ≤ alpha ^ 2 * U ^ 2 := by
    calc
      alpha * e / r = alpha * e * (1 / r) := by ring
      _ ≤ alpha * e * (alpha * e) := mul_le_mul_of_nonneg_left hinv (mul_nonneg ha he)
      _ = alpha ^ 2 * e ^ 2 := by ring
      _ ≤ alpha ^ 2 * U ^ 2 := mul_le_mul_of_nonneg_left he2 (sq_nonneg alpha)
  have hsum : alpha * e * (2 * c / r + q) ≤
      2 * c * alpha ^ 2 * U ^ 2 + alpha * U * q := by
    calc
      alpha * e * (2 * c / r + q) = 2 * c * (alpha * e / r) + alpha * e * q := by ring
      _ ≤ 2 * c * (alpha ^ 2 * U ^ 2) + alpha * U * q :=
        add_le_add (mul_le_mul_of_nonneg_left hdiv (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heU ha) hq)
      _ = _ := by ring
  have hP' : -(alpha * e * (2 * c / r + q)) ≤ alpha * P := by
    simpa only [neg_mul, mul_neg, mul_assoc] using mul_le_mul_of_nonneg_left hP ha
  have hep' : -ep ≤ C := by linarith [(abs_le.mp hep).1]
  have hepp' : -epp ≤ C := by linarith [(abs_le.mp hepp).1]
  have hfirst : ep * (alpha * P) ≤ C *
      (2 * c * alpha ^ 2 * U ^ 2 + alpha * U * q) := by
    calc
      ep * (alpha * P) ≤ ep * (-(alpha * e * (2 * c / r + q))) :=
        mul_le_mul_of_nonpos_left hP' hep0
      _ = (-ep) * (alpha * e * (2 * c / r + q)) := by ring
      _ ≤ C * (alpha * e * (2 * c / r + q)) :=
        mul_le_mul_of_nonneg_right hep' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC
  have hsecond : -epp * G ≤ C * (alpha ^ 2 * U ^ 2) :=
    (mul_le_mul_of_nonneg_right hepp' hG0).trans (mul_le_mul_of_nonneg_left hG hC)
  nlinarith only [hfirst, hsecond]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem profile_of_scaled_support
    (S : SolutionOn (I := I) (M := M) D) (O : M)
    {T t n Lambda alpha U eps : ℝ} {x : M}
    (ha : 0 < alpha) (hU : 0 ≤ U) (hn : 1 ≤ n)
    (hC : 0 ≤ eps)
    (he : Real.exp (Lambda * t) ≤ U)
    (hgradCost : profileGradientCost * alpha ^ 2 * U ^ 2 ≤ eps)
    (hparCost : DifferentialGeometry.Analysis.CutoffProfile.derivBound *
      (2 * (n - 1) * alpha ^ 2 * U ^ 2 +
        alpha * U * Real.sqrt ((n - 1) * Lambda) + alpha ^ 2 * U ^ 2) ≤ eps)
    (hedist : ContinuousWithinAt
      (fun p : ℝ × M => riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
      (spacetimeSlab (M := M) T) (t, x))
    (hfinite : riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (F : DistanceBarrier.ScaledDistanceSupport (I := I) S O T t x n Lambda
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal) :
    Nonempty (ParabolicCutoffLowerSupportAt (I := I) (flowG S) T eps
      (fun s y => DifferentialGeometry.Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (alpha * Real.exp (Lambda * s)) *
          riemannianEDistOf (I := I) (S.base.metric s) O y)) t x) := by
  let u : ℝ → M → ℝ := fun s y => alpha * F.rho s y
  let phi : ℝ → M → ℝ := fun s y => DifferentialGeometry.Analysis.CutoffProfile.value (u s y)
  have hu_time := F.time_diff.const_mul alpha
  have hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y := by
    filter_upwards [F.space_diff_nhds] with y hy
    with_unfolding_all exact hy.const_smul alpha
  have hlin : Differentiable ℝ (fun z : ℝ => alpha * z) :=
    fun z => (hasDerivAt_const_mul (x := z) alpha).differentiableAt
  have hlin' : DifferentiableAt ℝ (deriv (fun z : ℝ => alpha * z)) (F.rho t x) := by
    have hderiv : deriv (fun z : ℝ => alpha * z) = fun _ => alpha := by
      funext z
      exact (hasDerivAt_const_mul (x := z) alpha).deriv
    rw [hderiv]
    exact differentiableAt_const alpha
  have hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (S.base.metric t) (u t))) x :=
    grad_comp_mdiffAt (S.base.metric t) hlin hlin' F.space_diff_nhds F.grad_diff
  have hvalue : Differentiable ℝ DifferentialGeometry.Analysis.CutoffProfile.value :=
    DifferentialGeometry.Analysis.CutoffProfile.contDiff.differentiable (by simp)
  have hvalue' : DifferentiableAt ℝ
      (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x) := by
    have hC2 : ContDiff ℝ 2 DifferentialGeometry.Analysis.CutoffProfile.value :=
      DifferentialGeometry.Analysis.CutoffProfile.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (hC2.deriv' (n := 1)).differentiable (by simp) (u t x)
  have hphi_time : DifferentiableWithinAt ℝ (fun s => phi s x) (Icc 0 T) t := by
    exact (hvalue (u t x)).comp_differentiableWithinAt t hu_time
  have hphi_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (phi t) y := by
    filter_upwards [hu_space] with y hy
    exact (hvalue (u t y)).mdifferentiableAt.comp y hy
  have hphi_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (S.base.metric t) (phi t))) x :=
    grad_comp_mdiffAt (S.base.metric t) hvalue hvalue' hu_space hu_grad
  have hreal (s : ℝ) (y : M)
      (hy : riemannianEDistOf (I := I) (S.base.metric s) O y ≠ ⊤) :
      DifferentialGeometry.Analysis.CutoffProfile.evalue
          (ENNReal.ofReal (alpha * Real.exp (Lambda * s)) *
            riemannianEDistOf (I := I) (S.base.metric s) O y) =
        DifferentialGeometry.Analysis.CutoffProfile.value
          (alpha * (Real.exp (Lambda * s) *
            (riemannianEDistOf (I := I) (S.base.metric s) O y).toReal)) := by
    rw [DifferentialGeometry.Analysis.CutoffProfile.evalue_eq_value
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_pos ha (Real.exp_pos _)).le]
    congr 1
    ring
  have hfinite_nhds : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 ≠ ⊤ := by
    filter_upwards [hedist (Iio_mem_nhds hfinite.lt_top)] with p hp
    exact ne_of_lt hp
  have heq : phi t x = DifferentialGeometry.Analysis.CutoffProfile.evalue
      (ENNReal.ofReal (alpha * Real.exp (Lambda * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) O x) := by
    rw [hreal t x hfinite]
    dsimp only [phi, u]
    rw [F.eq_at]
  have hlower : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      0 ≤ phi p.1 p.2 ∧ phi p.1 p.2 ≤
        DifferentialGeometry.Analysis.CutoffProfile.evalue
          (ENNReal.ofReal (alpha * Real.exp (Lambda * p.1)) *
            riemannianEDistOf (I := I) (S.base.metric p.1) O p.2) := by
    filter_upwards [F.upper_nhds, hfinite_nhds] with p hp hfin
    refine ⟨(DifferentialGeometry.Analysis.CutoffProfile.mem_Icc _).1, ?_⟩
    rw [hreal p.1 p.2 hfin]
    exact DifferentialGeometry.Analysis.CutoffProfile.antitone_value
      (mul_le_mul_of_nonneg_left hp ha.le)
  have hgrad_u : gradientFun (I := I) (S.base.metric t) (u t) x =
      alpha • gradientFun (I := I) (S.base.metric t) (F.rho t) x := by
    exact gradientFun_const_smul (S.base.metric t) alpha F.space_diff_nhds.self_of_nhds
  have hexp2 : Real.exp (2 * Lambda * t) ≤ U ^ 2 := by
    have hid : Real.exp (2 * Lambda * t) = Real.exp (Lambda * t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hid]
    exact (sq_le_sq₀ (Real.exp_pos _).le hU).2 he
  have hGu : (S.base.metric t).inner x
      (gradientFun (I := I) (S.base.metric t) (u t) x)
      (gradientFun (I := I) (S.base.metric t) (u t) x) ≤ alpha ^ 2 * U ^ 2 := by
    rw [hgrad_u, SmoothRiemannianMetric.metric_inner_smul_self]
    exact (mul_le_mul_of_nonneg_left F.grad_sq (sq_nonneg alpha)).trans
      (mul_le_mul_of_nonneg_left hexp2 (sq_nonneg alpha))
  have hgrad_phi : gradientFun (I := I) (S.base.metric t) (phi t) x =
      deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x) •
        gradientFun (I := I) (S.base.metric t) (u t) x :=
    gradientFun_comp (S.base.metric t) (hvalue (u t x)) hu_space.self_of_nhds
  have hgradient : (S.base.metric t).inner x
      (gradientFun (I := I) (S.base.metric t) (phi t) x)
      (gradientFun (I := I) (S.base.metric t) (phi t) x) ≤ eps * phi t x := by
    rw [hgrad_phi, SmoothRiemannianMetric.metric_inner_smul_self]
    have hprofile := profileGradientCost_spec.2 (u t x)
    have hphi0 := (DifferentialGeometry.Analysis.CutoffProfile.mem_Icc (u t x)).1
    calc
      _ ≤ (deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x)) ^ 2 *
          (alpha ^ 2 * U ^ 2) := mul_le_mul_of_nonneg_left hGu (sq_nonneg _)
      _ ≤ (profileGradientCost * phi t x) * (alpha ^ 2 * U ^ 2) :=
        mul_le_mul_of_nonneg_right hprofile (by positivity)
      _ = (profileGradientCost * alpha ^ 2 * U ^ 2) * phi t x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgradCost hphi0
  have hpar_u : parabolicOperatorWithDrift (I := I) (flowG S) T
      (fun _ y => (0 : TangentSpace I y)) u t x =
        alpha * parabolicOperatorWithDrift (I := I) (flowG S) T
          (fun _ y => (0 : TangentSpace I y)) F.rho t x := by
    have htime : derivWithin (fun s => u s x) (Icc 0 T) t =
        alpha * derivWithin (fun s => F.rho s x) (Icc 0 T) t :=
      derivWithin_const_mul alpha F.time_diff
    have hlap : laplacianAt (I := I) (flowG S) t (u t) x =
        alpha * laplacianAt (I := I) (flowG S) t (F.rho t) x := by
      rw [laplacianAt_eq, laplacianAt_eq]
      exact laplacian_smul_at (LeviCivita (S.base.metric t)) (S.base.metric t) alpha
        F.space_diff_nhds F.grad_diff
    rw [parabolicOperatorWithDrift_eq, parabolicOperatorWithDrift_eq,
      heatOperatorWithDrift_zero_drift, heatOperatorWithDrift_zero_drift,
      heatOperator_eq_laplacianAt, heatOperator_eq_laplacianAt, htime, hlap]
    ring
  have hcomp := parabolic_comp_nhds (I := I) (flowG S) T
    (fun _ y => (0 : TangentSpace I y)) u t x hvalue hvalue' hu_time hu_space hu_grad
  have hpar : parabolicOperatorWithDrift (I := I) (flowG S) T
      (fun _ y => (0 : TangentSpace I y)) phi t x ≤ eps := by
    by_cases hsmall : u t x ≤ 1
    · change parabolicOperatorWithDrift (I := I) (flowG S) T _
        (fun s y => DifferentialGeometry.Analysis.CutoffProfile.value (u s y)) t x ≤ eps
      rw [hcomp, DifferentialGeometry.Analysis.CutoffProfile.deriv_zero_of_le hsmall,
        DifferentialGeometry.Analysis.CutoffProfile.deriv2_zero_of_le hsmall]
      simpa using hC
    · have hactive : 1 ≤ alpha * Real.exp (Lambda * t) *
          (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal := by
        have hu_eq : u t x = alpha * Real.exp (Lambda * t) *
            (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal := by
          dsimp only [u]
          rw [F.eq_at]
          ring
        rw [← hu_eq]
        exact (lt_of_not_ge hsmall).le
      have hr : 0 < (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal := by
        have hp := lt_of_lt_of_le zero_lt_one hactive
        exact (mul_pos_iff_of_pos_left (mul_pos ha (Real.exp_pos _))).mp hp
      have hh := finite_parabolic_algebra alpha U (n-1) (Real.sqrt ((n-1)*Lambda))
        DifferentialGeometry.Analysis.CutoffProfile.derivBound
        (Real.exp (Lambda*t)) _ _
        (deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x))
        (deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x))
        ((S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (u t) x)
          (gradientFun (I := I) (S.base.metric t) (u t) x))
        ha.le hU (sub_nonneg.mpr hn) (Real.sqrt_nonneg _)
        DifferentialGeometry.Analysis.CutoffProfile.derivBound_nonneg
        (Real.exp_pos _).le he hr hactive F.par_lower
        (DifferentialGeometry.Analysis.CutoffProfile.deriv_nonpos _)
        (DifferentialGeometry.Analysis.CutoffProfile.abs_deriv_le_derivBound _)
        (DifferentialGeometry.Analysis.CutoffProfile.abs_deriv2_le_derivBound _)
        (metric_inner_self_nonneg (S.base.metric t) x _) hGu
      change parabolicOperatorWithDrift (I := I) (flowG S) T _
        (fun s y => DifferentialGeometry.Analysis.CutoffProfile.value (u s y)) t x ≤ eps
      rw [hcomp, hpar_u]
      exact hh.trans hparCost
  exact ⟨{
    phi := phi
    eq_at := heq
    lower_nhds := hlower
    time_diff := hphi_time
    space_diff_nhds := hphi_space
    grad_diff := hphi_grad
    grad_sq_le := hgradient
    parabolic_le := hpar }⟩

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem finite_cost_bounds {n R : ℝ} (hn : 1 ≤ n) (hR : 0 < R) :
    let U := Real.exp (n ^ 2)
    let alpha := 8 / R
    let Lambda := n ^ 2 / R ^ 2
    let eps := (1 + (64 * profileGradientCost +
      DifferentialGeometry.Analysis.CutoffProfile.derivBound * (136 * n ^ 2 + 64)) *
        Real.exp (2 * n ^ 2)) / R ^ 2
    profileGradientCost * alpha ^ 2 * U ^ 2 ≤ eps ∧
      DifferentialGeometry.Analysis.CutoffProfile.derivBound *
        (2 * (n - 1) * alpha ^ 2 * U ^ 2 +
          alpha * U * Real.sqrt ((n - 1) * Lambda) + alpha ^ 2 * U ^ 2) ≤ eps := by
  dsimp only
  let U := Real.exp (n ^ 2)
  let C := DifferentialGeometry.Analysis.CutoffProfile.derivBound
  have hC : 0 ≤ C := DifferentialGeometry.Analysis.CutoffProfile.derivBound_nonneg
  have hG := profileGradientCost_spec.1
  have hc : n - 1 ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
  have hU : 0 < U := Real.exp_pos _
  have hU1 : 1 ≤ U := Real.one_le_exp (sq_nonneg n)
  have hU2 : Real.exp (2 * n ^ 2) = U ^ 2 := by
    dsimp only [U]
    rw [← Real.exp_nat_mul]
    congr 1
  have hroot : Real.sqrt ((n - 1) * (n ^ 2 / R ^ 2)) ≤ n ^ 2 / R := by
    apply (Real.sqrt_le_iff).2
    refine ⟨div_nonneg (sq_nonneg n) hR.le, ?_⟩
    have hh := mul_le_mul_of_nonneg_right hc (div_nonneg (sq_nonneg n) (sq_nonneg R))
    exact hh.trans_eq (by ring)
  have hpart : 2 * (n - 1) * (8 / R) ^ 2 * U ^ 2 +
      (8 / R) * U * Real.sqrt ((n - 1) * (n ^ 2 / R ^ 2)) +
      (8 / R) ^ 2 * U ^ 2 ≤ (136 * n ^ 2 + 64) * U ^ 2 / R ^ 2 := by
    have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
      (show 0 ≤ (8 / R) ^ 2 * U ^ 2 by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hroot (show 0 ≤ (8 / R) * U by positivity)
    have hUle : U ≤ U ^ 2 := by nlinarith only [hU1]
    have hthird := mul_le_mul_of_nonneg_left hUle
      (show 0 ≤ 8 * n ^ 2 / R ^ 2 by positivity)
    calc
      _ ≤ 2 * n ^ 2 * (8 / R) ^ 2 * U ^ 2 +
          (8 / R) * U * (n ^ 2 / R) + (8 / R) ^ 2 * U ^ 2 := by
        nlinarith only [hfirst, hsecond]
      _ = 128 * n ^ 2 * U ^ 2 / R ^ 2 + 8 * n ^ 2 / R ^ 2 * U +
          64 * U ^ 2 / R ^ 2 := by field_simp [hR.ne']; ring
      _ ≤ 128 * n ^ 2 * U ^ 2 / R ^ 2 + 8 * n ^ 2 / R ^ 2 * U ^ 2 +
          64 * U ^ 2 / R ^ 2 := by linarith only [hthird]
      _ = _ := by ring
  rw [hU2]
  constructor
  · have hh : 0 ≤ 1 + C * (136 * n ^ 2 + 64) * U ^ 2 := by positivity
    apply (le_div_iff₀ (sq_pos_of_pos hR)).2
    have hid : profileGradientCost * (8 / R) ^ 2 * U ^ 2 * R ^ 2 =
        64 * profileGradientCost * U ^ 2 := by field_simp [hR.ne']; ring
    rw [hid]
    dsimp only [C] at hh
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hpart hC
    have hextra : 0 ≤ (1 + 64 * profileGradientCost * U ^ 2) / R ^ 2 := by positivity
    calc
      _ ≤ C * ((136 * n ^ 2 + 64) * U ^ 2 / R ^ 2) := hh
      _ ≤ C * ((136 * n ^ 2 + 64) * U ^ 2 / R ^ 2) +
          (1 + 64 * profileGradientCost * U ^ 2) / R ^ 2 := le_add_of_nonneg_right hextra
      _ = _ := by dsimp only [C]; ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem actual_ball_support
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T t : ℝ} (hT : 0 < T) (hreg : Ioc 0 T ⊆ D.regular)
    (ht : t ∈ Icc 0 T) (htpos : 0 < t)
    (htB : t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M} (hOx : B.center ≠ x)
    (hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (B.radius / 2)) :
    Nonempty (DistanceBarrier.ScaledDistanceSupport (I := I) S B.center T t x
      (Module.finrank ℝ E) ((Module.finrank ℝ E : ℝ) ^ 2 / B.radius ^ 2)
      (riemannianEDistOf (I := I) (S.base.metric t) B.center x).toReal) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨(S.base.metric t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner, (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hx' : x ∈ Metric.eball B.center (ENNReal.ofReal (B.radius / 2)) := by
    rw [Metric.mem_eball', IsRiemannianManifold.out (I := I)]
    exact hx
  simpa only [riemannianEDistOf] using exists_ballFlow hS B hB hT hreg ht htpos htB hEnorm hOx hx'

theorem finite_distance_cutoff_on_controlled_ball
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    (hT : 0 < (time : ℝ)) (hTR : (time : ℝ) ≤ B.radius ^ 2)
    (hreg : Ioc 0 (time : ℝ) ⊆ D.regular)
    (hcomplete : ∀ s ∈ Icc 0 (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hqual : ∃ Kqual : ℝ, 0 ≤ Kqual ∧ ∀ s ∈ Icc 0 (time : ℝ), ∀ x : M,
      normSq0S (I := I) (S.base.metric s) x 4 (S.base.rm04 s x) ≤ Kqual) :
    let chi := finiteDistanceCutoff S B.radius B.center
    let eps := finiteDistanceCutoffConstant (Module.finrank ℝ E) / B.radius ^ 2
    (∀ s ∈ Icc 0 (time : ℝ), ∀ x, chi s x ∈ Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc 0 (time : ℝ), chi s B.center = 1) ∧
    ContinuousOn (fun p : ℝ × M => chi p.1 p.2) (spacetimeSlab (M := M) (time : ℝ)) ∧
    (∀ s ∈ Icc 0 (time : ℝ), ∀ x, 0 < chi s x → x ∈ B.setAt s) ∧
    (∀ s ∈ Icc 0 (time : ℝ), 0 < s → ∀ x, 0 < chi s x →
      Nonempty (ParabolicCutoffLowerSupportAt (I := I) (flowG S) (time : ℝ) eps chi s x)) := by
  let T : ℝ := time
  let R := B.radius
  let n : ℝ := Module.finrank ℝ E
  let Lambda := n ^ 2 / R ^ 2
  let alpha := 8 / R
  let U := Real.exp (n ^ 2)
  let eps := finiteDistanceCutoffConstant (Module.finrank ℝ E) / R ^ 2
  let z : ℝ → M → ENNReal := fun s x => ENNReal.ofReal (alpha * Real.exp (Lambda * s)) *
    riemannianEDistOf (I := I) (S.base.metric s) B.center x
  let chi := finiteDistanceCutoff S R B.center
  have hR : 0 < R := B.radius_pos
  have ha : 0 < alpha := div_pos (by norm_num) hR
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hLambda : 0 ≤ Lambda := div_nonneg (sq_nonneg n) (sq_nonneg R)
  have heps : 0 ≤ eps := (div_pos (finiteDistanceCutoffConstant_pos _) (sq_pos_of_pos hR)).le
  have hwindow : Icc 0 T ⊆ Icc (T - R ^ 2) T := by
    intro s hs
    exact ⟨by linarith only [hs.1, hTR], hs.2⟩
  have hslab : Icc 0 T ⊆ D.carrier := fun s hs => hB.1 (hwindow hs)
  have hedist : ContinuousOn
      (fun p : ℝ × M => riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2)
      (spacetimeSlab (M := M) T) := by
    obtain ⟨Kqual, _, hRmQual⟩ := hqual
    have hric : ∀ s ∈ Icc 0 T, ∀ x : M, ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric s) x v v| ≤
          (n ^ 2 * Real.sqrt Kqual) * (S.base.metric s).inner x v v := by
      intro s hs x v
      exact ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hRmQual s hs x)
    exact edistCont_Icc S hS hslab (fun s hs => hreg ⟨hs.1, hs.2.le⟩) hric B.center
  have hzcont : ContinuousOn (fun p : ℝ × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hcoef : Continuous (fun p : ℝ × M =>
        ENNReal.ofReal (alpha * Real.exp (Lambda * p.1))) :=
      ENNReal.continuous_ofReal.comp
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_fst)))
    exact hcoef.continuousOn.ennreal_mul hedist
      (fun _ _ => Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos ha (Real.exp_pos _))))
      (fun _ _ => Or.inr ENNReal.ofReal_ne_top)
  have hcont : ContinuousOn (fun p : ℝ × M => chi p.1 p.2)
      (spacetimeSlab (M := M) T) :=
    DifferentialGeometry.Analysis.CutoffProfile.continuous_evalue.comp_continuousOn hzcont
  have hrange (s : ℝ) (x : M) : chi s x ∈ Icc (0 : ℝ) 1 :=
    DifferentialGeometry.Analysis.CutoffProfile.evalue_mem_Icc _
  have hcenter (s : ℝ) : chi s B.center = 1 := by
    apply DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
    change z s B.center ≤ 1
    dsimp only [z]
    rw [riemannianEDistOf_self]
    simp only [mul_zero, zero_le_one]
  have hsmall {s : ℝ} (hs : s ∈ Icc 0 T) {x : M} (hpos : 0 < chi s x) :
      riemannianEDistOf (I := I) (S.base.metric s) B.center x < ENNReal.ofReal (R / 4) := by
    have hz : z s x < 2 := by
      by_contra h
      have hc := DifferentialGeometry.Analysis.CutoffProfile.evalue_zero_of_ge (le_of_not_gt h)
      change chi s x = 0 at hc
      linarith
    have hcoef : 0 < alpha * Real.exp (Lambda * s) := mul_pos ha (Real.exp_pos _)
    have hfinite : riemannianEDistOf (I := I) (S.base.metric s) B.center x ≠ ⊤ := by
      intro htop
      dsimp only [z] at hz
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hcoef)] at hz
      exact not_lt_of_ge le_top hz
    have hzreal : (alpha * Real.exp (Lambda * s)) *
        (riemannianEDistOf (I := I) (S.base.metric s) B.center x).toReal < 2 := by
      have hh := (ENNReal.toReal_lt_toReal
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) (by norm_num : (2 : ENNReal) ≠ ⊤)).mpr hz
      simpa only [z, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef.le,
        ENNReal.toReal_ofNat] using hh
    have hExp : 1 ≤ Real.exp (Lambda * s) := Real.one_le_exp (mul_nonneg hLambda hs.1)
    have hd0 := ENNReal.toReal_nonneg (a := riemannianEDistOf (I := I) (S.base.metric s) B.center x)
    have hmono := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hExp ha.le) hd0
    have hd : (riemannianEDistOf (I := I) (S.base.metric s) B.center x).toReal < R / 4 := by
      have hh : alpha * (riemannianEDistOf (I := I) (S.base.metric s) B.center x).toReal < 2 := by
        nlinarith only [hmono, hzreal]
      dsimp only [alpha] at hh
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      have hmul := (div_lt_iff₀ hR).1 (show
        8 * (riemannianEDistOf (I := I) (S.base.metric s) B.center x).toReal / R < 2 by
          convert hh using 1; ring)
      linarith only [hmul]
    exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (div_pos hR (by norm_num : (0 : ℝ) < 4)).le] using hd)
  have hmem {s : ℝ} (hs : s ∈ Icc 0 T) {x : M} (hpos : 0 < chi s x) : x ∈ B.setAt s := by
    exact (hsmall hs hpos).trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hR]))
  refine ⟨fun s _ x => hrange s x, fun s _ => hcenter s, hcont,
    fun s hs x hp => hmem hs hp, ?_⟩
  intro t ht htpos x hpos
  by_cases hOx : B.center = x
  · subst x
    have hz0 : z t B.center < 1 := by
      dsimp only [z]
      rw [riemannianEDistOf_self]
      simpa only [mul_zero] using (zero_lt_one : (0 : ENNReal) < 1)
    have hnear : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, B.center), z p.1 p.2 < 1 :=
      (hzcont (t, B.center) ⟨ht, mem_univ _⟩) (Iio_mem_nhds hz0)
    refine ⟨{
      phi := fun _ _ => 1
      eq_at := (hcenter t).symm
      lower_nhds := ?_
      time_diff := differentiableWithinAt_const 1
      space_diff_nhds := Eventually.of_forall fun _ => mdifferentiableAt_const
      grad_diff := ?_
      grad_sq_le := ?_
      parabolic_le := ?_ }⟩
    · filter_upwards [hnear] with p hp
      refine ⟨zero_le_one, ?_⟩
      change 1 ≤ DifferentialGeometry.Analysis.CutoffProfile.evalue (z p.1 p.2)
      rw [DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le hp.le]
    · exact gradientFun_mdiffAt (S.base.metric t) contMDiff_const B.center
    · rw [gradientFun_const]
      simpa only [map_zero, mul_one] using heps
    · have hheat : heatOperatorWithDrift (I := I) (flowG S) t
          (fun y => (0 : TangentSpace I y)) (fun _ : M => (1 : ℝ)) B.center = 0 := by
        unfold heatOperatorWithDrift laplacianAt laplacian driftTerm gradientAt
        have hzero : gradientFun (I := I) ((flowG S).metric t) (fun _ : M => (1 : ℝ)) = 0 := by
          funext y
          exact gradientFun_const ((flowG S).metric t) 1 y
        rw [hzero]
        simp
      unfold parabolicOperatorWithDrift
      rw [hheat]
      simp only [derivWithin_fun_const, Pi.zero_apply, sub_zero]
      exact heps
  · have hhalf : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
        ENNReal.ofReal (R / 2) :=
      (hsmall ht hpos).trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hR]))
    have hfinite := ne_of_lt (hhalf.trans_le le_top)
    obtain ⟨F⟩ := actual_ball_support S hS B hB hT hreg ht htpos (hwindow ht)
      (hcomplete t ht) hOx hhalf
    have he : Real.exp (Lambda * t) ≤ U := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left (ht.2.trans hTR) hLambda
      have hid : Lambda * R ^ 2 = n ^ 2 := by dsimp only [Lambda]; field_simp [hR.ne']
      exact hmul.trans_eq hid
    have hcost := finite_cost_bounds hn hR
    exact profile_of_scaled_support S B.center ha (Real.exp_pos _).le hn heps he
      hcost.1 hcost.2 (hedist (t, x) ⟨ht, mem_univ _⟩) hfinite F

variable [T2Space (TangentBundle I M)]

theorem fixed_ball_finite_distance_cutoff
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      ∀ x ∈ B.set, B.radius ^ 4 * FlowMetricBall.rmNormSq S s x ≤ 1)
    (hcomplete : ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hqual : ∃ Kqual : ℝ, 0 ≤ Kqual ∧
      ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ x : M,
        normSq0S (I := I) (S.base.metric s) x 4 (S.base.rm04 s x) ≤ Kqual)
    (O : M)
    (hO : riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center O <
      ENNReal.ofReal (B.radius / 2))
    (b : RealTimeInterval.FlowTime D)
    (hb : (b : ℝ) ∈ Icc ((time : ℝ) - B.radius ^ 2 / 2) (time : ℝ)) :
    let R := B.radius / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2))
    let a := (b : ℝ) - R ^ 2
    let S0 := S.timeShift a
    let chi := finiteDistanceCutoff S0 R O
    let Ksupport := {x | riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center x ≤
      ENNReal.ofReal B.radius}
    IsCompact Ksupport ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, chi s x ∈ Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc 0 (R ^ 2), chi s O = 1) ∧
    ContinuousOn (fun p : ℝ × M => chi p.1 p.2) (spacetimeSlab (M := M) (R ^ 2)) ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, x ∉ Ksupport → chi s x = 0) ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, 0 < chi s x → x ∈ B.set) ∧
    (∀ s ∈ Icc 0 (R ^ 2), 0 < s → ∀ x, 0 < chi s x →
      Nonempty (ParabolicCutoffLowerSupportAt (I := I) (flowG S0) (R ^ 2)
        (finiteDistanceCutoffConstant (Module.finrank ℝ E) / R ^ 2) chi s x)) ∧
    (∀ s x, chi s x = DifferentialGeometry.Analysis.CutoffProfile.evalue
      (ENNReal.ofReal ((8 / R) * Real.exp (((Module.finrank ℝ E : ℝ) ^ 2 / R ^ 2) * s)) *
        riemannianEDistOf (I := I) (S.base.metric (s + a)) O x)) ∧
    (∀ s ∈ Icc 0 (R ^ 2), s + a ∈ Icc ((b : ℝ) - R ^ 2) (b : ℝ) ∧
      s + a ∈ D.regular) := by
  let R := B.radius / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2))
  let a := (b : ℝ) - R ^ 2
  let S0 := S.timeShift a
  have hR : 0 < R := div_pos B.radius_pos (mul_pos (by norm_num) (Real.exp_pos _))
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  obtain ⟨C, hCO, hCR, hCreg, hcontain, hC⟩ :=
    fixed_ball_moving_rm_control S hS B hslab hreg hRm O hO b hb
  change C.radius = R at hCR
  have hwindow : Icc ((b : ℝ) - R ^ 2) (b : ℝ) ⊆
      Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
    have hRq : R ≤ B.radius / 4 := by
      have he : 1 ≤ Real.exp ((Module.finrank ℝ E : ℝ) ^ 2) := Real.one_le_exp (sq_nonneg _)
      apply (div_le_iff₀ (mul_pos (by norm_num) (Real.exp_pos _))).2
      nlinarith only [he, B.radius_pos]
    have hsquare := pow_le_pow_left₀ hR.le hRq 2
    intro s hs
    refine ⟨?_, hs.2.trans hb.2⟩
    nlinarith only [hs.1, hb.1, hsquare, sq_nonneg B.radius]
  have hclock (s : ℝ) (hs : s ∈ Icc 0 (R ^ 2)) :
      s + a ∈ Icc ((b : ℝ) - R ^ 2) (b : ℝ) := by
    dsimp only [a]
    constructor <;> linarith only [hs.1, hs.2]
  have hregular (s : ℝ) (hs : s ∈ Icc 0 (R ^ 2)) : s + a ∈ D.regular := by
    apply hCreg
    simpa only [hCR] using hclock s hs
  let t0 : RealTimeInterval.FlowTime (D.timeShift a) :=
    ⟨R ^ 2, by
      change R ^ 2 + a ∈ D.carrier
      have ht : R ^ 2 + a = (b : ℝ) := by dsimp only [a]; ring
      rw [ht]
      exact b.property⟩
  let C0 : FlowMetricBall S0 t0 := ⟨O, R, hR⟩
  have hC0 : C0.IsRmControlled := by
    constructor
    · intro s hs
      change s + a ∈ D.carrier
      have hs' : s ∈ Icc 0 (R ^ 2) := by simpa only [C0, t0, sub_self] using hs
      exact hslab (hwindow (hclock s hs'))
    · intro s hs x hx
      have hs' : s ∈ Icc 0 (R ^ 2) := by simpa only [C0, t0, sub_self] using hs
      have hx' : x ∈ C.setAt (s + a) := by
        change riemannianEDistOf (I := I) (S.base.metric (s + a)) C.center x <
          ENNReal.ofReal C.radius
        change riemannianEDistOf (I := I) (S.base.metric (s + a)) O x <
          ENNReal.ofReal R at hx
        simpa only [hCO, hCR] using hx
      have hbound := hC.2 (s+a) (by simpa only [hCR] using hclock s hs') x hx'
      change R ^ 4 * FlowMetricBall.rmNormSq S (s + a) x ≤ 1
      simpa only [hCR] using hbound
  have hreg0 : Ioc 0 (R ^ 2) ⊆ (D.timeShift a).regular := by
    intro s hs
    exact hregular s ⟨hs.1.le, hs.2⟩
  have hcomplete0 : ∀ s ∈ Icc 0 (R ^ 2),
      RiemannianMetricComplete (I := I) (S0.base.metric s) :=
    fun s hs => hcomplete (s+a) (hwindow (hclock s hs))
  have hqual0 : ∃ Kqual : ℝ, 0 ≤ Kqual ∧ ∀ s ∈ Icc 0 (R ^ 2), ∀ x : M,
      normSq0S (I := I) (S0.base.metric s) x 4 (S0.base.rm04 s x) ≤ Kqual := by
    obtain ⟨Kqual, hK, hbound⟩ := hqual
    exact ⟨Kqual, hK, fun s hs x => hbound (s+a) (hwindow (hclock s hs)) x⟩
  have hcut := finite_distance_cutoff_on_controlled_ball S0 (isSolutionOn_timeShift hS a)
    C0 hC0 hR2 le_rfl hreg0 hcomplete0 hqual0
  dsimp only [C0, t0] at hcut
  let chi := finiteDistanceCutoff S0 R O
  let Ksupport : Set M := {x | riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center x ≤
    ENNReal.ofReal B.radius}
  have hposset (s : ℝ) (hs : s ∈ Icc 0 (R ^ 2)) (x : M) (hp : 0 < chi s x) :
      x ∈ B.set := by
    apply hcontain (s+a) (by simpa only [hCR] using hclock s hs)
    have hx := hcut.2.2.2.1 s hs x hp
    change riemannianEDistOf (I := I) (S.base.metric (s+a)) C.center x < ENNReal.ofReal C.radius
    change riemannianEDistOf (I := I) (S.base.metric (s + a)) O x <
      ENNReal.ofReal R at hx
    simpa only [hCO, hCR] using hx
  have hzero (s : ℝ) (hs : s ∈ Icc 0 (R ^ 2)) (x : M) (hx : x ∉ Ksupport) : chi s x = 0 := by
    have hnonneg := (hcut.1 s hs x).1
    refine le_antisymm ?_ hnonneg
    by_contra h
    have hmem := hposset s hs x (lt_of_not_ge h)
    change riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center x <
      ENNReal.ofReal B.radius at hmem
    exact hx hmem.le
  have ht : (time : ℝ) ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) :=
    ⟨sub_le_self _ (sq_nonneg _), le_rfl⟩
  refine ⟨RiemannianMetricComplete.closedEBall_isCompact (hcomplete _ ht) B.center B.radius,
    hcut.1, hcut.2.1, hcut.2.2.1, hzero, hposset, hcut.2.2.2.2, ?_, ?_⟩
  · intro s x
    rfl
  · intro s hs
    exact ⟨hclock s hs, hregular s hs⟩

end DifferentialGeometry.PDE.RicciFlow

end
