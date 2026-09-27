import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import DifferentialGeometry.Analysis.Parabolic.Operator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Barrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.CalabiSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Laplacian

open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

private theorem cutoff_par_bound
    (a U c Q Cη E r P ep epp G : Real)
    (ha0 : 0 ≤ a)
    (hU : 0 ≤ U) (hc : 0 ≤ c) (hQ : 0 ≤ Q) (hCη : 0 ≤ Cη)
    (hE0 : 0 ≤ E) (hEU : E ≤ U) (hr : 0 < r)
    (hactive : 1 ≤ a * E * r)
    (hP : -E * (2 * c / r + Q) ≤ P)
    (hep0 : ep ≤ 0) (hep : |ep| ≤ Cη) (hepp : |epp| ≤ Cη)
    (hG0 : 0 ≤ G) (hG : G ≤ a ^ 2 * U ^ 2) :
    ep * (a * P) - epp * G ≤
      Cη * (2 * c * a ^ 2 * U ^ 2 + a * U * Q + a ^ 2 * U ^ 2) := by
  have hE_sq : E ^ 2 ≤ U ^ 2 :=
    (sq_le_sq₀ hE0 hU).2 hEU
  have hinv : 1 / r ≤ a * E := by
    exact (div_le_iff₀ hr).2 (by simpa [mul_assoc] using hactive)
  have hAEdiv : a * E / r ≤ a ^ 2 * U ^ 2 := by
    calc
      a * E / r = a * E * (1 / r) := by ring
      _ ≤ a * E * (a * E) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg ha0 hE0)
      _ = a ^ 2 * E ^ 2 := by ring
      _ ≤ a ^ 2 * U ^ 2 :=
        mul_le_mul_of_nonneg_left hE_sq (sq_nonneg a)
  have hA :
      a * E * (2 * c / r + Q) ≤
        2 * c * a ^ 2 * U ^ 2 + a * U * Q := by
    calc
      a * E * (2 * c / r + Q) =
          2 * c * (a * E / r) + a * E * Q := by ring
      _ ≤ 2 * c * (a ^ 2 * U ^ 2) + a * U * Q :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAEdiv
            (mul_nonneg (by norm_num) hc))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hEU ha0) hQ)
      _ = 2 * c * a ^ 2 * U ^ 2 + a * U * Q := by ring
  have hA0 : 0 ≤ a * E * (2 * c / r + Q) := by
    positivity
  have hPu :
      -(a * E * (2 * c / r + Q)) ≤ a * P := by
    have h := mul_le_mul_of_nonneg_left hP ha0
    nlinarith
  have hep_neg : -ep ≤ Cη := by
    linarith [(abs_le.mp hep).1]
  have hepp_neg : -epp ≤ Cη := by
    linarith [(abs_le.mp hepp).1]
  have hfirst :
      ep * (a * P) ≤
        Cη * (2 * c * a ^ 2 * U ^ 2 + a * U * Q) := by
    calc
      ep * (a * P) ≤
          ep * (-(a * E * (2 * c / r + Q))) :=
        mul_le_mul_of_nonpos_left hPu hep0
      _ = (-ep) * (a * E * (2 * c / r + Q)) := by ring
      _ ≤ Cη * (a * E * (2 * c / r + Q)) :=
        mul_le_mul_of_nonneg_right hep_neg hA0
      _ ≤ Cη * (2 * c * a ^ 2 * U ^ 2 + a * U * Q) :=
        mul_le_mul_of_nonneg_left hA hCη
  have hsecond : -epp * G ≤ Cη * (a ^ 2 * U ^ 2) := by
    calc
      -epp * G ≤ Cη * G :=
        mul_le_mul_of_nonneg_right hepp_neg hG0
      _ ≤ Cη * (a ^ 2 * U ^ 2) :=
        mul_le_mul_of_nonneg_left hG hCη
  calc
    ep * (a * P) - epp * G =
        ep * (a * P) + (-epp * G) := by ring
    _ ≤ Cη * (2 * c * a ^ 2 * U ^ 2 + a * U * Q) +
          Cη * (a ^ 2 * U ^ 2) :=
      add_le_add hfirst hsecond
    _ = Cη * (2 * c * a ^ 2 * U ^ 2 + a * U * Q + a ^ 2 * U ^ 2) := by
      ring

section LowerSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def DistanceBarrier.ScaledDistanceSupport.cutoffLowerSupport
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {O x : M} {T t d Λ r a U Csq Cη : Real}
    (ha : 0 ≤ a)
    (heU : Real.exp (Λ * t) ≤ U)
    (hc : 0 ≤ d - 1)
    (hr : r = (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal)
    (hfin : riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hfin_nhds : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 ≠ ⊤)
    (χ : Real → M → Real)
    (hχ : χ = fun s y =>
      DifferentialGeometry.Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (a * Real.exp (Λ * s)) *
          riemannianEDistOf (I := I) (S.base.metric s) O y))
    (hsq : ∀ s : Real,
      deriv DifferentialGeometry.Analysis.CutoffProfile.value s ^ 2 ≤
        Csq * DifferentialGeometry.Analysis.CutoffProfile.value s)
    (hη₁ : ∀ s : Real,
      |deriv DifferentialGeometry.Analysis.CutoffProfile.value s| ≤ Cη)
    (hη₂ : ∀ s : Real,
      |deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) s| ≤ Cη)
    (hρ : DistanceBarrier.ScaledDistanceSupport
      (I := I) S O T t x d Λ r) :
    ShiCutoffLowerSupportAt (I := I) (flowG (I := I) S) T
      (Csq * a ^ 2 * U ^ 2 +
        Cη * (2 * (d - 1) * a ^ 2 * U ^ 2 +
          a * U * Real.sqrt ((d - 1) * Λ) + a ^ 2 * U ^ 2)) χ t x := by
  classical
  have hU : 0 ≤ U := (Real.exp_pos _).le.trans heU
  have hCsq : 0 ≤ Csq := by
    have h := hsq 0
    rw [DifferentialGeometry.Analysis.CutoffProfile.deriv_zero_of_le (by norm_num),
      DifferentialGeometry.Analysis.CutoffProfile.one_of_le_one (by norm_num)] at h
    simpa using h
  have hCη : 0 ≤ Cη := (abs_nonneg _).trans (hη₁ 0)
  let Q : Real := Real.sqrt ((d - 1) * Λ)
  let ε : Real :=
    Csq * a ^ 2 * U ^ 2 +
      Cη * (2 * (d - 1) * a ^ 2 * U ^ 2 + a * U * Q + a ^ 2 * U ^ 2)
  let rho := hρ.rho
  let u : Real → M → Real := fun s y => a * rho s y
  let phi : Real → M → Real := fun s y =>
    DifferentialGeometry.Analysis.CutoffProfile.value (u s y)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hchi_real :
      ∀ s y,
        riemannianEDistOf (I := I) (S.base.metric s) O y ≠ ⊤ →
          χ s y = DifferentialGeometry.Analysis.CutoffProfile.value
            (a * (Real.exp (Λ * s) *
              (riemannianEDistOf (I := I) (S.base.metric s) O y).toReal)) := by
    intro s y hy
    rw [hχ]
    change DifferentialGeometry.Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (a * Real.exp (Λ * s)) *
          riemannianEDistOf (I := I) (S.base.metric s) O y) = _
    rw [DifferentialGeometry.Analysis.CutoffProfile.evalue_eq_value]
    · congr 1
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (mul_nonneg ha (Real.exp_pos _).le)]
      ring
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy
  have hu_time :
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t := by
    simpa only [u] using hρ.time_diff.const_mul a
  have hu_space :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
    filter_upwards [hρ.space_diff_nhds] with y hy
    convert hy.const_smul a using 1
    rfl
  have hu_grad : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) (S.base.metric t) (u t) y) x := by
    exact mdifferentiableAt_gradientFun_const_mul (S.base.metric t) a
      hρ.space_diff_nhds hρ.grad_diff
  have hvalue : Differentiable Real
      DifferentialGeometry.Analysis.CutoffProfile.value :=
    DifferentialGeometry.Analysis.CutoffProfile.contDiff.differentiable (by simp)
  have hvalue' : DifferentiableAt Real
      (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x) := by
    have hvalueC2 : ContDiff Real 2
        DifferentialGeometry.Analysis.CutoffProfile.value :=
      DifferentialGeometry.Analysis.CutoffProfile.contDiff.of_le (by
        have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
          exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        exact h)
    exact (hvalueC2.deriv' (n := 1)).differentiable (by simp) (u t x)
  have hphi_time :
      DifferentiableWithinAt Real (fun s => phi s x) (Set.Icc 0 T) t := by
    convert (hvalue (u t x)).comp_differentiableWithinAt t hu_time using 1 <;> rfl
  have hphi_space :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (phi t) y := by
    filter_upwards [hu_space] with y hy
    exact (hvalue (u t y)).mdifferentiableAt.comp y hy
  have hphi_grad : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) (phi t) y) x := by
    exact grad_comp_mdiffAt (I := I) (S.base.metric t)
      hvalue hvalue' hu_space hu_grad
  have hlower :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        0 ≤ phi p.1 p.2 ∧ phi p.1 p.2 ≤ χ p.1 p.2 := by
    filter_upwards [hρ.upper_nhds, hfin_nhds] with p hp hfin'
    constructor
    · exact (DifferentialGeometry.Analysis.CutoffProfile.mem_Icc (u p.1 p.2)).1
    · have hscaled :
          a * (Real.exp (Λ * p.1) *
              (riemannianEDistOf (I := I) (S.base.metric p.1) O p.2).toReal) ≤
            a * rho p.1 p.2 :=
        mul_le_mul_of_nonneg_left hp ha
      calc
        phi p.1 p.2 = DifferentialGeometry.Analysis.CutoffProfile.value
            (a * rho p.1 p.2) := rfl
        _ ≤ DifferentialGeometry.Analysis.CutoffProfile.value
            (a * (Real.exp (Λ * p.1) *
              (riemannianEDistOf (I := I) (S.base.metric p.1) O p.2).toReal)) :=
          DifferentialGeometry.Analysis.CutoffProfile.antitone_value hscaled
        _ = χ p.1 p.2 := (hchi_real p.1 p.2 hfin').symm
  have heq : phi t x = χ t x := by
    rw [hchi_real t x hfin]
    dsimp only [phi, u, rho]
    rw [hρ.eq_at, hr]
  refine
    { phi := phi
      eq_at := heq
      lower_nhds := hlower
      time_diff := hphi_time
      space_diff_nhds := hphi_space
      grad_diff := hphi_grad
      grad_sq_le := ?_
      parabolic_le := ?_ }
  · have hu_xdiff := hu_space.self_of_nhds
    have hgrad_u :
        gradientFun (I := I) (S.base.metric t) (u t) x =
          a • gradientFun (I := I) (S.base.metric t) (rho t) x := by
      have hu_eq : u t = a • rho t := by
        funext y
        simp only [u, Pi.smul_apply, smul_eq_mul]
      rw [hu_eq]
      exact gradientFun_const_smul (I := I) (S.base.metric t) a
        hρ.space_diff_nhds.self_of_nhds
    have hgrad_phi :
        gradientFun (I := I) (S.base.metric t) (phi t) x =
          deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x) •
            gradientFun (I := I) (S.base.metric t) (u t) x := by
      simpa only [phi] using
        (gradientFun_comp (I := I) (S.base.metric t)
          (hvalue (u t x)) hu_xdiff)
    have he_sq : Real.exp (2 * Λ * t) = Real.exp (Λ * t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have he2U : Real.exp (2 * Λ * t) ≤ U ^ 2 := by
      rw [he_sq]
      exact (sq_le_sq₀ (Real.exp_pos _).le hU).2 heU
    have hgrad_u_sq :
        (S.base.metric t).inner x
            (gradientFun (I := I) (S.base.metric t) (u t) x)
            (gradientFun (I := I) (S.base.metric t) (u t) x) ≤
          a ^ 2 * U ^ 2 := by
      rw [hgrad_u, metric_inner_smul_self (I := I) (S.base.metric t) x]
      exact (mul_le_mul_of_nonneg_left hρ.grad_sq (sq_nonneg a)).trans
        (mul_le_mul_of_nonneg_left he2U (sq_nonneg a))
    have hprofile := hsq (u t x)
    have hphi_nonneg : 0 ≤ DifferentialGeometry.Analysis.CutoffProfile.value (u t x) :=
      (DifferentialGeometry.Analysis.CutoffProfile.mem_Icc (u t x)).1
    have hmain : Csq * a ^ 2 * U ^ 2 ≤ ε := by
      dsimp only [ε]
      exact le_add_of_nonneg_right (mul_nonneg hCη (by positivity))
    calc
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (phi t) x)
          (gradientFun (I := I) (S.base.metric t) (phi t) x) =
          (deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x)) ^ 2 *
            (S.base.metric t).inner x
              (gradientFun (I := I) (S.base.metric t) (u t) x)
              (gradientFun (I := I) (S.base.metric t) (u t) x) := by
        rw [hgrad_phi, metric_inner_smul_self (I := I) (S.base.metric t) x]
      _ ≤ (deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x)) ^ 2 *
            (a ^ 2 * U ^ 2) :=
        mul_le_mul_of_nonneg_left hgrad_u_sq (sq_nonneg _)
      _ ≤ (Csq * DifferentialGeometry.Analysis.CutoffProfile.value (u t x)) *
            (a ^ 2 * U ^ 2) :=
        mul_le_mul_of_nonneg_right hprofile (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Csq * a ^ 2 * U ^ 2) * phi t x := by
        dsimp only [phi]
        ring
      _ ≤ ε * phi t x :=
        mul_le_mul_of_nonneg_right hmain hphi_nonneg
  · have hpar_u :
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) u t x =
          a * parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) rho t x := by
      exact parabolic_smul_nhds T (fun _ y => (0 : TangentSpace I y)) a rho t x
        hρ.space_diff_nhds hρ.grad_diff
    have hcomp :
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) phi t x =
          deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x) *
            parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
              (fun _ y => (0 : TangentSpace I y)) u t x -
          deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x) *
            (S.base.metric t).inner x
              (gradientFun (I := I) (S.base.metric t) (u t) x)
              (gradientFun (I := I) (S.base.metric t) (u t) x) := by
      simpa only [phi, gradientAt, flowG] using
        (parabolic_comp_nhds (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y))
          (φ := DifferentialGeometry.Analysis.CutoffProfile.value)
          u t x hvalue hvalue' hu_time hu_space hu_grad)
    by_cases hsmall : u t x ≤ 1
    · calc
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) phi t x =
            deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x) *
              parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
                (fun _ y => (0 : TangentSpace I y)) u t x -
            deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x) *
              (S.base.metric t).inner x
                (gradientFun (I := I) (S.base.metric t) (u t) x)
                (gradientFun (I := I) (S.base.metric t) (u t) x) := hcomp
        _ = 0 := by
          rw [DifferentialGeometry.Analysis.CutoffProfile.deriv_zero_of_le hsmall,
            DifferentialGeometry.Analysis.CutoffProfile.deriv2_zero_of_le hsmall]
          ring
        _ ≤ ε := by
          dsimp only [ε]
          positivity
    · let e : Real := Real.exp (Λ * t)
      let r0 : Real :=
        (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
      let Pρ : Real := parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y)) rho t x
      let G2 : Real := (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (u t) x)
        (gradientFun (I := I) (S.base.metric t) (u t) x)
      have hu_gt : 1 < u t x := lt_of_not_ge hsmall
      have hu_eq : u t x = a * e * r0 := by
        dsimp only [u, e, r0, rho]
        rw [hρ.eq_at, hr]
        ring
      have hactive : 1 ≤ a * e * r0 := by
        rw [← hu_eq]
        exact hu_gt.le
      have hr0 : 0 < r0 := by
        have hprod : 0 < a * e * r0 := by
          rw [← hu_eq]
          exact lt_trans zero_lt_one hu_gt
        by_contra h
        have hn := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg ha (Real.exp_pos (Λ * t)).le) (le_of_not_gt h)
        exact (not_lt_of_ge hn) hprod
      have he_sq : Real.exp (2 * Λ * t) = e ^ 2 := by
        dsimp only [e]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have he_sq_le : Real.exp (2 * Λ * t) ≤ U ^ 2 := by
        rw [he_sq]
        exact (sq_le_sq₀ (Real.exp_pos _).le hU).2 heU
      have hgrad_u :
          gradientFun (I := I) (S.base.metric t) (u t) x =
            a • gradientFun (I := I) (S.base.metric t) (rho t) x := by
        have hu_eq : u t = a • rho t := by
          funext y
          simp only [u, Pi.smul_apply, smul_eq_mul]
        rw [hu_eq]
        exact gradientFun_const_smul (I := I) (S.base.metric t) a
          hρ.space_diff_nhds.self_of_nhds
      have hG2_nonneg : 0 ≤ G2 := by
        dsimp only [G2]
        exact metric_inner_self_nonneg (I := I) (M := M) (S.base.metric t) x _
      have hG2 : G2 ≤ a ^ 2 * U ^ 2 := by
        dsimp only [G2]
        rw [hgrad_u, metric_inner_smul_self (I := I) (S.base.metric t) x]
        exact (mul_le_mul_of_nonneg_left hρ.grad_sq (sq_nonneg a)).trans
          (mul_le_mul_of_nonneg_left he_sq_le (sq_nonneg a))
      have hparρ : -e * (2 * (d - 1) / r0 + Q) ≤ Pρ := by
        have hr0eq : r0 = r := by
          dsimp only [r0]
          exact hr.symm
        rw [hr0eq]
        simpa only [e, r0, Q, Pρ, rho] using hρ.par_lower
      have hpart :
          Cη * (2 * (d - 1) * a ^ 2 * U ^ 2 + a * U * Q + a ^ 2 * U ^ 2) ≤ ε := by
        dsimp only [ε]
        exact le_add_of_nonneg_left
          (mul_nonneg (mul_nonneg hCsq (sq_nonneg a)) (sq_nonneg U))
      calc
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) phi t x =
            deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x) *
              (a * Pρ) -
            deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x) * G2 := by
          rw [hcomp, hpar_u]
        _ ≤ Cη * (2 * (d - 1) * a ^ 2 * U ^ 2 + a * U * Q + a ^ 2 * U ^ 2) := by
          exact cutoff_par_bound a U (d - 1) Q Cη e r0 Pρ
            (deriv DifferentialGeometry.Analysis.CutoffProfile.value (u t x))
            (deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) (u t x)) G2
            ha hU hc hQ hCη (Real.exp_pos _).le heU hr0 hactive hparρ
            (DifferentialGeometry.Analysis.CutoffProfile.deriv_nonpos (u t x))
            (hη₁ (u t x)) (hη₂ (u t x)) hG2_nonneg hG2
        _ ≤ ε := hpart

end LowerSupport

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

theorem nonempty_shi_barrier_cutoff_data_of_solution
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K) :
    ∀ O : M,
      Nonempty
        (ShiBarrierCutoffData
          (I := I) (flowG (I := I) S) T O) := by
  classical
  intro O
  let dNat : Nat := Module.finrank Real E
  let d : Real := dNat
  let Λ : Real := d ^ 2 * Real.sqrt K
  let R : Nat → Real := fun n => (n : Real) + 1
  let a : Nat → Real := fun n => (R n)⁻¹
  let U : Real := Real.exp (Λ * T)
  let z : Nat → Real → M → ENNReal := fun n s y =>
    ENNReal.ofReal (Real.exp (Λ * s) / R n) *
      riemannianEDistOf (I := I) (S.base.metric s) O y
  let chi : Nat → Real → M → Real := fun n s y =>
    DifferentialGeometry.Analysis.CutoffProfile.evalue (z n s y)
  let support : Nat → Set M := fun n =>
    {y | riemannianEDistOf (I := I) (S.base.metric 0) O y ≤
      ENNReal.ofReal (2 * R n)}
  have hdNat_pos : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have hd_one : (1 : Real) ≤ d := by
    dsimp only [d]
    exact_mod_cast hdNat_pos
  have hd_sub : 0 ≤ d - 1 := sub_nonneg.mpr hd_one
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, d]
    positivity
  have hR : ∀ n, 0 < R n := by
    intro n
    dsimp only [R]
    positivity
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      normSq0S (I := I) (S.base.metric s) y 4
        (S.base.rm04 s y) ≤ K := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v := by
    intro s hs y v
    simpa only [Λ, d, dNat] using
      (ricci_quadratic_form_bound_of_solution_curvature_bound
        (I := I) S y v (hcurv0 s hs y))
  have hpde :=
    metricPDE_Icc (I := I) S hS hslab (fun _ h => hreg ⟨h.1, h.2.le⟩)
  have hequiv :=
    metricEquiv_Icc (I := I) (fun s => S.base.metric s)
      hpde hricQuad
  have hedist :=
    edistCont_Icc (I := I) S hS hslab (fun _ h => hreg ⟨h.1, h.2.le⟩) hricQuad O
  obtain ⟨Csq, hCsq, hsq⟩ :=
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  obtain ⟨Cη, hCη, hη₁, hη₂⟩ :=
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  let Q : Real := Real.sqrt ((d - 1) * Λ)
  let Ccut : Real :=
    Csq * U ^ 2 +
      Cη * (2 * (d - 1) * U ^ 2 + U * Q + U ^ 2)
  let err : Nat → Real := fun n => Ccut * a n
  have hU : 0 ≤ U := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hCcut : 0 ≤ Ccut := by
    dsimp only [Ccut]
    positivity
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    exact inv_pos.mpr (hR n)
  have ha_le_one : ∀ n, a n ≤ 1 := by
    intro n
    dsimp only [a]
    rw [inv_le_one₀]
    · dsimp only [R]
      norm_num
    · exact hR n
  have ha_sq : ∀ n, a n ^ 2 ≤ a n := by
    intro n
    nlinarith [ha_pos n, ha_le_one n]
  have herr_nonneg : ∀ n, 0 ≤ err n := by
    intro n
    exact mul_nonneg hCcut (ha_pos n).le
  have herr_tendsto : Tendsto err atTop (nhds 0) := by
    have hbase :
        Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
          atTop (nhds 0) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hmul :=
      (tendsto_const_nhds.mul hbase :
        Tendsto
          (fun n : Nat =>
            Ccut * ((1 : Real) / ((n : Real) + 1)))
          atTop (nhds (Ccut * 0)))
    simpa only [err, a, R, one_div, mul_zero] using hmul
  have hsupport_compact : ∀ n, IsCompact (support n) := by
    intro n
    simpa only [support] using
      (RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcomplete O (2 * R n))
  have hrange :
      ∀ n s y, s ∈ Set.Icc 0 T →
        chi n s y ∈ Set.Icc (0 : Real) 1 := by
    intro n s y _
    exact
      DifferentialGeometry.Analysis.CutoffProfile.evalue_mem_Icc
        (z n s y)
  have hcenter :
      ∀ s, s ∈ Set.Icc 0 T →
        ∀ᶠ n in atTop, chi n s O = 1 := by
    intro s _
    exact Filter.Eventually.of_forall fun n => by
      dsimp only [chi, z]
      apply
        DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
      rw [riemannianEDistOf_self]
      simp only [mul_zero, zero_le_one]
  have hanchor :
      ∀ s ∈ Set.Icc 0 T, ∀ y : M,
        riemannianEDistOf (I := I) (S.base.metric 0) O y ≤
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y := by
    intro s hs y
    have hmetric :
        ∀ z : M, ∀ v : TangentSpace I z,
          (S.base.metric 0).inner z v v ≤
            Real.exp (2 * Λ * s) *
              (S.base.metric s).inner z v v := by
      intro z v
      have hlo := (hequiv s hs z v).1
      have hlo' :
          Real.exp (-(2 * Λ * s)) *
              (S.base.metric 0).inner z v v ≤
            (S.base.metric s).inner z v v := by
        simpa only [sub_zero] using hlo
      calc
        (S.base.metric 0).inner z v v =
            Real.exp (2 * Λ * s) *
              (Real.exp (-(2 * Λ * s)) *
                (S.base.metric 0).inner z v v) := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
          simp only [Real.exp_zero, one_mul]
        _ ≤ Real.exp (2 * Λ * s) *
              (S.base.metric s).inner z v v :=
          mul_le_mul_of_nonneg_left hlo' (Real.exp_pos _).le
    have hdist :=
      edistOf_le_of_quad
        (I := I) (S.base.metric s) (S.base.metric 0)
        (Real.exp_pos (2 * Λ * s)) hmetric O y
    have hsqrt :
        Real.sqrt (Real.exp (2 * Λ * s)) =
          Real.exp (Λ * s) := by
      calc
        Real.sqrt (Real.exp (2 * Λ * s)) =
            Real.exp ((2 * Λ * s) / 2) :=
          (Real.exp_half _).symm
        _ = Real.exp (Λ * s) := by
          congr 1
          ring
    simpa only [hsqrt] using hdist
  have hzcont :
      ∀ n, ContinuousOn
        (fun p : Real × M => z n p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    intro n
    have hreal :
        Continuous
          (fun p : Real × M => Real.exp (Λ * p.1) / R n) := by
      change Continuous
        (fun p : Real × M =>
          Real.exp ((d ^ 2 * Real.sqrt K) * p.1) * (R n)⁻¹)
      exact
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst)).mul continuous_const
    have hcoef :
        Continuous
          (fun p : Real × M =>
            ENNReal.ofReal (Real.exp (Λ * p.1) / R n)) :=
      ENNReal.continuous_ofReal.comp hreal
    have hmul :
        ContinuousOn
          (fun p : Real × M =>
            ENNReal.ofReal (Real.exp (Λ * p.1) / R n) *
              riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2)
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
      hcoef.continuousOn.ennreal_mul hedist
        (fun p _ => Or.inl
          (ENNReal.ofReal_ne_zero_iff.mpr
            (div_pos (Real.exp_pos _) (hR n))))
        (fun _ _ => Or.inr ENNReal.ofReal_ne_top)
    simpa only [z] using hmul
  have hjoint :
      ∀ n, ContinuousOn
        (fun p : Real × M => chi n p.1 p.2)
        (Set.Icc 0 T ×ˢ support n) := by
    intro n
    have hcomp :=
      DifferentialGeometry.Analysis.CutoffProfile.continuous_evalue
        |>.comp_continuousOn (hzcont n)
    have hcomp' :
        ContinuousOn
          (fun p : Real × M => chi n p.1 p.2)
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
      with_unfolding_all exact hcomp
    exact hcomp'.mono fun p hp => ⟨hp.1, Set.mem_univ p.2⟩
  have hsupport_zero :
      ∀ n s, s ∈ Set.Icc 0 T →
        ∀ y, y ∉ support n → chi n s y = 0 := by
    intro n s hs y hy
    apply
      DifferentialGeometry.Analysis.CutoffProfile.evalue_zero_of_ge
    by_contra hz
    have hzlt : z n s y < (2 : ENNReal) := lt_of_not_ge hz
    have hR0 : ENNReal.ofReal (R n) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (hR n)
    have hRtop : ENNReal.ofReal (R n) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hmul :=
      ENNReal.mul_lt_mul_left hR0 hRtop hzlt
    have hleft :
        z n s y * ENNReal.ofReal (R n) =
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y := by
      dsimp only [z]
      rw [ENNReal.ofReal_div_of_pos (hR n)]
      calc
        (ENNReal.ofReal (Real.exp (Λ * s)) /
              ENNReal.ofReal (R n) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y) *
              ENNReal.ofReal (R n) =
            (ENNReal.ofReal (Real.exp (Λ * s)) /
                ENNReal.ofReal (R n) *
              ENNReal.ofReal (R n)) *
                riemannianEDistOf
                  (I := I) (S.base.metric s) O y := by
          ac_rfl
        _ = ENNReal.ofReal (Real.exp (Λ * s)) *
              riemannianEDistOf
                (I := I) (S.base.metric s) O y := by
          rw [ENNReal.div_mul_cancel hR0 hRtop]
    have hright :
        (2 : ENNReal) * ENNReal.ofReal (R n) =
          ENNReal.ofReal (2 * R n) := by
      calc
        (2 : ENNReal) * ENNReal.ofReal (R n) =
            ENNReal.ofReal 2 * ENNReal.ofReal (R n) := by
          norm_num
        _ = ENNReal.ofReal (2 * R n) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
    have hsmall :
        ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y <
          ENNReal.ofReal (2 * R n) := by
      simpa only [hleft, hright] using hmul
    have hout :
        ¬ riemannianEDistOf
            (I := I) (S.base.metric 0) O y ≤
          ENNReal.ofReal (2 * R n) := by
      simpa only [support, Set.mem_ofPred_eq] using hy
    have hlarge :
        ENNReal.ofReal (2 * R n) <
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y :=
      (lt_of_not_ge hout).trans_le (hanchor s hs y)
    exact (not_lt_of_ge hlarge.le) hsmall
  refine
    ⟨{ chi := chi
       err := err
       support := support
       err_nonneg := herr_nonneg
       err_tendsto := herr_tendsto
       support_compact := hsupport_compact
       support_zero := hsupport_zero
       range := hrange
       center_exhausts := hcenter
       joint_cont := hjoint
       lowerSupport := ?_ }⟩
  intro n t ht htpos x hxchi
  by_cases hOx : O = x
  · subst x
    let phi : Real → M → Real := fun _ _ => 1
    have hchiO : chi n t O = 1 := by
      dsimp only [chi, z]
      apply
        DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
      rw [riemannianEDistOf_self]
      simp only [mul_zero, zero_le_one]
    have hz_at :
        ContinuousWithinAt
          (fun p : Real × M => z n p.1 p.2)
          (spacetimeSlab (M := M) T) (t, O) := by
      simpa only [spacetimeSlab] using
        (hzcont n (t, O) ⟨ht, Set.mem_univ O⟩)
    have hzlt : z n t O < (1 : ENNReal) := by
      dsimp only [z]
      rw [riemannianEDistOf_self]
      simpa only [mul_zero] using (zero_lt_one : (0 : ENNReal) < 1)
    have hz_nhds :
        ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, O),
          z n p.1 p.2 < (1 : ENNReal) :=
      hz_at (Iio_mem_nhds hzlt)
    refine
      { phi := phi
        eq_at := ?_
        lower_nhds := ?_
        time_diff := ?_
        space_diff_nhds := ?_
        grad_diff := ?_
        grad_sq_le := ?_
        parabolic_le := ?_ }
    · simpa only [phi] using hchiO.symm
    · filter_upwards [hz_nhds] with p hp
      constructor
      · exact zero_le_one
      · dsimp only [phi, chi]
        rw [
          DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
            hp.le]
    · exact differentiableWithinAt_const (c := (1 : Real))
    · exact Filter.Eventually.of_forall fun _ =>
        mdifferentiableAt_const
    · simpa only [phi] using
        (gradientFun_mdiffAt
          (I := I) ((flowG (I := I) S).metric t)
          (f := fun _ : M => (1 : Real)) contMDiff_const O)
    · have hgradzero :
          gradientFun
              (I := I) ((flowG (I := I) S).metric t)
              (phi t) O = 0 := by
        exact gradientFun_const
          (I := I) ((flowG (I := I) S).metric t) 1 O
      rw [hgradzero]
      dsimp only [phi]
      simpa only [map_zero, mul_one] using herr_nonneg n
    · have hheat_one :
          heatOperatorWithDrift
              (I := I) (flowG (I := I) S) t
              (fun y => (0 : TangentSpace I y))
              (phi t) O = 0 := by
        unfold heatOperatorWithDrift laplacianAt laplacian
          driftTerm gradientAt
        have hzero :
            gradientFun
                (I := I) ((flowG (I := I) S).metric t)
                (phi t) = 0 := by
          funext y
          exact gradientFun_const
            (I := I) ((flowG (I := I) S).metric t) 1 y
        rw [hzero]
        simp
      have hpar :
          parabolicOperatorWithDrift
              (I := I) (flowG (I := I) S) T
              (fun _ y => (0 : TangentSpace I y))
              phi t O = 0 := by
        unfold parabolicOperatorWithDrift
        rw [hheat_one]
        change derivWithin (Function.const Real (1 : Real)) (Set.Icc 0 T) t - 0 = 0
        rw [derivWithin_const]
        simp only [Pi.zero_apply, sub_self]
      rw [hpar]
      exact herr_nonneg n
  · have hdist_fin :
        riemannianEDistOf
            (I := I) (S.base.metric t) O x ≠ ⊤ := by
      intro htop
      have hcoef0 :
          ENNReal.ofReal (Real.exp (Λ * t) / R n) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr
          (div_pos (Real.exp_pos _) (hR n))
      have hz_top : z n t x = ⊤ := by
        change ENNReal.ofReal (Real.exp (Λ * t) / R n) *
            riemannianEDistOf (I := I) (S.base.metric t) O x = ⊤
        rw [htop, ENNReal.mul_top hcoef0]
      have hchi_zero : chi n t x = 0 := by
        dsimp only [chi]
        rw [hz_top,
          DifferentialGeometry.Analysis.CutoffProfile.evalue_top]
      linarith
    let hrho_exists :=
      exists_scaled_distance_calabi_upper_support_of_solution
        (I := I) S hS O hT hslab hreg hcomplete hK hcurv
          ht htpos x hdist_fin hOx
    let rho := Classical.choose hrho_exists
    have hrho_spec := Classical.choose_spec hrho_exists
    have hrho_eq := hrho_spec.1
    have hrho_upper := hrho_spec.2.1
    have hrho_time := hrho_spec.2.2.1
    have hrho_space := hrho_spec.2.2.2.1
    have hrho_grad := hrho_spec.2.2.2.2.1
    have hrho_grad_sq := hrho_spec.2.2.2.2.2.1
    have hrho_par := hrho_spec.2.2.2.2.2.2
    let upper : DistanceBarrier.ScaledDistanceSupport (I := I) S O T t x d Λ
        (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal :=
      { rho := rho
        eq_at := hrho_eq
        upper_nhds := hrho_upper
        time_diff := hrho_time
        space_diff_nhds := hrho_space
        grad_diff := hrho_grad
        grad_sq := hrho_grad_sq
        par_lower := hrho_par }
    have hdist_nhds :
        ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          riemannianEDistOf
              (I := I) (S.base.metric p.1) O p.2 ≠ ⊤ := by
      have hdist_at :
          ContinuousWithinAt
            (fun p : Real × M =>
              riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2)
            (spacetimeSlab (M := M) T) (t, x) := by
        simpa only [spacetimeSlab] using
          (hedist (t, x) ⟨ht, Set.mem_univ x⟩)
      have hev :
          ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
            riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2 < ⊤ :=
        hdist_at (Iio_mem_nhds hdist_fin.lt_top)
      filter_upwards [hev] with p hp
      exact ne_of_lt hp
    have heU : Real.exp (Λ * t) ≤ U :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hΛ)
    have hchi : chi n = fun s y =>
        DifferentialGeometry.Analysis.CutoffProfile.evalue
          (ENNReal.ofReal (a n * Real.exp (Λ * s)) *
            riemannianEDistOf (I := I) (S.base.metric s) O y) := by
      funext s y
      dsimp only [chi, z, a]
      rw [div_eq_mul_inv, mul_comm (Real.exp (Λ * s))]
    let lower := DistanceBarrier.ScaledDistanceSupport.cutoffLowerSupport
      (ha_pos n).le heU hd_sub rfl hdist_fin hdist_nhds (chi n) hchi hsq hη₁ hη₂ upper
    have herr_le :
        Csq * a n ^ 2 * U ^ 2 +
          Cη * (2 * (d - 1) * a n ^ 2 * U ^ 2 +
            a n * U * Real.sqrt ((d - 1) * Λ) + a n ^ 2 * U ^ 2) ≤ err n := by
      change Csq * a n ^ 2 * U ^ 2 +
        Cη * (2 * (d - 1) * a n ^ 2 * U ^ 2 +
          a n * U * Q + a n ^ 2 * U ^ 2) ≤ Ccut * a n
      calc
        Csq * a n ^ 2 * U ^ 2 +
            Cη * (2 * (d - 1) * a n ^ 2 * U ^ 2 +
              a n * U * Q + a n ^ 2 * U ^ 2) ≤
            Csq * a n * U ^ 2 +
              Cη * (2 * (d - 1) * a n * U ^ 2 + a n * U * Q + a n * U ^ 2) := by
          gcongr
          all_goals exact ha_sq n
        _ = Ccut * a n := by dsimp only [Ccut]; ring
    exact
      { lower with
        grad_sq_le := lower.grad_sq_le.trans
          (mul_le_mul_of_nonneg_right herr_le (by
            rw [lower.eq_at]
            exact (hrange n t x ht).1))
        parabolic_le := lower.parabolic_le.trans herr_le }

end DifferentialGeometry.PDE.RicciFlow
