import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.CalabiSupport
import DifferentialGeometry.Analysis.Parabolic.Bernstein.Cutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.BernsteinMaximum
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

open DifferentialGeometry.SmoothRiemannianMetric
  (metric_inner_cauchy_schwarz_sq
   metric_inner_smul_self)

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

section Constants

def shiCutoffDerivSqConst : Real :=
  Classical.choose CutoffProfile.exists_deriv_sq


theorem shiCutoffDerivSqConst_nonneg : 0 ≤ shiCutoffDerivSqConst :=
  (Classical.choose_spec CutoffProfile.exists_deriv_sq).1

theorem deriv_sq_le_shiCutoffDerivSqConst (s : Real) :
    deriv CutoffProfile.value s ^ 2 ≤ shiCutoffDerivSqConst * CutoffProfile.value s :=
  (Classical.choose_spec CutoffProfile.exists_deriv_sq).2 s

def shiInitialCutoffA (d : ℕ) (T K r₁ r₂ : Real) : Real :=
  shiCutoffDerivSqConst * (2 / (r₂ - r₁)) ^ 2 *
    Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt K) * T)

def shiInitialCutoffB (d : ℕ) (T K r₁ r₂ Clap : Real) : Real :=
  CutoffProfile.derivBound * (2 / (r₂ - r₁)) * Clap +
    CutoffProfile.derivBound * (2 / (r₂ - r₁)) ^ 2 *
      Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt K) * T)

def shiInitialCutoffD (r₁ r₂ Cconn : Real) : Real :=
  Real.sqrt shiCutoffDerivSqConst * (2 / (r₂ - r₁)) * Cconn


theorem shiInitialCutoffA_nonneg (d : ℕ) (T K r₁ r₂ : Real) :
    0 ≤ shiInitialCutoffA d T K r₁ r₂ :=
  mul_nonneg (mul_nonneg shiCutoffDerivSqConst_nonneg (sq_nonneg _))
    (Real.exp_nonneg _)

theorem shiInitialCutoffB_nonneg (d : ℕ) {T K r₁ r₂ Clap : Real} (hr : r₁ ≤ r₂)
    (hClap : 0 ≤ Clap) : 0 ≤ shiInitialCutoffB d T K r₁ r₂ Clap := by
  have hk : (0 : Real) ≤ 2 / (r₂ - r₁) :=
    div_nonneg (by norm_num) (by linarith)
  exact add_nonneg
    (mul_nonneg (mul_nonneg CutoffProfile.derivBound_nonneg hk) hClap)
    (mul_nonneg (mul_nonneg CutoffProfile.derivBound_nonneg (sq_nonneg _))
      (Real.exp_nonneg _))

theorem shiInitialCutoffD_nonneg {r₁ r₂ Cconn : Real} (hr : r₁ ≤ r₂)
    (hCconn : 0 ≤ Cconn) : 0 ≤ shiInitialCutoffD r₁ r₂ Cconn := by
  have hk : (0 : Real) ≤ 2 / (r₂ - r₁) :=
    div_nonneg (by norm_num) (by linarith)
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hk) hCconn

end Constants



private def shiftedCutoffProfile (r₁ kk s : Real) : Real :=
  CutoffProfile.value (1 + (s - r₁) * kk)

private theorem shiftedCutoffProfile_mem_Icc (r₁ kk s : Real) :
    shiftedCutoffProfile r₁ kk s ∈ Set.Icc (0 : Real) 1 :=
  CutoffProfile.mem_Icc _

private theorem shiftedCutoffProfile_eq_one {r₁ kk s : Real}
    (hkk : 0 ≤ kk) (hs : s ≤ r₁) : shiftedCutoffProfile r₁ kk s = 1 := by
  refine CutoffProfile.one_of_le_one ?_
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hkk]

private theorem shiftedCutoffProfile_eq_zero {r₁ kk s : Real}
    (hs : 1 ≤ (s - r₁) * kk) : shiftedCutoffProfile r₁ kk s = 0 :=
  CutoffProfile.zero_of_two_le (by linarith)

private theorem shiftedCutoffProfile_antitone {r₁ kk : Real} (hkk : 0 ≤ kk) :
    Antitone (shiftedCutoffProfile r₁ kk) := by
  intro a b hab
  refine CutoffProfile.antitone_value ?_
  have := mul_le_mul_of_nonneg_right (sub_le_sub_right hab r₁) hkk
  linarith

private theorem affineDeriv (r₁ kk s : Real) :
    HasDerivAt (fun q : Real => 1 + (q - r₁) * kk) kk s := by
  simpa using (((hasDerivAt_id s).sub_const r₁).mul_const kk).const_add (1 : Real)

private theorem valueDifferentiable :
    Differentiable Real CutoffProfile.value :=
  CutoffProfile.contDiff.differentiable (by simp)

private theorem derivValueDifferentiable :
    Differentiable Real (deriv CutoffProfile.value) := by
  have hvalueC2 : ContDiff Real 2 CutoffProfile.value :=
    CutoffProfile.contDiff.of_le (by
      have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      exact h)
  exact (hvalueC2.deriv' (n := 1)).differentiable (by simp)

private theorem shiftedCutoffProfile_hasDerivAt (r₁ kk s : Real) :
    HasDerivAt (shiftedCutoffProfile r₁ kk)
      (deriv CutoffProfile.value (1 + (s - r₁) * kk) * kk) s :=
  (valueDifferentiable (1 + (s - r₁) * kk)).hasDerivAt.comp s
    (affineDeriv r₁ kk s)

private theorem shiftedCutoffProfile_differentiable (r₁ kk : Real) :
    Differentiable Real (shiftedCutoffProfile r₁ kk) := fun s =>
  (shiftedCutoffProfile_hasDerivAt r₁ kk s).differentiableAt

private theorem shiftedCutoffProfile_deriv (r₁ kk : Real) :
    deriv (shiftedCutoffProfile r₁ kk) =
      fun s : Real => deriv CutoffProfile.value (1 + (s - r₁) * kk) * kk :=
  funext fun s => (shiftedCutoffProfile_hasDerivAt r₁ kk s).deriv

private theorem shiftedCutoffProfile_hasDerivAt2 (r₁ kk s : Real) :
    HasDerivAt (deriv (shiftedCutoffProfile r₁ kk))
      (deriv (deriv CutoffProfile.value) (1 + (s - r₁) * kk) * kk * kk) s := by
  rw [shiftedCutoffProfile_deriv]
  exact
    ((derivValueDifferentiable (1 + (s - r₁) * kk)).hasDerivAt.comp s
      (affineDeriv r₁ kk s)).mul_const kk

private theorem shiftedCutoffProfile_deriv2 (r₁ kk s : Real) :
    deriv (deriv (shiftedCutoffProfile r₁ kk)) s =
      deriv (deriv CutoffProfile.value) (1 + (s - r₁) * kk) * kk * kk :=
  (shiftedCutoffProfile_hasDerivAt2 r₁ kk s).deriv

private theorem selfCoupled_parabolic_bound
    {e1 e2 Ca Cs Cb lap gsq Ugrad Clap Cconn Th : Real}
    (he1 : -e1 ≤ Ca) (he1s : -e1 ≤ Cs) (hne1 : 0 ≤ -e1)
    (he2 : -e2 ≤ Cb) (hCb : 0 ≤ Cb)
    (hlap : lap ≤ Clap + Cconn * Th) (hClap : 0 ≤ Clap)
    (hCT : 0 ≤ Cconn * Th)
    (hg0 : 0 ≤ gsq) (hg : gsq ≤ Ugrad) :
    e1 * -lap - e2 * gsq ≤ (Ca * Clap + Cb * Ugrad) + Cs * (Cconn * Th) := by
  have h1 : (-e1) * lap ≤ Ca * Clap + Cs * (Cconn * Th) := by
    calc
      (-e1) * lap ≤ (-e1) * (Clap + Cconn * Th) :=
        mul_le_mul_of_nonneg_left hlap hne1
      _ = (-e1) * Clap + (-e1) * (Cconn * Th) := by ring
      _ ≤ Ca * Clap + Cs * (Cconn * Th) :=
        add_le_add (mul_le_mul_of_nonneg_right he1 hClap)
          (mul_le_mul_of_nonneg_right he1s hCT)
  have h2 : (-e2) * gsq ≤ Cb * Ugrad := by
    calc
      (-e2) * gsq ≤ Cb * gsq := mul_le_mul_of_nonneg_right he2 hg0
      _ ≤ Cb * Ugrad := mul_le_mul_of_nonneg_left hg hCb
  have hrw : e1 * -lap - e2 * gsq = (-e1) * lap + (-e2) * gsq := by ring
  rw [hrw]
  linarith [h1, h2]



variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]

structure ShiSelfCoupledLowerSupportAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T A : Real)
    (Λ : Real → M → Real)
    (χ : Real → M → Real)
    (t : Real) (x : M) where
  phi : Real → M → Real
  eq_at : phi t x = χ t x
  lower_nhds :
    ∀ᶠ q in 𝓝[spacetimeSlab (M := M) T] (t, x),
      0 ≤ phi q.1 q.2 ∧ phi q.1 q.2 ≤ χ q.1 q.2
  time_diff :
    DifferentiableWithinAt Real (fun s => phi s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (phi t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (phi t) y) x
  grad_sq_le :
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (phi t) x)
        (gradientFun (I := I) (G.metric t) (phi t) x) ≤
      A * phi t x
  parabolic_le :
    parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) phi t x ≤ Λ t x

def ShiSelfCoupledLowerSupportAt.toCutoffLowerSupport
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T A eps : Real} {Λ χ : Real → M → Real} {t : Real} {x : M}
    (h : ShiSelfCoupledLowerSupportAt (I := I) G T A Λ χ t x)
    (hA : A ≤ eps) (hΛ : Λ t x ≤ eps) (hχ : 0 ≤ χ t x) :
    ParabolicCutoffLowerSupportAt (I := I) G T eps χ t x where
  phi := h.phi
  eq_at := h.eq_at
  lower_nhds := h.lower_nhds
  time_diff := h.time_diff
  space_diff_nhds := h.space_diff_nhds
  grad_diff := h.grad_diff
  grad_sq_le := by
    refine h.grad_sq_le.trans ?_
    have hphi : 0 ≤ h.phi t x := by rw [h.eq_at]; exact hχ
    exact mul_le_mul_of_nonneg_right hA hphi
  parabolic_le := h.parabolic_le.trans hΛ

def InitialDistanceFlowLaplacianBound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (p : M) (B : Set M) (r₁ Ksec Clap Cconn : Real)
    (Theta : Real → M → Real) : Prop :=
  ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x ∈ B, ∀ rho : M → Real, ∀ U : Set M,
    IsOpen U → x ∈ U → ContMDiffOn I 𝓘(Real, Real) ∞ rho U →
    r₁ ≤ rho x →
    rho x = (riemannianEDistOf (I := I) (S.base.metric 0) p x).toReal →
    (∀ᶠ y in 𝓝 x,
      (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal ≤ rho y) →
    (S.base.metric 0).inner x
        (gradientFun (I := I) (S.base.metric 0) rho x)
        (gradientFun (I := I) (S.base.metric 0) rho x) = 1 →
    (∀ Y : TangentSpace I x,
      hessFun (I := I) (S.base.metric 0) rho x Y Y ≤
        (2 / rho x + Real.sqrt (-Ksec)) * (S.base.metric 0).inner x Y Y) →
    laplacianAt (I := I) (flowG (I := I) S) t rho x ≤
      Clap + Cconn * Theta t x

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
theorem hessianComparisonConstant_zero (g : SmoothRiemannianMetric I M)
    (rho : M → Real) (x : M) (Y : TangentSpace I x) :
    (2 / rho x + Real.sqrt (-(0 : Real))) * g.inner x Y Y =
      2 * g.inner x Y Y / rho x := by
  rw [neg_zero, Real.sqrt_zero]
  ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] in
theorem initialDistanceFlowLaplacianBound_zero_iff
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (p : M) (B : Set M) (r₁ Clap Cconn : Real)
    (Theta : Real → M → Real) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ 0 Clap Cconn Theta ↔
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x ∈ B, ∀ rho : M → Real, ∀ U : Set M,
        IsOpen U → x ∈ U → ContMDiffOn I 𝓘(Real, Real) ∞ rho U →
        r₁ ≤ rho x →
        rho x = (riemannianEDistOf (I := I) (S.base.metric 0) p x).toReal →
        (∀ᶠ y in 𝓝 x,
          (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal ≤ rho y) →
        (S.base.metric 0).inner x
            (gradientFun (I := I) (S.base.metric 0) rho x)
            (gradientFun (I := I) (S.base.metric 0) rho x) = 1 →
        (∀ Y : TangentSpace I x,
          hessFun (I := I) (S.base.metric 0) rho x Y Y ≤
            2 * (S.base.metric 0).inner x Y Y / rho x) →
        laplacianAt (I := I) (flowG (I := I) S) t rho x ≤
          Clap + Cconn * Theta t x := by
  constructor
  · intro h t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq hhess
    refine h t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq fun Y => ?_
    rw [hessianComparisonConstant_zero (I := I) (S.base.metric 0) rho x Y]
    exact hhess Y
  · intro h t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq hhess
    refine h t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq fun Y => ?_
    rw [← hessianComparisonConstant_zero (I := I) (S.base.metric 0) rho x Y]
    exact hhess Y

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] in
theorem sectionalBoundedBelow_zero_of_mem_cone (g : SmoothRiemannianMetric I M)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    SectionalBoundedBelow (I := I) g 0 := fun y =>
  (sectionalBoundedBelowAt_zero_iff (I := I) g y).mpr (hsec y)

structure ShiInitialDistanceCutoff
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (p : M) (r₁ r₂ A B Dcoef : Real)
    (Theta : Real → M → Real) where
  chi : M → Real
  support : Set M
  chi_continuous : Continuous chi
  chi_mem_Icc : ∀ x : M, chi x ∈ Set.Icc (0 : Real) 1
  chi_eq_one :
    ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
        chi x = 1
  support_compact : IsCompact support
  support_subset_ball :
    support ⊆
      {y : M |
        riemannianEDistOf (I := I) (S.base.metric 0) p y <
          ENNReal.ofReal r₂}
  support_zero : ∀ x : M, x ∉ support → chi x = 0
  lower_support :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < chi x →
      Nonempty
        (ShiSelfCoupledLowerSupportAt (I := I) (flowG (I := I) S) T A
          (fun s y => B + Dcoef * Real.sqrt (chi y) * Theta s y)
          (fun _ y => chi y) t x)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem gradientFun_sq_le_of_metric_le
    (g₀ g₁ : SmoothRiemannianMetric I M) {x : M} {c A : Real}
    (hc0 : 0 ≤ c) (hA0 : 0 ≤ A)
    (hle : ∀ v : TangentSpace I x, g₀.inner x v v ≤ c * g₁.inner x v v)
    (f : M → Real)
    (hA : g₀.inner x (gradientFun (I := I) g₀ f x)
      (gradientFun (I := I) g₀ f x) ≤ A) :
    g₁.inner x (gradientFun (I := I) g₁ f x)
      (gradientFun (I := I) g₁ f x) ≤ c * A := by
  set X : TangentSpace I x := gradientFun (I := I) g₁ f x with hX
  set Y : TangentSpace I x := gradientFun (I := I) g₀ f x with hY
  have hz0 : 0 ≤ g₁.inner x X X :=
    metric_inner_self_nonneg (I := I) (M := M) g₁ x X
  have hbnn : 0 ≤ g₀.inner x X X :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x X
  have hkey : g₁.inner x X X = g₀.inner x Y X := by
    rw [hX, hY, inner_gradientFun (I := I) g₁ f x X,
      inner_gradientFun (I := I) g₀ f x X]
  have hcs : (g₀.inner x Y X) ^ 2 ≤ g₀.inner x Y Y * g₀.inner x X X :=
    metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x Y X
  have h1 : (g₁.inner x X X) ^ 2 ≤ (c * A) * g₁.inner x X X := by
    calc
      (g₁.inner x X X) ^ 2 = (g₀.inner x Y X) ^ 2 := by rw [hkey]
      _ ≤ g₀.inner x Y Y * g₀.inner x X X := hcs
      _ ≤ A * g₀.inner x X X := mul_le_mul_of_nonneg_right hA hbnn
      _ ≤ A * (c * g₁.inner x X X) :=
        mul_le_mul_of_nonneg_left (hle X) hA0
      _ = (c * A) * g₁.inner x X X := by ring
  rcases eq_or_lt_of_le hz0 with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hc0 hA0
  · have h2 : g₁.inner x X X * g₁.inner x X X ≤ (c * A) * g₁.inner x X X := by
      rw [← pow_two]
      exact h1
    exact le_of_mul_le_mul_right h2 hpos

omit [IsManifold I 1 M] in
private theorem exists_initialDistance_calabi_support
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {R Ksec : Real} (p x : M)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hpx : p ≠ x)
    (hx : riemannianEDistOf (I := I) (S.base.metric 0) p x <
      ENNReal.ofReal R) :
    ∃ rho : M → Real, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(Real, Real) ∞ rho U ∧
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      rho x = (riemannianEDistOf (I := I) (S.base.metric 0) p x).toReal ∧
      (∀ᶠ y in 𝓝 x,
        (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal ≤ rho y) ∧
      (S.base.metric 0).inner x
          (gradientFun (I := I) (S.base.metric 0) rho x)
          (gradientFun (I := I) (S.base.metric 0) rho x) = 1 ∧
      ∀ Y : TangentSpace I x,
        hessFun (I := I) (S.base.metric 0) rho x Y Y ≤
          (2 / rho x + Real.sqrt (-Ksec)) *
            (S.base.metric 0).inner x Y Y := by
  classical
  obtain ⟨rho, U, hUopen, hxU, hrhoOn, hvalue, hupper, hgrad, hhess⟩ :=
    calabiDist_hess_support_on_of_sectional_lower_bound_of_isCompact_closedBall
      (I := I) (M := M) (S.base.metric 0) hball hKsec hsec hpx hx
  have hrhoAt : ContMDiffAt I 𝓘(Real, Real) ∞ rho x :=
    (hrhoOn x hxU).contMDiffAt (hUopen.mem_nhds hxU)
  have hrhoEv : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact ((hrhoOn y hy).contMDiffAt (hUopen.mem_nhds hy)).mdifferentiableAt
      (by simp)
  exact ⟨rho, U, hUopen, hxU, hrhoOn, hrhoAt, hrhoEv, hvalue, hupper, hgrad, hhess⟩

theorem nonempty_shiInitialDistanceCutoff_of_solution
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K Ksec R r₁ r₂ Clap Cconn : Real}
    (p : M)
    (_hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    {Theta : Real → M → Real}
    (hTheta : ∀ t : Real, ∀ y : M, 0 ≤ Theta t y)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn Theta) :
    Nonempty
      (ShiInitialDistanceCutoff (I := I) S T p r₁ r₂
        (shiInitialCutoffA (Module.finrank Real E) T K r₁ r₂)
        (shiInitialCutoffB (Module.finrank Real E) T K r₁ r₂ Clap)
        (shiInitialCutoffD r₁ r₂ Cconn) Theta) := by
  classical
  unfold shiInitialCutoffA shiInitialCutoffB shiInitialCutoffD
  set Csq : Real := shiCutoffDerivSqConst with hCsqDef
  have hCsq : (0 : Real) ≤ Csq := by
    rw [hCsqDef]
    exact shiCutoffDerivSqConst_nonneg
  have hsq : ∀ s : Real,
      deriv CutoffProfile.value s ^ 2 ≤ Csq * CutoffProfile.value s := by
    rw [hCsqDef]
    exact deriv_sq_le_shiCutoffDerivSqConst
  set Ce : Real := CutoffProfile.derivBound with hCeDef
  have hCe : (0 : Real) ≤ Ce := by
    rw [hCeDef]
    exact CutoffProfile.derivBound_nonneg
  have hCe₁ : ∀ s : Real, |deriv CutoffProfile.value s| ≤ Ce := by
    rw [hCeDef]
    exact CutoffProfile.abs_deriv_le_derivBound
  have hCe₂ : ∀ s : Real, |deriv (deriv CutoffProfile.value) s| ≤ Ce := by
    rw [hCeDef]
    exact CutoffProfile.abs_deriv2_le_derivBound
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hdiff : 0 < r₂ - r₁ := sub_pos.mpr hr₁₂
  set dR : Real := (Module.finrank Real E : Real) with hdR
  set Lam : Real := dR ^ 2 * Real.sqrt K with hLam
  set Ugrad : Real := Real.exp (2 * Lam * T) with hUgradDef
  set kk : Real := 2 / (r₂ - r₁) with hkkDef
  set rstar : Real := (r₁ + r₂) / 2 with hrstarDef
  have hk : 0 < kk := by rw [hkkDef]; exact div_pos (by norm_num) hdiff
  have hUgrad : 0 < Ugrad := by rw [hUgradDef]; exact Real.exp_pos _
  have hLam0 : 0 ≤ Lam := by rw [hLam, hdR]; positivity
  have hrstar₁ : r₁ < rstar := by rw [hrstarDef]; linarith
  have hrstar₂ : rstar < r₂ := by rw [hrstarDef]; linarith
  have hrstar0 : 0 < rstar := hr₁.trans hrstar₁
  have hkey : ∀ s : Real, rstar ≤ s → 1 ≤ (s - r₁) * kk := by
    intro s hs
    have hstep : (rstar - r₁) * kk = 1 := by
      rw [hrstarDef, hkkDef]
      field_simp
      ring
    have hmono : (rstar - r₁) * kk ≤ (s - r₁) * kk :=
      mul_le_mul_of_nonneg_right (by linarith) hk.le
    linarith [hstep ▸ hmono]
  set ed : M → ENNReal := fun y =>
    riemannianEDistOf (I := I) (S.base.metric 0) p y with hedDef
  set dtr : M → Real := fun y =>
    ENNReal.truncateToReal (ENNReal.ofReal r₂) (ed y) with hdtrDef
  set chi : M → Real := fun y => shiftedCutoffProfile r₁ kk (dtr y) with hchiDef
  set supp : Set M := {y : M | ed y ≤ ENNReal.ofReal rstar} with hsuppDef
  have hr₂top : ENNReal.ofReal r₂ ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have htrunc_const : ∀ c : Real, 0 ≤ c → c ≤ r₂ →
      ENNReal.truncateToReal (ENNReal.ofReal r₂) (ENNReal.ofReal c) = c := by
    intro c hc0 hcr₂
    rw [ENNReal.truncateToReal_eq_toReal hr₂top
      (ENNReal.ofReal_le_ofReal hcr₂), ENNReal.toReal_ofReal hc0]
  have hdtr_ge : ∀ (y : M) (c : Real), 0 ≤ c → c ≤ r₂ →
      ENNReal.ofReal c ≤ ed y → c ≤ dtr y := by
    intro y c hc0 hcr₂ hle
    have hmono := ENNReal.monotone_truncateToReal hr₂top hle
    rw [htrunc_const c hc0 hcr₂] at hmono
    exact hmono
  have hdtr_le : ∀ (y : M) (c : Real), 0 ≤ c → c ≤ r₂ →
      ed y ≤ ENNReal.ofReal c → dtr y ≤ c := by
    intro y c hc0 hcr₂ hle
    have hmono := ENNReal.monotone_truncateToReal hr₂top hle
    rw [htrunc_const c hc0 hcr₂] at hmono
    exact hmono
  have hdtr_toReal : ∀ y : M, ed y ≠ (⊤ : ENNReal) → dtr y ≤ (ed y).toReal := by
    intro y hy
    exact ENNReal.toReal_mono hy (min_le_right _ _)
  have hed_cont : Continuous ed := by
    rw [hedDef]
    simpa only [riemannianEDistOf] using
      continuous_riemannianEDist (I := I) (S.base.metric 0) p
  have hchi_cont : Continuous chi := by
    have h1 : Continuous dtr :=
      (ENNReal.continuous_truncateToReal hr₂top).comp hed_cont
    exact (shiftedCutoffProfile_differentiable r₁ kk).continuous.comp h1
  have hchi_Icc : ∀ y : M, chi y ∈ Set.Icc (0 : Real) 1 := fun y =>
    shiftedCutoffProfile_mem_Icc r₁ kk (dtr y)
  have hchi_one : ∀ y : M, ed y ≤ ENNReal.ofReal r₁ → chi y = 1 := by
    intro y hy
    exact shiftedCutoffProfile_eq_one hk.le
      (hdtr_le y r₁ hr₁.le hr₁₂.le hy)
  have hchi_zero_of_far :
      ∀ y : M, ENNReal.ofReal rstar ≤ ed y → chi y = 0 := by
    intro y hy
    exact shiftedCutoffProfile_eq_zero
      (hkey _ (hdtr_ge y rstar hrstar0.le hrstar₂.le hy))
  have hchi_zero : ∀ y : M, y ∉ supp → chi y = 0 := by
    intro y hy
    have hnot : ¬ ed y ≤ ENNReal.ofReal rstar := by
      rw [hsuppDef] at hy
      exact hy
    exact hchi_zero_of_far y (le_of_not_ge hnot)
  have hrstarR : rstar ≤ R := le_trans hrstar₂.le hr₂R
  have hsupp_compact : IsCompact supp := by
    have hcl : IsClosed supp := by
      rw [hsuppDef]
      exact isClosed_Iic.preimage hed_cont
    refine hball.of_isClosed_subset hcl ?_
    intro y hy
    have hy' : ed y ≤ ENNReal.ofReal rstar := by rw [hsuppDef] at hy; exact hy
    have hy'' : ed y ≤ ENNReal.ofReal R :=
      hy'.trans (ENNReal.ofReal_le_ofReal hrstarR)
    rw [hedDef] at hy''
    exact hy''
  have hsupp_ball : supp ⊆ {y : M | ed y < ENNReal.ofReal r₂} := by
    intro y hy
    have hy' : ed y ≤ ENNReal.ofReal rstar := by rw [hsuppDef] at hy; exact hy
    exact lt_of_le_of_lt hy' ((ENNReal.ofReal_lt_ofReal_iff hr₂).mpr hrstar₂)
  have hchi_pos_dist : ∀ y : M, 0 < chi y → ed y < ENNReal.ofReal rstar := by
    intro y hy
    by_contra hcon
    rw [hchi_zero_of_far y (le_of_not_gt hcon)] at hy
    exact lt_irrefl 0 hy
  set ball : Set M := {y : M | ed y ≤ ENNReal.ofReal R} with hballDef
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ ball,
      normSq0S (I := I) (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K := by
    intro s hs y hy
    have hy' : riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R := by
      rw [hballDef] at hy
      have hy'' : ed y ≤ ENNReal.ofReal R := hy
      rw [hedDef] at hy''
      exact hy''
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y hy'
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ ball, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) (S.base.metric s) y v v| ≤
        Lam * (S.base.metric s).inner y v v := by
    intro s hs y hy v
    rw [hLam, hdR]
    exact ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S y v (hcurv0 s hs y hy)
  have hpde := metricPDE_Icc (I := I) S hS hslab
    (fun _ h => hreg ⟨h.1, h.2.le⟩)
  have hequiv :=
    metricEquiv_Icc_on (I := I) (fun s => S.base.metric s) ball hpde hricQuad
  have hcompare : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ ball,
      ∀ v : TangentSpace I y,
        (S.base.metric 0).inner y v v ≤
          Real.exp (2 * Lam * s) * (S.base.metric s).inner y v v := by
    intro s hs y hy v
    have hlo' : Real.exp (-(2 * Lam * s)) * (S.base.metric 0).inner y v v ≤
        (S.base.metric s).inner y v v := by
      simpa only [sub_zero] using (hequiv s hs y hy v).1
    have hmul := mul_le_mul_of_nonneg_left hlo' (Real.exp_pos (2 * Lam * s)).le
    calc
      (S.base.metric 0).inner y v v =
          Real.exp (2 * Lam * s) *
            (Real.exp (-(2 * Lam * s)) * (S.base.metric 0).inner y v v) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (2 * Lam * s) * (S.base.metric s).inner y v v := hmul
  refine ⟨{ chi := chi
            support := supp
            chi_continuous := hchi_cont
            chi_mem_Icc := hchi_Icc
            chi_eq_one := hchi_one
            support_compact := hsupp_compact
            support_subset_ball := hsupp_ball
            support_zero := hchi_zero
            lower_support := ?_ }⟩
  intro t ht x hx
  have htIcc : t ∈ Set.Icc (0 : Real) T := ⟨ht.1.le, ht.2⟩
  have hexp_le : Real.exp (2 * Lam * t) ≤ Ugrad := by
    rw [hUgradDef]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by linarith only [hLam0]))
  have hxdist : ed x < ENNReal.ofReal rstar := hchi_pos_dist x hx
  by_cases hpx : p = x
  · subst hpx
    have hedp : ed p = 0 := by
      rw [hedDef]
      exact riemannianEDistOf_self (I := I) (S.base.metric 0) p
    have hchi_p : chi p = 1 := hchi_one p (by rw [hedp]; exact zero_le)
    have hnear : ∀ᶠ y in 𝓝 p, chi y = 1 := by
      have hlt : ed p < ENNReal.ofReal r₁ := by
        rw [hedp]
        exact ENNReal.ofReal_pos.mpr hr₁
      have hev : ∀ᶠ y in 𝓝 p, ed y < ENNReal.ofReal r₁ :=
        hed_cont.continuousAt (Iio_mem_nhds hlt)
      filter_upwards [hev] with y hy
      exact hchi_one y hy.le
    refine ⟨{ phi := fun _ _ => (1 : Real)
              eq_at := hchi_p.symm
              lower_nhds := ?_
              time_diff := differentiableWithinAt_const (c := (1 : Real))
              space_diff_nhds :=
                Filter.Eventually.of_forall fun _ => mdifferentiableAt_const
              grad_diff := ?_
              grad_sq_le := ?_
              parabolic_le := ?_ }⟩
    · have hprod : ∀ᶠ q in 𝓝 ((t, p) : Real × M), chi q.2 = 1 :=
        (continuous_snd.tendsto ((t, p) : Real × M)).eventually hnear
      filter_upwards [hprod.filter_mono
        (nhdsWithin_le_nhds (s := spacetimeSlab (M := M) T))] with q hq
      exact ⟨zero_le_one, le_of_eq hq.symm⟩
    · exact gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric t)
        (f := fun _ : M => (1 : Real)) contMDiff_const p
    · have hzero :
          gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun _ : M => (1 : Real)) p = 0 :=
        gradientFun_const (I := I) ((flowG (I := I) S).metric t) 1 p
      rw [hzero]
      have hA0 : (0 : Real) ≤ Csq * kk ^ 2 * Ugrad :=
        mul_nonneg (mul_nonneg hCsq (sq_nonneg kk)) hUgrad.le
      simpa only [map_zero, mul_one] using hA0
    · have hgradzero :
          gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun _ : M => (1 : Real)) = 0 := by
        funext y
        exact gradientFun_const (I := I) ((flowG (I := I) S).metric t) 1 y
      have hheat :
          heatOperatorWithDrift (I := I) (flowG (I := I) S) t
            (fun y => (0 : TangentSpace I y))
            (fun _ : M => (1 : Real)) p = 0 := by
        unfold heatOperatorWithDrift laplacianAt laplacian driftTerm gradientAt
        rw [hgradzero]
        simp
      have hpar :
          parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y))
            (fun (_ : Real) (_ : M) => (1 : Real)) t p = 0 := by
        unfold parabolicOperatorWithDrift
        rw [hheat]
        change derivWithin (Function.const Real (1 : Real)) (Set.Icc 0 T) t
          - 0 = 0
        rw [derivWithin_const]
        simp only [Pi.zero_apply, sub_self]
      rw [hpar]
      have hB0 : (0 : Real) ≤ Ce * kk * Clap + Ce * kk ^ 2 * Ugrad :=
        add_nonneg (mul_nonneg (mul_nonneg hCe hk.le) hClap)
          (mul_nonneg (mul_nonneg hCe (sq_nonneg kk)) hUgrad.le)
      have hD0 : (0 : Real) ≤
          Real.sqrt Csq * kk * Cconn * Real.sqrt (chi p) * Theta t p :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg Csq) hk.le) hCconn)
            (Real.sqrt_nonneg _))
          (hTheta t p)
      linarith
  · have hxRed : ed x < ENNReal.ofReal R :=
      hxdist.trans_le (ENNReal.ofReal_le_ofReal hrstarR)
    have hxball : x ∈ ball := by
      rw [hballDef]
      exact hxRed.le
    have hxR : riemannianEDistOf (I := I) (S.base.metric 0) p x <
        ENNReal.ofReal R := by
      rw [hedDef] at hxRed
      exact hxRed
    have hxB : x ∈ {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
      ENNReal.ofReal R} := hxR.le
    obtain ⟨rho, U, hUopen, hxU, hrhoOn, hrhoAt, hrhoEv, hrho_x, hrho_upper, hrho_grad0,
      hrho_hess⟩ :=
      exists_initialDistance_calabi_support (I := I) S (R := R) p x hball hKsec hsec
        hpx hxR
    have hrho_gradAt :
        MDifferentiableAt I (I.prod 𝓘(Real, E))
          (T% fun y : M =>
            gradientFun (I := I) ((flowG (I := I) S).metric t) rho y) x :=
      (gradientFun_contMDiffAt (I := I) ((flowG (I := I) S).metric t)
        hrhoAt).mdifferentiableAt (by simp)
    have hrho_gradsq0 :
        0 ≤ ((flowG (I := I) S).metric t).inner x
          (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
          (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x) :=
      metric_inner_self_nonneg (I := I) (M := M)
        ((flowG (I := I) S).metric t) x _
    have hrho_gradsq :
        ((flowG (I := I) S).metric t).inner x
          (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
          (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x) ≤
          Ugrad := by
      have hle :=
        gradientFun_sq_le_of_metric_le (I := I) (S.base.metric 0)
          ((flowG (I := I) S).metric t)
          (Real.exp_pos (2 * Lam * t)).le zero_le_one
          (fun v => hcompare t htIcc x hxball v) rho (le_of_eq hrho_grad0)
      calc
        ((flowG (I := I) S).metric t).inner x
            (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
            (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x) ≤
            Real.exp (2 * Lam * t) * 1 := hle
        _ = Real.exp (2 * Lam * t) := by ring
        _ ≤ Ugrad := hexp_le
    have hprof_diff : Differentiable Real (shiftedCutoffProfile r₁ kk) :=
      shiftedCutoffProfile_differentiable r₁ kk
    have hprof_diff' :
        DifferentiableAt Real (deriv (shiftedCutoffProfile r₁ kk)) (rho x) :=
      (shiftedCutoffProfile_hasDerivAt2 r₁ kk (rho x)).differentiableAt
    have hphi_space :
        ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => shiftedCutoffProfile r₁ kk (rho z)) y := by
      filter_upwards [hrhoEv] with y hy
      exact (hprof_diff (rho y)).mdifferentiableAt.comp y hy
    have hphi_grad :
        MDifferentiableAt I (I.prod 𝓘(Real, E))
          (T% fun y : M =>
            gradientFun (I := I) ((flowG (I := I) S).metric t)
              (fun z : M => shiftedCutoffProfile r₁ kk (rho z)) y) x :=
      grad_comp_mdiffAt (I := I) ((flowG (I := I) S).metric t) hprof_diff
        hprof_diff' hrhoEv hrho_gradAt
    have hphi_gradient :
        gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun z : M => shiftedCutoffProfile r₁ kk (rho z)) x =
          deriv (shiftedCutoffProfile r₁ kk) (rho x) •
            gradientFun (I := I) ((flowG (I := I) S).metric t) rho x :=
      gradientFun_comp (I := I) ((flowG (I := I) S).metric t)
        (hprof_diff (rho x)) hrhoEv.self_of_nhds
    have hderiv1 :
        deriv (shiftedCutoffProfile r₁ kk) (rho x) =
          deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk :=
      (shiftedCutoffProfile_hasDerivAt r₁ kk (rho x)).deriv
    have hderiv2 :
        deriv (deriv (shiftedCutoffProfile r₁ kk)) (rho x) =
          deriv (deriv CutoffProfile.value) (1 + (rho x - r₁) * kk) * kk * kk :=
      shiftedCutoffProfile_deriv2 r₁ kk (rho x)
    have hxdist₂ : ed x ≤ ENNReal.ofReal r₂ :=
      le_of_lt (hxdist.trans ((ENNReal.ofReal_lt_ofReal_iff hr₂).mpr hrstar₂))
    have hdtr_x : dtr x = (ed x).toReal := by
      rw [hdtrDef]
      exact ENNReal.truncateToReal_eq_toReal hr₂top hxdist₂
    have heq_at : shiftedCutoffProfile r₁ kk (rho x) = chi x := by
      rw [hchiDef, hrho_x, ← hdtr_x]
    have hval_chi : CutoffProfile.value (1 + (rho x - r₁) * kk) = chi x := by
      rw [← heq_at, shiftedCutoffProfile]
    have hgrad_bound :
        ((flowG (I := I) S).metric t).inner x
            (gradientFun (I := I) ((flowG (I := I) S).metric t)
              (fun z : M => shiftedCutoffProfile r₁ kk (rho z)) x)
            (gradientFun (I := I) ((flowG (I := I) S).metric t)
              (fun z : M => shiftedCutoffProfile r₁ kk (rho z)) x) ≤
          (Csq * kk ^ 2 * Ugrad) * shiftedCutoffProfile r₁ kk (rho x) := by
      rw [hphi_gradient,
        metric_inner_smul_self (I := I) ((flowG (I := I) S).metric t) x,
        hderiv1]
      have hprofile := hsq (1 + (rho x - r₁) * kk)
      have hCv : 0 ≤ Csq * CutoffProfile.value (1 + (rho x - r₁) * kk) :=
        mul_nonneg hCsq (CutoffProfile.mem_Icc _).1
      calc
        (deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) ^ 2 *
              ((flowG (I := I) S).metric t).inner x
                (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
                (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x) =
            (deriv CutoffProfile.value (1 + (rho x - r₁) * kk)) ^ 2 *
              (kk ^ 2 *
                ((flowG (I := I) S).metric t).inner x
                  (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
                  (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)) := by
          ring
        _ ≤ (Csq * CutoffProfile.value (1 + (rho x - r₁) * kk)) *
              (kk ^ 2 *
                ((flowG (I := I) S).metric t).inner x
                  (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
                  (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)) :=
          mul_le_mul_of_nonneg_right hprofile
            (mul_nonneg (sq_nonneg kk) hrho_gradsq0)
        _ ≤ (Csq * CutoffProfile.value (1 + (rho x - r₁) * kk)) *
              (kk ^ 2 * Ugrad) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrho_gradsq (sq_nonneg kk)) hCv
        _ = (Csq * kk ^ 2 * Ugrad) *
              shiftedCutoffProfile r₁ kk (rho x) := by
          rw [shiftedCutoffProfile]
          ring
    have hPrho :
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) (fun _ y => rho y) t x =
          -laplacianAt (I := I) (flowG (I := I) S) t rho x := by
      rw [parabolicOperatorWithDrift_eq, heatOperatorWithDrift_zero_drift,
        heatOperator_eq_laplacianAt]
      change derivWithin (Function.const Real (rho x)) (Set.Icc 0 T) t -
        laplacianAt (I := I) (flowG (I := I) S) t rho x = _
      rw [derivWithin_const]
      simp only [Pi.zero_apply, zero_sub]
    have hcomp :=
      parabolic_comp_nhds (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (φ := shiftedCutoffProfile r₁ kk) (fun _ y => rho y) t x hprof_diff
        hprof_diff' (differentiableWithinAt_const (c := rho x)) hrhoEv
        hrho_gradAt
    have hpar_bound :
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y))
            (fun _ y => shiftedCutoffProfile r₁ kk (rho y)) t x ≤
          (Ce * kk * Clap + Ce * kk ^ 2 * Ugrad) +
            Real.sqrt Csq * kk * Cconn * Real.sqrt (chi x) * Theta t x := by
      rw [hcomp, hPrho]
      change deriv (shiftedCutoffProfile r₁ kk) (rho x) *
            -laplacianAt (I := I) (flowG (I := I) S) t rho x -
          deriv (deriv (shiftedCutoffProfile r₁ kk)) (rho x) *
            ((flowG (I := I) S).metric t).inner x
              (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x)
              (gradientFun (I := I) ((flowG (I := I) S).metric t) rho x) ≤ _
      rw [hderiv1, hderiv2]
      by_cases hsmall : 1 + (rho x - r₁) * kk ≤ 1
      · rw [CutoffProfile.deriv_zero_of_le hsmall,
          CutoffProfile.deriv2_zero_of_le hsmall]
        have hB0 : (0 : Real) ≤ Ce * kk * Clap + Ce * kk ^ 2 * Ugrad :=
          add_nonneg (mul_nonneg (mul_nonneg hCe hk.le) hClap)
            (mul_nonneg (mul_nonneg hCe (sq_nonneg kk)) hUgrad.le)
        have hD0 : (0 : Real) ≤
            Real.sqrt Csq * kk * Cconn * Real.sqrt (chi x) * Theta t x :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg Csq) hk.le) hCconn)
              (Real.sqrt_nonneg _))
            (hTheta t x)
        simp only [zero_mul, sub_zero]
        linarith only [hB0, hD0]
      · have hbig : 1 < 1 + (rho x - r₁) * kk := lt_of_not_ge hsmall
        have hrho_r₁ : r₁ ≤ rho x := by
          by_contra hcon
          have hneg : rho x - r₁ ≤ 0 := by
            linarith only [lt_of_not_ge hcon]
          have hmul := mul_le_mul_of_nonneg_right hneg hk.le
          rw [zero_mul] at hmul
          linarith only [hmul, hbig]
        have hlapbound :=
          hlap t ht x hxB rho U hUopen hxU hrhoOn hrho_r₁ hrho_x hrho_upper hrho_grad0
            hrho_hess
        have hne1 :
            0 ≤ -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) := by
          have hmul :=
            mul_le_mul_of_nonneg_right
              (CutoffProfile.deriv_nonpos (1 + (rho x - r₁) * kk)) hk.le
          rw [zero_mul] at hmul
          linarith only [hmul]
        have hCa :
            -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) ≤
              Ce * kk := by
          have h : -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk)) ≤ Ce :=
            le_trans (neg_le_abs _) (hCe₁ (1 + (rho x - r₁) * kk))
          calc
            -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) =
                (-(deriv CutoffProfile.value (1 + (rho x - r₁) * kk))) * kk := by
              ring
            _ ≤ Ce * kk := mul_le_mul_of_nonneg_right h hk.le
        have hCb :
            -(deriv (deriv CutoffProfile.value) (1 + (rho x - r₁) * kk) * kk
                * kk) ≤ Ce * kk ^ 2 := by
          have h :
              -(deriv (deriv CutoffProfile.value) (1 + (rho x - r₁) * kk)) ≤
                Ce :=
            le_trans (neg_le_abs _) (hCe₂ (1 + (rho x - r₁) * kk))
          calc
            -(deriv (deriv CutoffProfile.value) (1 + (rho x - r₁) * kk) * kk
                  * kk) =
                (-(deriv (deriv CutoffProfile.value)
                  (1 + (rho x - r₁) * kk))) * kk ^ 2 := by
              ring
            _ ≤ Ce * kk ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg kk)
        have hCs :
            -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) ≤
              Real.sqrt Csq * Real.sqrt (chi x) * kk := by
          have habs :
              -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk)) ≤
                Real.sqrt Csq * Real.sqrt (chi x) := by
            calc
              -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk)) ≤
                  |deriv CutoffProfile.value (1 + (rho x - r₁) * kk)| :=
                neg_le_abs _
              _ = Real.sqrt
                    ((deriv CutoffProfile.value (1 + (rho x - r₁) * kk)) ^ 2) :=
                (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt
                    (Csq * CutoffProfile.value (1 + (rho x - r₁) * kk)) :=
                Real.sqrt_le_sqrt (hsq (1 + (rho x - r₁) * kk))
              _ = Real.sqrt Csq *
                    Real.sqrt
                      (CutoffProfile.value (1 + (rho x - r₁) * kk)) :=
                Real.sqrt_mul hCsq _
              _ = Real.sqrt Csq * Real.sqrt (chi x) := by rw [hval_chi]
          calc
            -(deriv CutoffProfile.value (1 + (rho x - r₁) * kk) * kk) =
                (-(deriv CutoffProfile.value (1 + (rho x - r₁) * kk))) * kk := by
              ring
            _ ≤ (Real.sqrt Csq * Real.sqrt (chi x)) * kk :=
              mul_le_mul_of_nonneg_right habs hk.le
        calc
          _ ≤ (Ce * kk * Clap + Ce * kk ^ 2 * Ugrad) +
                (Real.sqrt Csq * Real.sqrt (chi x) * kk) *
                  (Cconn * Theta t x) :=
            selfCoupled_parabolic_bound hCa hCs hne1 hCb
              (mul_nonneg hCe (sq_nonneg kk)) hlapbound hClap
              (mul_nonneg hCconn (hTheta t x)) hrho_gradsq0 hrho_gradsq
          _ = (Ce * kk * Clap + Ce * kk ^ 2 * Ugrad) +
                Real.sqrt Csq * kk * Cconn * Real.sqrt (chi x) * Theta t x := by
            ring
    have hnear_fin : ∀ᶠ y in 𝓝 x, ed y ≠ (⊤ : ENNReal) := by
      have hev : ∀ᶠ y in 𝓝 x, ed y < ENNReal.ofReal rstar :=
        hed_cont.continuousAt (Iio_mem_nhds hxdist)
      filter_upwards [hev] with y hy
      exact ne_top_of_lt hy
    have hlower_space :
        ∀ᶠ y in 𝓝 x, shiftedCutoffProfile r₁ kk (rho y) ≤ chi y := by
      filter_upwards [hnear_fin, hrho_upper] with y hyfin hyup
      have hdtr_rho : dtr y ≤ rho y := by
        refine le_trans (hdtr_toReal y hyfin) ?_
        rw [hedDef]
        exact hyup
      exact shiftedCutoffProfile_antitone hk.le hdtr_rho
    refine ⟨{ phi := fun _ y => shiftedCutoffProfile r₁ kk (rho y)
              eq_at := heq_at
              lower_nhds := ?_
              time_diff := differentiableWithinAt_const
                (c := shiftedCutoffProfile r₁ kk (rho x))
              space_diff_nhds := hphi_space
              grad_diff := hphi_grad
              grad_sq_le := hgrad_bound
              parabolic_le := hpar_bound }⟩
    have hprod : ∀ᶠ q in 𝓝 ((t, x) : Real × M),
        shiftedCutoffProfile r₁ kk (rho q.2) ≤ chi q.2 :=
      (continuous_snd.tendsto ((t, x) : Real × M)).eventually hlower_space
    filter_upwards [hprod.filter_mono
      (nhdsWithin_le_nhds (s := spacetimeSlab (M := M) T))] with q hq
    exact ⟨(shiftedCutoffProfile_mem_Icc r₁ kk (rho q.2)).1, hq⟩

theorem exists_shiInitialDistanceCutoff_of_solution
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K Ksec R r₁ r₂ Clap Cconn : Real}
    (p : M)
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    {Theta : Real → M → Real}
    (hTheta : ∀ t : Real, ∀ y : M, 0 ≤ Theta t y)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn Theta) :
    ∃ A B Dcoef : Real, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Dcoef ∧
      Nonempty
        (ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A B Dcoef Theta) :=
  ⟨shiInitialCutoffA (Module.finrank Real E) T K r₁ r₂,
    shiInitialCutoffB (Module.finrank Real E) T K r₁ r₂ Clap,
    shiInitialCutoffD r₁ r₂ Cconn,
    shiInitialCutoffA_nonneg _ _ _ _ _,
    shiInitialCutoffB_nonneg _ hr₁₂.le hClap,
    shiInitialCutoffD_nonneg hr₁₂.le hCconn,
    nonempty_shiInitialDistanceCutoff_of_solution (I := I) S hS p hT hslab hreg
      hball hKsec hsec hcurv hr₁ hr₁₂ hr₂R hClap hCconn hTheta hlap⟩

theorem exists_shiInitialDistanceCutoff_of_solution_of_sectional_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K R r₁ r₂ Clap Cconn : Real}
    (p : M)
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hsec : ∀ y : M, metricRm04At (I := I) (S.base.metric 0) y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    {Theta : Real → M → Real}
    (hTheta : ∀ t : Real, ∀ y : M, 0 ≤ Theta t y)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ 0 Clap Cconn Theta) :
    ∃ A B Dcoef : Real, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Dcoef ∧
      Nonempty
        (ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A B Dcoef Theta) :=
  exists_shiInitialDistanceCutoff_of_solution (I := I) S hS p hT hslab hreg
    hball le_rfl
    (fun y _ => sectionalBoundedBelow_zero_of_mem_cone (I := I)
      (S.base.metric 0) hsec y)
    hcurv hr₁ hr₁₂ hr₂R hClap hCconn hTheta hlap



omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_shiFixedCutoff_of_initialDistanceCutoff
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {T r₁ r₂ A B Dcoef : Real} {p : M}
    {Theta : Real → M → Real}
    (cut : ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A B Dcoef Theta)
    (hA : 0 ≤ A) (hD : 0 ≤ Dcoef)
    {Hbound cn : Real} (hH : 0 ≤ Hbound) (hcn : 0 ≤ cn)
    (hRm1 : ∀ s ∈ Set.Ioc (0 : Real) T, ∀ y : M, 0 < cut.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 1 s y ≤ Hbound ^ 2 / s)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < cut.chi x →
      ∃ s ∈ Set.Ioc (0 : Real) t,
        Theta t x ≤
          cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) :
    Nonempty
      (ShiFixedCutoff (I := I) (flowG (I := I) S) T
        (max A (B + Dcoef * (cn * Hbound)))) := by
  classical
  refine ⟨{ chi := fun _ y => cut.chi y
            support := cut.support
            err_nonneg := le_trans hA (le_max_left _ _)
            support_compact := cut.support_compact
            support_zero := fun _ _ x hx => cut.support_zero x hx
            range := fun _ _ x => cut.chi_mem_Icc x
            joint_cont := ?_
            lower_support := ?_ }⟩
  · exact (cut.chi_continuous.comp continuous_snd).continuousOn
  intro t ht htpos x hx
  have htIoc : t ∈ Set.Ioc (0 : Real) T := ⟨htpos, ht.2⟩
  obtain ⟨s, hs, hsle⟩ := hTheta t htIoc x hx
  have hsT : s ∈ Set.Ioc (0 : Real) T := ⟨hs.1, hs.2.trans ht.2⟩
  have hcurv1 := hRm1 s hsT x hx
  have hprod :
      s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x ≤ Hbound ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcurv1 hs.1.le
    rwa [mul_div_cancel₀ (Hbound ^ 2) (ne_of_gt hs.1)] at hmul
  have hchi0 : 0 ≤ cut.chi x := (cut.chi_mem_Icc x).1
  have hchi1 : cut.chi x ≤ 1 := (cut.chi_mem_Icc x).2
  have hsqrt :
      Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) ≤ Hbound := by
    calc
      Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) ≤
          Real.sqrt (Hbound ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Hbound := Real.sqrt_sq hH
  have hThetaBound : Theta t x ≤ cn * Hbound :=
    hsle.trans (mul_le_mul_of_nonneg_left hsqrt hcn)
  have hsqrt_chi : Real.sqrt (cut.chi x) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hchi1
    rwa [Real.sqrt_one] at h
  have hcoef0 : (0 : Real) ≤ Dcoef * Real.sqrt (cut.chi x) :=
    mul_nonneg hD (Real.sqrt_nonneg _)
  have hΛ :
      B + Dcoef * Real.sqrt (cut.chi x) * Theta t x ≤
        B + Dcoef * (cn * Hbound) := by
    have hstep :
        Dcoef * Real.sqrt (cut.chi x) * Theta t x ≤ Dcoef * (cn * Hbound) := by
      calc
        Dcoef * Real.sqrt (cut.chi x) * Theta t x ≤
            Dcoef * Real.sqrt (cut.chi x) * (cn * Hbound) :=
          mul_le_mul_of_nonneg_left hThetaBound hcoef0
        _ ≤ Dcoef * (cn * Hbound) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hcn hH)
          calc
            Dcoef * Real.sqrt (cut.chi x) ≤ Dcoef * 1 :=
              mul_le_mul_of_nonneg_left hsqrt_chi hD
            _ = Dcoef := mul_one _
    linarith only [hstep]
  obtain ⟨support⟩ := cut.lower_support t htIoc x hx
  exact
    ⟨support.toCutoffLowerSupport (le_max_left _ _)
      (hΛ.trans (le_max_right _ _)) hchi0⟩

end DifferentialGeometry.PDE.RicciFlow

end
