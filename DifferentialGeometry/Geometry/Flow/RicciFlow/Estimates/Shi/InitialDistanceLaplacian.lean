import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Family.Basic
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceCutoff

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]



def InitialConnectionDifferenceBound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (B : Set M) (Cconn : Real) (Theta : Real → M → Real) : Prop :=
  ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x ∈ B, ∀ u w : TangentSpace I x,
    Real.sqrt ((S.base.metric 0).inner x
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric t))
          (LeviCivita (I := I) (S.base.metric 0)) x u w)
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric t))
          (LeviCivita (I := I) (S.base.metric 0)) x u w)) ≤
      Cconn * Theta t x *
        Real.sqrt ((S.base.metric 0).inner x u u) *
        Real.sqrt ((S.base.metric 0).inner x w w)

def nablaRmTimeIntegral
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real → M → Real :=
  fun t x => ∫ s in (0 : Real)..t,
    Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRmTimeIntegral_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} (ht : 0 ≤ t) (x : M) :
    0 ≤ nablaRmTimeIntegral (I := I) S t x :=
  intervalIntegral.integral_nonneg_of_forall ht
    (fun _ => Real.sqrt_nonneg _)



omit [NeZero (Module.finrank Real E)] [IsManifold I 1 M] [SigmaCompactSpace M] in
private theorem laplacian_le_of_hessian_and_connectionDifference_bound
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {rho : M → Real} {U : Set M} {x : M} {Lam Chess Cd : Real}
    (hU : IsOpen U) (hrho : ContMDiffOn I 𝓘(Real, Real) ∞ rho U) (hx : x ∈ U)
    (hChess : 0 ≤ Chess) (hCd : 0 ≤ Cd)
    (hcomp : ∀ v : TangentSpace I x, g₀.inner x v v ≤ Lam * g₁.inner x v v)
    (hgrad : g₀.inner x (gradientFun (I := I) g₀ rho x)
      (gradientFun (I := I) g₀ rho x) ≤ 1)
    (hhess : ∀ v : TangentSpace I x,
      hessFun (I := I) g₀ rho x v v ≤ Chess * g₀.inner x v v)
    (hconn : ∀ u w : TangentSpace I x,
      Real.sqrt (g₀.inner x
          (CovariantDerivative.difference (LeviCivita (I := I) g₁)
            (LeviCivita (I := I) g₀) x u w)
          (CovariantDerivative.difference (LeviCivita (I := I) g₁)
            (LeviCivita (I := I) g₀) x u w)) ≤
        Cd * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)) :
    laplacian (I := I) (LeviCivita (I := I) g₁) g₁ rho x ≤
      (Module.finrank Real E : Real) * ((Chess + Cd) * Lam) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g₁ x
  have hinv : MetricInverseInBasis (I := I) g₁ x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g₁ basis hON
  have hlap :
      laplacian (I := I) (LeviCivita (I := I) g₁) g₁ rho x =
        ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          hessFun (I := I) g₁ rho x (basis i) (basis i) := by
    rw [lap_eq_hess_on (I := I) g₁ hU hrho hx,
      metricTracePair0SAt_eq_sum_basis (I := I) g₁ basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x))))
        hinv (hessTensorAt (I := I) g₁ rho x)]
    simp only [hessTensorAt_apply, identityInvMetric, diagonalInvMetric]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hlap]
  have hsqrtgrad :
      Real.sqrt (g₀.inner x (gradientFun (I := I) g₀ rho x)
        (gradientFun (I := I) g₀ rho x)) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hgrad
    rwa [Real.sqrt_one] at h
  have hdiag : ∀ i : Fin (Module.finrank Real (TangentSpace I x)),
      hessFun (I := I) g₁ rho x (basis i) (basis i) ≤ (Chess + Cd) * Lam := by
    intro i
    let e : TangentSpace I x := basis i
    let Dv : TangentSpace I x :=
      (CovariantDerivative.difference (LeviCivita (I := I) g₁)
        (LeviCivita (I := I) g₀) x e) e
    have hone : g₁.inner x e e = 1 := by simpa [e] using hON i i
    have he0 : 0 ≤ g₀.inner x e e :=
      DifferentialGeometry.metric_inner_self_nonneg
        (I := I) (M := M) g₀ x e
    have he_le : g₀.inner x e e ≤ Lam := by
      have h := hcomp e
      rw [hone, mul_one] at h
      exact h
    have hD : Real.sqrt (g₀.inner x Dv Dv) ≤ Cd * g₀.inner x e e := by
      have h := hconn e e
      calc
        Real.sqrt (g₀.inner x Dv Dv) ≤
            Cd * Real.sqrt (g₀.inner x e e) * Real.sqrt (g₀.inner x e e) := h
        _ = Cd * g₀.inner x e e := by
          rw [mul_assoc, ← pow_two, Real.sq_sqrt he0]
    have hdf : |mvfderiv (I := I) rho x Dv| ≤ Cd * g₀.inner x e e := by
      rw [← inner_gradientFun (I := I) g₀ rho x Dv]
      calc
        |g₀.inner x (gradientFun (I := I) g₀ rho x) Dv| ≤
            Real.sqrt (g₀.inner x (gradientFun (I := I) g₀ rho x)
              (gradientFun (I := I) g₀ rho x)) *
              Real.sqrt (g₀.inner x Dv Dv) :=
          DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
            (I := I) (M := M) g₀ x _ _
        _ ≤ 1 * (Cd * g₀.inner x e e) :=
          mul_le_mul hsqrtgrad hD (Real.sqrt_nonneg _) zero_le_one
        _ = Cd * g₀.inner x e e := one_mul _
    have hdiff := hessFun_sub_eq_neg_mvfderiv_connectionDifference
      (I := I) g₁ g₀ hU hrho hx e e
    change hessFun (I := I) g₁ rho x e e - hessFun (I := I) g₀ rho x e e =
      -mvfderiv (I := I) rho x Dv at hdiff
    have hh0 : hessFun (I := I) g₀ rho x e e ≤ Chess * Lam :=
      (hhess e).trans (mul_le_mul_of_nonneg_left he_le hChess)
    have hcdlam : Cd * g₀.inner x e e ≤ Cd * Lam :=
      mul_le_mul_of_nonneg_left he_le hCd
    change hessFun (I := I) g₁ rho x e e ≤ (Chess + Cd) * Lam
    have habs := neg_le_abs (mvfderiv (I := I) rho x Dv)
    nlinarith [hdiff, hh0, hdf, hcdlam, habs]
  calc
    ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        hessFun (I := I) g₁ rho x (basis i) (basis i) ≤
      ∑ _i : Fin (Module.finrank Real (TangentSpace I x)),
        ((Chess + Cd) * Lam) := Finset.sum_le_sum fun i _ => hdiag i
    _ = (Module.finrank Real E : Real) * ((Chess + Cd) * Lam) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real E by rfl]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialDistanceFlowLaplacianBoundOn_of_solution
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K Ksec r₁ Cconn : Real} {B : Set M}
    (_hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hCconn : 0 ≤ Cconn)
    {Theta : Real → M → Real}
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M, 0 ≤ Theta t y)
    (hdiff : InitialConnectionDifferenceBound (I := I) S T B Cconn Theta)
    (p : M) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        (2 / r₁ + Real.sqrt (-Ksec)))
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        Cconn)
      Theta := by
  classical
  set dR : Real := (Module.finrank Real E : Real) with hdR
  set Lam : Real := dR ^ 2 * Real.sqrt K with hLam
  set Ugrad : Real := Real.exp (2 * Lam * T) with hUgradDef
  have hLam0 : 0 ≤ Lam := by rw [hLam, hdR]; positivity
  have hUgrad : 0 < Ugrad := by rw [hUgradDef]; exact Real.exp_pos _
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      normSq0S (I := I) (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K := by
    intro s hs y hy
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y hy
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) (S.base.metric s) y v v| ≤
        Lam * (S.base.metric s).inner y v v := by
    intro s hs y hy v
    rw [hLam, hdR]
    exact ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S y v (hcurv0 s hs y hy)
  have hpde := metricPDE_Icc (I := I) S hS hslab
    (fun _ h => hreg ⟨h.1, h.2.le⟩)
  have hequiv :=
    metricEquiv_Icc_on (I := I) (fun s => S.base.metric s) B hpde hricQuad
  have hcompare : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B,
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
  intro t ht x hxB rho U hU hxU hrhoOn hr₁rho _hvalue _hupper hgradEq hhess
  have htIcc : t ∈ Set.Icc (0 : Real) T := ⟨ht.1.le, ht.2⟩
  have hexp_le : Real.exp (2 * Lam * t) ≤ Ugrad := by
    rw [hUgradDef]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by linarith only [hLam0]))
  have hcomp : ∀ v : TangentSpace I x,
      (S.base.metric 0).inner x v v ≤
        Ugrad * (S.base.metric t).inner x v v := by
    intro v
    have hnn : 0 ≤ (S.base.metric t).inner x v v :=
      DifferentialGeometry.metric_inner_self_nonneg
        (I := I) (M := M) (S.base.metric t) x v
    refine (hcompare t htIcc x hxB v).trans ?_
    exact mul_le_mul_of_nonneg_right hexp_le hnn
  have hrhox : 0 < rho x := lt_of_lt_of_le hr₁ hr₁rho
  have hhess' : ∀ v : TangentSpace I x,
      hessFun (I := I) (S.base.metric 0) rho x v v ≤
        (2 / r₁ + Real.sqrt (-Ksec)) * (S.base.metric 0).inner x v v := by
    intro v
    have ha0 : 0 ≤ (S.base.metric 0).inner x v v :=
      DifferentialGeometry.metric_inner_self_nonneg
        (I := I) (M := M) (S.base.metric 0) x v
    have hstep : 2 / rho x ≤ 2 / r₁ :=
      div_le_div_of_nonneg_left (by norm_num) hr₁ hr₁rho
    refine (hhess v).trans (mul_le_mul_of_nonneg_right ?_ ha0)
    linarith
  have hCd : 0 ≤ Cconn * Theta t x :=
    mul_nonneg hCconn (hTheta t ht x)
  have hconn := hdiff t ht x hxB
  have hgradle :
      (S.base.metric 0).inner x
          (gradientFun (I := I) (S.base.metric 0) rho x)
          (gradientFun (I := I) (S.base.metric 0) rho x) ≤ 1 :=
    le_of_eq hgradEq
  have hcore := laplacian_le_of_hessian_and_connectionDifference_bound
    (I := I) (S.base.metric 0) (S.base.metric t) hU hrhoOn hxU
    (by positivity) hCd hcomp hgradle hhess' hconn
  have hlapeq :
      laplacianAt (I := I) (flowG (I := I) S) t rho x =
        laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) rho x := rfl
  rw [hlapeq]
  refine hcore.trans (le_of_eq ?_)
  rw [hdR]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialDistanceFlowLaplacianBoundOn_of_solution_nablaRm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K Ksec r₁ Cconn : Real} {B : Set M}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hCconn : 0 ≤ Cconn)
    (hdiff : InitialConnectionDifferenceBound (I := I) S T B Cconn
      (nablaRmTimeIntegral (I := I) S))
    (p : M) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        (2 / r₁ + Real.sqrt (-Ksec)))
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        Cconn)
      (nablaRmTimeIntegral (I := I) S) :=
  initialDistanceFlowLaplacianBoundOn_of_solution (I := I) S hS hT hslab hreg
    hcurv hr₁ hCconn
    (fun _ ht y => nablaRmTimeIntegral_nonneg (I := I) S ht.1.le y) hdiff p

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialDistanceFlowLaplacianBoundOn_of_solution_of_sectional_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K r₁ Cconn : Real} {B : Set M}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hCconn : 0 ≤ Cconn)
    {Theta : Real → M → Real}
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M, 0 ≤ Theta t y)
    (hdiff : InitialConnectionDifferenceBound (I := I) S T B Cconn Theta)
    (p : M) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ 0
      (2 * (Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T)
        / r₁)
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        Cconn)
      Theta := by
  have h := initialDistanceFlowLaplacianBoundOn_of_solution (I := I) S hS hT
    hslab hreg hcurv hr₁ hCconn (Ksec := 0) hTheta hdiff p
  have hconst :
      (Module.finrank Real E : Real) *
          Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
          (2 / r₁ + Real.sqrt (-(0 : Real))) =
        2 * (Module.finrank Real E : Real) *
          Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T)
          / r₁ := by
    rw [neg_zero, Real.sqrt_zero]
    ring
  rwa [hconst] at h

end DifferentialGeometry.PDE.RicciFlow
