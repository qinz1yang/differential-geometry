import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Operator.HessianAlgebra
import DifferentialGeometry.Geometry.Operator.Scaling
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Mathlib.Data.Real.Pointwise

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open scoped Manifold ContDiff Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] in
private theorem metric_inner_smul_self
    (g : SmoothRiemannianMetric I M) (c : Real) {x : M} (v : TangentSpace I x) :
    g.inner x (c • v) (c • v) = c ^ 2 * g.inner x v v := by
  have h1 : ∀ w : TangentSpace I x, g.inner x (c • v) w = c * g.inner x v w := by
    intro w
    rw [(g.inner x).map_smul c v, smul_apply, smul_eq_mul]
  rw [h1 (c • v), g.symm x v (c • v), h1 v]
  ring

theorem inner_gradientFun_self_scaleMetric_const_smul
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M → Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    (scaleMetric (I := I) c hc g).inner x
        (gradientFun (I := I) (scaleMetric (I := I) c hc g) (a • f) x)
        (gradientFun (I := I) (scaleMetric (I := I) c hc g) (a • f) x) =
      a ^ 2 / c *
        g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [gradientFun_scale (I := I) c hc g (a • f) x,
    gradientFun_const_smul (I := I) g a hf, smul_smul, scaleMetric_inner,
    metric_inner_smul_self (I := I) g (c⁻¹ * a) _]
  field_simp

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

theorem laplacian_const_smul_of_contMDiffOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M → Real} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U) :
    laplacian (I := I) cov g (a • f) x = a * laplacian (I := I) cov g f x := by
  refine laplacian_smul_at (I := I) cov g a ?_ (gradientFun_mdiffOn (I := I) g hU hf hx)
  filter_upwards [hU.mem_nhds hx] with y hy
  exact ((hf y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)

theorem laplacian_scaleMetric_of_contMDiffOn
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M → Real} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) f x =
      c⁻¹ * laplacian (I := I) cov g f x :=
  laplacian_scaleMetric (I := I) c hc cov g (gradientFun_mdiffOn (I := I) g hU hf hx)

theorem laplacian_scaleMetric_const_smul_of_contMDiffOn
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M → Real} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) (a • f) x =
      a / c * laplacian (I := I) cov g f x := by
  rw [laplacian_const_smul_of_contMDiffOn (I := I) cov
      (scaleMetric (I := I) c hc g) a hU hx hf,
    laplacian_scaleMetric_of_contMDiffOn (I := I) c hc cov g hU hx hf]
  ring

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open scoped Manifold ContDiff BigOperators Bundle Topology Pointwise



theorem sSup_image_const_mul {c : Real} (hc : 0 ≤ c) (A : Set Real) :
    sSup ((fun a : Real => c * a) '' A) = c * sSup A := by
  have himg : (fun a : Real => c * a) '' A = c • A := by
    simp only [← Set.image_smul, smul_eq_mul]
  rw [himg, Real.sSup_smul_of_nonneg hc A, smul_eq_mul]

section SupWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem nablaRmSupWeight_curvatureScaleSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) (t : Real) (x : M) :
    nablaRmSupWeight (I := I) (curvatureScaleSolution (I := I) S hK h0) (K * t) x =
      nablaRmSupWeight (I := I) S t x / Real.sqrt K := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hsk : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hskne : Real.sqrt K ≠ 0 := ne_of_gt hsk
  have hskmul : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
  have hIcc : Set.Icc (0 : Real) (K * t) = (fun u : Real => K * u) '' Set.Icc 0 t := by
    ext s
    constructor
    · intro hs
      exact ⟨s / K, ⟨div_nonneg hs.1 hK.le,
        (div_le_iff₀ hK).mpr (by nlinarith [hs.2])⟩, by field_simp⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mul_nonneg hK.le hu.1, mul_le_mul_of_nonneg_left hu.2 hK.le⟩
  have hfun :
      (fun s : Real =>
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I)
            (curvatureScaleSolution (I := I) S hK h0) 1 s x)) ∘
          (fun u : Real => K * u) =
        (fun b : Real => K⁻¹ * b) ∘
          (fun u : Real =>
            Real.sqrt (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x)) := by
    funext u
    simp only [Function.comp_apply]
    rw [nablaKRm04NormSqIntrinsic_curvatureScaleSolution (I := I) S hK h0 1 (K * u) x,
      mul_div_cancel_left₀ u hKne]
    have hcancel : K * (K⁻¹ : Real) ^ (2 + 1) = (K⁻¹ : Real) ^ 2 := by
      have h1 : (K⁻¹ : Real) ^ (2 + 1) = K⁻¹ * (K⁻¹ : Real) ^ 2 := by ring
      rw [h1, ← mul_assoc, mul_inv_cancel₀ hKne, one_mul]
    have hexp : K * u *
          ((K⁻¹) ^ (2 + 1) * nablaKRm04NormSqIntrinsic (I := I) S 1 u x) =
        (K⁻¹) ^ 2 * (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x) := by
      calc K * u * ((K⁻¹) ^ (2 + 1) * nablaKRm04NormSqIntrinsic (I := I) S 1 u x)
          = K * (K⁻¹ : Real) ^ (2 + 1) *
              (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x) := by ring
        _ = (K⁻¹) ^ 2 * (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x) := by
            rw [hcancel]
    rw [hexp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (le_of_lt (inv_pos.mpr hK))]
  have hset :
      (fun s : Real =>
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I)
            (curvatureScaleSolution (I := I) S hK h0) 1 s x)) '' Set.Icc 0 (K * t) =
        (fun b : Real => K⁻¹ * b) ''
          ((fun u : Real =>
            Real.sqrt (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x)) ''
            Set.Icc 0 t) := by
    rw [hIcc, ← Set.image_comp, hfun, Set.image_comp]
  have hdefL : nablaRmSupWeight (I := I)
        (curvatureScaleSolution (I := I) S hK h0) (K * t) x =
      2 * Real.sqrt (K * t) *
        sSup ((fun s : Real =>
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I)
            (curvatureScaleSolution (I := I) S hK h0) 1 s x)) ''
          Set.Icc 0 (K * t)) := rfl
  have hdefR : nablaRmSupWeight (I := I) S t x =
      2 * Real.sqrt t *
        sSup ((fun u : Real =>
          Real.sqrt (u * nablaKRm04NormSqIntrinsic (I := I) S 1 u x)) ''
          Set.Icc 0 t) := rfl
  have hinv : K⁻¹ = (Real.sqrt K)⁻¹ * (Real.sqrt K)⁻¹ := by
    rw [← mul_inv, hskmul]
  rw [hdefL, hdefR, hset,
    sSup_image_const_mul (le_of_lt (inv_pos.mpr hK)), Real.sqrt_mul hK.le t, hinv]
  field_simp

end SupWeight



section LaplacianBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem initialDistanceFlowLaplacianBound_curvatureScaleSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier)
    {T r₁ Ksec Clap Cconn : Real} {B : Set M} (p : M)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn
      (nablaRmSupWeight (I := I) S)) :
    InitialDistanceFlowLaplacianBound (I := I)
      (curvatureScaleSolution (I := I) S hK h0) (K * T) p B (Real.sqrt K * r₁)
      (Ksec / K) (Clap / Real.sqrt K) Cconn
      (nablaRmSupWeight (I := I) (curvatureScaleSolution (I := I) S hK h0)) := by
  intro t' ht' x hxB rho' U hU hxU hrho'On hr₁rho' hvalue' hupper' hgrad' hhess'
  have hKne : K ≠ 0 := ne_of_gt hK
  set sk : Real := Real.sqrt K with hskdef
  have hsk : 0 < sk := Real.sqrt_pos.mpr hK
  have hskne : sk ≠ 0 := ne_of_gt hsk
  have hskmul : sk * sk = K := Real.mul_self_sqrt hK.le
  have hskinv : (0 : Real) < sk⁻¹ := inv_pos.mpr hsk
  set t : Real := t' / K with htdef
  have hKt : K * t = t' := by
    rw [htdef]
    field_simp
  have ht : t ∈ Set.Ioc (0 : Real) T := by
    refine ⟨div_pos ht'.1 hK, ?_⟩
    rw [htdef, div_le_iff₀ hK]
    nlinarith [ht'.2]
  set rho : M → Real := fun y => sk⁻¹ * rho' y with hrhodef
  have hrho'_eq : rho' = sk • rho := by
    funext y
    simp only [hrhodef, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hmet0 : (curvatureScaleSolution (I := I) S hK h0).base.metric 0 =
      scaleMetric (I := I) K hK (S.base.metric 0) :=
    curvatureScaleSolution_metric_zero (I := I) S hK h0
  have hpt : parabolicTime 0 K t' = t := by
    unfold parabolicTime
    rw [htdef]
    ring
  have hmett : (curvatureScaleSolution (I := I) S hK h0).base.metric t' =
      scaleMetric (I := I) K hK (S.base.metric t) := by
    rw [curvatureScaleSolution_metric (I := I) S hK h0 t', hpt]
  have hdist : ∀ y : M,
      (riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y).toReal =
        sk * (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal := by
    intro y
    rw [hmet0, edistOf_scale (I := I) K hK (S.base.metric 0) p y,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg K)]
  have hxnhds : U ∈ nhds x := hU.mem_nhds hxU
  have hrhoOn : ContMDiffOn I 𝓘(Real, Real) ∞ rho U := by
    rw [hrhodef]
    exact contMDiffOn_const.mul hrho'On
  have hrhoDiff : MDifferentiableAt I 𝓘(Real, Real) rho x :=
    ((hrhoOn x hxU).contMDiffAt hxnhds).mdifferentiableAt (by simp)
  have hvalue : rho x = (riemannianEDistOf (I := I) (S.base.metric 0) p x).toReal := by
    simp only [hrhodef]
    rw [hvalue', hdist x]
    field_simp
  have hr₁rho : r₁ ≤ rho x := by
    simp only [hrhodef]
    calc r₁ = sk⁻¹ * (sk * r₁) := by field_simp
      _ ≤ sk⁻¹ * rho' x := mul_le_mul_of_nonneg_left hr₁rho' hskinv.le
  have hupper : ∀ᶠ y in nhds x,
      (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal ≤ rho y := by
    filter_upwards [hupper'] with y hy
    rw [hdist y] at hy
    simp only [hrhodef]
    calc (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal
        = sk⁻¹ * (sk * (riemannianEDistOf (I := I) (S.base.metric 0) p y).toReal) := by
          field_simp
      _ ≤ sk⁻¹ * rho' y := mul_le_mul_of_nonneg_left hy hskinv.le
  have hgradEq : (S.base.metric 0).inner x
      (gradientFun (I := I) (S.base.metric 0) rho x)
      (gradientFun (I := I) (S.base.metric 0) rho x) = 1 := by
    rw [hmet0, hrho'_eq, inner_gradientFun_self_scaleMetric_const_smul (I := I) K hK
      (S.base.metric 0) sk hrhoDiff] at hgrad'
    have hsq : sk ^ 2 / K = 1 := by
      rw [sq, hskmul, div_self hKne]
    rw [hsq, one_mul] at hgrad'
    exact hgrad'
  have hhess : ∀ Y : TangentSpace I x,
      hessFun (I := I) (S.base.metric 0) rho x Y Y ≤
        (2 / rho x + Real.sqrt (-Ksec)) * (S.base.metric 0).inner x Y Y := by
    intro Y
    have h := hhess' Y
    rw [hmet0, hrho'_eq, hessFun_scaleMetric (I := I) K hK (S.base.metric 0),
      hessFun_smul (I := I) (S.base.metric 0) sk rho] at h
    have hsqrtdiv : Real.sqrt (-(Ksec / K)) = Real.sqrt (-Ksec) / sk := by
      rw [← neg_div, Real.sqrt_div' (-Ksec) hK.le]
    have hlhs : (sk • hessFun (I := I) (S.base.metric 0) rho) x Y Y =
        sk * hessFun (I := I) (S.base.metric 0) rho x Y Y := by
      simp [Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    have hrhs : (2 / (sk • rho) x + Real.sqrt (-(Ksec / K))) *
          (scaleMetric (I := I) K hK (S.base.metric 0)).inner x Y Y =
        sk * ((2 / rho x + Real.sqrt (-Ksec)) * (S.base.metric 0).inner x Y Y) := by
      simp only [Pi.smul_apply, smul_eq_mul, scaleMetric_inner, hsqrtdiv]
      rw [div_mul_eq_div_div_swap, ← hskmul]
      field_simp
    rw [hlhs, hrhs] at h
    exact le_of_mul_le_mul_left h hsk
  have hconc := hlap t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq hhess
  have hconn : (flowG (I := I) (curvatureScaleSolution (I := I) S hK h0)).connection t' =
      (flowG (I := I) S).connection t := by
    have h1 : (flowG (I := I) (curvatureScaleSolution (I := I) S hK h0)).connection t' =
        leviCivitaConnectionOfMetric (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric t') := rfl
    have h2 : (flowG (I := I) S).connection t =
        leviCivitaConnectionOfMetric (I := I) (S.base.metric t) := rfl
    rw [h1, h2, hmett, lcConn_scaleMetric]
  have hlapEq : laplacianAt (I := I)
        (flowG (I := I) (curvatureScaleSolution (I := I) S hK h0)) t' rho' x =
      sk⁻¹ * laplacianAt (I := I) (flowG (I := I) S) t rho x := by
    have hLdef : laplacianAt (I := I)
          (flowG (I := I) (curvatureScaleSolution (I := I) S hK h0)) t' rho' x =
        laplacian (I := I)
          ((flowG (I := I) (curvatureScaleSolution (I := I) S hK h0)).connection t')
          ((curvatureScaleSolution (I := I) S hK h0).base.metric t') rho' x := rfl
    have hRdef : laplacianAt (I := I) (flowG (I := I) S) t rho x =
        laplacian (I := I) ((flowG (I := I) S).connection t) (S.base.metric t) rho x :=
      rfl
    rw [hLdef, hRdef, hconn, hmett, hrho'_eq,
      laplacian_scaleMetric_const_smul_of_contMDiffOn (I := I) K hK
        ((flowG (I := I) S).connection t) (S.base.metric t) sk hU hxU hrhoOn,
      ← hskmul]
    field_simp
  have hwEq : nablaRmSupWeight (I := I)
        (curvatureScaleSolution (I := I) S hK h0) t' x =
      nablaRmSupWeight (I := I) S t x / sk := by
    rw [← hKt]
    exact nablaRmSupWeight_curvatureScaleSolution (I := I) S hK h0 t x
  rw [hlapEq, hwEq]
  calc sk⁻¹ * laplacianAt (I := I) (flowG (I := I) S) t rho x
      ≤ sk⁻¹ * (Clap + Cconn * nablaRmSupWeight (I := I) S t x) :=
        mul_le_mul_of_nonneg_left hconc hskinv.le
    _ = Clap / sk + Cconn * (nablaRmSupWeight (I := I) S t x / sk) := by
        field_simp

end LaplacianBound



section Corollary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

theorem shi_local_all_orders_curvature_scale_of_flowLaplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T K R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hK : 0 < K) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / (2 * Real.sqrt K)) (R / Real.sqrt K),
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K)}
        r Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
            ENNReal.ofReal (R / (2 * Real.sqrt K)) →
          Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C * K ∧
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
              C * K / Real.sqrt t ^ m := by
  have hsk : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hskne : Real.sqrt K ≠ 0 := ne_of_gt hsk
  have hradius : Real.sqrt K * (R / Real.sqrt K) = R := by
    field_simp
  have hballEq : {y : M |
      riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
          ENNReal.ofReal R} =
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    have h := closedBall_scaleMetric_eq (I := I) (S.base.metric 0) K hK p
      (R / Real.sqrt K)
    rw [hradius] at h
    rw [curvatureScaleSolution_metric_zero (I := I) S hK h0]
    exact h
  refine shi_local_all_orders_curvature_scale_of_laplacianInput (I := I) S hS
    (Clap := Clap / Real.sqrt K) p halpha hK hT hTomega hR h0 hball hKsec hsec hu
    (div_nonneg hClap hsk.le) hCconn ?_
  intro r hr
  have hrmem : r / Real.sqrt K ∈
      Set.Ioc (R / (2 * Real.sqrt K)) (R / Real.sqrt K) := by
    refine ⟨?_, ?_⟩
    · rw [div_mul_eq_div_div]
      have h := mul_lt_mul_of_pos_right hr.1 (inv_pos.mpr hsk)
      simpa [div_eq_mul_inv] using h
    · have h := mul_le_mul_of_nonneg_right hr.2 (inv_pos.mpr hsk).le
      simpa [div_eq_mul_inv] using h
  have hbase := initialDistanceFlowLaplacianBound_curvatureScaleSolution (I := I) S hK h0
    p (hlap (r / Real.sqrt K) hrmem)
  have hEq : Real.sqrt K * (r / Real.sqrt K) = r := by
    field_simp
  rw [hEq] at hbase
  rw [hballEq]
  exact hbase

end Corollary

end DifferentialGeometry.PDE.RicciFlow

end
