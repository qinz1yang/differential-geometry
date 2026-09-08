import DifferentialGeometry.Geometry.Comparison.DistanceIndex
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Geometry.Curvature.SectionalCone

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential
open Variation
open CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem intrinsicJacobi_endpoint_deriv_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) (L : Real)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (huw : g.inner p u w = 0)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      ∀ Z : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StdAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) Z
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) Z) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      g.inner (γ L) (J L) (J L) / L := by
  classical
  dsimp only
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hgeo : Geodesic.IsGeodesic (I := I) g γ := intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hunit0 : g.inner (γ 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u 0).trans hu
  obtain ⟨F, hFdiff, hFpar, hFON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ hL (hgeo.isGeodesicOn (Icc 0 L)) hunit0
  let e : Fin (Module.finrank Real E - 1) → ∀ t, TangentSpace I (γ t) := fun i => (F i).toFun
  let c := perpCoeff (I := I) g e J L
  let z : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) := fun t => (t / L) • c
  let dz : Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) := fun _ => (1 / L) • c
  have hz : ContDiff Real ∞ z := (contDiff_id.div_const L).smul_const c
  have hdz : deriv z = dz := by
    funext t
    exact (((hasDerivAt_id t).div_const L).smul_const c).deriv
  have hbound := intrinsicJacobi_endpoint_indexForm_le_of_minimizing
    (I := I) g hEnorm p u w L hL hu huw hmin e hFdiff hFpar hFON hFperp hFbundle
    (fun t => t / L) (contDiff_id.div_const L) (by simp) (div_self hL.ne')
  dsimp only at hbound
  have hidx := perpLift_indexForm (I := I) g γ e z z 0 L
    (fun t _ => hz.differentiable (by simp) t) (fun t _ => hz.differentiable (by simp) t)
    (fun i t ht => hFdiff i t (by simpa [uIcc_of_le hL.le] using ht))
    (fun i t ht => hFpar i t (by simpa [uIcc_of_le hL.le] using ht))
    (fun t ht => hFON t (by simpa [uIcc_of_le hL.le] using ht))
  rw [hdz] at hidx
  have hbound' : g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      DifferentialGeometry.Analysis.ODE.indexForm (perpCurvOp (I := I) g γ e) 0 L z dz z dz :=
    hbound.trans_eq hidx
  have hnorm : inner Real c c = g.inner (γ L) (J L) (J L) := by
    have hspeed : 0 < g.inner (γ L) (curveVelocity (I := I) γ L) (curveVelocity (I := I) γ L) := by
      have heq : g.inner (γ L) (curveVelocity (I := I) γ L) (curveVelocity (I := I) γ L) = 1 :=
        (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u L).trans hu
      rw [heq]
      exact zero_lt_one
    have hperp : g.inner (γ L) (J L) (curveVelocity (I := I) γ L) = 0 := by
      rw [g.symm]
      exact intrJacobi_perp_ne (I := I) g hEnorm p u w hL.ne' huw
    have hlift := perpLift_coeff (I := I) g e J L (by simp) hspeed
      (fun i => hFperp L ⟨hL.le, le_rfl⟩ i) hperp
      (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
    have hinner := perpLift_inner (I := I) g e c c L (fun i j => hFON L ⟨hL.le, le_rfl⟩ i j)
    change g.inner (γ L) (perpFrameLift (I := I) e (perpCoeff (I := I) g e J) L)
      (perpFrameLift (I := I) e (perpCoeff (I := I) g e J) L) = inner Real c c at hinner
    rw [hlift] at hinner
    exact hinner.symm
  have hcurv (t) (ht : t ∈ Icc (0 : Real) L) :
      0 ≤ inner Real (perpCurvOp (I := I) g γ e t (z t)) (z t) := by
    rw [perpCurv_inner (I := I) g γ e (z t) (z t) t]
    change 0 ≤ g.inner (γ t)
      ((riemannOp (LeviCivita (I := I) g) (γ t))
        (perpFrameLift (I := I) e z t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
      (perpFrameLift (I := I) e z t)
    rw [g.symm, ← rm04_eq_inner_riem (I := I) g (γ t)
      (perpFrameLift (I := I) e z t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) (perpFrameLift (I := I) e z t)]
    exact hsec t ht _
  have hint : IntervalIntegrable (DifferentialGeometry.Analysis.ODE.indexIntegrand
      (perpCurvOp (I := I) g γ e) z dz z dz) MeasureTheory.volume 0 L :=
    DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand
      (perpCurv_smooth (I := I) g γ hγ e hFbundle).continuous.continuousOn
      hz.continuous.continuousOn continuousOn_const hz.continuous.continuousOn continuousOn_const
  have hmono := intervalIntegral.integral_mono_on hL.le hint
    (intervalIntegrable_const (c := (1 / L) ^ 2 * inner Real c c))
    (fun t ht => by
      dsimp only [DifferentialGeometry.Analysis.ODE.indexIntegrand, dz]
      rw [real_inner_smul_left, real_inner_smul_right]
      nlinarith [hcurv t ht])
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have halg : L * ((1 / L) ^ 2 * inner Real c c) = g.inner (γ L) (J L) (J L) / L := by
    rw [hnorm]
    field_simp
  rw [halg] at hmono
  exact hbound'.trans hmono


private theorem branchHess_perp_le_of_minimizing
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExpInvBranch (I := I) g hEnorm p)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈
      B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      ∀ Z : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StdAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) Z
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) Z)
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1))
    (hYperp : g.inner
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u)) 1) Y = 0) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y / L := by
  let uL : TangentSpace I p := L • u
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let γL : Real → M := intrinsicGeodesic (I := I) g hEnorm p uL
  have hsrc' : tangentSpaceModelContinuousLinearEquiv (I := I) p uL ∈
      B.hom.source := by
    simpa only [uL] using hsrc
  obtain ⟨W, hW⟩ :=
    exists_intrinsicJacobi_one_eq (I := I) g hEnorm p B hsrc' Y
  have hGauss := intrinsicJacobi_perp (I := I) g hEnorm p uL W
  have hGauss' :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p uL 1)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p uL) 1)
          (intrinsicJacobi (I := I) g hEnorm p uL W 1) =
        g.inner p uL W := by
    with_unfolding_all exact hGauss
  have huLW : g.inner p uL W = 0 := by
    rw [hW, hYperp] at hGauss'
    exact hGauss'.symm
  have huW : g.inner p u W = 0 := by
    have hscaled : L * g.inner p u W = 0 := by
      simpa only [uL, map_smul, smul_apply, smul_eq_mul] using huLW
    exact (mul_eq_zero.mp hscaled).resolve_left hL.ne'
  let w : TangentSpace I p := L⁻¹ • W
  have hLw : L • w = W := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have huw : g.inner p u w = 0 := by
    dsimp only [w]
    rw [map_smul (g.inner p u), smul_eq_mul, huW, mul_zero]
  let J : ∀ t, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  let JL : ∀ t, TangentSpace I (γL t) :=
    intrinsicJacobi (I := I) g hEnorm p uL W
  have hγscale (t : Real) : γL t = γ (L * t) := by
    dsimp only [γL, γ, uL]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p u (L * t)]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p (L • u) t]
    apply congrArg (fun v : TangentSpace I p =>
      intrinsicGeodesic (I := I) g hEnorm p v 1)
    module
  have hJLscale (t : Real) : @Eq E (JL t : E) (J (L * t) : E) := by
    have hscale := intrinsicJacobi_smul (I := I) g hEnorm p u w L t
    rw [hLw] at hscale
    with_unfolding_all exact hscale
  have hDJscale :
      @Eq E (covDerivAlong (I := I) g γL JL 1 : E)
        (L • covDerivAlong (I := I) g γ J L : E) := by
    have hcong := covDerivAlong_congr_curve (I := I) (t := (1 : Real)) g JL
      (fun t => J (L * t))
      (Filter.Eventually.of_forall hγscale)
      (Filter.Eventually.of_forall hJLscale)
    have hcomp := covDeriv_comp_mul (I := I) g γ J L 1
    rw [mul_one] at hcomp
    exact hcong.trans hcomp
  have hJLone : JL 1 = Y := by
    simpa only [JL] using hW
  have hJoneScale : @Eq E (JL 1 : E) (J L : E) := by
    have hscale := hJLscale 1
    rw [mul_one] at hscale
    exact hscale
  have hq : γL 1 = γ L := by
    simpa only [mul_one] using hγscale 1
  have hindex := intrinsicJacobi_endpoint_deriv_le
    (I := I) g hEnorm p u w L hL hu huw hmin hsec
  have huL_pos : 0 < g.inner p uL uL := by
    dsimp only [uL]
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hroot : Real.sqrt (g.inner p uL uL) = L := by
    dsimp only [uL]
    rw [sqrt_gInner_smul_self (I := I) g p hL.le u, hu, Real.sqrt_one,
      mul_one]
  have hshape := branchHess_shape (I := I) B hsrc' huL_pos
    (w₁ := W) (w₂ := W) huLW huLW
  dsimp only at hshape
  rw [show intrinsicGeodesic (I := I) g hEnorm p uL = γL by rfl] at hshape
  rw [show intrinsicJacobi (I := I) g hEnorm p uL W = JL by rfl] at hshape
  rw [hroot] at hshape
  have hleft :
      g.inner (γL 1) (covDerivAlong (I := I) g γL JL 1) (JL 1) / L =
        g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) := by
    rw [hq]
    rw [hDJscale, hJoneScale]
    rw [map_smul (g.inner (γ L)), smul_apply, smul_eq_mul,
      mul_div_cancel_left₀ _ hL.ne']
  have hright :
      g.inner (γL 1) (JL 1) (JL 1) / L =
        g.inner (γ L) (J L) (J L) / L := by
    rw [hq, hJoneScale]
  rw [← hJLone, hshape, hleft, hright]
  exact hindex

private theorem branchHess_perp_radial_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExpInvBranch (I := I) g hEnorm p)
    (hv : 0 < g.inner p v v)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p v ∈
      B.hom.source)
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p v 1))
    (hYperp : g.inner
      (intrinsicGeodesic (I := I) g hEnorm p v 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p v) 1) Y = 0) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Y
        (curveVelocity (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p v) 1) = 0 := by
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p v
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun w =>
    intrinsicJacobi (I := I) g hEnorm p v w
  obtain ⟨w, hw⟩ :=
    exists_intrinsicJacobi_one_eq (I := I) g hEnorm p B hsrc Y
  have hGauss := intrinsicJacobi_perp (I := I) g hEnorm p v w
  have hGauss' :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p v 1)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p v) 1)
          (intrinsicJacobi (I := I) g hEnorm p v w 1) =
        g.inner p v w := by
    with_unfolding_all exact hGauss
  have hvw : g.inner p v w = 0 := by
    rw [hw, hYperp] at hGauss'
    exact hGauss'.symm
  have hDperp :
      g.inner (γ 1) (covDerivAlong (I := I) g γ (J w) 1)
        (curveVelocity (I := I) γ 1) = 0 := by
    rw [g.symm (γ 1)]
    simpa only [γ, J] using
      intrJacobi_dperp (I := I) g hEnorm p v w one_ne_zero hvw
  have hshape := branchHess_jacobi (I := I) B hsrc hv
    (w₁ := w) (w₂ := v)
  dsimp only at hshape
  rw [show intrinsicGeodesic (I := I) g hEnorm p v = γ by rfl] at hshape
  rw [show intrinsicJacobi (I := I) g hEnorm p v w = J w by rfl] at hshape
  rw [intrJacobi_self (I := I) g hEnorm p v, hDperp, hvw,
    zero_div, zero_mul, zero_div, sub_zero] at hshape
  rw [← hw]
  simpa only [γ, J] using hshape

private theorem branchHess_symm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (B : ExpInvBranch (I := I) g hEnorm p)
    (hv : 0 < g.inner p v v)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p v ∈
      B.hom.source)
    (Y Z : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p v 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Y Z =
      hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p v 1) Z Y := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p v
  obtain ⟨U, hUopen, hqU, hrU⟩ :=
    branchRadius_open (I := I) B hsrc hv
  obtain ⟨rSmooth, hrSmooth, hr_eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hUopen hqU hrU
  have hcongr := hessFun_congr (I := I) g hr_eq
  have hsymm := hessFun_symm_of_boundaryless (I := I) g hrSmooth q Y Z
  change hessFun (I := I) g (branchRadius (I := I) g B) q Y Z =
    hessFun (I := I) g (branchRadius (I := I) g B) q Z Y
  calc
    _ = hessFun (I := I) g rSmooth q Y Z := by
      exact congrArg (fun T => T Y Z) hcongr.symm
    _ = hessFun (I := I) g rSmooth q Z Y := hsymm
    _ = _ := by
      exact congrArg (fun T => T Z Y) hcongr

theorem branchHess_le_of_minimizing_of_sectional_curvature_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (L : Real)
    (B : ExpInvBranch (I := I) g hEnorm p)
    (hL : 0 < L)
    (hu : g.inner p u u = 1)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈
      B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Set.Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (hsec : ∀ t ∈ Set.Icc (0 : Real) L,
      metricRm04At (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) ∈
        DifferentialGeometry.tensor04SectionalNonnegativeCone
          (I := I) (M := M))
    (Y : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1)) :
    hessFun (I := I) g (branchRadius (I := I) g B)
        (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y ≤
      g.inner (intrinsicGeodesic (I := I) g hEnorm p (L • u) 1) Y Y / L := by
  let v : TangentSpace I p := L • u
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p v
  let q : M := γ 1
  let V : TangentSpace I q := curveVelocity (I := I) γ 1
  let Hess := hessFun (I := I) g (branchRadius (I := I) g B) q
  have hv : 0 < g.inner p v v := by
    dsimp only [v]
    rw [gInner_smul_self (I := I) g p L u, hu]
    positivity
  have hVsq : g.inner q V V = L ^ 2 := by
    calc
      g.inner q V V = g.inner p v v := by
        with_unfolding_all exact
          intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v 1
      _ = L ^ 2 := by
        dsimp only [v]
        rw [gInner_smul_self (I := I) g p L u, hu, mul_one]
  have hVpos : 0 < g.inner q V V := hVsq.symm ▸ sq_pos_of_pos hL
  let a : Real := g.inner q V Y / L ^ 2
  let Z : TangentSpace I q := Y - a • V
  have hZperp : g.inner q V Z = 0 := by
    dsimp only [Z, a]
    rw [map_sub, map_smul, smul_eq_mul, hVsq]
    field_simp
    ring
  have hsec' : ∀ t ∈ Set.Icc (0 : Real) L,
      ∀ W : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p u t),
        0 ≤ metricRm04StdAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u t) W
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) W := by
    intro t ht W
    exact
      (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u t)).mp
          (hsec t ht) W
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
  have hZbound : Hess Z Z ≤ g.inner q Z Z / L := by
    simpa only [Hess, q, γ, v] using
      branchHess_perp_le_of_minimizing (I := I) g hEnorm p u L B
        hL hu hsrc hmin hsec' Z hZperp
  have hZV : Hess Z V = 0 := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_perp_radial_eq_zero (I := I) g hEnorm p v B hv hsrc Z hZperp
  have hsymm : Hess Z V = Hess V Z := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_symm (I := I) g hEnorm p v B hv hsrc Z V
  have hVZ : Hess V Z = 0 := hsymm.symm.trans hZV
  have hsrcv : (v : E) ∈ B.hom.source := by
    with_unfolding_all exact hsrc
  have hVV : Hess V V = 0 := by
    simpa only [Hess, q, γ, v, V] using
      branchHess_radial (I := I) B (u := v) hsrcv hv
  have hYdecomp : Y = Z + a • V := by
    dsimp only [Z]
    module
  have hHZaV : Hess Z (a • V) = 0 := by
    calc
      Hess Z (a • V) = a • Hess Z V := (Hess Z).map_smul a V
      _ = 0 := by rw [hZV, smul_zero]
  have hHaVZ : Hess (a • V) Z = 0 := by
    calc
      Hess (a • V) Z = a • Hess V Z := LinearMap.map_smul₂ Hess a V Z
      _ = 0 := by rw [hVZ, smul_zero]
  have hHaVaV : Hess (a • V) (a • V) = 0 := by
    calc
      Hess (a • V) (a • V) = a • Hess V (a • V) :=
        LinearMap.map_smul₂ Hess a V (a • V)
      _ = a • (a • Hess V V) := by rw [(Hess V).map_smul]
      _ = 0 := by rw [hVV, smul_zero, smul_zero]
  have hHdecomp : Hess Y Y = Hess Z Z := by
    rw [hYdecomp]
    have hleft := LinearMap.map_add₂ Hess Z (a • V) (Z + a • V)
    have hrightZ := (Hess Z).map_add Z (a • V)
    have hrightaV := (Hess (a • V)).map_add Z (a • V)
    calc
      Hess (Z + a • V) (Z + a • V) =
          (Hess Z Z + Hess Z (a • V)) +
            (Hess (a • V) Z + Hess (a • V) (a • V)) :=
        hleft.trans
          (congrArg₂ (fun x y : Real => x + y) hrightZ hrightaV)
      _ = Hess Z Z := by rw [hHZaV, hHaVZ, hHaVaV]; ring
  have hZVinner : g.inner q Z V = 0 := by
    rw [g.symm q]
    exact hZperp
  have hGZaV : g.inner q Z (a • V) = 0 := by
    calc
      g.inner q Z (a • V) = a • g.inner q Z V :=
        (g.inner q Z).map_smul a V
      _ = 0 := by rw [hZVinner, smul_zero]
  have hGaVZ : g.inner q (a • V) Z = 0 := by
    calc
      g.inner q (a • V) Z = a • g.inner q V Z :=
        ContinuousLinearMap.map_smul₂ (g.inner q) a V Z
      _ = 0 := by rw [hZperp, smul_zero]
  have hGaVaV :
      g.inner q (a • V) (a • V) = a ^ 2 * g.inner q V V := by
    rw [ContinuousLinearMap.map_smul₂, ContinuousLinearMap.map_smul,
      smul_eq_mul]
    ring
  have hnorm :
      g.inner q Y Y = g.inner q Z Z + a ^ 2 * g.inner q V V := by
    rw [hYdecomp]
    have hleft :=
      ContinuousLinearMap.map_add₂ (g.inner q) Z (a • V) (Z + a • V)
    have hrightZ := (g.inner q Z).map_add Z (a • V)
    have hrightaV := (g.inner q (a • V)).map_add Z (a • V)
    calc
      g.inner q (Z + a • V) (Z + a • V) =
          (g.inner q Z Z + g.inner q Z (a • V)) +
            (g.inner q (a • V) Z + g.inner q (a • V) (a • V)) :=
        hleft.trans
          (congrArg₂ (fun x y : Real => x + y) hrightZ hrightaV)
      _ = g.inner q Z Z + a ^ 2 * g.inner q V V := by
        rw [hGZaV, hGaVZ, hGaVaV]
        ring
  have hnorm_le : g.inner q Z Z ≤ g.inner q Y Y := by
    rw [hnorm]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) hVpos.le)
  calc
    Hess Y Y = Hess Z Z := hHdecomp
    _ ≤ g.inner q Z Z / L := hZbound
    _ ≤ g.inner q Y Y / L := (div_le_div_iff_of_pos_right hL).2 hnorm_le

end Riemannian
end Geometry
end DifferentialGeometry

end
