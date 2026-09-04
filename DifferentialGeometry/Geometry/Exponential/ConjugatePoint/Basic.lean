import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem covDeriv_comp_affine
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (c d t : ℝ) :
    covDerivAlong (I := I) g
        (fun s => γ (c * s + d)) (fun s => V (c * s + d)) t =
      c • covDerivAlong (I := I) g γ V (c * t + d) := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  have hrep :
      chartRepAt (I := I) (fun s => γ (c * s + d))
          (fun s => V (c * s + d)) t =
        fun s => chartRepAt (I := I) γ V (c * t + d) (c * s + d) := rfl
  have hcurve :
      chartCurve (I := I) (γ (c * t + d)) (fun s => γ (c * s + d)) =
        fun s => chartCurve (I := I) (γ (c * t + d)) γ (c * s + d) := rfl
  rw [hrep, chartCovDerivAlong_def, chartCovDerivAlong_def, hcurve]
  have hderiv (f : ℝ → E) :
      deriv (fun s => f (c * s + d)) t = c • deriv f (c * t + d) := by
    calc
      deriv (fun s => f (c * s + d)) t =
          deriv (fun s => (fun r => f (r + d)) (c * s)) t := rfl
      _ = c • deriv (fun r => f (r + d)) (c * t) :=
        deriv_comp_mul_left c (fun r : ℝ => f (r + d)) t
      _ = c • deriv f (c * t + d) := by rw [deriv_comp_add_const]
  rw [hderiv, hderiv,
    ChartChristoffel.contraction_smul_left, smul_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem curveVelocity_comp_affine
    (γ : ℝ → M) (c d t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    curveVelocity (I := I) (fun s => γ (c * s + d)) t =
      c • curveVelocity (I := I) γ (c * t + d) := by
  let a : ℝ → ℝ := fun s => c * s + d
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t := by
    have ha_inf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a := by
      exact contMDiff_const.mul contMDiff_id |>.add contMDiff_const
    exact ha_inf.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (f := a) (g := γ) (x := t) hγ ha (1 : ℝ)
  have ha_one : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t (1 : ℝ) = c := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt a (c • (1 : ℝ →L[ℝ] ℝ)) t := by
      have hadd : HasFDerivAt a
          ((c • (1 : ℝ →L[ℝ] ℝ)) + (0 : ℝ →L[ℝ] ℝ)) t := by
        change HasFDerivAt (fun s : ℝ => c * s + d)
          ((c • (1 : ℝ →L[ℝ] ℝ)) + (0 : ℝ →L[ℝ] ℝ)) t
        refine HasFDerivAt.add ?_ (hasFDerivAt_const (x := t) d)
        refine ((c • (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt
          (x := t)).congr_of_eventuallyEq ?_
        filter_upwards with s
        simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
      rw [add_zero] at hadd
      exact hadd
    rw [hfd.fderiv]
    change c • ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) = c
    rw [one_apply_eq_self, smul_eq_mul, mul_one]
  change mfderiv 𝓘(ℝ, ℝ) I (γ ∘ a) t (1 : ℝ) =
    c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ)
  rw [hcomp, ha_one]
  let A := mfderiv 𝓘(ℝ, ℝ) I γ (a t)
  have hA : A
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) (a t)).symm c) =
      c • A
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) (a t)).symm 1) := by
    rw [← A.map_smul]
    congr 1
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, ℝ)) (a t)).injective
    simp
  with_unfolding_all exact hA

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] in
private theorem jacobi_comp_affine
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) (c d : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hJ : IsJacobiAlong (I := I) g γ J) :
    IsJacobiAlong (I := I) g
      (fun s => γ (c * s + d)) (fun s => J (c * s + d)) := by
  intro t
  let δ : ℝ → M := fun s => γ (c * s + d)
  let L : ∀ s, TangentSpace I (δ s) := fun s => J (c * s + d)
  let DJ : ∀ s, TangentSpace I (γ s) :=
    fun s => covDerivAlong (I := I) g γ J s
  have hDL : (fun s => covDerivAlong (I := I) g δ L s) =
      fun s => c • DJ (c * s + d) := by
    funext s
    exact covDeriv_comp_affine (I := I) g γ J c d s
  have hD2 :
      covDerivAlong (I := I) g δ
          (fun s => covDerivAlong (I := I) g δ L s) t =
        (c * c) • covDerivAlong (I := I) g γ DJ (c * t + d) := by
    rw [hDL]
    rw [covDerivAlong_smul]
    rw [covDeriv_comp_affine (I := I) g γ DJ c d t, smul_smul]
  have hvel :
      curveVelocity (I := I) δ t =
        c • curveVelocity (I := I) γ (c * t + d) := by
    exact curveVelocity_comp_affine (I := I) γ c d t
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
  change
    covDerivAlong (I := I) g δ
        (fun s => covDerivAlong (I := I) g δ L s) t +
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (δ t))
        (L t) (curveVelocity (I := I) δ t)
        (curveVelocity (I := I) δ t) = 0
  rw [hD2, hvel]
  simp only [map_smul, smul_apply, smul_smul]
  rw [← smul_add, hJ (c * t + d), smul_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
private theorem intrinsicGeodesic_smooth
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (intrinsicGeodesic (I := I) g hEnorm p u) := by
  have hvar := intrinsicVar_smooth (I := I) g hEnorm p (u : E) 0
  have hincl : ContMDiff 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hcomp := hvar.comp hincl
  rw [show intrinsicGeodesic (I := I) g hEnorm p u =
      (fun q : ℝ × ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + q.1 • (0 : TangentSpace I p)) q.2) ∘
        fun t : ℝ => ((0 : ℝ), t) by
    funext t
    simp only [Function.comp_apply, zero_smul, add_zero]]
  exact hcomp

omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrGeo_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
    intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd) =
      fun t => intrinsicGeodesic (I := I) g hEnorm p u (1 - t) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
  let rev : ℝ → M := fun t => γ ((-1 : ℝ) * t + 1)
  have hγ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm p u
  have hδ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ δ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm z.proj (-z.snd)
  have hrev_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ rev := by
    have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (-1 : ℝ) * t + 1) :=
      contMDiff_const.mul contMDiff_id |>.add contMDiff_const
    exact hγ_inf.comp ha
  have hδ_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g δ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm z.proj (-z.snd)
  have hγ_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hrev_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g rev := by
    intro t
    exact
      DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_comp_affine
        (I := I) (hγ_geo ((-1 : ℝ) * t + 1))
  have hfoot : δ 0 = rev 0 := by
    dsimp only [δ, rev]
    rw [intrinsicGeodesic_zero]
    dsimp only [z, γ, intrinsicVelocityLift]
    norm_num
  have hδvel :
      (curveVelocity (I := I) δ 0 : E) = (-z.snd : E) := by
    simpa only [curveVelocity, δ] using
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm z.proj (-z.snd)
  have hrevvel :
      (curveVelocity (I := I) rev 0 : E) = (-z.snd : E) := by
    have h := curveVelocity_comp_affine (I := I) γ (-1) 1 0
      (hγ_inf.contMDiffAt.mdifferentiableAt (by simp))
    have h' : curveVelocity (I := I) rev 0 =
        (-1 : ℝ) • curveVelocity (I := I) γ 1 := by
      change curveVelocity (I := I) rev 0 =
        (-1 : ℝ) • curveVelocity (I := I) γ ((-1 : ℝ) * 0 + 1) at h
      have ht : (-1 : ℝ) * 0 + 1 = 1 := by norm_num
      rw [ht] at h
      exact h
    rw [h', neg_one_smul]
    rfl
  have hvel : (curveVelocity (I := I) δ 0 : E) =
      (curveVelocity (I := I) rev 0 : E) :=
    hδvel.trans hrevvel.symm
  have heq : δ = rev :=
    isGeodesic_eq_of_initial (I := I) g hδ_geo hrev_geo
      hδ_inf.continuous hrev_inf.continuous hfoot hvel
  change δ = fun t => γ (1 - t)
  rw [heq]
  funext t
  dsimp only [rev]
  congr 1
  ring

omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrGeo_rev_vel
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
    let δ := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
    tangentSpaceModelContinuousLinearEquiv (I := I) (δ 1)
        (mfderiv 𝓘(ℝ, ℝ) I δ 1 (1 : ℝ)) =
      -tangentSpaceModelContinuousLinearEquiv (I := I) p u := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
  have hδ : δ = fun t => γ (1 - t) := by
    simpa only [δ, γ, z] using intrGeo_reverse (I := I) g hEnorm p u
  have hγ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm p u
  have hcomp := curveVelocity_comp_affine (I := I) γ (-1) 1 1
    (hγ_inf.contMDiffAt.mdifferentiableAt (by simp))
  have hfun :
      (fun t : ℝ => γ (1 - t)) =
        fun t : ℝ => γ ((-1 : ℝ) * t + 1) := by
    funext t
    congr 1
    ring
  have hcompE := congrArg
    (tangentSpaceModelContinuousLinearEquiv (I := I)
      (γ ((-1 : ℝ) * 1 + 1))) hcomp
  rw [map_smul] at hcompE
  have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
  rw [ht] at hcompE
  rw [← hfun] at hcompE
  have hzero := intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p u
  have hzeroE := congrArg
    (tangentSpaceModelContinuousLinearEquiv (I := I)
      (intrinsicGeodesic (I := I) g hEnorm p u 0)) hzero
  have hγ0 : intrinsicGeodesic (I := I) g hEnorm p u 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p u
  rw [hγ0] at hzeroE
  change tangentSpaceModelContinuousLinearEquiv (I := I) (δ 1)
      (curveVelocity (I := I) δ 1) =
    -tangentSpaceModelContinuousLinearEquiv (I := I) p u
  rw [hδ]
  have hrev1 : (fun t : ℝ => γ (1 - t)) 1 = γ 0 := by norm_num
  rw [hrev1]
  calc
    tangentSpaceModelContinuousLinearEquiv (I := I) (γ 0)
        (curveVelocity (I := I) (fun t => γ (1 - t)) 1) =
      -tangentSpaceModelContinuousLinearEquiv (I := I) (γ 0)
        (curveVelocity (I := I) γ 0) := by
          simpa only [neg_one_smul] using hcompE
    _ = -tangentSpaceModelContinuousLinearEquiv (I := I) p u :=
      congrArg Neg.neg hzeroE

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exp_pair_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u a : TangentSpace I p)
    (b : E) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
    g.inner z.proj
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from w))
          (u : E) (a : E))
        b =
      g.inner p a
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
            (show TangentSpace I z.proj from w))
          (-z.snd : E) b) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let uE : E := tangentSpaceModelContinuousLinearEquiv (I := I) p u
  let aE : E := tangentSpaceModelContinuousLinearEquiv (I := I) p a
  let zE : E := tangentSpaceModelContinuousLinearEquiv (I := I) z.proj (-z.snd)
  let bT : TangentSpace I z.proj :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj).symm b
  have huE : (show TangentSpace I p from uE) = u := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
  have haE : (show TangentSpace I p from aE) = a := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
  have hzE : (show TangentSpace I z.proj from zE) = -z.snd := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj).injective
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
  have hbT : (show TangentSpace I z.proj from b) = bT := by
    simp only [bT, tangentSpaceModelContinuousLinearEquiv_symm_apply]
    rfl
  let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
  generalize hrev_def : (fun t => γ ((-1 : ℝ) * t + 1)) = rev
  have hδrev : δ = rev := by
    have h := intrGeo_reverse (I := I) g hEnorm p u
    change δ = fun t => γ (1 - t) at h
    rw [h, ← hrev_def]
    funext t
    congr 1
    ring
  let F : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from (uE + s • aE : E)) t
  let G : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm z.proj
      (show TangentSpace I z.proj from (zE + s • b : E)) t
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ)
  let K : ∀ t : ℝ, TangentSpace I (δ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => G s t) 0 (1 : ℝ)
  have hF_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => F q.1 q.2) := by
    simpa only [F] using
      intrinsicVar_smooth (I := I) g hEnorm p uE aE
  have hG_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => G q.1 q.2) := by
    simpa only [G] using
      intrinsicVar_smooth (I := I) g hEnorm z.proj zE b
  have hF_smooth : IsSmoothVariation (I := I) F :=
    hF_inf.of_le ENat.LEInfty.out
  have hG_smooth : IsSmoothVariation (I := I) G :=
    hG_inf.of_le ENat.LEInfty.out
  have hγ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm p u
  have hδ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ δ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm z.proj (-z.snd)
  have hJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) F hF_smooth t
    have hF0 : (fun v => F 0 v) = γ := by
      funext v
      simp only [F, zero_smul, add_zero]
      rw [huE]
    rw [hF0] at h
    simpa only [F, J] using h
  have hDJdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g F hF_smooth t
    have hF0 : (fun v => F 0 v) = γ := by
      funext v
      simp only [F, zero_smul, add_zero]
      rw [huE]
    rw [hF0] at h
    simpa only [F, J] using h
  have hKdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) δ K t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) G hG_smooth t
    have hG0 : (fun v => G 0 v) = δ := by
      funext v
      simp only [G, zero_smul, add_zero]
      rw [hzE]
    rw [hG0] at h
    simpa only [G, K] using h
  have hDKdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) δ
          (fun s => covDerivAlong (I := I) g δ K s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g G hG_smooth t
    have hG0 : (fun v => G 0 v) = δ := by
      funext v
      simp only [G, zero_smul, add_zero]
      rw [hzE]
    rw [hG0] at h
    simpa only [G, K] using h
  have hJacJ : IsJacobiAlong (I := I) g γ J := by
    have hcurve :
        (fun t => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from uE) t) = γ := by
      funext t
      rw [huE]
    have h := intrinsic_jacobi (I := I) g hEnorm p uE aE
    rw [hcurve] at h
    simpa only [γ, J, F] using h
  have hJacK : IsJacobiAlong (I := I) g δ K := by
    have hcurve :
        (fun t => intrinsicGeodesic (I := I) g hEnorm z.proj
          (show TangentSpace I z.proj from zE) t) = δ := by
      funext t
      rw [hzE]
    have h := intrinsic_jacobi (I := I) g hEnorm z.proj zE b
    rw [hcurve] at h
    simpa only [δ, K, G] using h
  cases hδrev
  let Hrev : ℝ → ℝ → M := fun s t => F s ((-1 : ℝ) * t + 1)
  let JR : ∀ t : ℝ, TangentSpace I (δ t) :=
    fun t => J ((-1 : ℝ) * t + 1)
  have hHrev_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => Hrev q.1 q.2) := by
    have hflip :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : ℝ × ℝ => (q.1, (-1 : ℝ) * q.2 + 1)) :=
      contMDiff_fst.prodMk
        (contMDiff_const.mul contMDiff_snd |>.add contMDiff_const)
    exact hF_inf.comp hflip
  have hHrev_smooth : IsSmoothVariation (I := I) Hrev :=
    hHrev_inf.of_le ENat.LEInfty.out
  have hJRdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) δ JR t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) Hrev hHrev_smooth t
    have hH0 : (fun v => Hrev 0 v) = δ := by
      rw [← hrev_def]
      funext v
      simp only [Hrev, F, zero_smul, add_zero]
      rw [huE]
    rw [hH0] at h
    simpa only [Hrev, JR] using h
  have hDJRdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) δ
          (fun s => covDerivAlong (I := I) g δ JR s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g Hrev hHrev_smooth t
    have hH0 : (fun v => Hrev 0 v) = δ := by
      rw [← hrev_def]
      funext v
      simp only [Hrev, F, zero_smul, add_zero]
      rw [huE]
    rw [hH0] at h
    simpa only [Hrev, JR] using h
  have hJacJR : IsJacobiAlong (I := I) g δ JR := by
    rw [← hrev_def]
    simpa only [JR, Hrev, F] using
      jacobi_comp_affine (I := I) g γ J (-1) 1 hγ_inf hJacJ
  have hWderiv (t : ℝ) :
      HasDerivAt (jacobiWronskian (I := I) g δ K JR) 0 t :=
    hasDerivAt_wronsk (I := I) (n := ∞) (by simp) g δ K JR t hδ_inf
      (hKdiff t) (hJRdiff t) (hDKdiff t) (hDJRdiff t)
      (hJacK t) (hJacJR t)
  have hWcont :
      ContinuousOn (jacobiWronskian (I := I) g δ K JR)
        (Icc (0 : ℝ) 1) := by
    intro t _
    exact (hWderiv t).continuousAt.continuousWithinAt
  have hWconst := constant_of_has_deriv_right_zero hWcont
    (fun t ht => (hWderiv t).hasDerivWithinAt)
  have hW10 :
      jacobiWronskian (I := I) g δ K JR 1 =
        jacobiWronskian (I := I) g δ K JR 0 :=
    hWconst 1 (by norm_num)
  have hJ0 : J 0 = 0 := by
    have hconst :
        (fun s : ℝ => F s 0) = fun _ : ℝ => p := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm p _
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s 0) 0 (1 : ℝ) = 0
    rw [hconst, mfderiv_const]
    rfl
  have hDJ0 :
      covDerivAlong (I := I) g γ J 0 = a := by
    have hcurve :
        (fun t => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from uE) t) = γ := by
      funext t
      rw [huE]
    have hp0 : intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from uE) 0 = γ 0 := by
      rw [huE]
    have h := intrinsic_jacobi_d0 (I := I) g hEnorm p uE aE
    have htransport := hp0 ▸ h
    rw [hcurve] at htransport
    have h' : covDerivAlong (I := I) g γ J 0 =
        (show TangentSpace I p from aE) := by
      with_unfolding_all
        simpa only [γ, J, F] using htransport
    exact h'.trans haE
  have hJ1 := intrinsic_jacobi_one (I := I) g hEnorm p uE aE
  have hK0 : K 0 = 0 := by
    have hconst :
        (fun s : ℝ => G s 0) = fun _ : ℝ => z.proj := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm z.proj _
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => G s 0) 0 (1 : ℝ) = 0
    rw [hconst, mfderiv_const]
    rfl
  have hDK0 :
      covDerivAlong (I := I) g δ K 0 = bT := by
    have hcurve :
        (fun t => intrinsicGeodesic (I := I) g hEnorm z.proj
          (show TangentSpace I z.proj from zE) t) = δ := by
      funext t
      rw [hzE]
    have hp0 : intrinsicGeodesic (I := I) g hEnorm z.proj
        (show TangentSpace I z.proj from zE) 0 = δ 0 := by
      rw [hzE]
    have h := intrinsic_jacobi_d0 (I := I) g hEnorm z.proj zE b
    have htransport := hp0 ▸ h
    rw [hcurve] at htransport
    have h' : covDerivAlong (I := I) g δ K 0 =
        (show TangentSpace I z.proj from b) := by
      with_unfolding_all
        simpa only [δ, K, G] using htransport
    exact h'.trans hbT
  have hK1 := intrinsic_jacobi_one (I := I) g hEnorm z.proj zE b
  have hDJR (t : ℝ) :
      covDerivAlong (I := I) g δ JR t =
        (-1 : ℝ) • covDerivAlong (I := I) g γ J ((-1 : ℝ) * t + 1) := by
    rw [← hrev_def]
    simpa only [JR] using
      covDeriv_comp_affine (I := I) g γ J (-1) 1 t
  have hJR0 : JR 0 = J 1 := by
    change J ((-1 : ℝ) * 0 + 1) = J 1
    have ht : (-1 : ℝ) * 0 + 1 = 1 := by norm_num
    rw [ht]
  have hJR1 : JR 1 = J 0 := by
    change J ((-1 : ℝ) * 1 + 1) = J 0
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht]
  have hDJR1 :
      covDerivAlong (I := I) g δ JR 1 =
        -covDerivAlong (I := I) g γ J 0 := by
    have h := hDJR 1
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht] at h
    simpa only [neg_one_smul] using h
  have hδ0 : δ 0 = z.proj := by
    simpa only [δ] using
      intrinsicGeodesic_zero (I := I) g hEnorm z.proj (-z.snd)
  have hδ1 : δ 1 = p := by
    have h := congrFun hrev_def 1
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht] at h
    have hγ0 : γ 0 = p := by
      simpa only [γ] using
        intrinsicGeodesic_zero (I := I) g hEnorm p u
    exact h.symm.trans hγ0
  have hpair :
      g.inner p (K 1) a = g.inner z.proj bT (J 1) := by
    simp only [jacobiWronskian] at hW10
    rw [hJR1, hJ0, hDJR1, hDJ0, hK0, hDK0, hJR0] at hW10
    have hz1 :
        g.inner (δ 1) (covDerivAlong (I := I) g δ K 1)
            (0 : TangentSpace I (δ 1)) = 0 :=
      map_zero _
    have hz0 :
        g.inner (δ 0) (0 : TangentSpace I (δ 0))
            (covDerivAlong (I := I) g δ JR 0) = 0 := by
      rw [map_zero]
      rfl
    have hWsimple :
        0 - g.inner (δ 1) (K 1) (-a) =
          g.inner (δ 0) bT (J 1) - 0 := by
      calc
        0 - g.inner (δ 1) (K 1) (-a) =
            g.inner (δ 1) (covDerivAlong (I := I) g δ K 1)
                (0 : TangentSpace I (δ 1)) -
              g.inner (δ 1) (K 1) (-a) := by rw [hz1]
        _ =
            g.inner (δ 0) bT (J 1) -
              g.inner (δ 0) (0 : TangentSpace I (δ 0))
                (covDerivAlong (I := I) g δ JR 0) := hW10
        _ = g.inner (δ 0) bT (J 1) - 0 := by rw [hz0]
    rw [hδ1, hδ0] at hWsimple
    have hneg1 :
        g.inner p (K 1) (-a) = -g.inner p (K 1) a :=
      map_neg (g.inner p (K 1)) a
    rw [hneg1, sub_zero, zero_sub, neg_neg] at hWsimple
    exact hWsimple
  calc
    g.inner z.proj
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from w))
          (u : E) (a : E))
        b =
      g.inner z.proj b (J 1) := by
        with_unfolding_all
          change g.inner z.proj
              (mfderiv 𝓘(ℝ, E) I
                (fun w : E => expMapIntrinsic (I := I) g hEnorm p
                  (show TangentSpace I p from w)) uE aE)
              bT = g.inner z.proj bT (J 1)
          rw [← hJ1]
          exact g.symm z.proj _ _
    _ = g.inner p (K 1) a := hpair.symm
    _ =
      g.inner p a
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
            (show TangentSpace I z.proj from w))
          (-z.snd : E) b) := by
      with_unfolding_all
        change g.inner p (K 1) a =
          g.inner p a
            (mfderiv 𝓘(ℝ, E) I
              (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
                (show TangentSpace I z.proj from w)) zE b)
        rw [← hK1]
        exact g.symm p _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def IsConjVec
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x : E) : Prop :=
  ¬ Function.Injective fun w : E =>
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm b)) x
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm w)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem isConjVec_iff
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMapIntrinsic (I := I) g hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm b)) x
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm w) = 0 := by
  classical
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
  let f : E →L[ℝ] TangentSpace I
      (expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm x)) :=
    (mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm b)) x).comp
          e.symm.toContinuousLinearMap
  have hker : Function.Injective (fun w : E => f w) ↔
      ∀ w : E, f w = 0 → w = 0 := by
    constructor
    · intro hinj w hw
      have h0 : f w = f 0 := by rw [hw, map_zero]
      exact hinj h0
    · intro hker a b hab
      have hab' : f a = f b := hab
      have hsub : f (a - b) = 0 := by
        calc f (a - b) = f a - f b := map_sub f a b
          _ = 0 := by rw [hab', sub_self]
      exact sub_eq_zero.mp (hker _ hsub)
  with_unfolding_all change (¬ Function.Injective fun w : E => f w) ↔
    ∃ w : E, w ≠ 0 ∧ f w = 0
  rw [hker]
  push Not
  constructor
  · rintro ⟨w, hw0, hwne⟩
    exact ⟨w, hwne, hw0⟩
  · rintro ⟨w, hwne, hw0⟩
    exact ⟨w, hw0, hwne⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem conjVec_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) :
    IsConjVec (I := I) g hEnorm p (u : E) ↔
      let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
      IsConjVec (I := I) g hEnorm z.proj (-z.snd : E) := by
  classical
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let A : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun w : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from w))
      (u : E)
  let B : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
        (show TangentSpace I z.proj from w))
      (-z.snd : E)
  change (¬ Function.Injective A) ↔ ¬ Function.Injective B
  apply not_congr
  constructor
  · intro hA x y hxy
    have hAsurj : Function.Surjective A :=
      LinearMap.surjective_of_injective hA
    have hB0 : B (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := hAsurj (x - y)
    have hsquare :
        g.inner z.proj (x - y) (x - y) = 0 := by
      calc
        g.inner z.proj (x - y) (x - y) =
            g.inner z.proj (A a) (x - y) := by rw [ha]
        _ = g.inner p a (B (x - y)) := by
          with_unfolding_all
            exact (exp_pair_reverse (I := I) g hEnorm p u
              (show TangentSpace I p from a) (x - y))
        _ = 0 := by
          rw [hB0]
          exact map_zero _
    have hsub : x - y = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos z.proj (x - y) hne)) hsquare
    exact sub_eq_zero.mp hsub
  · intro hB x y hxy
    have hBsurj : Function.Surjective B :=
      LinearMap.surjective_of_injective hB
    have hA0 : A (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨b, hb⟩ := hBsurj (x - y)
    have hsquare :
        g.inner p (x - y) (x - y) = 0 := by
      calc
        g.inner p (x - y) (x - y) =
            g.inner p (x - y) (B b) := by rw [hb]
        _ = g.inner z.proj (A (x - y)) b := by
          symm
          with_unfolding_all
            exact (exp_pair_reverse (I := I) g hEnorm p u
              (show TangentSpace I p from x - y) b)
        _ = 0 := by
          rw [hA0]
          have hz :
              g.inner z.proj (0 : TangentSpace I z.proj) b = 0 := by
            rw [map_zero]
            rfl
          exact hz
    have hsub : x - y = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos p (x - y) hne)) hsquare
    exact sub_eq_zero.mp hsub

omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isConjVec_iff_jacobi
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + s • w) 1) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff (I := I) g hEnorm p x]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [intrinsic_jacobi_one (I := I) g hEnorm p x w]
  with_unfolding_all rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem jacobiVar_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x w : E) :
    mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x + s • w) 0) 0 (1 : ℝ) = 0 := by
  have hconst : (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) 0) = fun _ : ℝ => p := by
    funext s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  rw [hconst, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem jacobiVar_smul
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : E) {c : ℝ} (hc : c ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1) 0 (1 : ℝ) := by
  have hfun :
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + s • (c⁻¹ • w)) c) =
        fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
    funext s
    have hscale : c • (u + s • (c⁻¹ • w)) = c • u + s • w := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      field_simp
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c =
        intrinsicGeodesic (I := I) g hEnorm p
          (c • (show TangentSpace I p from u + s • (c⁻¹ • w))) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c).symm
      _ = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
        exact congrArg
          (fun z : E => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from z) 1)
          hscale
  rw [hfun]
  rfl

omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem conjVec_jacobi_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) {c : ℝ} (hc : c ≠ 0)
    (hconj : IsConjVec (I := I) g hEnorm p (c • u)) :
    ∃ z : E, z ≠ 0 ∧
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • z) c) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff_jacobi (I := I) g hEnorm p (c • u)] at hconj
  obtain ⟨w, hw, hwend⟩ := hconj
  refine ⟨c⁻¹ • w, smul_ne_zero (inv_ne_zero hc) hw, ?_⟩
  rw [jacobiVar_smul (I := I) g hEnorm p u w hc]
  exact hwend

end Riemannian
end Geometry
end DifferentialGeometry
