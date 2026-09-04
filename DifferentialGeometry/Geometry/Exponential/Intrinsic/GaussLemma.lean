import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Analysis.Calculus.Seminorm.Radial
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.SpeedDerivative
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
  (image_radialDist_le_intervalIntegral_of_slope_le psd_sqrt_lipschitz)

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function MeasureTheory
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional Real E]
    [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem launch_inner_deriv
    (g : SmoothRiemannianMetric I M) (p : M) (u w : E) :
    HasDerivAt
      (fun s : Real => g.inner p (u + s • w) (u + s • w))
      (2 * g.inner p u w) 0 := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hexpand :
      (fun s : Real => g.inner p (u + s • w) (u + s • w)) =
        (fun s : Real =>
          gp u u + s * (gp u w + gp w u) + s ^ 2 * gp w w) := by
    funext s
    change gp (u + s • w) (u + s • w) = _
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  have hd1 : HasDerivAt (fun _ : Real => gp u u) 0 0 :=
    hasDerivAt_const _ _
  have hd2 :
      HasDerivAt (fun s : Real => s * (gp u w + gp w u))
        (gp u w + gp w u) 0 := by
    simpa using (hasDerivAt_id (0 : Real)).mul_const (gp u w + gp w u)
  have hd3 : HasDerivAt (fun s : Real => s ^ 2 * gp w w) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : Real)).mul_const (gp w w)
  have hd :
      HasDerivAt
        (fun s : Real =>
          gp u u + s * (gp u w + gp w u) + s ^ 2 * gp w w)
        (gp u w + gp w u) 0 := by
    have hd' : HasDerivAt
        (fun s : Real =>
          gp u u + s * (gp u w + gp w u) + s ^ 2 * gp w w)
        (0 + (gp u w + gp w u) + 0) 0 := by
      refine ((hd1.add hd2).add hd3).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun _ => rfl
    simpa only [zero_add, add_zero] using hd'
  have hsymm : gp w u = gp u w := g.symm p w u
  have hval : (2 : Real) * gp u w = gp u w + gp w u := by
    rw [hsymm]
    ring
  exact hval ▸ hd

theorem intrinsic_gauss
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : E) :
    g.inner
        (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u))
        (intrinsicVelocityLift (I := I) g hEnorm p
          (show TangentSpace I p from u) 1).snd
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from v))
          u w)
      = g.inner p u w := by
  classical
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + s • w) t
  have hF : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun q : Real × Real => F q.1 q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p u w).of_le
      ENat.LEInfty.out
  let γ : Real → M := fun t => F 0 t
  let V : ∀ t, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(Real, Real) I (fun r => F 0 r) t (1 : Real)
  let W : ∀ t, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(Real, Real) I (fun s => F s t) 0 (1 : Real)
  have hγ : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
        (fun t : Real => ((0 : Real), t)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hF : ContMDiff _ _ _ _).comp hincl
  have hVdiff : ∀ t : Real,
      DifferentiableAt Real
        (chartRepAt (I := I) γ V t) t := by
    intro t
    simpa only [γ, V] using
      velocityField_chartRep_differentiableAt (I := I) F hF t
  have hWdiff : ∀ t : Real,
      DifferentiableAt Real
        (chartRepAt (I := I) γ W t) t := by
    intro t
    simpa only [γ, W] using
      variationField_chartRep_differentiableAt (I := I) F hF t
  have hphi_deriv : ∀ t : Real,
      HasDerivAt (fun r : Real => g.inner (γ r) (V r) (W r))
        (g.inner p u w) t := by
    intro t
    have hmc :=
      metric_compat_hasDerivAt_inner (I := I)
        (by exact_mod_cast (by norm_num : (1 : Nat) ≤ 8))
        g γ V W t hγ (hVdiff t) (hWdiff t)
    have hγC2 : ContMDiffAt 𝓘(Real, Real) I 2 γ t :=
      hγ.contMDiffAt.of_le (by norm_num)
    have hgeo : HasGeodesicEquationAt (I := I) g γ t := by
      simpa only [γ, F, zero_smul, add_zero] using
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) t)
    have hVcov : covDerivAlong (I := I) g γ V t = 0 := by
      exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t hγC2 hgeo
    have hcomm := commute_ds_dt_intrinsic (I := I) g F hF t
    have hspeed :
        (fun s : Real => speedSq (I := I) g F s t) =
          (fun s : Real => g.inner p (u + s • w) (u + s • w)) := by
      funext s
      have hcurve : (fun r : Real => F s r) =
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u + s • w) := by
        funext r
        rfl
      simp only [speedSq]
      rw [hcurve]
      exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u + s • w) t
    have hS1 := speedSq_hasDerivAt (I := I) g F t hF
    rw [hspeed] at hS1
    have hlaunch := launch_inner_deriv (I := I) g p u w
    have hcov_pair :
        g.inner (F 0 t)
          (covDerivAlong (I := I) g (fun s : Real => F s t)
            (fun s : Real =>
              mfderiv 𝓘(Real, Real) I
                (fun r : Real => F s r) t (1 : Real)) 0)
          (mfderiv 𝓘(Real, Real) I
            (fun r : Real => F 0 r) t (1 : Real))
          = g.inner p u w := by
      have htwo := hS1.unique hlaunch
      linarith
    have hWcov : covDerivAlong (I := I) g γ W t =
        covDerivAlong (I := I) g (fun s : Real => F s t)
          (fun s : Real =>
            mfderiv 𝓘(Real, Real) I
              (fun r : Real => F s r) t (1 : Real)) 0 := by
      simpa only [γ, W] using hcomm.symm
    have hsecond :
        g.inner (γ t) (V t)
          (covDerivAlong (I := I) g γ W t) =
          g.inner p u w := by
      rw [hWcov]
      have hsymm := g.symm (F 0 t)
        (covDerivAlong (I := I) g (fun s : Real => F s t)
          (fun s : Real =>
            mfderiv 𝓘(Real, Real) I
              (fun r : Real => F s r) t (1 : Real)) 0)
        (mfderiv 𝓘(Real, Real) I
          (fun r : Real => F 0 r) t (1 : Real))
      simpa only [γ, V] using hsymm.symm.trans hcov_pair
    have hfirst :
        g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t) = 0 := by
      rw [hVcov]
      simp
    convert hmc using 1
    rw [hfirst, hsecond, zero_add]
  let φ : Real → Real := fun t => g.inner (γ t) (V t) (W t)
  have hφderiv : ∀ t : Real, HasDerivAt φ (g.inner p u w) t := by
    intro t
    simpa only [φ] using hphi_deriv t
  have hφcont : Continuous φ :=
    continuous_iff_continuousAt.mpr (fun t => (hφderiv t).continuousAt)
  have hFTC :
      ∫ _t in (0 : Real)..1, g.inner p u w = φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num) hφcont.continuousOn
      (fun t _ => hφderiv t) intervalIntegrable_const
  have hconst : ∫ _t in (0 : Real)..1, g.inner p u w = g.inner p u w := by
    rw [intervalIntegral.integral_const]
    simp
  have hW0 : W 0 = 0 := by
    have hconst_curve : (fun s : Real => F s 0) = fun _ : Real => p := by
      funext s
      simp only [F]
      exact intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u + s • w)
    simp only [W]
    rw [hconst_curve, mfderiv_const]
    rfl
  have hφ0 : φ 0 = 0 := by
    simp only [φ]
    rw [hW0]
    simp
  have hφ1 : φ 1 = g.inner p u w := by
    rw [hconst] at hFTC
    linarith
  have hV1 :
      V 1 =
        (intrinsicVelocityLift (I := I) g hEnorm p
          (show TangentSpace I p from u) 1).snd := by
    simp only [V, F, intrinsicVelocityLift]
    rw [zero_smul, add_zero]
    have heq :
        (fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u) r) =
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u) := rfl
    exact congrArg (fun L : Real →L[Real] E => L 1)
      (mfderiv_congr (I := 𝓘(Real, Real)) (I' := I) (x := (1 : Real)) heq)
  have hW1 :
      W 1 =
        mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from v))
          u w := by
    simpa only [W, F] using
      intrinsic_jacobi_one (I := I) g hEnorm p u w
  have hγ1 :
      γ 1 =
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u) := by
    simp only [γ, F, zero_smul, add_zero]
    exact (expMapIntrinsic_def (I := I) g hEnorm p
      (show TangentSpace I p from u)).symm
  have h := hφ1
  simp only [φ] at h
  rw [hW1, hV1, hγ1] at h
  exact h

theorem intrinsic_gauss_modelEquiv
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : E) :
    g.inner
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u))
        (intrinsicVelocityLift (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u) 1).snd
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
          u
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) u).symm w))
      = g.inner p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm w) := by
  let e : TangentSpace I p ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) p
  have hexp :
      (fun v : E =>
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from v)) =
        fun v : E =>
          expMapIntrinsic (I := I) g hEnorm p (e.symm v) := by
    funext v
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  have h := intrinsic_gauss (I := I) g hEnorm p u w
  rw [hexp] at h
  have hu : (show TangentSpace I p from u) = e.symm u := by
    apply e.injective
    rfl
  have hw : (show TangentSpace I p from w) = e.symm w := by
    apply e.injective
    rfl
  let eModel : TangentSpace 𝓘(Real, E) u ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) u
  have hwModel :
      (show TangentSpace 𝓘(Real, E) u from w) = eModel.symm w := by
    apply eModel.injective
    rfl
  convert h using 1
  · rw [← hu, ← hwModel]
  · rw [← hu, ← hw]

section IntrinsicFramedRadial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [FiniteDimensional Real V] [NeZero (Module.finrank Real V)]
variable {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners Real V H'} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
variable [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
variable [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
  [IsContinuousRiemannianBundle V (fun x : N ↦ TangentSpace J x)]

theorem intrFrame_radial_le
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : N) (z v : V) :
    |Inner.inner Real z v| ≤
      ‖z‖ * Real.sqrt
        (intrFrameMetric (I := J) g hEnorm p z v v) := by
  classical
  by_cases hz : z = 0
  · subst z
    simp
  let u : TangentSpace J p := normalFrame (I := J) g p z
  let w : TangentSpace J p := normalFrame (I := J) g p v
  let q : N := intrinsicFramedExp (I := J) g hEnorm p z
  let U : TangentSpace J q :=
    (intrinsicVelocityLift (I := J) g hEnorm p u 1).snd
  let W : TangentSpace J q :=
    mfderiv 𝓘(Real, V) J
      (intrinsicFramedExp (I := J) g hEnorm p) z v
  have hW :
      W =
        mfderiv 𝓘(Real, V) J
          (fun b : V =>
            expMapIntrinsic (I := J) g hEnorm p
              (show TangentSpace J p from b))
          (u : V) (w : V) := by
    dsimp only [W]
    rw [intrFrame_mfderiv]
    exact (intrinsic_jacobi_one (I := J) g hEnorm p (u : V) (w : V)).trans rfl
  have hq :
      q = expMapIntrinsic (I := J) g hEnorm p u := by
    exact intrFrame_apply (I := J) g hEnorm p z
  have hgauss : g.inner q U W = Inner.inner Real z v := by
    rw [hW, hq]
    simpa only [u, w, normalFrame_inner] using
      intrinsic_gauss (I := J) g hEnorm p (u : V) (w : V)
  have hspeed :
      Real.sqrt (g.inner q U U) = ‖z‖ := by
    have hsq := intrinsicGeodesic_speedSq_eq
      (I := J) g hEnorm p u 1
    change g.inner q U U = g.inner p u u at hsq
    rw [hsq]
    exact normalFrame_sqrt (I := J) g p z
  calc
    |Inner.inner Real z v| = |g.inner q U W| := by rw [hgauss]
    _ ≤ Real.sqrt (g.inner q U U) * Real.sqrt (g.inner q W W) :=
      abs_metric_inner_le_sqrt_metric_quadratic
        (I := J) (M := N) g q U W
    _ = ‖z‖ * Real.sqrt
        (intrFrameMetric (I := J) g hEnorm p z v v) := by
      rw [hspeed, intrFrameMetric_apply]

theorem intrLift_norm_le
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : N) {η : Real → V} {a b : Real}
    (hab : a ≤ b) (hηa : η a = 0)
    (hη : ContDiffOn Real 1 η (Set.Icc a b)) :
    ENNReal.ofReal ‖η b‖ ≤
      Manifold.pathELength J
        ((intrinsicFramedExp (I := J) g hEnorm p) ∘ η) a b := by
  classical
  let F : V → N := intrinsicFramedExp (I := J) g hEnorm p
  let γ : Real → N := F ∘ η
  let B : V →L[Real] V →L[Real] Real := innerSL Real
  let ρ : Real → Real := fun t => Real.sqrt (B (η t) (η t))
  let φ : Real → Real := fun t =>
    Real.sqrt
      (g.inner (γ t)
        (mfderivWithin 𝓘(Real, Real) J γ (Set.Icc a b) t 1)
        (mfderivWithin 𝓘(Real, Real) J γ (Set.Icc a b) t 1))
  have hBsym : ∀ x y : V, B x y = B y x := by
    intro x y
    change Inner.inner Real x y = Inner.inner Real y x
    exact real_inner_comm y x
  have hBnn : ∀ x : V, 0 ≤ B x x := by
    intro x
    change 0 ≤ Inner.inner Real x x
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hηm :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, V) 1 η (Set.Icc a b) :=
    hη.contMDiffOn
  have hγ :
      ContMDiffOn 𝓘(Real, Real) J 1 γ (Set.Icc a b) := by
    exact ((intrFrame_smooth (I := J) g hEnorm p).of_le
      (by norm_num)).comp_contMDiffOn hηm
  have hρc : ContinuousOn ρ (Set.Icc a b) := by
    exact (psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn
      hη.continuousOn
  have hρa : ρ a ≤ 0 := by
    simp only [ρ, hηa, map_zero, Real.sqrt_zero, le_refl]
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [hηa, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hUnique : UniqueMDiffOn 𝓘(Real, Real) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift :
      Continuous
        (fun t : Real =>
          (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps :
      Set.MapsTo
        (fun t : Real =>
          (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
        (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) :=
    fun t ht => by simpa using ht
  have hVel :
      ContinuousOn
        (fun t : Real =>
          TotalSpace.mk' V
            (E := (TangentSpace J : N → Type _)) (γ t)
            (mfderivWithin 𝓘(Real, Real) J γ (Set.Icc a b) t 1))
        (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun _ _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    simp only [φ]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := J) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t :=
    fun _ _ => Real.sqrt_nonneg _
  have hφint :
      MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume :=
    hφc.integrableOn_compact isCompact_Icc
  have hφcont :
      ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz
      exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq :
      ∀ t ∈ Set.Ioo a b,
        φ t =
          Real.sqrt
            (g.inner (γ t)
              (mfderiv 𝓘(Real, Real) J γ t 1)
              (mfderiv 𝓘(Real, Real) J γ t 1)) := by
    intro t ht
    simp only [φ]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hchain :
      ∀ x ∈ Set.Icc a b,
        mfderivWithin 𝓘(Real, Real) J (F ∘ η) (Set.Icc a b) x 1 =
          (mfderiv 𝓘(Real, V) J F (η x)).comp
            (mfderivWithin 𝓘(Real, Real) 𝓘(Real, V)
              η (Set.Icc a b) x) 1 := by
    intro x hx
    have hηdiff :
        MDifferentiableWithinAt 𝓘(Real, Real) 𝓘(Real, V)
          η (Set.Icc a b) x :=
      (hηm.mdifferentiableOn one_ne_zero) x hx
    have hFdiff :
        MDifferentiableWithinAt 𝓘(Real, V) J F Set.univ (η x) :=
      (intrFrame_smooth (I := J) g hEnorm p).mdifferentiableAt
        (by decide) |>.mdifferentiableWithinAt
    have hc := mfderivWithin_comp
      (I := 𝓘(Real, Real)) (I' := 𝓘(Real, V)) (I'' := J)
      (f := η) (g := F) (s := Set.Icc a b) (u := Set.univ)
      x hFdiff hηdiff (fun _ _ => Set.mem_univ _) (hUnique x hx)
    have happ := congrArg
      (fun D : Real →L[Real] TangentSpace J ((F ∘ η) x) => D 1) hc
    rw [mfderivWithin_univ] at happ
    with_unfolding_all exact happ
  have hslope :
      ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
        ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    let cv : V :=
      mfderivWithin 𝓘(Real, Real) 𝓘(Real, V)
        η (Set.Icc a b) x 1
    let hContinuousSMul : ContinuousSMul Real V := IsBoundedSMul.continuousSMul
    have hηderiv :
        @HasDerivWithinAt Real inferInstance V inferInstance inferInstance inferInstance
          hContinuousSMul η cv (Set.Ici x) x := by
      have hηdiff :
          MDifferentiableWithinAt 𝓘(Real, Real) 𝓘(Real, V)
            η (Set.Icc a b) x :=
        (hηm.mdifferentiableOn one_ne_zero) x hxIcc
      have hmf :
          HasMFDerivWithinAt 𝓘(Real, Real) 𝓘(Real, V)
            η (Set.Icc a b) x
            (mfderivWithin 𝓘(Real, Real) 𝓘(Real, V)
              η (Set.Icc a b) x) :=
        hηdiff.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hderiv :
          @HasDerivWithinAt Real inferInstance V inferInstance inferInstance inferInstance
            hContinuousSMul η cv (Set.Icc a b) x := by
        exact @HasFDerivWithinAt.hasDerivWithinAt Real inferInstance V inferInstance
          inferInstance inferInstance η x (Set.Icc a b) hContinuousSMul _ hmf
      refine hderiv.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz
        exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hηx : η x = 0
    · have htend :
          Filter.Tendsto (fun z => slope ρ x z)
            (nhdsWithin x (Set.Ioi x)) (nhds ‖cv‖) := by
        have hquot :
            Filter.Tendsto (fun z => (z - x)⁻¹ • η z)
              (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hηderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z
            simp only [Set.mem_sdiff, Set.mem_Ioi,
              Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (Filter.tendsto_congr' ?_).mp h0
          filter_upwards with z
          rw [slope_def_module, hηx, sub_zero]
        have htend' := continuous_norm.tendsto cv |>.comp hquot
        refine (Filter.tendsto_congr' ?_).mp htend'
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        simp only [Function.comp_apply, ρ, slope_def_module, hηx,
          map_zero, Real.sqrt_zero, sub_zero]
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzx),
          B, smul_eq_mul]
        change (z - x)⁻¹ * ‖η z‖ =
          (z - x)⁻¹ * Real.sqrt (Inner.inner Real (η z) (η z))
        rw [real_inner_self_eq_norm_sq,
          Real.sqrt_sq (norm_nonneg _)]
      have hφx : φ x = ‖cv‖ := by
        have hF0 : F 0 = p := by
          simp only [F, intrFrame_zero]
        simp only [φ]
        with_unfolding_all rw [show γ = F ∘ η from rfl, hchain x hxIcc,
          ContinuousLinearMap.comp_apply, Function.comp_apply, hηx,
          intrFrame_deriv_zero, hF0]
        with_unfolding_all
          change Real.sqrt
            (g.inner p (normalFrame (I := J) g p cv) (normalFrame (I := J) g p cv)) = ‖cv‖
        exact normalFrame_sqrt (I := J) g p cv
      rw [hφx] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa
        apply hηx
        rw [← hxa, hηa]
      have hmem : Set.Icc a b ∈ nhds x :=
        Icc_mem_nhds hxIoo.1 hxIoo.2
      have hηdiff : DifferentiableAt Real η x :=
        ((hη.differentiableOn one_ne_zero) x hxIcc).differentiableAt hmem
      have hηHDA : HasDerivAt η
          (mfderiv 𝓘(Real, Real) 𝓘(Real, V) η x 1) x := by
        rw [mfderiv_eq_fderiv]
        exact hηdiff.hasDerivAt
      have hcv :
          cv = mfderiv 𝓘(Real, Real) 𝓘(Real, V) η x 1 := by
        simp only [cv]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hpos : 0 < B (η x) (η x) := by
        simp only [B]
        change 0 < Inner.inner Real (η x) (η x)
        rw [real_inner_self_eq_norm_sq]
        positivity
      have hρderiv :
          HasDerivAt ρ
            (B (η x) cv / Real.sqrt (B (η x) (η x))) x := by
        rw [hcv]
        exact radialDist_hasDerivAt B hBsym η
          (mfderiv 𝓘(Real, Real) 𝓘(Real, V) η x 1)
          hηHDA hpos
      let ρ' : Real :=
        B (η x) cv / Real.sqrt (B (η x) (η x))
      have hφx :
          φ x =
            Real.sqrt
              (intrFrameMetric (I := J) g hEnorm p (η x) cv cv) := by
        simp only [φ]
        rw [show γ = F ∘ η from rfl, hchain x hxIcc,
          ContinuousLinearMap.comp_apply, intrFrameMetric_apply]
        rfl
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx]
        have hnorm : Real.sqrt (B (η x) (η x)) = ‖η x‖ := by
          simp only [B]
          change Real.sqrt (Inner.inner Real (η x) (η x)) = ‖η x‖
          rw [real_inner_self_eq_norm_sq,
            Real.sqrt_sq (norm_nonneg _)]
        simp only [ρ', hnorm]
        have hn : 0 < ‖η x‖ := norm_pos_iff.mpr hηx
        apply (div_le_iff₀ hn).2
        calc
          B (η x) cv ≤ |B (η x) cv| := le_abs_self _
          _ ≤ ‖η x‖ * Real.sqrt
              (intrFrameMetric (I := J) g hEnorm p (η x) cv cv) := by
                change |Inner.inner Real (η x) cv| ≤
                  ‖η x‖ * Real.sqrt
                    (intrFrameMetric (I := J) g hEnorm p (η x) cv cv)
                exact intrFrame_radial_le g hEnorm p (η x) cv
          _ = Real.sqrt
              (intrFrameMetric (I := J) g hEnorm p (η x) cv cv) *
                ‖η x‖ := mul_comm _ _
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact
        (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  have hftc : ρ b ≤ ∫ t in a..b, φ t :=
    image_radialDist_le_intervalIntegral_of_slope_le
      hab hρc hρa hφint hφcont hslope
  have hpath :
      ENNReal.ofReal (∫ t in a..b, φ t) ≤
        Manifold.pathELength J γ a b := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          exact hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo
    filter_upwards with t ht
    rw [hφ_eq t ht]
    exact le_of_eq
      (hEnorm (γ t) (mfderiv 𝓘(Real, Real) J γ t 1)).symm
  have hρb : ρ b = ‖η b‖ := by
    simp only [ρ, B]
    change Real.sqrt (Inner.inner Real (η b) (η b)) = ‖η b‖
    rw [real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
  rw [← hρb]
  exact (ENNReal.ofReal_le_ofReal hftc).trans hpath

end IntrinsicFramedRadial

end Riemannian
end Geometry
end DifferentialGeometry
