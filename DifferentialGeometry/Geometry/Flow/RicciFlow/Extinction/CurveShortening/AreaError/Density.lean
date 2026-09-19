import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation
import DifferentialGeometry.Geometry.Curve.NormalVelocityErrorDensity
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Topology.Manifold.OpenSubtypeModel

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem areaError_integrand_eq_normalVelocityErrorDensity
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (x t : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x) :
    Real.sqrt (c.normSq g (c.normalVelocityError g J) x t) * c.speed g x t =
      normalVelocityErrorDensity
        ((g t).inner (c.lift x t), c.X x t, c.Dx g c.X x t, c.velocity J x t) := by
  have hnonneg : 0 ≤ (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
    DifferentialGeometry.metric_inner_self_nonneg (g t) _ _
  have hs : c.speed g x t ^ 2 =
      (g t).inner (c.lift x t) (c.X x t) (c.X x t) := Real.sq_sqrt hnonneg
  have hK := curvatureVector_eq_speed_inv_sq_Dx_sub_tangent g c x t hc
  have hK' : c.curvatureVector g x t =
      ((g t).inner (c.lift x t) (c.X x t) (c.X x t))⁻¹ • c.Dx g c.X x t -
        (((g t).inner (c.lift x t) (c.X x t) (c.X x t))⁻¹ ^ 2 *
          (g t).inner (c.lift x t) (c.Dx g c.X x t) (c.X x t)) • c.X x t := by
    rw [hK, zpow_neg, zpow_ofNat, hs]
    congr 1
    congr 1
    rw [(g t).symm (c.lift x t) (c.X x t) (c.Dx g c.X x t)]
    rw [show c.speed g x t ^ 4 = (c.speed g x t ^ 2) ^ 2 by ring, hs]
    rw [div_eq_mul_inv, inv_pow, mul_comm]
  have hN : c.normalVelocityError g J x t =
      (c.velocity J x t - c.curvatureVector g x t) -
        (((g t).inner (c.lift x t) (c.X x t) (c.X x t))⁻¹ *
          (g t).inner (c.lift x t) (c.velocity J x t - c.curvatureVector g x t)
            (c.X x t)) • c.X x t := by
    unfold normalVelocityError unitTangent
    simp only [map_smul, smul_eq_mul, smul_smul]
    rw [← hs, ← inv_pow]
    congr 1
    congr 1
    ring
  unfold normalVelocityErrorDensity
  dsimp only
  rw [normSq, hN, hK']
  rfl

theorem areaError_eq_integral_normalVelocityErrorDensity
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (t : ℝ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t)) :
    c.areaError g J t = ∫ x in (0 : ℝ)..1,
      normalVelocityErrorDensity
        ((g t).inner (c.lift x t), c.X x t, c.Dx g c.X x t, c.velocity J x t) := by
  unfold areaError integral
  exact intervalIntegral.integral_congr fun x _ =>
    areaError_integrand_eq_normalVelocityErrorDensity c g J x t (hc x)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curve
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {U : TopologicalSpace.Opens F}

omit [FiniteDimensional ℝ F] in
theorem X_opens_eq_deriv (c : CurveMap U) (x t : ℝ) :
    c.X (I := 𝓘(ℝ, F)) x t = deriv (fun y => (c.lift y t : F)) x := by
  have h := DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, F))
    (fun y => c.lift y t) x
  have he := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) h
  change @Eq F _ _ at he ⊢
  rw [mfderiv_eq_fderiv] at he
  exact he.symm

omit [FiniteDimensional ℝ F] in
theorem velocity_opens_eq_derivWithin (c : CurveMap U) (J : Set ℝ) (x t : ℝ)
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (c.lift x) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    c.velocity (I := 𝓘(ℝ, F)) J x t = derivWithin (fun y => (c.lift x y : F)) J t := by
  have h := mfderiv_comp_mfderivWithin t
    ((contMDiff_subtype_val (I := 𝓘(ℝ, F)) (U := U) (n := ∞)).mdifferentiableAt (by simp)) hc
    hJ.uniqueMDiffWithinAt
  have he := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) h
  change @Eq F _ _ at he ⊢
  change (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun y => (c.lift x y : F)) J t) 1 =
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : U → F) (c.lift x t)
      ((mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (c.lift x) J t) 1) at he
  rw [DifferentialGeometry.mfderiv_subtype_val_apply] at he
  rw [mfderivWithin_eq_fderivWithin] at he
  exact he.symm

theorem Dx_X_opens_eq_deriv_deriv_add (c : CurveMap U)
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U) (x t : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 (fun y => c.lift y t) x) :
    c.Dx g c.X x t = deriv (deriv (fun y => (c.lift y t : F))) x +
      chartChristoffelContraction (g t) (c.lift x t)
        (deriv (fun y => (c.lift y t : F)) x)
        (deriv (fun y => (c.lift y t : F)) x) (c.lift x t) := by
  have h := covariantAcceleration_modelCoord_of_contMDiffAt (g t) (fun y => c.lift y t) x hc
  have hchart : chartCurve (I := 𝓘(ℝ, F)) (c.lift x t) (fun y => c.lift y t) =
      fun y => (c.lift y t : F) := rfl
  rw [hchart] at h
  change @Eq F (c.Dx g c.X x t)
    (deriv (deriv (fun y => (c.lift y t : F))) x +
      chartChristoffelContraction (g t) (c.lift x t)
        (deriv (fun y => (c.lift y t : F)) x)
        (deriv (fun y => (c.lift y t : F)) x) (c.lift x t))
  simpa only [tangentSpaceModelContinuousLinearEquiv_apply, DifferentialGeometry.extChartAt_opens_apply,
    Dx, X, covariantAcceleration_def] using h

theorem areaError_integrand_opens_eq_normalVelocityErrorDensity
    (c : CurveMap U) (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U) (J : Set ℝ) (x t : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 (fun y => c.lift y t) x)
    (hv : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (c.lift x) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    Real.sqrt (c.normSq g (c.normalVelocityError g J) x t) * c.speed g x t =
      normalVelocityErrorDensity
        ((g t).inner (c.lift x t), deriv (fun y => (c.lift y t : F)) x,
          deriv (deriv (fun y => (c.lift y t : F))) x +
            chartChristoffelContraction (g t) (c.lift x t)
              (deriv (fun y => (c.lift y t : F)) x)
              (deriv (fun y => (c.lift y t : F)) x) (c.lift x t),
          derivWithin (fun y => (c.lift x y : F)) J t) := by
  rw [areaError_integrand_eq_normalVelocityErrorDensity c g J x t hc,
    X_opens_eq_deriv c x t,
    Dx_X_opens_eq_deriv_deriv_add c g x t hc,
    velocity_opens_eq_derivWithin c J x t hv hJ]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
