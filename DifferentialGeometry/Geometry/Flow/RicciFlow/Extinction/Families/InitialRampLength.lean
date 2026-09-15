import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem initialRamp_speed_eq (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (lambda x t : ℝ) :
    (initialRamp γ).speed (fun _ => g) lambda x t =
      Real.sqrt (g.inner (loopLift γ x) (loopVelocity (I := I) γ x)
        (loopVelocity (I := I) γ x) + lambda ^ 2) := by
  rw [ProductCurve.speed, ProductCurve.inner, initialRamp_X_snd, mul_one, mul_one]
  rfl

theorem initialRamp_speed_le (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (lambda x t : ℝ) :
    (initialRamp γ).speed (fun _ => g) lambda x t ≤
      Real.sqrt (g.inner (loopLift γ x) (loopVelocity (I := I) γ x)
        (loopVelocity (I := I) γ x)) + |lambda| := by
  rw [initialRamp_speed_eq]
  have hq := metric_inner_self_nonneg g (loopLift γ x) (loopVelocity (I := I) γ x)
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hq, sq_abs lambda,
    mul_nonneg (Real.sqrt_nonneg (g.inner (loopLift γ x)
      (loopVelocity (I := I) γ x) (loopVelocity (I := I) γ x))) (abs_nonneg lambda)]

theorem initialRamp_length_le (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) (lambda t : ℝ) :
    (initialRamp γ).length (fun _ => g) lambda t ≤
      loopLength g γ.toContinuousLoop + |lambda| := by
  let q : ℝ → ℝ := fun x => g.inner (loopLift γ.toContinuousLoop x)
    (loopVelocity (I := I) γ.toContinuousLoop x) (loopVelocity (I := I) γ.toContinuousLoop x)
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      ((DifferentialGeometry.metricQuad_cont g).comp γ.continuous_firstJet)
  have hr : ContinuousOn (fun x => (initialRamp γ).speed (fun _ => g) lambda x t)
      (Icc (0 : ℝ) 1) := by
    simp_rw [initialRamp_speed_eq]
    exact (hq.add continuousOn_const).sqrt
  have hh : ContinuousOn (fun x => Real.sqrt (q x) + |lambda|) (Icc (0 : ℝ) 1) :=
    hq.sqrt.add continuousOn_const
  have hle := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hr.intervalIntegrable_of_Icc zero_le_one)
    (hh.intervalIntegrable_of_Icc zero_le_one)
    (fun x _ => initialRamp_speed_le g γ.toContinuousLoop lambda x t)
  rw [intervalIntegral.integral_add
    (hq.sqrt.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const,
    intervalIntegral.integral_const] at hle
  simp only [sub_zero, one_smul] at hle
  rw [ProductCurve.length, ProductCurve.integral]
  simp only [one_mul]
  change (∫ x in (0 : ℝ)..1, (initialRamp γ).speed (fun _ => g) lambda x t) ≤ _
  convert hle using 1
  rw [loopLength, ← restrict_Ioc_eq_restrict_Icc, ← intervalIntegral.integral_of_le zero_le_one]

theorem initialRamp_length_le_add_one (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) {lambda : ℝ} (hlambda : 0 ≤ lambda) (hlambda_one : lambda ≤ 1)
    (t : ℝ) :
    (initialRamp γ).length (fun _ => g) lambda t ≤ loopLength g γ.toContinuousLoop + 1 := by
  have h := initialRamp_length_le g γ lambda t
  rw [abs_of_nonneg hlambda] at h
  exact h.trans (add_le_add_right hlambda_one _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
