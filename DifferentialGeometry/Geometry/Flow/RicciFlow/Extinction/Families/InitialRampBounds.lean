import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [TopologicalSpace Q] in
theorem initialRamp_projection_lift (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).projection.lift x t = γ x := rfl

omit [TopologicalSpace Q] in
theorem initialRamp_y (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).y x t = x := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_X_snd (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    ((initialRamp γ).X (I := I) x t).2 = 1 := by
  simp only [ProductCurve.X, initialRamp_y, deriv_id'']

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_immersedOn (γ : Surgery.Topology.Circle → Q) :
    (initialRamp γ).ImmersedOn (I := I) (univ : Set ℝ) := by
  intro x t _ h
  have h2 : ((initialRamp γ).X (I := I) x t).2 = (0 : ℝ) := by
    rw [h]; rfl
  rw [initialRamp_X_snd] at h2
  exact one_ne_zero h2

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_speed_pos (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    0 < (initialRamp γ).speed (fun _ : ℝ => g) lambda x t := by
  rw [ProductCurve.speed, ProductCurve.inner]
  refine Real.sqrt_pos.2 ?_
  have hX2 : ((initialRamp γ).X (I := I) x t).2 = 1 := initialRamp_X_snd γ x t
  have h1 : 0 ≤ g.inner ((initialRamp γ).projection.lift x t)
      ((initialRamp γ).X (I := I) x t).1 ((initialRamp γ).X (I := I) x t).1 :=
    metric_inner_self_nonneg g _ _
  have h2 : 0 < lambda ^ 2 * ((initialRamp γ).X (I := I) x t).2 *
      ((initialRamp γ).X (I := I) x t).2 := by
    rw [hX2]
    positivity
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_angle (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).angle (fun _ : ℝ => g) lambda x t =
      lambda * ((initialRamp γ).speed (fun _ : ℝ => g) lambda x t)⁻¹ := by
  have hX2 : ((initialRamp γ).X (I := I) x t).2 = 1 := initialRamp_X_snd γ x t
  rw [ProductCurve.angle, ProductCurve.unitTangent, ProductCurve.verticalUnit,
    ProductCurve.inner]
  simp only [Prod.smul_fst, Prod.smul_snd, hX2, mul_one, smul_eq_mul,
    ContinuousLinearMap.map_zero, zero_add]
  field_simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_angle_pos (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    0 < (initialRamp γ).angle (fun _ : ℝ => g) lambda x t := by
  rw [initialRamp_angle g hlambda γ x t]
  exact mul_pos hlambda (inv_pos.mpr (initialRamp_speed_pos g hlambda γ x t))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_isRampOn (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) :
    (initialRamp γ).IsRampOn (fun _ : ℝ => g) lambda (univ : Set ℝ) :=
  ⟨fun x t _ => initialRamp_immersedOn γ x t trivial,
    fun x t _ => initialRamp_angle_pos g hlambda γ x t⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_smoothOn {γ : Surgery.Topology.Circle → Q}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle))) :
    (initialRamp γ).SmoothOn (I := I) (univ : Set ℝ) := by
  refine ⟨?_, ?_⟩
  · change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.1 : Surgery.Topology.Circle)) (univ ×ˢ (univ : Set ℝ))
    have hfst : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.1) :=
      contMDiff_iff_contDiff.mpr contDiff_fst
    have hcomp : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
        ((fun t : ℝ => γ (t : Surgery.Topology.Circle)) ∘ fun p : ℝ × ℝ => p.1) :=
      hγ.comp hfst
    simpa only [Set.univ_prod_univ, Function.comp_def] using hcomp.contMDiffOn
  · change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1) (univ ×ˢ (univ : Set ℝ))
    simpa only [Set.univ_prod_univ] using
      (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1)).contDiffOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
