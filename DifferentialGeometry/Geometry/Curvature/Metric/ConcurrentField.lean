import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.Components.Basic

set_option autoImplicit false
noncomputable section
open Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
theorem connectionRiemannCurvatureField_eq_zero_of_cov_eq_id
    (g : SmoothRiemannianMetric I M)
    (R X Y : (y : M) → TangentSpace I y) {x : M}
    (hX : MDifferentiableAt I I.tangent (T% X) x)
    (hY : MDifferentiableAt I I.tangent (T% Y) x)
    (hR : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g R y v = v) :
    connectionRiemannCurvatureField (metricCov g) X Y R x = 0 := by
  have hRY : (fun y => metricCov g R y (Y y)) =ᶠ[𝓝 x] Y :=
    hR.mono fun y hy => hy (Y y)
  have hRX : (fun y => metricCov g R y (X y)) =ᶠ[𝓝 x] X :=
    hR.mono fun y hy => hy (X y)
  have hRYt : (T% (fun y => metricCov g R y (Y y))) =ᶠ[𝓝 x] (T% Y) :=
    hRY.mono fun y hy => congrArg (fun v => (⟨y, v⟩ : TangentBundle I M)) hy
  have hRXt : (T% (fun y => metricCov g R y (X y))) =ᶠ[𝓝 x] (T% X) :=
    hRX.mono fun y hy => congrArg (fun v => (⟨y, v⟩ : TangentBundle I M)) hy
  have hfirst := metricCov_congr_nhds g (hY.congr_of_eventuallyEq hRYt) hY hRY
  have hsecond := metricCov_congr_nhds g (hX.congr_of_eventuallyEq hRXt) hX hRX
  have htor := torsion_free_at_apply
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g x) hX hY
  unfold connectionRiemannCurvatureField
  rw [hfirst, hsecond, hR.self_of_nhds]
  exact sub_eq_zero.mpr htor

theorem metricRm04_concurrent_eq_zero
    (g : SmoothRiemannianMetric I M)
    (R : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hR : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g R y v = v)
    (u v w : TangentSpace I x) : metricRm04At g x (vec4 u v (R x) w) = 0 := by
  obtain ⟨X, _hXnear, hX⟩ :=
    CovariantDerivative.exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x u
  obtain ⟨Y, _hYnear, hY⟩ :=
    CovariantDerivative.exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x v
  obtain ⟨W, _hWnear, hW⟩ :=
    CovariantDerivative.exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x w
  have hcurv := CovariantDerivative.riemannCurvature04At_apply_smooth g
    (metricCov g) (metricCov_smooth g) X Y R W x
  have hz := connectionRiemannCurvatureField_eq_zero_of_cov_eq_id g R X Y
    (X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hR
  rw [hz, map_zero] at hcurv
  simpa only [metricRm04At, hX, hY, hW] using hcurv

theorem metricRm13_concurrent_eq_zero
    (g : SmoothRiemannianMetric I M)
    (R : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hR : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g R y v = v)
    (alpha : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) 1 x)
    (u v : TangentSpace I x) : metricRm13At g x alpha (vec3 u v (R x)) = 0 := by
  obtain ⟨X, _hXnear, hX⟩ :=
    CovariantDerivative.exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x u
  obtain ⟨Y, _hYnear, hY⟩ :=
    CovariantDerivative.exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x v
  have hcurv := CovariantDerivative.riemannCurvatureAt_apply_smooth
    (metricCov g) (metricCov_smooth g) X Y R alpha
  have hz := connectionRiemannCurvatureField_eq_zero_of_cov_eq_id g R X Y
    (X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hR
  rw [hz, map_zero] at hcurv
  simpa only [metricRm13At, hX, hY] using hcurv

theorem metricRicci_concurrent_eq_zero
    (g : SmoothRiemannianMetric I M)
    (R : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hR : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g R y v = v)
    (u : TangentSpace I x) : metricRicciAt g x (vec2 u (R x)) = 0 := by
  classical
  rw [metricRicciAt_eq_trace,
    ricciFromRm13At_apply_basis_trace (Module.finBasis ℝ (TangentSpace I x))]
  apply Finset.sum_eq_zero
  intro a _ha
  exact metricRm13_concurrent_eq_zero g R hR _ _ u

end DifferentialGeometry.Geometry.Curvature
