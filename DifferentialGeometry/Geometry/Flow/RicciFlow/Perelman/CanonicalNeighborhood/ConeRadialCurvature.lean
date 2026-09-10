import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeKoszul
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.Components.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
open Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem metricRm04_coneEuler_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ h y.2) (hr : z.1 ≠ 0)
    (u v w : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    metricRm04At g z (vec4 u v (coneEulerField z) w) = 0 := by
  let R : ContMDiffSection 𝓘(ℝ, ℝ × V) (ℝ × V) ∞
      (TangentSpace 𝓘(ℝ, ℝ × V) : (ℝ × V) → Type _) :=
    ⟨coneEulerField, coneEulerField_contMDiff⟩
  apply metricRm04_concurrent_eq_zero g R _ u v w
  have hrnear : ∀ᶠ y : ℝ × V in 𝓝 z, y.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually_ne hr
  filter_upwards [eventually_eventually_nhds.mpr hmetric, hh, hrnear] with y hgy hhy hry
  intro a
  exact leviCivita_coneEuler_of_coneForm g hgy hhy hry a

theorem metricRm04_coneRadial_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ h y.2) (hr : z.1 ≠ 0)
    (u v w : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    metricRm04At g z (vec4 u v (constantModelVectorField (1, 0) z) w) = 0 := by
  have hz := metricRm04_coneEuler_eq_zero g hmetric hh hr u v w
  have hmul : metricRm04At g z (vec4 u v (coneEulerField z) w) =
      z.1 * metricRm04At g z (vec4 u v (constantModelVectorField (1, 0) z) w) := by
    have hupdate (a : TangentSpace 𝓘(ℝ, ℝ × V) z) :
        Function.update (vec4 u v (constantModelVectorField (1, 0) z) w) (2 : Fin 4) a =
          vec4 u v a w := by
      funext i
      fin_cases i <;> rfl
    have h := (metricRm04At g z).map_update_smul
      (vec4 u v (constantModelVectorField (1, 0) z) w) (2 : Fin 4) z.1
        (constantModelVectorField (1, 0) z)
    rw [hupdate, hupdate] at h
    exact h
  rw [hmul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
