import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import DifferentialGeometry.Geometry.Curvature.ScalarGradientTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ScalarDerivativeTransport

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

theorem exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence
    {D r : ℝ} (hrD : r < D + 1) {N : ℕ} (hN : 2 ≤ N)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ → RealTimeInterval) (age : ℕ → ℝ), (∀ i, 0 < age i) →
      ∀ S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, Icc (0 : ℝ) (age i) ⊆ (J i).carrier) →
      (∀ i, Ioo (0 : ℝ) (age i) ⊆ (J i).regular) →
      (∀ i j, j ≤ 2 → ∀ t ∈ Icc (0 : ℝ) (age i),
        ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j ((S i).base.metric t) y ≤ B) →
      MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
        (fun i => (S i).base.metric (age i))
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace ThreeSpace (X i)]
        [∀ i, IsManifold ThreeModel ∞ (X i)] [∀ i, T2Space (X i)],
      ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel (X i))
        (Phi : ∀ i, standardCapWindow D → X i)
        (hPhi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i))
        (q birth : ℕ → ℝ) (hq : ∀ i, 0 < q i),
      (∀ i t, t ∈ Icc (0 : ℝ) (age i) → (S i).base.metric t =
        localPullMetric (scaleMetric (q i) (hq i) (gflow i (birth i + t / q i)))
          (Phi i) (hPhi i)) →
      ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
        (∀ w : TangentSpace ThreeModel (Phi i y),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
            (metricScalarAt (gflow i (birth i + age i / q i))) (Phi i y) w)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) *
              Real.sqrt (metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y)) *
              Real.sqrt ((gflow i (birth i + age i / q i)).inner (Phi i y) w w)) ∧
        |derivWithin (fun t => metricScalarAt (gflow i t) (Phi i y))
          (Iic (birth i + age i / q i)) (birth i + age i / q i)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) ^ 2 := by
  obtain ⟨C, hC, hbounds⟩ := exists_relative_scalar_derivative_bounds_of_curvature_jets
    (I := ThreeModel) (M := standardCapWindow D) B hB
  refine ⟨C, hC, ?_⟩
  intro J age hage S hS hcarrier hregular hjets hconv X _ _ _ _ gflow Phi hPhi q birth hq hmetric
  have hlower := eventually_half_lt_metricScalarAt_of_metric_cp_convergence hrD hN
    (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hlower] with i hi
  intro y hy
  have ht : age i ∈ Icc (0 : ℝ) (age i) := ⟨(hage i).le, le_rfl⟩
  have ht' : age i ∈ Ioc (0 : ℝ) (age i) := ⟨hage i, le_rfl⟩
  have hR : 1 / 2 ≤ (S i).scalar (age i) y := (hi y hy).le
  have hb := hbounds (J i) (S i) (hS i) 0 (age i) (hcarrier i) (hregular i)
    {z : standardCapWindow D | ‖z.val‖ ≤ r} (hjets i)
  constructor
  · apply scalar_gradient_bound_of_localPull_scaleMetric
      (gflow i (birth i + age i / q i)) (Phi i) (hPhi i) (hq i) y
    have hgradient := hb.1 (age i) ht y hy hR
    change ∀ v : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt ((S i).base.metric (age i))) y v)| ≤
        C * metricScalarAt ((S i).base.metric (age i)) y *
          Real.sqrt (metricScalarAt ((S i).base.metric (age i)) y) *
          Real.sqrt (((S i).base.metric (age i)).inner y v v) at hgradient
    rwa [hmetric i (age i) ht] at hgradient
  · exact (S i).abs_derivWithin_scalar_le_of_parabolic_localPullMetric (hS i) (gflow i)
      (Phi i) (hPhi i) (hq i) (hmetric i) (hcarrier i) ht' y
      (hb.2 (age i) ht' y hy hR)

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

private local instance (U : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

theorem exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {D r : ℝ}, r < D + 1 → ∀ {N : ℕ}, 4 ≤ N →
      ∀ (J : ℕ → RealTimeInterval) (age : ℕ → ℝ), (∀ i, 0 < age i) →
      ∀ S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, Icc (0 : ℝ) (age i) ⊆ (J i).carrier) →
      (∀ i, Ioo (0 : ℝ) (age i) ⊆ (J i).regular) →
      MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
        (fun i => (S i).base.metric (age i))
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace ThreeSpace (X i)]
        [∀ i, IsManifold ThreeModel ∞ (X i)] [∀ i, T2Space (X i)],
      ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel (X i))
        (Phi : ∀ i, standardCapWindow D → X i)
        (hPhi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i))
        (q birth : ℕ → ℝ) (hq : ∀ i, 0 < q i),
      (∀ i t, t ∈ Icc (0 : ℝ) (age i) → (S i).base.metric t =
        localPullMetric (scaleMetric (q i) (hq i) (gflow i (birth i + t / q i)))
          (Phi i) (hPhi i)) →
      ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
        (∀ w : TangentSpace ThreeModel (Phi i y),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
            (metricScalarAt (gflow i (birth i + age i / q i))) (Phi i y) w)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) *
              Real.sqrt (metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y)) *
              Real.sqrt ((gflow i (birth i + age i / q i)).inner (Phi i y) w w)) ∧
        |derivWithin (fun t => metricScalarAt (gflow i t) (Phi i y))
          (Iic (birth i + age i / q i)) (birth i + age i / q i)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) ^ 2 := by
  obtain ⟨B, hB, hjets⟩ := exists_eventually_window_curvature_derivative_bounds_of_metric_cp_convergence
  obtain ⟨C, hC, hbounds⟩ := exists_relative_scalar_derivative_bounds_of_terminal_curvature_jets
    (E := ThreeSpace) B (zero_le_one.trans hB)
  refine ⟨C, hC, ?_⟩
  intro D r hrD N hN J age hage S hS hcarrier hregular hconv X _ _ _ _ gflow Phi hPhi q birth hq hmetric
  have hlower := eventually_half_lt_metricScalarAt_of_metric_cp_convergence hrD (by omega : 2 ≤ N)
    (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hlower, hjets D r hrD N hN (fun i => (S i).base.metric (age i)) hconv] with i hi hji
  intro y hy
  have ht : age i ∈ Icc (0 : ℝ) (age i) := ⟨(hage i).le, le_rfl⟩
  have ht' : age i ∈ Ioc (0 : ℝ) (age i) := ⟨hage i, le_rfl⟩
  have hR : 1 / 2 ≤ (S i).scalar (age i) y := (hi y hy).le
  have hb := hbounds (J i) (S i) (hS i) 0 (age i) (hage i) (hcarrier i) (hregular i)
    y (fun j hj => hji j hj y hy) hR
  constructor
  · apply scalar_gradient_bound_of_localPull_scaleMetric
      (gflow i (birth i + age i / q i)) (Phi i) (hPhi i) (hq i) y
    have hgradient := hb.1
    change ∀ v : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt ((S i).base.metric (age i))) y v)| ≤
        C * metricScalarAt ((S i).base.metric (age i)) y *
          Real.sqrt (metricScalarAt ((S i).base.metric (age i)) y) *
          Real.sqrt (((S i).base.metric (age i)).inner y v v) at hgradient
    rwa [hmetric i (age i) ht] at hgradient
  · exact (S i).abs_derivWithin_scalar_le_of_parabolic_localPullMetric (hS i) (gflow i)
      (Phi i) (hPhi i) (hq i) (hmetric i) (hcarrier i) ht' y
      hb.2

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
end
