import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.ParabolicTerminalBall
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem shi_curvDerivNorm_scaleMetric_of_localPullMetric_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (g : SmoothRiemannianMetric I N)
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    {T Q θ K r : ℝ} (hQ : 0 < Q) (hθ : 0 < θ) (hK : 0 < K) (hr : 0 < r)
    (hcarrier : Icc (T - θ / Q) T ⊆ D.carrier)
    (hregular : Ioo (T - θ / Q) T ⊆ D.regular)
    (hterminal : S.base.metric T = localPullMetric g f hf)
    (x : N) (hcompact : IsCompact (riemannianClosedBallOf g x (r / Real.sqrt Q)))
    (hball : riemannianBallOf g x (r / Real.sqrt Q) ⊆ range f)
    (hcurv : ∀ t ∈ Icc (T - θ / Q) T,
      ∀ y : M, f y ∈ riemannianClosedBallOf g x (r / Real.sqrt Q) →
        curvDerivNormSq 0 (S.base.metric t) y ≤ (K * Q) ^ 2) :
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q hQ g) x ≤
      shiLocalUniformBound (Module.finrank ℝ E) m (K * (θ / 4))
        (((r / 2) / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * θ))) *
          Real.sqrt K / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (θ / 4)))) *
          K / Real.sqrt (θ / 4) ^ m := by
  have hR : 0 < r / Real.sqrt Q := div_pos hr (Real.sqrt_pos.mpr hQ)
  obtain ⟨p, hp, hcpt⟩ := Geometry.Metric.exists_lift_isCompact_riemannianClosedBallOf_localPullMetric
    g f hf hinj x hR hcompact hball
  have hhalf : (r / 2) / Real.sqrt Q < r / Real.sqrt Q :=
    div_lt_div_of_pos_right (by linarith) (Real.sqrt_pos.mpr hQ)
  have hcompact' : IsCompact (riemannianClosedBallOf (S.base.metric T) p
      ((r / 2) / Real.sqrt Q)) := by
    rw [hterminal]
    exact hcpt _ hhalf
  have hcurv' : ∀ t ∈ Icc (T - θ / Q) T,
      ∀ y ∈ riemannianClosedBallOf (S.base.metric T) p ((r / 2) / Real.sqrt Q),
        curvDerivNormSq 0 (S.base.metric t) y ≤ (K * Q) ^ 2 := by
    intro t ht y hy
    apply hcurv t ht y
    rw [hterminal] at hy
    have hd := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric g f hf) g f hf (c := 1) zero_lt_one
      (fun z v => by rw [localPullMetric_inner, one_mul]) p y
    simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
    rw [hp] at hd
    exact (hd.trans hy).trans (ENNReal.ofReal_le_ofReal hhalf.le)
  have hshi := shi_curvDerivNorm_parabolicClosedWindow_on_terminal_ball S hS hQ hθ hK
    (half_pos hr) hcarrier hregular p hcompact' hcurv'
  intro m
  have hpball : p ∈ riemannianClosedBallOf
      ((S.parabolicClosedWindow T Q θ hQ hθ.le).base.metric 0) p ((r / 2) / 4) := by
    change riemannianEDistOf _ p p ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hh := hshi.2.2.2 m 0 ⟨by linarith, le_rfl⟩ p hpball
  rw [SolutionOn.parabolicClosedWindow_metric_zero, hterminal, curvDerivNorm_scaleMetric,
    curvDerivNorm_localPullMetric, hp, ← curvDerivNorm_scaleMetric] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow
