import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bFixedScaleFlowLimit

/-!
# A13b consumer: local Ricci flows on the balls of the fixed-scale limit

`FILL910.A13b_exists_local_flows_on_limit_balls` calls `FILL910.A13b_fixed_scale_local_flow_limit` with
all of its inputs and keeps the part a chapter-12/13 consumer reads first: a complete connected pointed
limit `P` of a subsequence of the scaled stages and, for every `k`, a Ricci flow on the ball
`B_P(basepoint, (k + 1)/2)` on the window `[-(τ k / 2), 0]` whose time-0 metric is the limit metric.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- Consumer of A13b: under its inputs, a subsequence of the scaled stages converges to a complete
connected pointed limit `P`, and every ball `B_P(basepoint, (k + 1)/2)` carries a Ricci flow on
`[-(τ k / 2), 0]` with time-0 metric the limit metric. -/
theorem A13b_exists_local_flows_on_limit_balls
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (τ K : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k / lam n)
        (K k * lam n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (lam n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (lam n)))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (lam n) (hlam n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f),
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∀ k : ℕ, ∃ (V : Opens P.M) (G : ℝ → SmoothRiemannianMetric ThreeModel V),
          (V : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) ∧
          G 0 = P.metric.restrictOpen V ∧
          IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := V)
            (RealTimeInterval.closed (-(τ k / 2)) 0 (neg_nonpos.mpr (half_pos (hτ k)).le))) := by
  intro X
  obtain ⟨-, -, -, -, -, f, hf, P, F, -, hPc, hconn, -, V, -, hV, -, -, -, -, Gloc, hG0, hG, -⟩ :=
    A13b_fixed_scale_local_flow_limit H t y lam hlam τ K hτ htraced hr₀ hw hseed
  exact ⟨f, hf, P, F, hPc, hconn, fun k => ⟨V k, Gloc k, hV k, hG0 k, hG k⟩⟩

end FILL910
