import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.OpenExhaustion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureEscape
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.IncompleteLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryTerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ParabolicTerminalBallFlow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MetricPinchingLimit

noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {a r A θ : ℝ} {C : ℝ≥0} (ha : 0 ≤ a) (hr : 0 < r) (hA : 1 ≤ A)
    (hθ : 0 < θ) (htime : 6 * C * (A * θ) ≤ 1) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
    G.flow.base.metric (H.time last) = H.initialMetric last →
    ∀ (x : G.terminalRegularOpen) {q Q : ℝ}, 0 < q → q ≤ Q → ∀ hQ : 1 ≤ Q,
    IsCompact (riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r)) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi →
    (∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r),
      metricScalarAt L.metric y ≤ 2 * (A * Q)) →
    (∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r),
      Nonempty (BackwardPointTrace H first last hle y.val)) →
    H.time first ≤ s - θ / Q →
    ∀ m : ℕ, ∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x a,
      curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤ B m := by
  let K := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
  let B := fun m => (shiLocalUniformBound 3 m (K * (A * θ / 4))
    (((r * Real.sqrt A / 2) / (4 * Real.exp (9 * K * (A * θ)))) * Real.sqrt K /
      (4 * Real.exp (9 * K * (A * θ / 4)))) * K / Real.sqrt (A * θ / 4) ^ m) *
        (A * Real.sqrt A ^ m)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hK : 0 < K := by dsimp only [K]; positivity [hPhi.pos 4, hPhi.pos 0]
  refine ⟨B, ?_, ?_⟩
  · intro m
    exact mul_nonneg (div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
      (by positivity)) (by positivity)
  intro H first last hle s G L hinit x q Q hq hqQ hQ hcompact hderiv hfinal hpinch hpinchFinal
    hscalar htrace hstart m y hy
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAQ : 1 ≤ A * Q := hQ.trans (le_mul_of_one_le_left hQp.le hA)
  have hqAQ : q ≤ A * Q := hqQ.trans (le_mul_of_one_le_left hQp.le hA)
  have hradius (b : ℝ) : b * Real.sqrt A / Real.sqrt (A * Q) = b / Real.sqrt Q := by
    rw [Real.sqrt_mul hAp.le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hAp)]
  have hball (b : ℝ) : riemannianClosedBallOf (scaleMetric Q hQp L.metric) x b =
      riemannianClosedBallOf L.metric x (b / Real.sqrt Q) := by
    conv_lhs => rw [show b = Real.sqrt Q * (b / Real.sqrt Q) by field_simp]
    exact riemannianClosedBallOf_scaleMetric Q hQp L.metric x _
  have houter : (a * Real.sqrt A + r * Real.sqrt A) / Real.sqrt (A * Q) = (a + r) / Real.sqrt Q := by
    rw [← add_mul, hradius]
  have ht : A * θ / (A * Q) = θ / Q := by field_simp
  have hbound := H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace
    first last hle G L hinit x (mul_nonneg ha (Real.sqrt_nonneg _))
    (mul_pos hr (Real.sqrt_pos.mpr hAp)) hq hqAQ hAQ (mul_pos hAp hθ)
    (by rw [houter, ← hball]; exact hcompact) hPhi hderiv (fun y _ => hfinal y.val)
    hpinch hpinchFinal (by simpa only [houter, ← hball] using hscalar)
    (by simpa only [houter, ← hball] using htrace) (by simpa only [ht] using hstart) htime y
      (by rw [hradius, ← hball]; exact hy) m
  have hmetric : scaleMetric (A * Q) (zero_lt_one.trans_le hAQ) L.metric =
      scaleMetric A hAp (scaleMetric Q hQp L.metric) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner]
    ring
  rw [hmetric, curvDerivNorm_scaleMetric] at hbound
  exact (div_le_iff₀ (by positivity : 0 < A * Real.sqrt A ^ m)).mp hbound



private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    {rho : ℝ}
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p B := by
  dsimp only
  intro R hR hRrho p
  obtain ⟨r, A, θ, hr, _hRr, hA, hθ, htime, hbuf⟩ := hbuffer R hR hRrho
  obtain ⟨B, hB, hbound⟩ := exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces
    Phi hPhi hR.le hr hA hθ htime
  refine ⟨B p, hB p, ?_⟩
  filter_upwards [hbuf] with n hn
  intro y hy
  obtain ⟨first, hle, htrace, hstart⟩ := hn.2.2
  exact hbound (H n) first (last n) hle (G n) (L n) (hinit n) (x n)
    (hq n) (hqQ n) (hQ n) hn.1 (fun j _ hj => hderiv n j hj) (hfinal n)
    (fun j _ hj => hpinch n j hj) (hpinchFinal n) hn.2.1 htrace hstart p y hy


theorem exists_terminal_pointed_convergence_of_buffered_backward_traces
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) y a)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  dsimp only
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
  have hcompact : ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R) := by
    intro R hR hRrho
    obtain ⟨r, A, θ, hr, _, _, _, _, hbuf⟩ := hbuffer R hR hRrho
    filter_upwards [hbuf] with n hn
    exact hn.1.of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (X.obj n).metric (X.obj n).basepoint)
        continuous_const) (riemannianClosedBallOf_mono _ _ (by linarith))
  have hjets := exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal hbuffer
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric y a) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvol
  exact exists_pointed_convergence_with_uniform_metric_bounds_on_base_components
    X hrho hcompact hjets hvolX

theorem exists_normalized_terminal_pointed_convergence_of_backward_traces_and_volume_tests
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hvolume : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop,
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ∀ b : ℝ, 0 < b → b < a / Real.sqrt (Q n) → ∀ᶠ t in 𝓝[<] s n,
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stage (last n)).Carrier
              ((G n).flow.base.metric t) (riemannianBallOf ((G n).flow.base.metric t) y.val b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  dsimp only
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
  have hcompact : ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R) := by
    intro R hR hRrho
    obtain ⟨r, A, θ, hr, _, _, _, _, hbuf⟩ := hbuffer R hR hRrho
    filter_upwards [hbuf] with n hn
    exact hn.1.of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (X.obj n).metric (X.obj n).basepoint)
        continuous_const) (riemannianClosedBallOf_mono _ _ (by linarith))
  have hjets := exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal hbuffer
  have hvol := OrientedThreeStage.IncomingSlab.normalized_inner_ball_volume_lower_bound_of_eventually_volume_ball_ge
    (fun n => (H n).stage (last n)) (fun n => (H n).time (last n)) s G L x Q
      (fun n => zero_lt_one.trans_le (hQ n)) rho hcompact hvolume
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric y a) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvol
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    exists_pointed_convergence_with_uniform_metric_bounds_on_base_components X hrho hcompact hjets hvolX
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

theorem exists_normalized_terminal_pointed_convergence_at_scalar_escape_radius
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hinner : ∀ R : ℝ, 0 < R → R < rho → ∃ A : ℝ, ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) R) ∧
      ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) R,
        metricScalarAt (L n).metric y / Q n ≤ A)
    (htrace : ∀ R : ℝ, 0 < R → R < rho → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ n in atTop,
      ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) R,
          Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
        (H n).time first ≤ s n - θ / Q n)
    (z : ∀ n, (G n).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (z n)).toReal)
      atTop (𝓝 rho))
    (hescape : Tendsto (fun n => metricScalarAt (L n).metric (z n) / Q n) atTop atTop)
    (hvolume : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop,
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ∀ b : ℝ, 0 < b → b < a / Real.sqrt (Q n) → ∀ᶠ t in 𝓝[<] s n,
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stage (last n)).Carrier
              ((G n).flow.base.metric t) (riemannianBallOf ((G n).flow.base.metric t) y.val b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        (∀ (k : ℕ → ℕ), StrictMono k →
          (∀ n, riemannianEDistOf (X.obj (f (k n))).metric (X.obj (f (k n))).basepoint
            (z (f (k n))) ≠ ⊤) ∧
          Tendsto (fun n => (riemannianEDistOf (X.obj (f (k n))).metric
            (X.obj (f (k n))).basepoint (z (f (k n)))).toReal) atTop (𝓝 rho) ∧
          Tendsto (fun n => metricScalarAt (L (f (k n))).metric (z (f (k n))) / Q (f (k n)))
            atTop atTop) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n := by
    intro R hR hRrho
    let r := (rho - R) / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hS : R + r < rho := by dsimp [r]; linarith
    have hSR : 0 < R + r := add_pos hR hr
    obtain ⟨B, hB⟩ := hinner (R + r) hSR hS
    obtain ⟨θ0, hθ0, htr⟩ := htrace (R + r) hSR hS
    let A := max 1 B
    have hA : 1 ≤ A := le_max_left _ _
    have hAp : 0 < A := zero_lt_one.trans_le hA
    let θ := min θ0 (1 / (6 * (C + 1) * A))
    have hθ : 0 < θ := by dsimp [θ]; positivity
    have hθ0' : θ ≤ θ0 := min_le_left _ _
    have hθbudget : θ * (6 * (C + 1) * A) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * C * (A * θ) ≤ 1 := by
      nlinarith [mul_nonneg hAp.le hθ.le]
    refine ⟨r, A, θ, hr, hS, hA, hθ, hbudget, ?_⟩
    filter_upwards [hB, htr] with n hn ht
    obtain ⟨first, hle, htrace, hstart⟩ := ht
    refine ⟨hn.1, ?_, first, hle, htrace, ?_⟩
    · intro y hy
      have hscalar := (div_le_iff₀ (zero_lt_one.trans_le (hQ n))).mp (hn.2 y hy)
      have hBA : B ≤ A := le_max_right _ _
      have hQp : 0 < Q n := zero_lt_one.trans_le (hQ n)
      nlinarith
    · have hdiv := div_le_div_of_nonneg_right hθ0' (zero_lt_one.trans_le (hQ n)).le
      linarith
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    exists_normalized_terminal_pointed_convergence_of_backward_traces_and_volume_tests
      Phi hPhi H last s G L hinit x q Q hscale hq hqQ hQ hderiv hfinal hpinch hpinchFinal
      hrho hbuffer hvolume
  refine ⟨f, hf, r, hr, hrlim, P, F, M, ?_, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩
  intro k hk
  exact ⟨fun n => hfinite (f (k n)), hdist.comp (hf.comp hk).tendsto_atTop,
    hescape.comp (hf.comp hk).tendsto_atTop⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem RetainedCoreHistory.normalized_inner_ball_volume_lower_bound_of_tested_backward_traces
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ}
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (A.toHistory.stageAt time).Carrier) (b : ℝ), 0 < b → b ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) y b)) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) y a) := by
  intro r R hr hrR hRrho J hJ
  obtain ⟨b, A, θ0, hb, _, hA, hθ0, hbudget, hbuf⟩ := hbuffer r hr (hrR.trans hRrho)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hgap : 0 < R - r := sub_pos.mpr hrR
  let a0 := min (b / 2) (min (R - r) (min σ (min 1 (1 / (J + 1)))))
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have ha0b : a0 ≤ b / 2 := min_le_left _ _
  have ha0R : a0 ≤ R - r := (min_le_right _ _).trans (min_le_left _ _)
  have ha0σ : a0 ≤ σ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have ha01 : a0 ≤ 1 := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have ha0J : a0 ≤ 1 / (J + 1) := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let θ := min (A * θ0) ((a0 * Real.sqrt A) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθA : θ ≤ A * θ0 := min_le_left _ _
  obtain ⟨α, hα, _, hαθ, hball⟩ :=
    ObservedHistory.exists_uniform_parabolically_controlled_incoming_terminal_ball_radius hPhi hθ
  have hαa0 : α ≤ a0 * Real.sqrt A := by
    have hh : α ^ 2 ≤ (a0 * Real.sqrt A) ^ 2 := hαθ.trans (min_le_right _ _)
    nlinarith [mul_pos ha0 hsqrtA]
  let a := α / Real.sqrt A
  have ha : 0 < a := div_pos hα hsqrtA
  have haa0 : a ≤ a0 := (div_le_iff₀ hsqrtA).mpr hαa0
  have hab : a < b := (haa0.trans ha0b).trans_lt (by linarith)
  have haJ : a * (J + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (haa0.trans ha0J)
  have ha1 : a ≤ 1 := haa0.trans ha01
  have hasmall : a ^ 4 * J ^ 2 ≤ 1 := by
    have h1 : a ^ 2 ≤ a := by nlinarith
    have h2 : a ^ 2 * J ≤ 1 :=
      (mul_le_mul_of_nonneg_right h1 hJ).trans (by linarith)
    have hh := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hJ) h2 2
    nlinarith only [hh]
  refine ⟨a, κ, ha, hκ, by linarith [haa0.trans ha0R], hasmall, ?_⟩
  filter_upwards [hbuf] with n hn y hy
  obtain ⟨first, htrace, hstart⟩ := hn.2.2
  have hQp : 0 < Q n := zero_lt_one.trans_le (hQ n)
  have hAQ : 1 ≤ A * Q n := (hQ n).trans (le_mul_of_one_le_left hQp.le hA)
  have hsqrtQ : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQp
  have hsub : riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)) ⊆
      riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) (x n) (r + b) := by
    have heq : riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)) =
        riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) y b := by
      rw [← riemannianClosedBallOf_scaleMetric (Q n) hQp]
      congr 1
      field_simp
    rw [heq]
    exact riemannianClosedBallOf_subset_of_add_radius_le _ hr.le hb.le le_rfl hy
  have hcompact : IsCompact (riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n))) :=
    hn.1.of_isClosed_subset (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (L n).metric y)
      continuous_const) hsub
  have hradius : α / Real.sqrt (A * Q n) = a / Real.sqrt (Q n) := by
    rw [Real.sqrt_mul hAp.le]
    dsimp [a]
    field_simp
  have hstart' : (H n).time first ≤ s n - θ / (A * Q n) := by
    have hh : θ / (A * Q n) ≤ θ0 / Q n := by
      have hh := div_le_div_of_nonneg_right hθA (mul_pos hAp hQp).le
      have heq : A * θ0 / (A * Q n) = θ0 / Q n := by field_simp
      rwa [heq] at hh
    linarith
  have hbudget' : 6 * C * θ ≤ 1 := (mul_le_mul_of_nonneg_left hθA (by positivity)).trans hbudget
  obtain ⟨p, S, _, _, _, _, hslabs, hlast, B, _, hBRadius, hB, _, himage, _, _⟩ :=
    hball (H n).toHistory first (Fin.last (H n).eventCount) (Fin.le_last first) (G n) (L n) y
      hAQ (hinit n) (div_pos hb hsqrtQ) hcompact (hq n)
      ((hqQ n).trans (le_mul_of_one_le_left hQp.le hA))
      (fun j _ _ => hderiv n j) (fun z _ => hfinal n z.val)
      (fun j _ _ => hpinch n j) (hpinchFinal n)
      (fun z hz => hn.2.1 z (hsub hz)) (fun z hz => htrace z (hsub hz)) hstart' hbudget'
      (by rw [hradius]; exact (div_lt_div_iff_of_pos_right hsqrtQ).mpr hab)
  have hBr : B.radius = a / Real.sqrt (Q n) := hBRadius.trans hradius
  have hBσ : B.radius ≤ σ := by
    rw [hBr]
    have hsq : 1 ≤ Real.sqrt (Q n) := Real.one_le_sqrt.mpr (hQ n)
    exact (div_le_self ha.le hsq).trans (haa0.trans ha0σ)
  exact (H n).normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball
    (G n) (L n) (hinit n) (hs n) first
    (riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n))) hstart'
    (sub_le_self _ (div_nonneg hθ.le (mul_pos hAp hQp).le)) S
    (fun j hf => hslabs j hf (Fin.le_last _)) hlast (x n) y hQp hr.le
    (by linarith [hab.le]) B hB hBr hn.1 hy (by simpa only [hBRadius] using himage) hBσ (htested n)

theorem RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_tested_backward_traces
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) = (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (A.toHistory.stageAt time).Carrier) (b : ℝ), 0 < b → b ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) y b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hbuffer' : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ Fin.last (H n).eventCount),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n := by
    intro R hR hRrho
    obtain ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, hb⟩ := hbuffer R hR hRrho
    refine ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, ?_⟩
    filter_upwards [hb] with n hn
    obtain ⟨first, htrace, hstart⟩ := hn.2.2
    exact ⟨hn.1, hn.2.1, first, Fin.le_last first, htrace, hstart⟩
  have hvol := RetainedCoreHistory.normalized_inner_ball_volume_lower_bound_of_tested_backward_traces
    Phi hPhi H s G L hinit hs x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal
      hbuffer hκ hσ htested
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces
      Phi hPhi (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) s G L hinit
      x q Q hq hqQ hQ (fun n j _ => hderiv n j) hfinal (fun n j _ => hpinch n j)
      hpinchFinal hrho hbuffer' hvol
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem exists_eventually_backward_window_on_bounded_scalar_ball_of_growing_preparation :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (R Amax : ℝ), 0 < R → 1 ≤ Amax →
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      (∀ᶠ i in atTop, ∀ y, y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
          (R / Real.sqrt ((A i).flow.scalar (time i) (x i))) →
        (A i).flow.scalar (time i) y ≤ 2 * Amax * (A i).flow.scalar (time i) (x i)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ : ℝ, 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i) ∧
          ∀ y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
            (R / Real.sqrt ((A i).flow.scalar (time i) (x i))),
            Nonempty (BackwardPointTrace (H i) first (last i) hle y) := by
  obtain ⟨C, hC, hbase⟩ := exists_eventually_backward_window_on_bounded_scalar_ball_at_scalar_derivative_contact
  refine ⟨C, hC, ?_⟩
  intro R Amax hR hAmax eps heps hepssmall
  let rcap := StandardCap.transitionEnd + eps⁻¹ + 2 +
    2 * (2 * StandardCap.transitionEnd + (R + 1) * Real.sqrt (8 * Amax))
  let D := 64 * (rcap + eps⁻¹) + 1
  have hrcap : StandardCap.transitionEnd + eps⁻¹ + 1 < rcap := by
    dsimp [rcap]
    nlinarith [StandardCap.transitionEnd_pos, Real.sqrt_nonneg (8 * Amax), mul_nonneg (by linarith : 0 ≤ R + 1) (Real.sqrt_nonneg (8 * Amax))]
  have hfit : 64 * (rcap + eps⁻¹) < D := by dsimp [D]; linarith
  have hcapture : 2 * StandardCap.transitionEnd + (R + 1) * Real.sqrt (8 * Amax) < rcap / 2 := by
    dsimp [rcap]
    nlinarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
  obtain ⟨δ₀, hδ₀, htrace⟩ := hbase R Amax hR hAmax 4 le_rfl D rcap eps
    heps hepssmall hrcap hfit hcapture
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hupper hfail
  have hevent := (hmargin.eventually_ge_atTop (D + 1)).and ((hδ δ₀ hδ₀).and hupper)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  let f : ℕ → ℕ := fun i => i + M
  have hf : Tendsto f atTop atTop := tendsto_add_atTop_nat M
  have hgood (i : ℕ) := hM (f i) (by dsimp [f]; omega)
  obtain ⟨θ, hθ, hbudget, htraces⟩ := htrace
    (fun i => H (f i)) (fun i => last (f i)) (fun i => time (f i))
    (fun i => A (f i)) (fun i => hinit (f i)) (fun i => parameters (f i))
    (fun i => records (f i)) (fun i => hcanonical (f i)) (fun i => (hgood i).1)
    (fun i => hm (f i)) (herrorlim.comp hf) (fun i => hcap (f i))
    q₀ a₀ a hq₀ ha₀ ha (fun i => htime (f i)) (fun i => hfixed (f i))
    (fun i => hlower (f i)) (fun i => (hgood i).2.1) (fun i => hderiv (f i))
    (fun i => hfinal (f i)) (fun i => x (f i)) (hhigh.comp hf)
    (fun i => hgradient (f i)) (fun i => (hgood i).2.2) (fun i => hfail (f i))
  refine ⟨θ, hθ, hbudget, ?_⟩
  have hmapped : ∀ᶠ i in Filter.map f atTop,
      ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
        (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i) ∧
        ∀ y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
          (R / Real.sqrt ((A i).flow.scalar (time i) (x i))),
          Nonempty (BackwardPointTrace (H i) first (last i) hle y) := htraces
  simpa only [f, map_add_atTop_eq_nat] using hmapped

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_buffered_backward_traces_of_scalar_derivative_contacts :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
      let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i));
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, (G i).terminalRegularOpen,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      ∀ hQ : ∀ i, 0 < (A i).flow.scalar (time i) (x i).val,
      ∀ rho : ℝ, 0 < rho →
      (∀ R : ℝ, 0 < R → R < rho → ∃ B : ℝ,
        ∀ᶠ i in atTop, ∀ y : (G i).terminalRegularOpen,
          y ∈ riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) R →
          metricScalarAt (L i).metric y ≤ B * (A i).flow.scalar (time i) (x i).val) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i).val, v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i).val * Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i).val v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i).val v)|) ∨
        C * (A i).flow.scalar (time i) (x i).val ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i).val) (Iic (time i)) (time i)|) →
      ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
        0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧
        ∀ᶠ i in atTop,
          IsCompact (riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r)) ∧
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r),
            metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
          ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
            (∀ y ∈ riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r),
              Nonempty (BackwardPointTrace (H i) first (last i) hle y.val)) ∧
            (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val := by
  obtain ⟨C, hC, hbase⟩ := exists_eventually_backward_window_on_bounded_scalar_ball_of_growing_preparation
  refine ⟨C, hC, ?_⟩
  intro eps heps hepssmall H last time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ rho hrho hupper hfail R hR hRrho
  let r := (rho - R) / 2
  have hr : 0 < r := half_pos (sub_pos.mpr hRrho)
  have hRr : R + r < rho := by dsimp [r]; linarith
  obtain ⟨B, hB⟩ := hupper (R + r) (by positivity) hRr
  let Amax := max 1 B
  have hAmax : 1 ≤ Amax := le_max_left _ _
  have hscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (time i) y.val := by
    change metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) y = _
    rw [metricScalarAt_restrictOpen]
    rfl
  have hbound : ∀ᶠ i in atTop, ∀ y,
      y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i).val
        ((R + r) / Real.sqrt ((A i).flow.scalar (time i) (x i).val)) →
      (A i).flow.scalar (time i) y ≤ 2 * Amax * (A i).flow.scalar (time i) (x i).val := by
    filter_upwards [hB] with i hi y hy
    let y' : (G i).terminalRegularOpen := ⟨y, by
      change y ∈ (G i).terminalRegularRegion
      rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
      trivial⟩
    have hy' := ((A i).mem_scaled_endpoint_closedBall_iff _ (hQ i) (x i) y' (R + r)).mpr hy
    have hb := hi y' hy'
    rw [hscalar] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      have hbA : B ≤ Amax := le_max_right _ _
      linarith) (hQ i).le)
  obtain ⟨θ, hθ, hbudget, htraces⟩ := hbase (R + r) Amax (by positivity) hAmax eps heps hepssmall
    H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal (fun i => (x i).val)
    hhigh hgradient hbound hfail
  refine ⟨r, Amax, θ, hr, hRr, hAmax, hθ, hbudget, ?_⟩
  filter_upwards [htraces, hB] with i hi hbi
  have hcompact : CompactSpace (G i).terminalRegularOpen := by
    apply isCompact_iff_compactSpace.mp
    change IsCompact (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    exact isCompact_univ
  let _ := hcompact
  refine ⟨(Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact, ?_, ?_⟩
  · intro y hy
    have hb := hbi y hy
    have hcoef : B ≤ 2 * Amax := by have := le_max_right (1 : ℝ) B; dsimp [Amax] at *; linarith
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef (hQ i).le])
  · obtain ⟨first, hle, hstart, ht⟩ := hi
    refine ⟨first, hle, ?_, hstart⟩
    intro y hy
    exact ht y.val (((A i).mem_scaled_endpoint_closedBall_iff _ (hQ i) (x i) y (R + r)).mp hy)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_scalar_escape_radius_with_buffered_backward_traces_of_contacts :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
      let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i));
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, (G i).terminalRegularOpen,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      ∀ hQ : ∀ i, 0 < (A i).flow.scalar (time i) (x i).val,
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i),
        q₀ < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
          |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
            C * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
              Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
      (∀ i, q₀ ≤ (A i).flow.scalar (time i) (x i).val) →
      (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
        ∀ y : (G i).terminalRegularOpen,
          riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric)
            (x i) y < ENNReal.ofReal R →
          metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i).val, v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i).val * Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i).val v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i).val v)|) ∨
        C * (A i).flow.scalar (time i) (x i).val ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i).val) (Iic (time i)) (time i)|) →
      ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
        (∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
          0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧
          ∀ᶠ i in atTop,
            IsCompact (riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r)) ∧
            (∀ y ∈ riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r),
              metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
            ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
              (∀ y ∈ riemannianClosedBallOf
                (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQ i) (L i).metric) (x i) (R + r),
                Nonempty (BackwardPointTrace (H i) first (last i) hle y.val)) ∧
              (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val) ∧
        ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
          (∀ i, riemannianEDistOf
            (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (hQ (ind i)) (L (ind i)).metric)
              (x (ind i)) (z i) ≠ ⊤) ∧
          Tendsto (fun i => (riemannianEDistOf
            (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (hQ (ind i)) (L (ind i)).metric)
              (x (ind i)) (z i)).toReal) atTop (𝓝 rho) ∧
          Tendsto (fun i => metricScalarAt (L (ind i)).metric (z i) /
            (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) atTop atTop := by
  obtain ⟨C, hC, hbuffer⟩ := exists_buffered_backward_traces_of_scalar_derivative_contacts
  refine ⟨C, hC, ?_⟩
  intro eps heps hepssmall H last time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ hinterior hqQ hfailure hfail
  have hscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (time i) y.val := by
    change metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) y = _
    rw [metricScalarAt_restrictOpen]
    rfl
  obtain ⟨rho, ind, hrho, hind, hinner, z, hfinite, hdist, hscalarEscape⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds
      (fun i => (H i).stage (last i)) (fun i => (H i).time (last i)) time G L x
      (fun i => (A i).flow.scalar (time i) (x i).val) hQ C (fun _ => q₀) hqQ
      hinterior (fun _ => C) hfinal (fun i => (hscalar i (x i)).le) hfailure
  refine ⟨rho, hrho, ind, hind, ?_, z, hfinite, hdist, hscalarEscape⟩
  apply hbuffer eps heps hepssmall H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ rho hrho ?_ hfail
  intro R hR hRrho
  obtain ⟨B, hB⟩ := hinner R hR hRrho
  refine ⟨B, ?_⟩
  filter_upwards [hB] with i hi y hy
  exact (div_le_iff₀ (hQ i)).mp (hi.2 y hy)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact


private theorem endpoint_scalar_eq {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

theorem RetainedCoreHistory.exists_normalized_pointed_convergence_at_scalar_escape_of_scalar_derivative_contact :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → RetainedCoreHistory.{u})
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
          ((H i).time (Fin.last (H i).eventCount)) (time i)),
      let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
      let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage ((Fin.last (H i).eventCount)));
      ∀ (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) = (H i).initialMetric (Fin.last (H i).eventCount)),
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i).toHistory j (parameters i)),
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ (b : ((H i).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, (G i).terminalRegularOpen,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      ∀ hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val,
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i),
        q₀ < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
          |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
            C * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
              Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
      (∀ i, q₀ ≤ (A i).flow.scalar (time i) (x i).val) →
      (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
        ∀ y : (G i).terminalRegularOpen,
          riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
            (x i) y < ENNReal.ofReal R →
          metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i).val, v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i).val * Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i).val v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i).val v)|) ∨
        C * (A i).flow.scalar (time i) (x i).val ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i).val) (Iic (time i)) (time i)|) →
      ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
      (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
      (∀ i, Perelman.PhiAlmostNonnegative (G i).flow (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
      (∀ i, (H i).horizon < time i) →
      ∀ κ σ : ℝ, 0 < κ → 0 < σ →
      (∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
        let B := (H i).extendHorizon t ht.le
          ((G i).closedPrefix t ((H i).time_le_horizon.trans_lt ht) hts) (hinit i);
        let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩;
        ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ →
          B.toHistory.isParabolicallyRmControlledBall tm y b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b)) →
      ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
        ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := (G (ind i)).terminalRegularOpen
                basepoint := x (ind i)
                metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                  (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
        ∃ (f : ℕ → ℕ), StrictMono f ∧
          ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
          ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
            (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
            let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
            let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
            let F' := F.liftTargetOpen U hp;
            ∃ M : MetricConvergenceData F',
              metricScalarAt P.metric P.basepoint = 1 ∧
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
              (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
              (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
              (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
              (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n, ∀ v : TangentSpace ThreeModel y,
                (1 - eps) * P.metric.inner y v v ≤
                    (X.obj (f n)).metric.inner (F'.map n y)
                      (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                      (1 + eps) * P.metric.inner y v v) ∧
              (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
              Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n))).toReal)
                atTop (𝓝 rho) ∧
              Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
                (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val) atTop atTop := by
  obtain ⟨C, hC, hbase⟩ := ObservedHistory.exists_scalar_escape_radius_with_buffered_backward_traces_of_contacts
  refine ⟨C, hC, ?_⟩
  intro eps heps hepssmall H time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ hinterior hqQ hfailure hfail
    Phi hPhi hpinch hpinchFinal hs κ σ hκ hσ htested
  obtain ⟨rho, hrho, ind, hind, hbuf, z, hfinite, hdist, hscalarEscape⟩ :=
    hbase eps heps hepssmall (fun i => (H i).toHistory) (fun i => Fin.last (H i).eventCount)
      time A hinit parameters records hcanonical hmargin hm herrorlim hcap q₀ a₀ a hq₀ ha₀ ha htime
      hfixed hlower hδ hderiv hfinal x hhigh hgradient (fun i => zero_lt_one.trans_le (hQ i))
      hinterior hqQ hfailure hfail
  refine ⟨rho, hrho, ind, hind, z, ?_⟩
  dsimp only
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact, hcapture, hmetric⟩ :=
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_tested_backward_traces
      Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
      (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
      (fun i => hs (ind i)) (fun i => x (ind i)) (fun _ => q₀)
      (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => (endpoint_scalar_eq (A (ind i)) (x (ind i))).symm) (fun _ => hq₀) (fun i => hqQ (ind i)) (fun i => hQ (ind i))
      (fun i j => hderiv (ind i) j (Fin.le_last _)) (fun i => hfinal (ind i))
      (fun i => hpinch (ind i)) (fun i => hpinchFinal (ind i)) hrho (by
        intro R hR hRrho
        obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbuf R hR hRrho
        refine ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, ?_⟩
        filter_upwards [hind.tendsto_atTop.eventually hb] with i hi
        obtain ⟨first, hle, htrace, hstart⟩ := hi.2.2
        exact ⟨hi.1, hi.2.1, first, htrace, hstart⟩) hκ hσ (fun i => htested (ind i))
  refine ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact, hcapture,
    hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop, hscalarEscape.comp hf.tendsto_atTop⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_eventually_incomingFootprintLift_of_pointed_convergence
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (g : ∀ i, SmoothRiemannianMetric ThreeModel (G i).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i => { M := (G i).terminalRegularOpen, basepoint := x i, metric := g i } } P phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (g (phi i)).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
        (∀ y ∈ riemannianClosedBallOf (g (phi i)) (x (phi i)) R,
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i))
    (V : Opens P.M) (hV : IsCompact (closure (V : Set P.M))) :
    ∃ R θ : ℝ, 0 < R ∧ R < rho ∧ 0 < θ ∧ (∀ i, 0 < θ / Q i) ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
      ∃ Ψ : V → (H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
        (G (phi i)) (riemannianClosedBallOf (g (phi i)) (x (phi i)) R),
        (∀ y ∈ riemannianClosedBallOf (g (phi i)) (x (phi i)) R,
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i) ∧
        IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ ∧ Function.Injective Ψ ∧
        (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
          (G (phi i)) (riemannianClosedBallOf (g (phi i)) (x (phi i)) R) ∘ Ψ =
            (fun z : V => F.map i z.val) := by
  obtain ⟨R, hR, hRrho, hmaps⟩ :=
    F.exists_eventually_image_compact_subset_inner_ball hrho hradial hcompact hupper hV
  obtain ⟨θ, hθ, hbuffer⟩ := hbuffer R hR hRrho
  refine ⟨R, θ, hR, hRrho, hθ, fun i => div_pos hθ (hQ i), ?_⟩
  filter_upwards [hmaps, hbuffer] with i hi hbi
  obtain ⟨first, hle, htrace, hstart⟩ := hbi
  let Fv : V → (G (phi i)).terminalRegularOpen := fun z => F.map i z.val
  have hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Fv := by
    apply DifferentialGeometry.isLocalDiffeomorph_restrict_open V
    intro z
    exact (F.partialDiffeomorph i).isLocalDiffeomorphAt ThreeModel ThreeModel ∞
      (hi.1 (subset_closure z.property))
  have hFvinj : Function.Injective Fv := by
    intro z w hzw
    apply Subtype.ext
    exact (F.partialDiffeomorph i).toPartialEquiv.injOn
      (hi.1 (subset_closure z.property)) (hi.1 (subset_closure w.property)) hzw
  let K := riemannianClosedBallOf (g (phi i)) (x (phi i)) R
  have himage (z : V) : Fv z ∈ interior K :=
    Geometry.Metric.riemannianBallOf_subset_interior_riemannianClosedBallOf
      (g (phi i)) (x (phi i)) R (hi.2 ⟨z.val, subset_closure z.property, rfl⟩)
  exact ⟨first, hle,
    (H (phi i)).backwardSurvivorIncomingFootprintLift first (last (phi i)) hle
      (G (phi i)) K htrace Fv himage, htrace, hstart,
    (H (phi i)).backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph first (last (phi i)) hle
      (G (phi i)) K htrace Fv himage hFv,
    (H (phi i)).backwardSurvivorIncomingFootprintLift_injective first (last (phi i)) hle
      (G (phi i)) K htrace Fv himage hFvinj,
    rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_eventually_historical_solution_of_pointed_convergence
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i => { M := (G i).terminalRegularOpen, basepoint := x i, metric := scaleMetric (Q i) (hQ i) (L i).metric } } P phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
        (∀ y ∈ riemannianClosedBallOf (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R,
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i))
    (V : Opens P.M) (hV : IsCompact (closure (V : Set P.M))) :
    ∃ R θ : ℝ, ∃ hθ : 0 < θ, 0 < R ∧ R < rho ∧ (∀ i, 0 < θ / Q i) ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
      ∃ (Ψ : V → (H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
        (G (phi i)) (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => F.map i z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R)))
        (S : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))),
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R,
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i) ∧
        Function.Injective Ψ ∧
        (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
          (G (phi i)) (riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R) ∘ Ψ =
              (fun z : V => F.map i z.val) ∧
        IsSolutionOn S ∧
        S.base.metric 0 = localPullMetric
          (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric)
          (fun z : V => F.map i z.val) hFv ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric (Q (phi i)) (hQ (phi i)) (gflow (s (phi i) + t / Q (phi i)))) Ψ hΨ) ∧
        (∀ (j : Fin (H (phi i)).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last (phi i)),
          ∀ t ∈ Icc ((H (phi i)).time j.castSucc) ((H (phi i)).time j.succ),
            gflow t = (((H (phi i)).backwardSurvivorSlabMetric first (last (phi i)) hle j hf hl t).restrictOpen ((H (phi i)).backwardSurvivorIncomingDomain first (last (phi i)) hle
                (G (phi i)))).restrictOpen
                  ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                    (G (phi i)) (riemannianClosedBallOf
                      (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R))) ∧
        (∀ t ∈ Icc ((H (phi i)).time (last (phi i))) (s (phi i)),
          gflow t = ((H (phi i)).backwardSurvivorIncomingMetric first (last (phi i)) hle
            (G (phi i)) (L (phi i)) t).restrictOpen
              ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                (G (phi i)) (riemannianClosedBallOf
                  (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R))) ∧
        gflow (s (phi i)) = localPullMetric (L (phi i)).metric
          ((H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R))
          ((H (phi i)).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R)) := by
  obtain ⟨R, θ, hR, hRrho, hθ, hdepth, hlifts⟩ :=
    exists_eventually_incomingFootprintLift_of_pointed_convergence H last G x
      (fun i => scaleMetric (Q i) (hQ i) (L i).metric) Q hQ F hrho hradial hcompact hupper hbuffer V hV
  refine ⟨R, θ, hθ, hR, hRrho, hdepth, ?_⟩
  filter_upwards [hlifts] with i hi
  obtain ⟨first, hle, Ψ, htrace, hstart, hΨ, hinj, hmap⟩ := hi
  let K := riemannianClosedBallOf
    (scaleMetric (Q (phi i)) (hQ (phi i)) (L (phi i)).metric) (x (phi i)) R
  let Fv : V → (G (phi i)).terminalRegularOpen := fun z => F.map i z.val
  have hmapF : (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
      (G (phi i)) K ∘ Ψ = Fv := hmap
  have hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Fv := by
    rw [← hmapF]
    exact DifferentialGeometry.isLocalDiffeomorph_comp
      ((H (phi i)).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi i)) hle
        (G (phi i)) K) hΨ
  have himage (z : V) : Fv z ∈ interior K := by
    have hz := (Ψ z).property
    change (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
      (G (phi i)) K (Ψ z) ∈ interior K at hz
    exact (congrFun hmapF z) ▸ hz
  obtain ⟨Ψ', hΨ', gflow, S, _, hmap', hS, hzero, hmetric, hslabs, hlast, hterminal⟩ :=
    (H (phi i)).exists_historical_localPullback_solution_from_incoming_slab first (last (phi i)) hle
      (G (phi i)) (L (phi i)) (hinit (phi i)) K htrace Fv hFv himage
      (hQ (phi i)) hθ.le hstart
  have heq : Ψ' = Ψ := by
    funext z
    apply (H (phi i)).backwardSurvivorIncomingFootprintMap_injective first (last (phi i)) hle
      (G (phi i)) K
    exact (congrFun hmap' z).trans (congrFun hmap z).symm
  have hmetric' (t : ℝ) : S.base.metric t = localPullMetric
      (scaleMetric (Q (phi i)) (hQ (phi i)) (gflow (s (phi i) + t / Q (phi i)))) Ψ hΨ := by
    simpa only [heq] using hmetric t
  exact ⟨first, hle, Ψ, hΨ, hFv, gflow, S, htrace, hstart, hinj, hmap, hS, hzero, hmetric', hslabs, hlast, hterminal⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem centered_ball_in_scaled_buffer (g : SmoothRiemannianMetric I M)
    {Q R r : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hr : 0 < r) {x z : M}
    (hK : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ g) x (R + r)))
    (hz : riemannianEDistOf (scaleMetric Q hQ g) x z < ENNReal.ofReal R) :
    IsCompact (riemannianClosedBallOf g z (r / Real.sqrt Q)) ∧
      riemannianBallOf g z (r / Real.sqrt Q) ⊆
        interior (riemannianClosedBallOf (scaleMetric Q hQ g) x (R + r)) := by
  have heq : riemannianClosedBallOf (scaleMetric Q hQ g) z r =
      riemannianClosedBallOf g z (r / Real.sqrt Q) := by
    conv_lhs => rw [show r = Real.sqrt Q * (r / Real.sqrt Q) by field_simp]
    exact riemannianClosedBallOf_scaleMetric Q hQ g z _
  have hsub : riemannianClosedBallOf g z (r / Real.sqrt Q) ⊆
      riemannianBallOf (scaleMetric Q hQ g) x (R + r) := by
    intro y hy
    have hy' : riemannianEDistOf (scaleMetric Q hQ g) z y ≤ ENNReal.ofReal r := by
      change y ∈ riemannianClosedBallOf (scaleMetric Q hQ g) z r
      rwa [heq]
    change riemannianEDistOf (scaleMetric Q hQ g) x y < _
    calc
      _ ≤ riemannianEDistOf (scaleMetric Q hQ g) x z +
          riemannianEDistOf (scaleMetric Q hQ g) z y := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal R + ENNReal.ofReal r :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy') hz hy'
      _ = ENNReal.ofReal (R + r) := (ENNReal.ofReal_add hR.le hr.le).symm
  refine ⟨hK.of_isClosed_subset (isClosed_riemannianClosedBallOf g z _) ?_, ?_⟩
  · intro y hy
    exact (show riemannianEDistOf (scaleMetric Q hQ g) x y < ENNReal.ofReal (R + r) from hsub hy).le
  · intro y hy
    exact riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _ (hsub (show riemannianEDistOf g z y ≤ ENNReal.ofReal (r / Real.sqrt Q) from le_of_lt hy))

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (q Q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hQ : ∀ i, 1 ≤ Q i)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i => { M := (G i).terminalRegularOpen, basepoint := x i, metric := scaleMetric (Q i) (zero_lt_one.trans_le (hQ i)) (L i).metric } } P phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v)
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r), metricScalarAt (L (phi i)).metric y ≤ 2 * (A * Q (phi i))) ∧
        ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
            (x (phi i)) (R + r),
            Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
          (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i))
    (V : Opens P.M) (hV : IsCompact (closure (V : Set P.M))) :
    ∃ R r A θ : ℝ, ∃ hθ : 0 < θ, ∃ B : ℕ → ℝ,
      0 < R ∧ 0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 6 * C * (A * θ) ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
      ∃ (Ψ : V → (H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
        (G (phi i)) (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => F.map i z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r))))
        (S : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))),
        (V : Set P.M) ⊆ F.source i ∧
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r), metricScalarAt (L (phi i)).metric y ≤ 2 * (A * Q (phi i))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r),
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i) ∧
        Function.Injective Ψ ∧
        (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
          (G (phi i)) (riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)) ∘ Ψ =
              (fun z : V => F.map i z.val) ∧
        IsSolutionOn S ∧
        S.base.metric 0 = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (fun z : V => F.map i z.val) hFv ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (gflow (s (phi i) + t / Q (phi i)))) Ψ hΨ) ∧
        (∀ (j : Fin (H (phi i)).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last (phi i)),
          ∀ t ∈ Icc ((H (phi i)).time j.castSucc) ((H (phi i)).time j.succ),
            gflow t = (((H (phi i)).backwardSurvivorSlabMetric first (last (phi i)) hle j hf hl t).restrictOpen ((H (phi i)).backwardSurvivorIncomingDomain first (last (phi i)) hle
                (G (phi i)))).restrictOpen
                  ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                    (G (phi i)) (riemannianClosedBallOf
                      (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))) ∧
        (∀ t ∈ Icc ((H (phi i)).time (last (phi i))) (s (phi i)),
          gflow t = ((H (phi i)).backwardSurvivorIncomingMetric first (last (phi i)) hle
            (G (phi i)) (L (phi i)) t).restrictOpen
              ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                (G (phi i)) (riemannianClosedBallOf
                  (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))) ∧
        gflow (s (phi i)) = localPullMetric (L (phi i)).metric
          ((H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))
          ((H (phi i)).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r))) ∧
        ∀ m : ℕ, ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z : V,
          curvDerivNorm m (S.base.metric t) z ≤ B m := by
  obtain ⟨R, hR, hRrho, hmaps⟩ :=
    F.exists_eventually_image_compact_subset_inner_ball hrho hradial hcompact hupper hV
  obtain ⟨r, A, θ, hr, hRr, hA, hθ, htime, hbuffer⟩ := hbuffer R hR hRrho
  let b := 4 * Real.sqrt 3 * A * (1 + Phi 4 + Phi 0)
  let B : ℕ → ℝ := fun m => shiLocalUniformBound 3 m (b * (θ / 4))
    (((r / 2) / (4 * Real.exp (9 * b * θ))) * Real.sqrt b /
      (4 * Real.exp (9 * b * (θ / 4)))) * b / Real.sqrt (θ / 4) ^ m
  have hb : 0 < b := by dsimp only [b]; positivity [hPhi.pos 4, hPhi.pos 0]
  refine ⟨R, r, A, θ, hθ, B, hR, hr, hRr, hA, htime, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hb.le) (by positivity)
  filter_upwards [hmaps, hbuffer] with i hi hbi
  obtain ⟨hK, hscalar, first, hle, htrace, hstart⟩ := hbi
  let K := riemannianClosedBallOf
    (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
    (x (phi i)) (R + r)
  let Fv : V → (G (phi i)).terminalRegularOpen := fun z => F.map i z.val
  have hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Fv := by
    apply DifferentialGeometry.isLocalDiffeomorph_restrict_open V
    intro z
    exact (F.partialDiffeomorph i).isLocalDiffeomorphAt ThreeModel ThreeModel ∞
      (hi.1 (subset_closure z.property))
  have hinjF : Function.Injective Fv := by
    intro z w heq
    apply Subtype.ext
    exact (F.partialDiffeomorph i).toPartialEquiv.injOn
      (hi.1 (subset_closure z.property)) (hi.1 (subset_closure w.property)) heq
  have hnear (z : V) : riemannianEDistOf
      (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
      (x (phi i)) (Fv z) < ENNReal.ofReal R := hi.2 ⟨z.val, subset_closure z.property, rfl⟩
  have himage (z : V) : Fv z ∈ interior K := by
    apply Geometry.Metric.riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _
    exact (hnear z).trans_le (ENNReal.ofReal_le_ofReal (by linarith : R ≤ R + r))
  obtain ⟨Ψ, hΨ, gflow, S, hPsi, hmap, hS, hzero, hmetric, hslabs, hlast, hterminal⟩ :=
    (H (phi i)).exists_historical_localPullback_solution_from_incoming_slab first (last (phi i)) hle
      (G (phi i)) (L (phi i)) (hinit (phi i)) K htrace Fv hFv himage
      (zero_lt_one.trans_le (hQ (phi i))) hθ.le hstart
  have hinj : Function.Injective Ψ := by
    rw [hPsi]
    exact (H (phi i)).backwardSurvivorIncomingFootprintLift_injective first (last (phi i)) hle
      (G (phi i)) K htrace Fv himage hinjF
  refine ⟨first, hle, Ψ, hΨ, hFv, gflow, S, (fun z hz => hi.1 (subset_closure hz)), hK, hscalar, htrace, hstart, hinj, hmap, hS, hzero,
    hmetric, hslabs, hlast, hterminal, ?_⟩
  intro m t ht z
  obtain ⟨hcompactZ, hballZ⟩ := Geometry.Metric.centered_ball_in_scaled_buffer (L (phi i)).metric
    (zero_lt_one.trans_le (hQ (phi i))) hR hr hK (hnear z)
  have hpoint : (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
      (G (phi i)) K (Ψ z) = Fv z := congrFun hmap z
  have hqAQ : q (phi i) ≤ A * Q (phi i) :=
    (hqQ (phi i)).trans (le_mul_of_one_le_left (by linarith [hQ (phi i)]) hA)
  have h := (H (phi i)).curvDerivNorm_historical_localPullback_le_of_backwardPointTrace
    first (last (phi i)) hle (G (phi i)) (L (phi i)) (hinit (phi i)) K gflow hslabs hlast Ψ hΨ S
    (C := C)
    hr (hq (phi i)) hqAQ (hQ (phi i)) hA hθ (fun t _ => hmetric t) z
    (by simpa only [hpoint] using hcompactZ) (by simpa only [hpoint] using hballZ) hPhi
    (fun j _ hl => hderiv (phi i) j hl)
    (fun y _ => hfinal (phi i) y.val)
    (fun j _ hl => hpinch (phi i) j hl) (hpinchFinal (phi i)) hscalar htrace hstart
    (by nlinarith [htime])
  exact h m t ht

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem metricCInfConvergenceOnCompacts_terminal_of_pointed_localPullback
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (V : TopologicalSpace.Opens P.M) (N : ℕ)
    (hsource : ∀ i, (V : Set P.M) ⊆ F.source (i + N))
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := V) D)
    (hF : ∀ i, IsLocalDiffeomorph I I ∞
      (fun z : V => F.map (i + N) z.val))
    (hterminal : ∀ i, (S i).base.metric 0 =
      localPullMetric (X.obj (f (i + N))).metric (fun z : V => F.map (i + N) z.val) (hF i)) :
    MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
      (P.metric.restrictOpen V) (P.metric.restrictOpen V) := by
  apply metricCInfConvergenceOnCompacts_of_pointed_pullback F C hcanonical V N hsource
  intro i z v w
  rw [hterminal i, localPullMetric_inner]
  have hval : MDifferentiableAt I I (Subtype.val : V → P.M) z := (contMDiff_subtype_val (I := I) (U := V) (n := ∞)).mdifferentiableAt (by decide)
  have hmap := (F.partialDiffeomorph (i + N)).mdifferentiableAt (by decide) (hsource i z.property)
  have hv := mfderiv_comp_apply z hmap hval v
  have hw := mfderiv_comp_apply z hmap hval w
  simp only [mfderiv_subtype_val_apply] at hv hw
  change (X.obj (f (i + N))).metric.inner (F.map (i + N) z.val) _ _ = _
  exact congrArg₂ (fun v' w' => (X.obj (f (i + N))).metric.inner (F.map (i + N) z.val) v' w') hv hw

end DifferentialGeometry.PDE.RicciFlow

end
end

section

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable {H : ObservedHistory.{u}} {first next last : Fin (H.eventCount + 1)}
  {hfirst : first ≤ last} {hnext : next ≤ last} {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
  (KLong KShort : Set G.terminalRegularOpen)
  {E XH M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]
  {U V W : Opens M} (hWU : W ≤ U) (hWV : W ≤ V)
  (FLong : U → H.backwardSurvivorIncomingFootprint first last hfirst G KLong)
  (FShort : V → H.backwardSurvivorIncomingFootprint next last hnext G KShort)
  (hLong : IsLocalDiffeomorph I ThreeModel ∞ FLong)
  (hShort : IsLocalDiffeomorph I ThreeModel ∞ FShort)
  (hmap : H.backwardSurvivorIncomingFootprintMap first last hfirst G KLong ∘
      FLong ∘ Opens.inclusion hWU =
    H.backwardSurvivorIncomingFootprintMap next last hnext G KShort ∘
      FShort ∘ Opens.inclusion hWV)

include hmap in
private theorem historical_scaled_localPullback_overlap_of_terminal_map_eq
    (L : G.TerminalLimitMetric)
    (gLong : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (gShort : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    (hLongSlabs : ∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gLong t = ((H.backwardSurvivorSlabMetric first last hfirst j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hfirst G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (hShortSlabs : ∀ (j : Fin H.eventCount) (hj : next ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gShort t = ((H.backwardSurvivorSlabMetric next last hnext j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain next last hnext G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    (hLongLast : ∀ t ∈ Icc (H.time last) s,
      gLong t = (H.backwardSurvivorIncomingMetric first last hfirst G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (hShortLast : ∀ t ∈ Icc (H.time last) s,
      gShort t = (H.backwardSurvivorIncomingMetric next last hnext G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    {Q : ℝ} (hQ : 0 < Q) {t : ℝ}
    (htfirst : H.time first ≤ s + t / Q) (htnext : H.time next ≤ s + t / Q) (ht : t ≤ 0) :
    (localPullMetric (scaleMetric Q hQ (gLong (s + t / Q))) FLong hLong).restrictOpenOfSubset hWU =
      (localPullMetric (scaleMetric Q hQ (gShort (s + t / Q))) FShort hShort).restrictOpenOfSubset hWV := by
  have hclock : s + t / Q ≤ s := add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht hQ.le)
  have heq : (localPullMetric (gLong (s + t / Q)) FLong hLong).restrictOpenOfSubset hWU =
      (localPullMetric (gShort (s + t / Q)) FShort hShort).restrictOpenOfSubset hWV := by
    rcases le_total first next with hfn | hnf
    · exact localPullMetric_backwardSurvivorIncomingFootprint_overlap_of_terminal_eq
        hfn G KLong KShort hWU hWV FLong FShort hLong hShort hmap L gLong gShort
        hLongSlabs hShortSlabs hLongLast hShortLast ⟨htnext, hclock⟩
    · exact (localPullMetric_backwardSurvivorIncomingFootprint_overlap_of_terminal_eq
        hnf G KShort KLong hWV hWU FShort FLong hShort hLong hmap.symm L gShort gLong
        hShortSlabs hLongSlabs hShortLast hLongLast ⟨htfirst, hclock⟩).symm
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have h := congrArg (fun g => g.inner z v w) heq
  simp only [SmoothRiemannianMetric.restrictSubset_inner] at h ⊢
  change Q * _ = Q * _
  exact congrArg (Q * ·) h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact


private theorem exists_compatible_solution_limits_of_pointed_terminal_pullbacks
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (V : ℕ → TopologicalSpace.Opens P.M) (N : ℕ → ℕ)
    (hsource : ∀ n i, (V n : Set P.M) ⊆ F.source (i + N n))
    (θ : ℕ → ℝ) (hθ : ∀ n, 0 < θ n)
    (S : ∀ n, ℕ → SolutionOn (I := I) (M := V n)
      (RealTimeInterval.closed (-(θ n)) 0 (neg_nonpos.mpr (hθ n).le)))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hF : ∀ n i, IsLocalDiffeomorph I I ∞ (fun z : V n => F.map (i + N n) z.val))
    (hterminal : ∀ n i, (S n i).base.metric 0 = localPullMetric
      (X.obj (f (i + N n))).metric (fun z : V n => F.map (i + N n) z.val) (hF n i))
    (hcurv : ∀ n m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc (-(θ n / 2)) 0, ∀ z : V n, curvDerivNorm m ((S n i).base.metric t) z ≤ B)
    (hcompat : ∀ n m t, t ∈ Icc (-(θ n / 4)) 0 → t ∈ Icc (-(θ m / 4)) 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : V n ⊓ V m ≤ V n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : V n ⊓ V m ≤ V m))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I (V n),
        (∀ n, g n 0 = P.metric.restrictOpen (V n)) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := V n)
          (RealTimeInterval.closed (-(θ n / 4)) 0 (by linarith [hθ n])))) ∧
        (∀ n, ∀ K : Set (V n), IsCompact K → ∀ q : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(θ n / 4)) 0,
            metricDerivNormSupOn K q ((S n (rho i - N n)).base.metric t)
              (g n t) (P.metric.restrictOpen (V n)) < ε) ∧
        ∀ n m t, t ∈ Icc (-(θ n / 4)) 0 → t ∈ Icc (-(θ m / 4)) 0 →
          (g n t).restrictOpenOfSubset (inf_le_left : V n ⊓ V m ≤ V n) =
            (g m t).restrictOpenOfSubset (inf_le_right : V n ⊓ V m ≤ V m) := by
  have ht : ∀ n, MetricCInfConvergenceOnCompacts (fun i => (S n i).base.metric 0)
      (P.metric.restrictOpen (V n)) (P.metric.restrictOpen (V n)) :=
    fun n => metricCInfConvergenceOnCompacts_terminal_of_pointed_localPullback
      F C hcanonical (V n) (N n) (hsource n) (S n) (hF n) (hterminal n)
  apply exists_common_compatible_solution_subsequence_on_open_sets_and_intervals_of_terminal_convergence
    V (fun n => RealTimeInterval.closed (-(θ n)) 0 (neg_nonpos.mpr (hθ n).le))
    S hS (fun n => P.metric.restrictOpen (V n)) (fun n => -(θ n / 4)) (fun _ => 0)
    (fun n => by linarith [hθ n]) ?_ ?_ ht ?_ N hcompat
  · intro n t ht
    exact ⟨by linarith [ht.1, hθ n], ht.2⟩
  · intro n t ht
    exact ⟨by linarith [ht.1, hθ n], ht.2⟩
  · intro n K _ m
    obtain ⟨B, hB, hb⟩ := hcurv n m
    refine ⟨B, hB, hb.mono ?_⟩
    intro i hi t ht z _
    exact hi t ⟨by linarith [ht.1, hθ n], ht.2⟩ z

end DifferentialGeometry.PDE.RicciFlow

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_compatible_historical_solution_limits_of_pointed_convergence
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (q Q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hQ : ∀ i, 1 ≤ Q i)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i => { M := (G i).terminalRegularOpen, basepoint := x i, metric := scaleMetric (Q i) (zero_lt_one.trans_le (hQ i)) (L i).metric } } P phi)
    (Mconv : MetricConvergenceData F)
    (hcanonical : ∀ i, Mconv.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (last n)).Carrier,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r), metricScalarAt (L (phi i)).metric y ≤ 2 * (A * Q (phi i))) ∧
        ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
            (x (phi i)) (R + r),
            Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
          (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i))
    (V : ℕ → TopologicalSpace.Opens P.M) (hV : ∀ n, IsCompact (closure (V n : Set P.M))) :
    ∃ R r A θ : ℕ → ℝ, ∃ hθ : ∀ n, 0 < θ n, ∃ B : ℕ → ℕ → ℝ, ∃ N : ℕ → ℕ,
    ∃ S : ∀ n, ℕ → SolutionOn (I := ThreeModel) (M := V n)
      (RealTimeInterval.closed (-(θ n)) 0 (neg_nonpos.mpr (hθ n).le)),
      (∀ n, 0 < R n ∧ 0 < r n ∧ R n + r n < rho ∧ 1 ≤ A n ∧
        6 * C * (A n * θ n) ≤ 1 ∧ ∀ m, 0 ≤ B n m) ∧
      (∀ n i,
      ∃ first : Fin ((H (phi (i + N n))).eventCount + 1), ∃ hle : first ≤ last (phi (i + N n)),
      ∃ (Ψ : (V n) → (H (phi (i + N n))).backwardSurvivorIncomingFootprint first (last (phi (i + N n))) hle
        (G (phi (i + N n))) (riemannianClosedBallOf
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : (V n) => F.map (i + N n) z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (phi (i + N n))).backwardSurvivorIncomingFootprint first (last (phi (i + N n))) hle
            (G (phi (i + N n))) (riemannianClosedBallOf
              (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))))),
        ((V n) : Set P.M) ⊆ F.source (i + N n) ∧
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric)
          (x (phi (i + N n))) ((R n) + (r n))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric)
          (x (phi (i + N n))) ((R n) + (r n)), metricScalarAt (L (phi (i + N n))).metric y ≤ 2 * ((A n) * Q (phi (i + N n)))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n)),
          Nonempty (BackwardPointTrace (H (phi (i + N n))) first (last (phi (i + N n))) hle y.val)) ∧
        (H (phi (i + N n))).time first ≤ s (phi (i + N n)) - (θ n) / Q (phi (i + N n)) ∧
        Function.Injective Ψ ∧
        (H (phi (i + N n))).backwardSurvivorIncomingFootprintMap first (last (phi (i + N n))) hle
          (G (phi (i + N n))) (riemannianClosedBallOf
            (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))) ∘ Ψ =
              (fun z : (V n) => F.map (i + N n) z.val) ∧
        IsSolutionOn (S n i) ∧
        (S n i).base.metric 0 = localPullMetric
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric)
          (fun z : (V n) => F.map (i + N n) z.val) hFv ∧
        (∀ t, (S n i).base.metric t = localPullMetric
          (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (gflow (s (phi (i + N n)) + t / Q (phi (i + N n))))) Ψ hΨ) ∧
        (∀ (j : Fin (H (phi (i + N n))).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last (phi (i + N n))),
          ∀ t ∈ Icc ((H (phi (i + N n))).time j.castSucc) ((H (phi (i + N n))).time j.succ),
            gflow t = (((H (phi (i + N n))).backwardSurvivorSlabMetric first (last (phi (i + N n))) hle j hf hl t).restrictOpen ((H (phi (i + N n))).backwardSurvivorIncomingDomain first (last (phi (i + N n))) hle
                (G (phi (i + N n))))).restrictOpen
                  ((H (phi (i + N n))).backwardSurvivorIncomingFootprint first (last (phi (i + N n))) hle
                    (G (phi (i + N n))) (riemannianClosedBallOf
                      (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))))) ∧
        (∀ t ∈ Icc ((H (phi (i + N n))).time (last (phi (i + N n)))) (s (phi (i + N n))),
          gflow t = ((H (phi (i + N n))).backwardSurvivorIncomingMetric first (last (phi (i + N n))) hle
            (G (phi (i + N n))) (L (phi (i + N n))) t).restrictOpen
              ((H (phi (i + N n))).backwardSurvivorIncomingFootprint first (last (phi (i + N n))) hle
                (G (phi (i + N n))) (riemannianClosedBallOf
                  (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))))) ∧
        gflow (s (phi (i + N n))) = localPullMetric (L (phi (i + N n))).metric
          ((H (phi (i + N n))).backwardSurvivorIncomingFootprintMap first (last (phi (i + N n))) hle
            (G (phi (i + N n))) (riemannianClosedBallOf
              (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n))))
          ((H (phi (i + N n))).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi (i + N n))) hle
            (G (phi (i + N n))) (riemannianClosedBallOf
              (scaleMetric (Q (phi (i + N n))) (zero_lt_one.trans_le (hQ (phi (i + N n)))) (L (phi (i + N n))).metric) (x (phi (i + N n))) ((R n) + (r n)))) ∧
        ∀ m : ℕ, ∀ t ∈ Icc (-((θ n) / 2)) 0, ∀ z : (V n),
          curvDerivNorm m ((S n i).base.metric t) z ≤ (B n) m ) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ g : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel (V n),
        (∀ n, g n 0 = P.metric.restrictOpen (V n)) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := ThreeModel) (M := V n)
          (RealTimeInterval.closed (-(θ n / 4)) 0 (by linarith [hθ n])))) ∧
        (∀ n, ∀ K : Set (V n), IsCompact K → ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(θ n / 4)) 0,
            metricDerivNormSupOn K k ((S n (ψ i - N n)).base.metric t)
              (g n t) (P.metric.restrictOpen (V n)) < ε) ∧
        ∀ n m t, t ∈ Icc (-(θ n / 4)) 0 → t ∈ Icc (-(θ m / 4)) 0 →
          (g n t).restrictOpenOfSubset (inf_le_left : V n ⊓ V m ≤ V n) =
            (g m t).restrictOpenOfSubset (inf_le_right : V n ⊓ V m ≤ V m) := by
  classical
  have hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v := by
    intro K hK C hC
    have hconv : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : Mconv.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact Mconv.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv
      (by nlinarith : 0 < C ^ 2 - 1)] with i hi
    intro z hz v
    simpa only [add_sub_cancel] using (hi.2 z hz v).2
  have rows (n : ℕ) := exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence
    H last G x L hinit q Q hq hqQ hQ F hrho hradial hcompact hupper Phi hPhi
    hderiv hfinal hpinch hpinchFinal hbuffer (V n) (hV n)
  choose R r A θ hθ B hR hr hRr hA hbudget hB hevent using rows
  choose N hN using fun n => eventually_atTop.mp (hevent n)
  have hrow (n : ℕ) (i : {k : ℕ // N n ≤ k}) := hN n i.val i.property
  choose first hle Ψ hΨ hFv gflow rowS hsource hK hscalar htrace hstart hinj hmap hS hzero hmetric
    hslabs hlast hterminal hcurv using hrow
  let S (n i : ℕ) := rowS n ⟨i + N n, Nat.le_add_left _ _⟩
  refine ⟨R, r, A, θ, hθ, B, N, S,
    (fun n => ⟨hR n, hr n, hRr n, hA n, hbudget n, hB n⟩), ?_, ?_⟩
  · intro n i
    let j : {k : ℕ // N n ≤ k} := ⟨i + N n, Nat.le_add_left _ _⟩
    exact ⟨first n j, hle n j, Ψ n j, hΨ n j, hFv n j, gflow n j,
      hsource n j, hK n j, hscalar n j, htrace n j, hstart n j, hinj n j,
      hmap n j, hS n j, hzero n j, hmetric n j, hslabs n j, hlast n j,
      hterminal n j, hcurv n j⟩
  · have hcompat : ∀ n m t, t ∈ Icc (-(θ n / 4)) 0 → t ∈ Icc (-(θ m / 4)) 0 →
        (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
          (inf_le_left : V n ⊓ V m ≤ V n)) =ᶠ[atTop]
        (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
          (inf_le_right : V n ⊓ V m ≤ V m)) := by
      intro n m t htn htm
      filter_upwards [eventually_ge_atTop (N n), eventually_ge_atTop (N m)] with i hin him
      have ein : (⟨i - N n + N n, Nat.le_add_left (N n) (i - N n)⟩ : {k : ℕ // N n ≤ k}) =
          ⟨i, hin⟩ := Subtype.ext (Nat.sub_add_cancel hin)
      have eim : (⟨i - N m + N m, Nat.le_add_left (N m) (i - N m)⟩ : {k : ℕ // N m ≤ k}) =
          ⟨i, him⟩ := Subtype.ext (Nat.sub_add_cancel him)
      change ((rowS n ⟨i - N n + N n, Nat.le_add_left _ _⟩).base.metric t).restrictOpenOfSubset
          (inf_le_left : V n ⊓ V m ≤ V n) =
        ((rowS m ⟨i - N m + N m, Nat.le_add_left _ _⟩).base.metric t).restrictOpenOfSubset
          (inf_le_right : V n ⊓ V m ≤ V m)
      rw [ein, eim, hmetric n ⟨i, hin⟩ t, hmetric m ⟨i, him⟩ t]
      have hclockn : (H (phi i)).time (first n ⟨i, hin⟩) ≤ s (phi i) + t / Q (phi i) := by
        have ht : -(θ n) ≤ t := by linarith [htn.1, hθ n]
        have hh := div_le_div_of_nonneg_right ht (zero_lt_one.trans_le (hQ (phi i))).le
        rw [neg_div] at hh
        linarith [hstart n ⟨i, hin⟩]
      have hclockm : (H (phi i)).time (first m ⟨i, him⟩) ≤ s (phi i) + t / Q (phi i) := by
        have ht : -(θ m) ≤ t := by linarith [htm.1, hθ m]
        have hh := div_le_div_of_nonneg_right ht (zero_lt_one.trans_le (hQ (phi i))).le
        rw [neg_div] at hh
        linarith [hstart m ⟨i, him⟩]
      apply historical_scaled_localPullback_overlap_of_terminal_map_eq (G (phi i))
        _ _ (inf_le_left : V n ⊓ V m ≤ V n) (inf_le_right : V n ⊓ V m ≤ V m)
        (Ψ n ⟨i, hin⟩) (Ψ m ⟨i, him⟩) (hΨ n ⟨i, hin⟩) (hΨ m ⟨i, him⟩)
        (by
          funext z
          have hn := congrFun (hmap n ⟨i, hin⟩)
            (TopologicalSpace.Opens.inclusion (inf_le_left : V n ⊓ V m ≤ V n) z)
          have hm := congrFun (hmap m ⟨i, him⟩)
            (TopologicalSpace.Opens.inclusion (inf_le_right : V n ⊓ V m ≤ V m) z)
          exact hn.trans hm.symm)
        (L (phi i)) (gflow n ⟨i, hin⟩) (gflow m ⟨i, him⟩)
        (hslabs n ⟨i, hin⟩) (hslabs m ⟨i, him⟩) (hlast n ⟨i, hin⟩) (hlast m ⟨i, him⟩)
        (zero_lt_one.trans_le (hQ (phi i))) hclockn hclockm htn.2
    exact DifferentialGeometry.PDE.RicciFlow.exists_compatible_solution_limits_of_pointed_terminal_pullbacks F Mconv hcanonical V N
      (fun n i => hsource n ⟨i + N n, Nat.le_add_left _ _⟩) θ hθ S
      (fun n i => hS n ⟨i + N n, Nat.le_add_left _ _⟩)
      (fun n i => hFv n ⟨i + N n, Nat.le_add_left _ _⟩)
      (fun n i => hzero n ⟨i + N n, Nat.le_add_left _ _⟩)
      (fun n m => ⟨B n m, hB n m, Eventually.of_forall
        (fun i t ht z => hcurv n ⟨i + N n, Nat.le_add_left _ _⟩ m t ht z)⟩) hcompat

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact


private theorem endpoint_scalar_eq {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

private theorem exists_tested_pointed_convergence_with_backward_traces_at_scalar_escape_of_contacts :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → RetainedCoreHistory.{u})
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
          ((H i).time (Fin.last (H i).eventCount)) (time i)),
      let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
      let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage ((Fin.last (H i).eventCount)));
      ∀ (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) = (H i).initialMetric (Fin.last (H i).eventCount)),
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i).toHistory j (parameters i)),
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ (b : ((H i).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, (G i).terminalRegularOpen,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      ∀ hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val,
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i),
        q₀ < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
          |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
            C * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
              Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
      (∀ i, q₀ ≤ (A i).flow.scalar (time i) (x i).val) →
      (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
        ∀ y : (G i).terminalRegularOpen,
          riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
            (x i) y < ENNReal.ofReal R →
          metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i).val, v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i).val * Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i).val v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i).val v)|) ∨
        C * (A i).flow.scalar (time i) (x i).val ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i).val) (Iic (time i)) (time i)|) →
      ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
      (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
      (∀ i, Perelman.PhiAlmostNonnegative (G i).flow (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
      (∀ i, (H i).horizon < time i) →
      ∀ κ σ : ℝ, 0 < κ → 0 < σ →
      (∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
        let B := (H i).extendHorizon t ht.le
          ((G i).closedPrefix t ((H i).time_le_horizon.trans_lt ht) hts) (hinit i);
        let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩;
        ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ →
          B.toHistory.isParabolicallyRmControlledBall tm y b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b)) →
      ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
        ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
        (∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
          0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧
          ∀ᶠ i in atTop,
            IsCompact (riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
              (x i) (R + r)) ∧
            (∀ y ∈ riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
              (x i) (R + r), metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
            ∃ first : Fin ((H i).eventCount + 1),
              (∀ y ∈ riemannianClosedBallOf
                (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
                (x i) (R + r), Nonempty (BackwardPointTrace (H i).toHistory first
                  (Fin.last (H i).eventCount) (Fin.le_last first) y.val)) ∧
              (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val) ∧
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := (G (ind i)).terminalRegularOpen
                basepoint := x (ind i)
                metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                  (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
        ∃ (f : ℕ → ℕ), StrictMono f ∧
          ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
          ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
            (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
            let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
            let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
            let F' := F.liftTargetOpen U hp;
            ∃ M : MetricConvergenceData F',
              metricScalarAt P.metric P.basepoint = 1 ∧
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
              (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
              (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
              (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
              (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n, ∀ v : TangentSpace ThreeModel y,
                (1 - eps) * P.metric.inner y v v ≤
                    (X.obj (f n)).metric.inner (F'.map n y)
                      (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                      (1 + eps) * P.metric.inner y v v) ∧
              (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
              Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n))).toReal)
                atTop (𝓝 rho) ∧
              Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
                (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val) atTop atTop := by
  obtain ⟨C, hC, hbase⟩ := exists_scalar_escape_radius_with_buffered_backward_traces_of_contacts
  refine ⟨C, hC, ?_⟩
  intro eps heps hepssmall H time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ hinterior hqQ hfailure hfail
    Phi hPhi hpinch hpinchFinal hs κ σ hκ hσ htested
  obtain ⟨rho, hrho, ind, hind, hbuf, z, hfinite, hdist, hscalarEscape⟩ :=
    hbase eps heps hepssmall (fun i => (H i).toHistory) (fun i => Fin.last (H i).eventCount)
      time A hinit parameters records hcanonical hmargin hm herrorlim hcap q₀ a₀ a hq₀ ha₀ ha htime
      hfixed hlower hδ hderiv hfinal x hhigh hgradient (fun i => zero_lt_one.trans_le (hQ i))
      hinterior hqQ hfailure hfail
  refine ⟨rho, hrho, ind, hind, z, ?_, ?_⟩
  · intro R hR hRrho
    obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbudget, hbuffers⟩ := hbuf R hR hRrho
    refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbudget, hbuffers.mono ?_⟩
    intro i hi
    obtain ⟨first, hle, htraces, hstart⟩ := hi.2.2
    exact ⟨hi.1, hi.2.1, first, htraces, hstart⟩
  · dsimp only
    obtain ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact, hcapture, hmetric⟩ :=
      RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_tested_backward_traces
        Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
        (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
        (fun i => hs (ind i)) (fun i => x (ind i)) (fun _ => q₀)
        (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => (endpoint_scalar_eq (A (ind i)) (x (ind i))).symm) (fun _ => hq₀) (fun i => hqQ (ind i)) (fun i => hQ (ind i))
        (fun i j => hderiv (ind i) j (Fin.le_last _)) (fun i => hfinal (ind i))
        (fun i => hpinch (ind i)) (fun i => hpinchFinal (ind i)) hrho (by
          intro R hR hRrho
          obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbuf R hR hRrho
          refine ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, ?_⟩
          filter_upwards [hind.tendsto_atTop.eventually hb] with i hi
          obtain ⟨first, hle, htrace, hstart⟩ := hi.2.2
          exact ⟨hi.1, hi.2.1, first, htrace, hstart⟩) hκ hσ (fun i => htested (ind i))
    refine ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact, hcapture,
      hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop, hscalarEscape.comp hf.tendsto_atTop⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem RetainedCoreHistory.exists_compatible_historical_solution_limits_at_scalar_escape_of_scalar_derivative_contact :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
      ∀ (H : ℕ → RetainedCoreHistory.{u})
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
          ((H i).time (Fin.last (H i).eventCount)) (time i)),
      let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
      let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage ((Fin.last (H i).eventCount)));
      ∀ (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) = (H i).initialMetric (Fin.last (H i).eventCount)),
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i).toHistory j (parameters i)),
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      Tendsto (fun i => (parameters i).modelRadius) atTop atTop →
      (∀ i, max ⌈eps⁻¹⌉₊ 4 + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ (b : ((H i).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, ∀ j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ b, (records i j).delta b ≤ δ) →
      (∀ i j, j.succ ≤ (Fin.last (H i).eventCount) → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, (G i).terminalRegularOpen,
      let Q := fun i => (A i).flow.scalar (time i) (x i).val;
      Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      ∀ hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val,
      (∀ i y, ∀ t ∈ Ioo ((H i).time ((Fin.last (H i).eventCount))) (time i),
        q₀ < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
          |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
            C * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
              Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
      (∀ i, q₀ ≤ (A i).flow.scalar (time i) (x i).val) →
      (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
        ∀ y : (G i).terminalRegularOpen,
          riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
            (x i) y < ENNReal.ofReal R →
          metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i).val, v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i).val * Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i).val v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i).val v)|) ∨
        C * (A i).flow.scalar (time i) (x i).val ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i).val) (Iic (time i)) (time i)|) →
      ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
      (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
      (∀ i, Perelman.PhiAlmostNonnegative (G i).flow (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
      (∀ i, (H i).horizon < time i) →
      ∀ κ σ : ℝ, 0 < κ → 0 < σ →
      (∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
        let B := (H i).extendHorizon t ht.le
          ((G i).closedPrefix t ((H i).time_le_horizon.trans_lt ht) hts) (hinit i);
        let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩;
        ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ →
          B.toHistory.isParabolicallyRmControlledBall tm y b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b)) →
      ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
        ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
        (∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
          0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧
          ∀ᶠ i in atTop,
            IsCompact (riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
              (x i) (R + r)) ∧
            (∀ y ∈ riemannianClosedBallOf
              (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
              (x i) (R + r), metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
            ∃ first : Fin ((H i).eventCount + 1),
              (∀ y ∈ riemannianClosedBallOf
                (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i)) (L i).metric)
                (x i) (R + r), Nonempty (BackwardPointTrace (H i).toHistory first
                  (Fin.last (H i).eventCount) (Fin.le_last first) y.val)) ∧
              (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val) ∧
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := (G (ind i)).terminalRegularOpen
                basepoint := x (ind i)
                metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                  (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
        ∃ (f : ℕ → ℕ), StrictMono f ∧
          ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
          ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
            (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
            let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
            let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
            let F' := F.liftTargetOpen U hp;
            ∃ M : MetricConvergenceData F',
              metricScalarAt P.metric P.basepoint = 1 ∧
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
              (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
              (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
              (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
              (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n, ∀ v : TangentSpace ThreeModel y,
                (1 - eps) * P.metric.inner y v v ≤
                    (X.obj (f n)).metric.inner (F'.map n y)
                      (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                      (1 + eps) * P.metric.inner y v v) ∧
              (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
              Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n))).toReal)
                atTop (𝓝 rho) ∧
              Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
                (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val) atTop atTop ∧
              ∀ (V : ℕ → TopologicalSpace.Opens P.M), (∀ n, IsCompact (closure (V n : Set P.M))) →
    ∃ Rrow rrow Arow θ : ℕ → ℝ, ∃ hθ : ∀ n, 0 < θ n, ∃ B : ℕ → ℕ → ℝ, ∃ N : ℕ → ℕ,
    ∃ S : ∀ n, ℕ → SolutionOn (I := ThreeModel) (M := V n)
      (RealTimeInterval.closed (-(θ n)) 0 (neg_nonpos.mpr (hθ n).le)),
      (∀ n, 0 < Rrow n ∧ 0 < rrow n ∧ Rrow n + rrow n < rho ∧ 1 ≤ Arow n ∧
        6 * C * (Arow n * θ n) ≤ 1 ∧ ∀ m, 0 ≤ B n m) ∧
      (∀ n i,
      ∃ first : Fin ((H (ind (f (i + N n)))).eventCount + 1), ∃ hle : first ≤ Fin.last (H (ind (f (i + N n)))).eventCount,
      ∃ (Ψ : (V n) → (H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprint first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
        (G (ind (f (i + N n)))) (riemannianClosedBallOf
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : (V n) => F'.map (i + N n) z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprint first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
            (G (ind (f (i + N n)))) (riemannianClosedBallOf
              (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))))),
        ((V n) : Set P.M) ⊆ F'.source (i + N n) ∧
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric)
          (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric)
          (x (ind (f (i + N n)))) ((Rrow n) + (rrow n)), metricScalarAt (L (ind (f (i + N n)))).metric y ≤ 2 * ((Arow n) * Q (ind (f (i + N n))))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n)),
          Nonempty (BackwardPointTrace (H (ind (f (i + N n)))).toHistory first (Fin.last (H (ind (f (i + N n)))).eventCount) hle y.val)) ∧
        (H (ind (f (i + N n)))).time first ≤ time (ind (f (i + N n))) - (θ n) / Q (ind (f (i + N n))) ∧
        Function.Injective Ψ ∧
        (H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
          (G (ind (f (i + N n)))) (riemannianClosedBallOf
            (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))) ∘ Ψ =
              (fun z : (V n) => F'.map (i + N n) z.val) ∧
        IsSolutionOn (S n i) ∧
        (S n i).base.metric 0 = localPullMetric
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric)
          (fun z : (V n) => F'.map (i + N n) z.val) hFv ∧
        (∀ t, (S n i).base.metric t = localPullMetric
          (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (gflow (time (ind (f (i + N n))) + t / Q (ind (f (i + N n)))))) Ψ hΨ) ∧
        (∀ (j : Fin (H (ind (f (i + N n)))).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ Fin.last (H (ind (f (i + N n)))).eventCount),
          ∀ t ∈ Icc ((H (ind (f (i + N n)))).time j.castSucc) ((H (ind (f (i + N n)))).time j.succ),
            gflow t = (((H (ind (f (i + N n)))).toHistory.backwardSurvivorSlabMetric first (Fin.last (H (ind (f (i + N n)))).eventCount) hle j hf hl t).restrictOpen ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingDomain first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
                (G (ind (f (i + N n)))))).restrictOpen
                  ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprint first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
                    (G (ind (f (i + N n)))) (riemannianClosedBallOf
                      (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))))) ∧
        (∀ t ∈ Icc ((H (ind (f (i + N n)))).time (Fin.last (H (ind (f (i + N n)))).eventCount)) (time (ind (f (i + N n)))),
          gflow t = ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingMetric first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
            (G (ind (f (i + N n)))) (L (ind (f (i + N n)))) t).restrictOpen
              ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprint first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
                (G (ind (f (i + N n)))) (riemannianClosedBallOf
                  (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))))) ∧
        gflow (time (ind (f (i + N n)))) = localPullMetric (L (ind (f (i + N n)))).metric
          ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
            (G (ind (f (i + N n)))) (riemannianClosedBallOf
              (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n))))
          ((H (ind (f (i + N n)))).toHistory.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (Fin.last (H (ind (f (i + N n)))).eventCount) hle
            (G (ind (f (i + N n)))) (riemannianClosedBallOf
              (scaleMetric (Q (ind (f (i + N n)))) (zero_lt_one.trans_le (hQ (ind (f (i + N n))))) (L (ind (f (i + N n)))).metric) (x (ind (f (i + N n)))) ((Rrow n) + (rrow n)))) ∧
        ∀ m : ℕ, ∀ t ∈ Icc (-((θ n) / 2)) 0, ∀ z : (V n),
          curvDerivNorm m ((S n i).base.metric t) z ≤ (B n) m ) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ g : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel (V n),
        (∀ n, g n 0 = P.metric.restrictOpen (V n)) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := ThreeModel) (M := V n)
          (RealTimeInterval.closed (-(θ n / 4)) 0 (by linarith [hθ n])))) ∧
        (∀ n, ∀ K : Set (V n), IsCompact K → ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(θ n / 4)) 0,
            metricDerivNormSupOn K k ((S n (ψ i - N n)).base.metric t)
              (g n t) (P.metric.restrictOpen (V n)) < ε) ∧
        (∀ n m t, t ∈ Icc (-(θ n / 4)) 0 → t ∈ Icc (-(θ m / 4)) 0 →
          (g n t).restrictOpenOfSubset (inf_le_left : V n ⊓ V m ≤ V n) =
            (g m t).restrictOpenOfSubset (inf_le_right : V n ⊓ V m ≤ V m)) ∧
        ∀ n t, t ∈ Icc (-(θ n / 4)) 0 → ∀ y : V n,
          metricAlgebraicCurvatureTensorAt (g n t) y ∈
            algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)
 := by
  obtain ⟨C, hC, hbase⟩ := ObservedHistory.exists_tested_pointed_convergence_with_backward_traces_at_scalar_escape_of_contacts
  refine ⟨C, hC, ?_⟩
  intro eps heps hepssmall H time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x Q hhigh hgradient hQ hinterior hqQ hfailure hfail
    Phi hPhi hpinch hpinchFinal hs κ σ hκ hσ htested
  obtain ⟨rho, hrho, ind, hind, z, hbuffer, f, hf, r, hr, hrlim, P, F, M, hscalarOne,
    hdomains, hradial, hcompact, hcapture, hmetric, hfinite, hdist, hescape⟩ :=
    hbase eps heps hepssmall H time A hinit parameters records hcanonical hmargin hm herrorlim hcap
      q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hQ hinterior hqQ hfailure hfail
      Phi hPhi hpinch hpinchFinal hs κ σ hκ hσ htested
  refine ⟨rho, hrho, ind, hind, z, hbuffer, f, hf, r, hr, hrlim, P, F, M, hscalarOne,
    hdomains, hradial, hcompact, hcapture, hmetric, hfinite, hdist, hescape, ?_⟩
  intro V hV
  have hrows := ObservedHistory.exists_compatible_historical_solution_limits_of_pointed_convergence
    (fun i => (H (ind i)).toHistory) (fun i => Fin.last (H (ind i)).eventCount)
    (fun i => G (ind i)) (fun i => x (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
    (fun _ => q₀) (fun i => Q (ind i)) (fun _ => hq₀) (fun i => hqQ (ind i)) (fun i => hQ (ind i))
    _ M hdomains hrho hradial hcompact Phi hPhi
    (fun i j _ => hderiv (ind i) j (Fin.le_last _)) (fun i => hfinal (ind i))
    (fun i j _ => hpinch (ind i) j) (fun i => hpinchFinal (ind i))
    (by
      intro R hR hRrho
      obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbudget, hevent⟩ := hbuffer R hR hRrho
      refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbudget, ?_⟩
      filter_upwards [(hind.comp hf).tendsto_atTop.eventually hevent] with i hi
      obtain ⟨first, htrace, hstart⟩ := hi.2.2
      exact ⟨hi.1, hi.2.1, first, Fin.le_last _, htrace, hstart⟩) V hV
  obtain ⟨Rrow, rrow, Arow, θ, hθ, B, N, S, hconstants, hsource, ψ, hψ,
    g, hgzero, hgsol, hgconv, hgcompat⟩ := hrows
  refine ⟨Rrow, rrow, Arow, θ, hθ, B, N, S, hconstants, hsource, ψ, hψ,
    g, hgzero, hgsol, hgconv, hgcompat, ?_⟩
  intro n t ht
  let _ : SigmaCompactSpace (V n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (V n).isOpen)
  have hscale : Tendsto (fun i => Q (ind (f (ψ i - N n + N n)))) atTop atTop := by
    apply ((hhigh.comp hind.tendsto_atTop).comp (hf.comp hψ).tendsto_atTop).congr'
    filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop (N n))] with i hi
    simp only [Function.comp_apply, Nat.sub_add_cancel hi]
    rfl
  refine Perelman.CanonicalNeighborhood.FiniteHorn.curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
    (fun i => (S n (ψ i - N n)).base.metric t) (g n t) (P.metric.restrictOpen (V n))
    ?_ hPhi (fun i => Q (ind (f (ψ i - N n + N n))))
    (fun i => zero_lt_one.trans_le (hQ (ind (f (ψ i - N n + N n))))) hscale ?_
  · intro K hK m ε hε
    obtain ⟨j, hj⟩ := hgconv n K hK m ε hε
    exact ⟨j, fun i hi => hj i hi t ht⟩
  · apply Eventually.of_forall
    intro i y
    obtain ⟨first, hle, Ψ, hΨ, hFv, gflow, _, _, _, _, hstart, _, _, _, _,
      hmetric, hslabs, hlast, _, _⟩ := hsource n (ψ i - N n)
    have hp := (H (ind (f (ψ i - N n + N n)))).toHistory.phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback
      first (Fin.last _) hle _ _ _ gflow hslabs hlast hPhi.contDiff.continuous
      (fun j _ _ => hpinch (ind (f (ψ i - N n + N n))) j)
      (hpinchFinal (ind (f (ψ i - N n + N n))))
      (zero_lt_one.trans_le (hQ (ind (f (ψ i - N n + N n))))) hstart
      Ψ hΨ (S n (ψ i - N n)) (fun v _ => hmetric v)
    exact hp t ⟨by linarith [ht.1, hθ n], ht.2⟩ y

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end
