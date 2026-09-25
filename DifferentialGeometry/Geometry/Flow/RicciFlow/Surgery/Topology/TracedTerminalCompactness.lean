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
    (P : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P n))
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
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P₀ n))
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
    Phi hPhi P₀ H s G L hinit hs x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal
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
      ∀ (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ i, RetainedCoreHistory (P₀ i))
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
  intro eps heps hepssmall P₀ H time A G L hinit parameters records hcanonical hmargin hm herrorlim hcap
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
      Phi hPhi (fun i => P₀ (ind i)) (fun i => H (ind i)) (fun i => time (ind i))
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
