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
