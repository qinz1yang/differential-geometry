import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone2_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceConeWindow_P6WA

/-!
# L6-B 第 2 层窗口版：`BoundedCurvatureAtDistanceCone:258`（`Cone2:46` in `_P6L`，`_P6WA`）

P6WIN 接口约定：同 `BoundedCurvatureAtDistanceConeWindow_P6WA`：`U` 后加 `(c : ℕ → ℝ)`、
`hQc : Tendsto (fun n => Q n * (s n - c n)) atTop atTop`，`hderiv` / `hfinal` / `htested` guard
`c n ≤ t →`，pinching 取 `Ico … ∩ Ici (c n)`；两个下层（`Cone:108`、`TTC:226`）换窗口版，
`(c, hQc)` 原样传。结论逐字。consumer：`_P6L` 由窗口版推回。
-/

set_option autoImplicit false


noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- **`_window_P6WA`**：`_P6L` 的时间窗版；原
`RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests`
（`Cone:258`）。改动同 `Cone:108` 窗口版：`U` 后加 `c`、`hQc`；guard `c n ≤ t`，pinching 取
`Ici (c n)`。结论逐字。 -/
theorem
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests_window_P6WA
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
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) (c : ℕ → ℝ)
    (hQc : Tendsto (fun n => Q n * (s n - c n)) atTop atTop)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), c n ≤ t →
      q n < ((H n).toHistory.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), c n ≤ t →
      q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (c n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (c n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
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
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n), c n ≤ t →
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U n, ∀ (y : (A.toHistory.stageAt time).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ n →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
                y b)) :
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
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
          F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hvol :=
    RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests_window_P6WA
    Phi hPhi H s G L hinit hs x q Q hq hqQ hQ U c hQc hderiv hfinal hpinch hpinchFinal
      hU hbuffer σ hκ hσ₀ hσQ htested
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces_window_P6WA
      Phi hPhi (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) s G L hinit
      x q Q hq hqQ hQ U c hQc (fun n j first _ hf _ => hderiv n j first hf) hfinal
      (fun n j _ => hpinch n j) hpinchFinal hrho hU (by
        intro R hR hRrho
        obtain ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, hb⟩ := hbuffer R hR hRrho
        refine ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, ?_⟩
        filter_upwards [hb] with n hn
        obtain ⟨first, htrace, hstart⟩ := hn.2.2
        exact ⟨hn.1, hn.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

/-- consumer：`_P6L`（`Cone:258`）由窗口版丢 guard 推出。 -/
example : type_of%
    @RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests_P6L.{u}
    := by
  intro Phi hPhi C H s G L hinit hs x q Q hscale hq hqQ hQ U hderiv hfinal hpinch hpinchFinal rho
    hrho hU hbuffer κ σ₀ σ hκ hσ₀ hσQ htested
  obtain ⟨c, -, hQc⟩ := exists_window_start_P6WA s Q (fun n => zero_lt_one.trans_le (hQ n))
  exact
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests_window_P6WA
    Phi hPhi H s G L hinit hs x q Q hscale hq hqQ hQ U c hQc
    (fun n j first hf z hz A t ht _ => hderiv n j first hf z hz A t ht)
    (fun n y hy t ht _ => hfinal n y hy t ht) (fun n j t ht x => hpinch n j t ht.1 x)
    (fun n t ht x => hpinchFinal n t ht.1 x) hrho hU hbuffer σ hκ hσ₀ hσQ
    (fun n t ht hts _ => htested n t ht hts)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
