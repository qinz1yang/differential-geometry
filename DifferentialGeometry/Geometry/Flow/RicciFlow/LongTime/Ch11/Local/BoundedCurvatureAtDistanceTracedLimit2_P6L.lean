import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedLimit_P6L

/-!
# L6-A #10′：`TracedLimit:47_P6L` 的 `rho + 2 ≤ Rad` 导出版（`_rad_P6L`，供 TP:97_P6L）

O-CH11-P6A2 G4 的
`RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_traced_buffer_P6L`
（`BoundedCurvatureAtDistanceTracedLimit_P6L.lean`，已交，不改）在证明内由 `TCE:166_P6L` 的统一界与
`hfailure` 推出 escape 半径 `rho ≤ R₀`，但结论没有导出它；TP:97_P6L 调 `BT:137_P6L`（`Rad_BT = rho + 1`）、
`TSL:170_P6L(m)`、`TC:493_P6L` 时要 `rho + 2 ≤ Rad`（rev1a C4）。本文件照抄其证明（私有辅助同抄），
结论在 `0 < rho` 后多一项 `rho + 2 ≤ Rad`；其余逐字。末尾 consumer 由本版推回 `TL:47_P6L`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
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
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem endpoint_scalar_eq_limit_P6L {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

/-- 成员关系桥（rev1a C2.1）：若 scaled 终端极限球 `B_{Q·L}(x, Rad)` 的点都在 `U`，且 `√Q·r ≤ Rad`，
则 closed slab 端点度量球 `B_s(x, r) ⊆ U`（`terminalRegularRegion = univ`，距离相等）。 -/
private theorem endpoint_ball_subset_of_scaled_limit_ball_P6L {P : OrientedThreeStage.{u}}
    {a s : ℝ} (A : P.ClosedSlab a s) {Q : ℝ} (hQ : 0 < Q)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (U : Set P.Carrier)
    {Rad r : ℝ} (hr : Real.sqrt Q * r ≤ Rad)
    (hU : ∀ y ∈ riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
      Rad, y.val ∈ U) :
    riemannianBallOf (A.flow.base.metric s) x.val r ⊆ U := by
  intro w hw
  have hmem : w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
    change w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ _]
    trivial
  apply hU ⟨w, hmem⟩
  change riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
    ⟨w, hmem⟩ < ENNReal.ofReal Rad
  rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric]
  have hw' : riemannianEDistOf (A.flow.base.metric s) x.val w < ENNReal.ofReal r := hw
  have hsq : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
  calc ENNReal.ofReal (Real.sqrt Q) * riemannianEDistOf (A.flow.base.metric s) x.val w
      < ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal r := by
        have h := ENNReal.mul_lt_mul_left hsq ENNReal.ofReal_ne_top hw'
        rwa [mul_comm, mul_comm (ENNReal.ofReal r)] at h
    _ = ENNReal.ofReal (Real.sqrt Q * r) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg Q)).symm
    _ ≤ ENNReal.ofReal Rad := ENNReal.ofReal_le_ofReal hr

/-- **`_rad_P6L`**：同 `TL:47_P6L`（`…_of_traced_buffer_P6L`，前提逐字），结论在 `0 < rho` 后多导出
`rho + 2 ≤ Rad`（证明内 `hrhoR : rho ≤ R₀` 与 `hfailure` 的 `R₀ + 2 ≤ Rad`）。 -/
theorem RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_traced_buffer_rad_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i)) :
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount));
    ∀ (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount)),
    (∀ i, (H i).horizon < time i) →
    ∀ (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ), (∀ i, 0 < q i) →
    ∀ (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier),
    (∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
    (∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2) →
    (∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
          Cgrad * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
            Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val),
    (∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val) →
    ∀ (Rad : ℝ), (∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        (L i).metric) (x i) Rad, y.val ∈ U i) →
    (∀ R ε B : ℝ, 0 < R → 0 < ε → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          (L i).metric) (x i) (R + ε),
        metricScalarAt (L i).metric y ≤ B * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            (L i).metric) (x i) R,
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val)) →
    (∃ R : ℝ, 0 < R ∧ R + 2 ≤ Rad ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : (G i).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) y < ENNReal.ofReal R →
        metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
    ∀ (κ σ₀ : ℝ) (σ : ℕ → ℝ), 0 < κ → 0 < σ₀ →
    (∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val)) →
    (∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i);
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b)) →
    ∃ (rho : ℝ), 0 < rho ∧ rho + 2 ≤ Rad ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
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
            (∀ R : ℝ, 0 ≤ R → R < rho →
              IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
            (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
              F'.target n) ∧
            (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n,
              ∀ v : TangentSpace ThreeModel y,
              (1 - eps) * P.metric.inner y v v ≤
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                (X.obj (f n)).metric.inner (F'.map n y)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                    (1 + eps) * P.metric.inner y v v) ∧
            (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
            Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
              (z (f n))).toReal) atTop (𝓝 rho) ∧
            Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
              (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
              atTop atTop := by
  intro G L hinit hs Ctime Cgrad q hq U hderiv hfinal hgradient x hQ hqQ Rad hU htrace hfailure
    Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  have hQpos : ∀ i, 0 < (A i).flow.scalar (time i) (x i).val :=
    fun i => zero_lt_one.trans_le (hQ i)
  obtain ⟨R₀, hR₀, hR₀Rad, hfail₀⟩ := hfailure
  have hUt : ∀ i, ∀ᶠ t in 𝓝[<] time i, riemannianBallOf ((G i).flow.base.metric t) (x i).val
      (2 * (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
        Real.sqrt (2 * (A i).flow.scalar (time i) (x i).val))) ⊆ U i := by
    intro i
    have hlpr := Perelman.CanonicalNeighborhood.localPropagationRadius_pos Cgrad.coe_nonneg
    have hlpr' := Perelman.CanonicalNeighborhood.localPropagationRadius_le Cgrad.coe_nonneg
    have hsQ : 0 < Real.sqrt ((A i).flow.scalar (time i) (x i).val) :=
      Real.sqrt_pos.mpr (hQpos i)
    have hs2 : Real.sqrt ((A i).flow.scalar (time i) (x i).val) ≤
        Real.sqrt (2 * (A i).flow.scalar (time i) (x i).val) :=
      Real.sqrt_le_sqrt (by linarith [hQpos i])
    have h1 := div_le_div_of_nonneg_left hlpr.le hsQ hs2
    have h2 : Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
        (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
          Real.sqrt ((A i).flow.scalar (time i) (x i).val)) =
        Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad :=
      mul_div_cancel₀ _ hsQ.ne'
    have h3 := mul_le_mul_of_nonneg_left h1 hsQ.le
    have hrad : Real.sqrt ((A i).flow.scalar (time i) (x i).val) *
        (2 * (2 * (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
          Real.sqrt (2 * (A i).flow.scalar (time i) (x i).val)))) ≤ Rad := by
      nlinarith
    have hρ : 0 < 2 * (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
        Real.sqrt (2 * (A i).flow.scalar (time i) (x i).val)) := by
      have : 0 < Real.sqrt (2 * (A i).flow.scalar (time i) (x i).val) := hsQ.trans_le hs2
      positivity
    exact (A i).eventually_moving_ball_subset_of_terminal_ball_P6L (U i) (x i).val hρ
      (endpoint_ball_subset_of_scaled_limit_ball_P6L (A i) (hQpos i) (x i) (U i) hrad (hU i))
  obtain ⟨rho, ind, hrho, hind, hinner, z, hfinite, hdist, hscalarEscape⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds_P6L
      (fun i => (H i).stage (Fin.last (H i).eventCount))
      (fun i => (H i).time (Fin.last (H i).eventCount)) time G L x
      (fun i => (A i).flow.scalar (time i) (x i).val) hQpos Cgrad q hqQ U hgradient hUt
      (fun i => (endpoint_scalar_eq_limit_P6L (A i) (x i)).le) ⟨R₀, hR₀, hfail₀⟩
  have hrhoR : rho ≤ R₀ := by
    by_contra hlt
    have hlt : R₀ < rho := lt_of_not_ge hlt
    obtain ⟨B, hB⟩ := hinner ((R₀ + rho) / 2) (by linarith) (by linarith)
    apply hfail₀
    refine ⟨B, hB.mono fun i hi y hy => hi.2 y ?_⟩
    exact (hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))).le
  have hUrho : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        (L i).metric) (x i) rho, y.val ∈ U i :=
    fun i y hy => hU i y (DifferentialGeometry.riemannianBallOf_mono _ _ (by linarith) hy)
  have hbuf : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r),
          metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
        ∃ first : Fin ((H i).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
              (x i) (R + r),
            Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val := by
    intro R hR hRrho
    let r := (rho - R) / 2
    have hr : 0 < r := half_pos (sub_pos.mpr hRrho)
    have hRr : R + r < rho := by dsimp [r]; linarith
    obtain ⟨B, hB⟩ := hinner (R + r) (by positivity) hRr
    let Amax := max 1 B
    have hAmax : 1 ≤ Amax := le_max_left _ _
    have hBA : B ≤ Amax := le_max_right _ _
    obtain ⟨B', hB'⟩ := hinner (R + r + r / 2) (by positivity) (by dsimp only [r]; linarith)
    obtain ⟨θ₀, hθ₀, htr⟩ := htrace (R + r) (r / 2) (max 1 B') (by positivity) (by positivity)
      (hB'.mono fun i hi y hy => by
        have hb := (div_le_iff₀ (hQpos i)).mp (hi.2 y hy)
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 B') (hQpos i).le])
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * Amax))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * Amax) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (Amax * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hAmax) hθ.le]
    refine ⟨r, Amax, θ, hr, hRr, hAmax, hθ, hbudget, ?_⟩
    filter_upwards [hB, htr] with i hi hti
    obtain ⟨first, hfirst, htrf⟩ := hti
    refine ⟨hi.1, ?_, first, htrf, ?_⟩
    · intro y hy
      have hb := (div_le_iff₀ (hQpos i)).mp (hi.2 y hy)
      have hQi := hQpos i
      nlinarith [mul_le_mul_of_nonneg_right hBA hQi.le]
    · have hdiv : θ / (A i).flow.scalar (time i) (x i).val ≤
          θ₀ / (A i).flow.scalar (time i) (x i).val :=
        div_le_div_of_nonneg_right hθθ₀ (hQpos i).le
      linarith
  have hbufR : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
          metricScalarAt (L (ind i)).metric y ≤
            2 * (Amax * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)) ∧
        ∃ first : Fin ((H (ind i)).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
            Nonempty (BackwardPointTrace (H (ind i)).toHistory first
              (Fin.last (H (ind i)).eventCount) (Fin.le_last first) y.val)) ∧
          (H (ind i)).time first ≤
            time (ind i) - θ / (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val := by
    intro R hR hRrho
    obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbuf R hR hRrho
    exact ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hind.tendsto_atTop.eventually hb⟩
  have hvol :=
    RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests_P6L
    Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
    (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
    (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => hq (ind i))
    (fun i => hqQ (ind i)) (fun i => hQ (ind i)) (fun i => U (ind i))
    (fun i j => hderiv (ind i) j) (fun i => hfinal (ind i))
    (fun i => hpinch (ind i)) (fun i => hpinchFinal (ind i)) (fun i => hUrho (ind i)) hbufR
    (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ (ind i)) (fun i => htested (ind i))
  refine ⟨rho, hrho, by linarith, ind, hind, z, ?_⟩
  dsimp only
  have hconv :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces_P6L
      Phi hPhi (fun i => (H (ind i)).toHistory) (fun i => Fin.last (H (ind i)).eventCount)
      (fun i => time (ind i)) (fun i => G (ind i)) (fun i => L (ind i))
      (fun i => hinit (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
      (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => hq (ind i))
      (fun i => hqQ (ind i)) (fun i => hQ (ind i)) (fun i => U (ind i))
      (fun i j first _ hf _ => hderiv (ind i) j first hf) (fun i => hfinal (ind i))
      (fun i j _ => hpinch (ind i) j) (fun i => hpinchFinal (ind i)) hrho
      (fun i => hUrho (ind i)) (by
        intro R hR hRrho
        obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbufR R hR hRrho
        refine ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, ?_⟩
        filter_upwards [hb] with i hi
        obtain ⟨first, htrace, hstart⟩ := hi.2.2
        exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  dsimp only at hconv
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hcanonicalDomain, hradial, hcompact, hcapture,
      hmetric⟩ := hconv
  have hscalarOne : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M
      hcanonicalDomain (by
        intro n
        change metricScalarAt (scaleMetric
          ((A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
          (hQpos (ind (f n))) (L (ind (f n))).metric) (x (ind (f n))) = 1
        rw [metricScalarAt_scaleMetric, endpoint_scalar_eq_limit_P6L, inv_mul_cancel₀]
        exact (hQpos (ind (f n))).ne')
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact,
    hcapture, hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop,
    hscalarEscape.comp hf.tendsto_atTop⟩

/-- consumer：`TL:47_P6L`（已交形）由 `_rad_P6L` 丢掉 `rho + 2 ≤ Rad` 推出。 -/
example :
  type_of% @RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_traced_buffer_P6L.{u}
    := by
  intro H time A G L hinit hs Ctime Cgrad q hq U hderiv hfinal hgradient x hQ hqQ Rad hU htrace
    hfailure Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  obtain ⟨rho, hrho, -, h⟩ :=
    RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_traced_buffer_rad_P6L H time
      A hinit hs Ctime Cgrad q hq U hderiv hfinal hgradient x hQ hqQ Rad hU htrace hfailure Phi hPhi
      hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  exact ⟨rho, hrho, h⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
