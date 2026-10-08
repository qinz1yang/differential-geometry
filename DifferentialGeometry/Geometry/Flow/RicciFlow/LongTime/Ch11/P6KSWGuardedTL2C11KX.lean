import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedTPC11KX

/-!
# KSW-EXIT G4：T1（TL2）的 guarded 壳 → 叶 S1（Cone）/ S2（TTC）（O-CH11-KSWEXIT，`_C11KX`）

G3 剩余 binder T1 = `GuardedTL2Leaf_C11KX`。TL2 证明里 U 侧数据只经三处：
* escape-radius `exists_terminal_scalar_escape_radius_of_derivative_bounds_window_P6WB`（只用梯度，窗口
  `c < s` 任意）——**直接调旧叶**，窗口换 `c′`（`exists_guard_window_C11KX`）；
* **S1** Cone `normalized_terminal_ball_volume_lower_bound_of_scaled_tests_age_C11KS2`
  （hderiv / hfinal / htested）——binder `GuardedConeLeaf_C11KX`；
* **S2** TTC `exists_terminal_pointed_convergence_of_buffered_backward_traces_age_C11KS2`
  （hderiv / hfinal）——binder `GuardedTTCLeaf_C11KX`。
**关键事实（支持 S1 / S2 为真）**：TL2 自己构造 buffer（`hbuf`，本文件逐字）时已取
`θ := min θ₀ (1/(6(Ctime + 1)·Amax))`，即 `6·Ctime·(Amax·θ) ≤ 1`，buffer 球上 `R ≤ 2·Amax·Q`、深度
`θ/Q` ⇒ `2·Ctime·(2·Amax·Q)·(θ/Q) ≤ 2/3 ≤ 1`：叶内（S1 / S2 消费 buffer 的位置）guard 自动成立。
S1 / S2 的 guard 用 top 标量 `Rtop`（参数 + 一致性 `metricScalarAt (L n).metric y = Rtop n y`，TL2 处
`Rtop := R(time, ·)`，一致性 = `endpoint_scalar_eq_limit_C11KX`）。
`guardedTL2Leaf_of_cone_ttc_C11KX`（PROVISIONAL[S1, S2]）；consumer
`shortSLT_guarded_of_cone_ttc_tc_C11KX`（PROVISIONAL[S1, S2, T4]）。
S1 / S2 的证书（G5）= 把 guard 穿进 Cone:50 / TTC:59·159·249，在树内叶
`curvDerivNorm_…_window_P6WA`（TTC:129）/ Cone:150·229 调用点用 buffer 预算验 guard。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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

/-- **叶 S1（`_C11KX`，binder）**：Cone `…_scaled_tests_age_C11KS2` 逐字，加 top 标量 `Rtop`（与终端极限度量
标量一致：`metricScalarAt (L n).metric y = Rtop n y`），`hderiv` / `hfinal` / `htested` 加 guard
`GuardKX_C11KX (Rtop n) (q n) C (s n) t ·`。叶内用点 = buffer 球（`R ≤ 2·A·Q`）× 深度 `θ/Q`，
`6·C·(A·θ) ≤ 1` ⇒ guard 自动成立。 -/
def GuardedConeLeaf_C11KX : Prop :=
  ∀
    (Phi : ℝ → ℝ) (_ : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (_ : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (Rtop : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier → ℝ)
    (_ : ∀ n (y : (G n).terminalRegularOpen), metricScalarAt (L n).metric y = Rtop n y.val)
    (_ : ∀ n, 0 < q n) (_ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) (c : ℕ → ℝ)
    (_ : ∃ β : ℝ, 0 < β ∧ ∀ᶠ n in atTop, β ≤ Q n * (s n - c n))
    (_ : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), c n ≤ t →
      q n < ((H n).toHistory.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (Fin.le_last _)) →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (_ : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), c n ≤ t →
      q n < (G n).flow.scalar t y → GuardKX_C11KX (Rtop n) (q n) C (s n) t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (_ : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (c n)) Phi)
    (_ : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (c n)) Phi)
    {rho : ℝ}
    (_ : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (_ : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
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
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (_ : 0 < κ) (_ : 0 < σ₀)
    (_ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (_ : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n), c n ≤ t →
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U n, GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      ∀ (y : (A.toHistory.stageAt time).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ n →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
                y b)),
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            y a)

/-- **叶 S2（`_C11KX`，binder）**：TTC `…_buffered_backward_traces_age_C11KS2` 逐字，加 `Rtop`（同 S1），
`hderiv` / `hfinal` 加 guard `GuardKX_C11KX (Rtop n) (q n) C (s n) t ·`。 -/
def GuardedTTCLeaf_C11KX : Prop :=
  ∀
    (Phi : ℝ → ℝ) (_ : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (_ : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (Rtop : ∀ n, ((H n).stage (last n)).Carrier → ℝ)
    (_ : ∀ n (y : (G n).terminalRegularOpen), metricScalarAt (L n).metric y = Rtop n y.val)
    (_ : ∀ n, 0 < q n) (_ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (last n)).Carrier) (a : ℕ → ℝ)
    (_ : ∃ β : ℝ, 0 < β ∧ ∀ᶠ n in atTop, β ≤ Q n * (s n - a n))
    (_ : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), a n ≤ t →
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (_ : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), a n ≤ t → q n < (G n).flow.scalar t y →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (_ : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (a n)) Phi)
    (_ : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n) ∩ Ici (a n)) Phi)
    {rho : ℝ} (_ : 0 < rho)
    (_ : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (_ : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
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
    (_ : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
              y a)),
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
            (1 + eps) * P.metric.inner z v v

private theorem endpoint_scalar_eq_limit_C11KX {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

/-- 成员关系桥（rev1a C2.1）：若 scaled 终端极限球 `B_{Q·L}(x, Rad)` 的点都在 `U`，且 `√Q·r ≤ Rad`，
则 closed slab 端点度量球 `B_s(x, r) ⊆ U`（`terminalRegularRegion = univ`，距离相等）。 -/
private theorem endpoint_ball_subset_of_scaled_limit_ball_C11KX {P : OrientedThreeStage.{u}}
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

/-- **T1 壳（`_C11KX`，PROVISIONAL[S1, S2]）**：TL2 `…_traced_buffer_rad_age_C11KS2` 证明逐字；Cone / TTC
换 binder S1 / S2（`Rtop := R(time, ·)`，一致性 = `endpoint_scalar_eq_limit_C11KX`）；escape-radius
（只用梯度）直接调旧叶，窗口换 `c′`。 -/
theorem guardedTL2Leaf_of_cone_ttc_C11KX (hS1 : GuardedConeLeaf_C11KX.{u})
    (hS2 : GuardedTTCLeaf_C11KX.{u}) : GuardedTL2Leaf_C11KX.{u} := by
  intro H time A G L hinit hs Ctime Cgrad q hq U a ha hderiv hfinal hgradient x hQ hqQ hQa Rad hU
    htrace hfailure Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  choose c' hac' hc' hg' using fun i => exists_guard_window_C11KX (A i) (q i) Ctime (a i) (ha i)
  have hgr' : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      c' i ≤ t → q i < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
          Cgrad * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
            Real.sqrt (((G i).flow.base.metric t).inner y v v) :=
    fun i y hy t ht hct hqt v =>
      hgradient i y hy t ht ((hac' i).trans hct) hqt (hg' i y t hct ht.2.le) v
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
      (endpoint_ball_subset_of_scaled_limit_ball_C11KX (A i) (hQpos i) (x i) (U i) hrad (hU i))
  obtain ⟨rho, ind, hrho, hind, hinner, z, hfinite, hdist, hscalarEscape⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds_window_P6WB
      (fun i => (H i).stage (Fin.last (H i).eventCount))
      (fun i => (H i).time (Fin.last (H i).eventCount)) time G L x
      (fun i => (A i).flow.scalar (time i) (x i).val) hQpos Cgrad q hqQ U c' hc' hgr' hUt
      (fun i => (endpoint_scalar_eq_limit_C11KX (A i) (x i)).le) ⟨R₀, hR₀, hfail₀⟩
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
    hS1
    Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
    (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
    (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
    (fun i => (A (ind i)).flow.scalar (time (ind i)))
    (fun i y => endpoint_scalar_eq_limit_C11KX (A (ind i)) y) (fun i => hq (ind i))
    (fun i => hqQ (ind i)) (fun i => hQ (ind i)) (fun i => U (ind i)) (fun i => a (ind i))
    (age_comp_C11KS2 hQa hind.tendsto_atTop)
    (fun i j => hderiv (ind i) j) (fun i => hfinal (ind i))
    (fun i => hpinch (ind i)) (fun i => hpinchFinal (ind i)) (fun i => hUrho (ind i)) hbufR
    (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ (ind i)) (fun i => htested (ind i))
  refine ⟨rho, hrho, by linarith, ind, hind, z, ?_⟩
  dsimp only
  have hconv :=
    hS2
      Phi hPhi (fun i => (H (ind i)).toHistory) (fun i => Fin.last (H (ind i)).eventCount)
      (fun i => time (ind i)) (fun i => G (ind i)) (fun i => L (ind i))
      (fun i => hinit (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
      (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
      (fun i => (A (ind i)).flow.scalar (time (ind i)))
      (fun i y => endpoint_scalar_eq_limit_C11KX (A (ind i)) y) (fun i => hq (ind i))
      (fun i => hqQ (ind i)) (fun i => hQ (ind i)) (fun i => U (ind i)) (fun i => a (ind i))
      (age_comp_C11KS2 hQa hind.tendsto_atTop)
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
        rw [metricScalarAt_scaleMetric, endpoint_scalar_eq_limit_C11KX, inv_mul_cancel₀]
        exact (hQpos (ind (f n))).ne')
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact,
    hcapture, hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop,
    hscalarEscape.comp hf.tendsto_atTop⟩

/-- **consumer（G4，PROVISIONAL[S1, S2, T4]）**：G1 壳 ∘ G2 ∘ G3 ∘ T1 壳。 -/
theorem shortSLT_guarded_of_cone_ttc_tc_C11KX (hS1 : GuardedConeLeaf_C11KX.{u})
    (hS2 : GuardedTTCLeaf_C11KX.{u}) (hT4 : GuardedTCLeaf_C11KX.{u}) {θ : ℝ} (hθ : 0 < θ) :
    ShortSLTGuarded_C11KX.{u} θ :=
  shortSLT_guarded_of_TL2_TC_C11KX (guardedTL2Leaf_of_cone_ttc_C11KX hS1 hS2) hT4 hθ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
