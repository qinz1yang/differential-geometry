import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingDepthExtension2C_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LimitKappaP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

/-!
# 深度 driver 的 κ 条件形孪生 `hkappaC`（O-CH11-KAPPA-ADAPT G3，后缀 `_P6KA`）

P6ANCH2 G4′ 的 maximal-depth driver `exists_subseq_forall_depthExtendable_bcadC_P6L2` 里，`hwitC` /
`hderivC` / `hbcadC` 已是"traced region ⇒ …"条件形，`hkappa` 仍是**全局**（`∀ D T`，任意深度的 trace 上
κ）。本文件把它换成**条件形** `hkappaC`（与 `hwitC` 同形：子列 `φ` 前，traced region `(2D, T, K)` ⇒
`D`-球出发、深度 `T` 的 trace 上 κ），即 driver 自举的归纳假设：延伸一步时只用当前深度的 traced region。
* **schedule 分支**：`exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L2`
  **没有 `hradii`**，取 `ρnc := 0` 后其 `hkappa` 空真（`0 < r'' ≤ 0` 矛盾）⇒ 初始正深度**完全不用 κ**。
* **Tstar 分支**：window anchor 引理只经局部流极限
  `exists_local_pointed_flow_limits_of_depth_schedule_P6L` 的 κ 子句（block 的 `hnc` 与 `hncW`）用 κ，且只在
  `(D, T) = (k + 3, τ k)`。⇒ (a) **wrapper**
  `exists_local_pointed_flow_limits_of_depth_schedule_kS_P6KA`：调原引理时取 `ρnc := 0`（κ 输入空真），
  再用输出 block 里的 survivor-map 数据 + `volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B` +
  **实例形** `hkappaS`（`∀ k`，`(k + 3, τ k)`）
  重建两个 κ 子句（原证明 hncB 逐字）；(b) **anchor 孪生** `…_kappaC_P6KA`（原文逐字，κ 实例由
  `hkappaC σ` + `hext`（深度 `τ k < Tstar`、半径 `2(k + 3)`）给）；(c) **driver 孪生**
  `exists_subseq_forall_depthExtendable_kappaC_P6KA`。
* consumer `exists_subseq_forall_depthExtendable_bcadC_viaKappaC_P6KA`：原 driver 签名**逐字**
  （全局 `hkappa`）⇒ 原结论，经 driver 孪生（全局 ⇒ 条件形是平凡的）——条件形严格更弱。
无新 binder / 合同 Prop：`hkappaC` 是 driver 前提的条件形（同 `hwitC`），不是新具名合同。
塔层产出 `hkappaC`（不循环）= G2 `hfpL_of_TR_P6KA` 的逐深度孪生（DISTLA2 G1 / BCDBOOT
`hstopE_deep_tower_P6BB` 的 depth-capped 孪生）+ R4 中心对齐，见 state HANDOVER。
陈述 / 证明由 build-logs/scratch/O-CH11-KAPPA-ADAPT/gen/gen_g3.py 从源文件逐字抽取（assert）+ 定点替换生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

/-- 深度 schedule 的数值事实（`CrossingWindowAnchorBound2C_P6L2` 私有引理逐字副本，改名）。 -/
private theorem depth_schedule_facts_P6KA {T : ℝ} (hT : 0 < T) :
    (∀ k : ℕ, 0 < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    (∀ k : ℕ, T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) < T) ∧
    (∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ s < T, ∃ k : ℕ, s < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
  have hβ (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) = 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    field_simp
    push_cast
    ring
  have hβ1 (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast
    linarith
  have hβ0 (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτ (n : ℕ) : 0 < T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτT (n : ℕ) : T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < T := by
    rw [mul_div_assoc]
    nlinarith [hβ1 n]
  refine ⟨hτ, hτT, fun n => mul_pos (hβ0 n) (hτ n), fun n => ?_, fun n m hnm => ?_,
    fun s hs => ?_⟩
  · nlinarith [hβ1 n, hτ n]
  · have h1 : 1 / ((m + 2 : ℕ) : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 2)
    have h3 : 0 ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
      rw [← hβ]
      positivity
    have h4 : 1 - 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by linarith
    change ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) * (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) * (T * ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))
    rw [mul_div_assoc, mul_div_assoc, hβ, hβ]
    exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h4 hT.le) (mul_nonneg hT.le h3) (h3.trans h4)
  · by_cases hs0 : s < 0
    · exact ⟨0, hs0.trans (mul_pos (hβ0 0) (hτ 0))⟩
    push Not at hs0
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * T / (T - s))
    refine ⟨n, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hn2 : 2 * T / (T - s) < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hx : 2 * T * (1 / ((n + 2 : ℕ) : ℝ)) < T - s := by
      rw [div_lt_iff₀ hTs] at hn2
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc, hβ]
    nlinarith [mul_nonneg hT.le (sq_nonneg (1 / ((n + 2 : ℕ) : ℝ)))]

open Perelman.CanonicalNeighborhood.FiniteHorn

private local instance opensSigmaCompactAnchor_P6KA {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : TopologicalSpace.Opens Y) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

namespace ObservedHistory

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact

/-- **局部流极限 wrapper（`_P6KA`，PROVED）**：原引理
`exists_local_pointed_flow_limits_of_depth_schedule_P6L` 的结论**逐字**，κ 输入只要实例形 `hkappaS`
（`D = k + 3`、`T = τ k`，即 `htraced` 已控的深度与半径）。证明：原引理取 `ρnc := 0`（κ 输入空真）得
全部非 κ 输出 + block 的 survivor-map 数据，再按原 hncB 重建 κ 子句。 -/
theorem exists_local_pointed_flow_limits_of_depth_schedule_kS_P6KA
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
        (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappaS : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - τ k / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel) (M := W k n)
          (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) ∧
        (∀ s ∈ Icc (-τ k) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - τ k / R n ∧
          ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
              W k n → ((H n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
                ((H n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                        (hf j))) ∧
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
          ∀ z : W k n, ∀ r : ℝ, 0 < r →
          r ≤ ρnc n * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop,
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
        ∀ σ' ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ z : W k n,
          (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
        ∀ (x : W k n) (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n s) x (metricAlgebraicCurvatureTensorAt (h k n s) x)
          (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n s) x))) ∧
      (∀ k : ℕ, ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, σ < 0 →
        ∀ᶠ n in atTop, ∀ z : W k n, ∀ r : ℝ, 0 < r → r ≤ ρnc n * Real.sqrt (R n) →
          Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j),
                IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k),
                (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
                (∀ k, IsSolutionOn ({ base.metric := Gloc k } :
                  SolutionOn (I := ThreeModel) (M := V k)
                    (RealTimeInterval.closed (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0
                      (neg_nonpos.mpr (mul_pos (by positivity) (hτ k)).le)))) ∧
                (∀ k l, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
                  s ∈ Icc (-(((l + 1 : ℕ) : ℝ) / ((l + 2 : ℕ) : ℝ) * τ l)) 0 →
                  (Gloc k s).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
                    (Gloc l s).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          (Gloc k s) (P.metric.restrictOpen (V k)) < η := by
  intro X
  obtain ⟨W, h, hblock, hlipW, hscalW, hlowW, hpinchW, -, f, hf, P, F, hCd, hPc, hconn, hballF,
      V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hG, hGcompat, ψ, hψ, hconv⟩ :=
    exists_local_pointed_flow_limits_of_depth_schedule_P6L H t y R hR hRlim τ hτ htraced hr₀ hw
      hseed hκ (fun _ => 0) (fun _ _ _ _ => Eventually.of_forall fun _ _ _ _ _ _ _ _ hr'' hρ _ =>
        (lt_irrefl (0 : ℝ) (hr''.trans_le hρ)).elim) hPhi hpinch
  -- κ 子句重建（原证明 hncB 逐字；ball 成员由输出 block 的 `W = B(basepoint, k + 3)` 换回原尺度）
  have hncB : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ z : W k n, ∀ r : ℝ,
        0 < r → r ≤ ρnc n * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
        IsCompact (riemannianClosedBallOf (h k n σ) z r) →
        (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
          r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
        ENNReal.ofReal (κ * r ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
            (riemannianBallOf (h k n σ) z r) := by
    intro k
    filter_upwards [hblock k, hkappaS k] with n hn hkn
    intro σ hσ z r hr hrρ hsub hcpt hcurv
    have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
    obtain ⟨a, hat, ha, f, hf, hinj, hc, hlast, hp⟩ := hn.2.2.2.1
    refine ObservedHistory.volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B (H n) (t n) (hR n)
      a hat ha f hf hinj hc hlast hp hκ.le ?_ hr hrρ hlow hσ.2 z hcpt hcurv
    intro x v hvt hav tr r'' hr'' hρ hpc
    have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      have h1 : (x : ((H n).stageAt (t n)).Carrier) ∈ riemannianBallOf
          (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n)
          ((k + 3 : ℕ) : ℝ) := (Set.ext_iff.mp hn.1 x).mp x.property
      rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n)] at h1
    have hav' : (t n : ℝ) - τ k / R n ≤ v := by rw [← ha]; exact hav
    exact hkn x hxW v hvt hav' tr r'' hr'' hρ hpc
  refine ⟨W, h, fun k => ?_, hlipW, hscalW, hlowW, hpinchW,
    fun k σ hσ _ => (hncB k).mono fun _ hn => hn σ hσ, f, hf, P, F, hCd, hPc, hconn, hballF,
    V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hG, hGcompat, ψ, hψ, hconv⟩
  filter_upwards [hblock k, hncB k] with n hn hnc
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hnc⟩

/-- **window anchor 的 κ 条件形孪生（`_P6KA`，PROVED）**：
`exists_subseq_windowAnchorBound_of_depthExtendable_bcadC_P6L2` 逐字，只把全局 `hkappa` 换成条件形
`hkappaC`（同 `hwitC` 形）。κ 只在 `(k + 3, τ k)`、`τ k < Tstar` 用，traced region（半径 `2(k + 3)`）
由 `hext` 给。 -/
theorem exists_subseq_windowAnchorBound_of_depthExtendable_kappaC_P6KA
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar : ℝ}
    (hT : 0 < Tstar)
    (hext : ∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T)
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ (ψ i))).stageMetric
          ((Hs (σ (ψ i))).activeStage (ts (σ (ψ i)))) (ts (σ (ψ i)))) (ys (σ (ψ i)))
          (A / Real.sqrt (R (σ (ψ i)))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ (ψ i))).horizon),
        (w : ℝ) = ts (σ (ψ i)) - T' / R (σ (ψ i)) →
      ∀ (hwt : w ≤ ts (σ (ψ i)))
        (Bt : BackwardPointTrace (Hs (σ (ψ i))) ((Hs (σ (ψ i))).activeStage w)
          ((Hs (σ (ψ i))).activeStage (ts (σ (ψ i))))
          ((Hs (σ (ψ i))).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ (ψ i))).stageMetric ((Hs (σ (ψ i))).activeStage w) w)
          (Bt.point ((Hs (σ (ψ i))).activeStage w) le_rfl
            ((Hs (σ (ψ i))).activeStage_mono hwt)) ≤
          M * R (σ (ψ i)) := by
  have hRσ : Tendsto (fun m => R (σ m)) atTop atTop := hRlim.comp hσ.tendsto_atTop
  have hRpos : ∀ m, 0 < R (σ m) := fun m => hR (σ m)
  obtain ⟨hτs0, hτsT, hc0, hcτ, hcmono, hcex⟩ := depth_schedule_facts_P6KA hT
  have hcT' : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < Tstar := fun k => (hcτ k).trans (hτsT k)
  have hcT : ∀ s ∈ Ioc (-Tstar) 0, ∃ k : ℕ, -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) < s := fun s hs =>
    (hcex (-s) (by linarith [hs.1])).imp fun _ hk => by linarith
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, hncW, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn,
      hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hGsol, hGcompat, ψ₁, hψ₁, hconv⟩ :=
    exists_local_pointed_flow_limits_of_depth_schedule_kS_P6KA
      (fun m => Hs (σ m)) (fun m => ts (σ m)) (fun m => ys (σ m)) (fun m => R (σ m)) hRpos hRσ
      (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) hτs0
      (fun k => hext _ (hτs0 k) (hτsT k) _ (by positivity))
      hr₀ hw (hσ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (σ m))
      (fun k => by
        obtain ⟨K, hK0, hKev⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
        exact Filter.eventually_map.mp (hkappaC σ hσ ((k + 3 : ℕ) : ℝ)
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by positivity) (hτs0 k) hK0
          (Filter.eventually_map.mpr hKev))) hPhi
      (fun D T hD hT => hσ.tendsto_atTop.eventually (hpinch D T hD hT))
  let _ : ConnectedSpace P.M := hconn
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  obtain ⟨Gl, hGlsol, hGlres⟩ :=
    exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule hT V hVmono hVcover
      Gloc hGsol hGcompat
  have hGl0 : Gl 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hVcover x
    have heq := (hGlres k 0 ⟨by linarith [hc0 k], le_rfl⟩).trans (hG0 k)
    exact congrArg (fun q : SmoothRiemannianMetric ThreeModel (V k) => q.inner ⟨x, hk⟩ v w) heq
  have hconvG : ∀ k (K' : Set (V k)), IsCompact K' → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ₁ i,
        ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))) 0,
        metricDerivNormSupOn K' p
          (localPullMetric (h k (f (ψ₁ i)) s) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi))
          ((Gl s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    refine ⟨hi', fun s hs => ?_⟩
    rw [hGlres k s hs]
    exact hb s hs
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-(Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) 0
          (neg_nonpos.mpr (hτs0 k).le))) := fun k => (hblock k).mono fun _ hn => hn.2.1
  -- 局部化：`t₀ := t n`，例外时刻集 = `{0}` ∪ event 时刻（`ζ = 0`）
  let E' : ℕ → Set ℝ := fun m => Iic 0 ∩
    ({s | (ts (σ m) : ℝ) ≤ (ts (σ m) : ℝ) + s / R (σ m)} ∪
      {s | ∃ i, (ts (σ m) : ℝ) + s / R (σ m) = (Hs (σ m)).time i})
  have hEs : ∀ m s, s ≤ 0 → s ∉ E' m →
      (ts (σ m) : ℝ) + s / R (σ m) < ts (σ m) ∧
        ∀ i, (ts (σ m) : ℝ) + s / R (σ m) ≠ (Hs (σ m)).time i := by
    intro m s hs hsE
    simp only [E', mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE' : ∀ m, (E' m \ Icc (-(0 : ℝ)) 0).Finite := by
    intro m
    refine (Set.finite_range fun i : Fin ((Hs (σ m)).eventCount + 1) =>
      R (σ m) * ((Hs (σ m)).time i - ts (σ m))).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    have hRm := hRpos m
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs' : (ts (σ m) : ℝ) ≤ (ts (σ m) : ℝ) + s / R (σ m) := hs
      have hsR : 0 ≤ s / R (σ m) := by linarith
      have hsn : 0 ≤ s := by
        by_contra hneg
        have := div_neg_of_neg_of_pos (not_le.mp hneg) hRm
        linarith
      linarith
    · refine ⟨i, ?_⟩
      have hi' : (ts (σ m) : ℝ) + s / R (σ m) = (Hs (σ m)).time i := hi
      have : s / R (σ m) = (Hs (σ m)).time i - ts (σ m) := by
        linarith
      change R (σ m) * ((Hs (σ m)).time i - ts (σ m)) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s hRm.ne'
  obtain ⟨D, hD, hL1⟩ := exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L2.{u}
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1s|) C2s) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1s|) C2s ≤ C := hC ▸ le_max_right _ _
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max Cs ((Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hqWsq : (Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : Cs ≤ qW := hqW ▸ le_max_left _ _
  have hqs' : ∀ m, qs (σ m) ≤ R (σ m) * qW := fun m =>
    (hqs (σ m)).trans ((mul_le_mul_of_nonneg_right hqWs (hRpos m).le).trans_eq (mul_comm _ _))
  -- 局部化：witness / 导数 / BCAD 都是 trace-local（G1 的 `_P6L`）
  have hW := hL1 (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hτs0 (fun k => (hcτ k).le)
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.1)
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hlow (qs := fun m => qs (σ m)) (E := E')
    hε hC1 hC0 hqs' hqWsq
    (fun k => by
      obtain ⟨K, hK, htrK⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
      exact Filter.eventually_map.mp (hwitC σ hσ ((k + 3 : ℕ) : ℝ)
        (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by positivity) (hτs0 k) hK
        (Filter.eventually_map.mpr htrK))) hEs
  have hderivB := eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L2
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1)
    (E := E') (Ct := (Ctime : ℝ)) (qD := Cq) (NNReal.coe_nonneg _)
    (qst := fun m => qcan (σ m)) (fun m => (hqcan (σ m)).trans_eq (mul_comm _ _))
    (fun k => by
      obtain ⟨K, hK, htrK⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
      exact Filter.eventually_map.mp (hderivC σ hσ ((k + 3 : ℕ) : ℝ)
        (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by positivity) (hτs0 k) hK
        (Filter.eventually_map.mpr htrK)))
    (fun m s hs hsE => (hEs m s hs hsE).2)
  have happrox := survivor_blocks_scalar_le_at_distance_block_P6L2
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) (fun k => (hcτ k).le)
    (fun A Dd hA hDd => (hbcadC A Dd hA hDd).imp fun _ hC' k s hs hs0 => by
      obtain ⟨K, hK, htrK⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
      exact Filter.eventually_map.mp (hC' σ hσ s hs0 ((k + 3 : ℕ) : ℝ) (by positivity)
        (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by linarith [hs.1, hcτ k]) hK
        (Filter.eventually_map.mpr htrK)))
  have hradiiσ : Tendsto (fun m => ρnc (σ m) * Real.sqrt (R (σ m))) atTop atTop :=
    hradii.comp hσ.tendsto_atTop
  obtain ⟨C₀, hC₀⟩ := exists_uniform_scalar_bound_of_local_flow_limit_on_window hf F Cd hcan hPc
    hconn hV hVF hφF
    (fun k => by
      filter_upwards [hf.tendsto_atTop.eventually (hblock k),
        hballF ((k + 3 : ℕ) : ℝ) (by positivity)] with j hj hb x hx
      have hx' : x ∈ (W k (f j) : Set _) := hx
      rw [hj.1] at hx'
      exact hb (show riemannianEDistOf _ _ _ ≤ _ from le_of_lt hx'))
    hT hτs0 hcτ hcmono hcT hGl0 hGlsol hψ₁ hconvG hsol hRσ hPhi
    (fun k => (hpinchW k).mono fun _ hn s hs x => hn s ⟨by linarith [hs.1, hcτ k], hs.2⟩ x)
    hlip (ζ := fun _ => (0 : ℝ)) tendsto_const_nhds hE' hεX hC1
    (by positivity : (0 : ℝ) < κ / 250) hW hderivB
    (fun hcomplete =>
      parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed
        hT (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
        (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hc0 hcτ hcT' hcmono hcex hsol hκ
        hradiiσ hncW hf F hVmono hVcover hVF φ hφ hφF hGlsol hcomplete hψ₁ hconvG 1 one_pos)
    happrox
  refine ⟨fun i => f (ψ₁ i), hf.comp hψ₁, max C₀ 0 + 1, by positivity,
    fun T' hT' hT'T A hA => ?_⟩
  exact eventually_scalar_backwardPointTrace_le_of_window_limit
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hf F Cd hcan hPc hV hφF
    (fun k => (hcτ k).le) hcmono hcT hψ₁ hconvG hC₀ hT' hT'T hA

/-- **maximal-depth driver 的 κ 条件形孪生（`_P6KA`，PROVED）**：
`exists_subseq_forall_depthExtendable_bcadC_P6L2` 逐字，`hkappa` → `hkappaC`。schedule 分支取
`ρnc := 0`（κ 空真）；Tstar 分支走 anchor 孪生。至此 driver 的 trace-local 前提里 `hwitC` / `hderivC` /
`hbcadC` / `hkappaC` 全是条件形；`hseed` / `hpinch` 仍全局。 -/
theorem exists_subseq_forall_depthExtendable_kappaC_P6KA
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n)
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  have hC0 : (0 : ℝ) ≤ Cst := Cst.coe_nonneg
  -- (1) 深度 schedule：基点 anchor（L6 形，`Q` 依赖半径）+ 单窗口 survival
  choose Q hQ2 hQev using fun k : ℕ => hanchor0 (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
  have hτs0 : ∀ k : ℕ, 0 < 1 / (4 * ((Cst : ℝ) + 1) * Q k) := fun k => by
    have := hQ2 k
    positivity
  have hτs1 : ∀ k : ℕ, 1 / (4 * ((Cst : ℝ) + 1) * Q k) ≤ 1 := fun k => by
    have := hQ2 k
    rw [div_le_one (by positivity)]
    nlinarith
  have hstepk : ∀ k : ℕ, 4 * (Cst : ℝ) * Q k * (1 / (4 * ((Cst : ℝ) + 1) * Q k)) ≤ 1 := by
    intro k
    have hQ0 : 0 < Q k := by linarith [hQ2 k]
    rw [show 4 * (Cst : ℝ) * Q k * (1 / (4 * ((Cst : ℝ) + 1) * Q k)) =
      (Cst : ℝ) / ((Cst : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  -- 条件形：traced region 取在半径 `2(k + 3)`（`hwitC` 的条件），再缩到 `k + 3` 喂 schedule
  have htr2 : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (Hs n).isTracedRegion (ts n) (ys n) (2 * ((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (1 / (4 * ((Cst : ℝ) + 1) * Q k) / R n) (K * R n) := by
    intro k
    obtain ⟨K, hK, hev⟩ := hsurvive (2 * ((k + 3 : ℕ) : ℝ)) _ (Q k) (by positivity) (hτs0 k)
      (hQ2 k) (hstepk k)
    exact ⟨K, hK, by filter_upwards [hev, hQev k] with n hn hq using hn hq⟩
  have htr : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (Hs n).isTracedRegion (ts n) (ys n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (1 / (4 * ((Cst : ℝ) + 1) * Q k) / R n) (K * R n) := by
    intro k
    obtain ⟨K, hK, hev⟩ := htr2 k
    have hk0 : (0 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by positivity
    refine ⟨K, hK, hev.mono fun n hn =>
      hn.mono_radius (div_pos (by positivity) (Real.sqrt_pos.2 (hR n))) ?_⟩
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hwitB : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n),
        (ts n : ℝ) - 1 / (4 * ((Cst : ℝ) + 1) * Q k) / R n ≤ v →
      (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x,
        qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart ε := fun k => by
    obtain ⟨K, hK, hev⟩ := htr2 k
    exact Filter.eventually_map.mp (hwitC id strictMono_id ((k + 3 : ℕ) : ℝ) _ K (by positivity)
      (hτs0 k) hK (Filter.eventually_map.mpr hev))
  -- (2) 基点时刻一致界（局部化的 `TimeZeroScalarBound`）⇒ 初始正深度
  have hqsN : ∀ n, qs n ≤ R n * Cs := fun n => (hqs n).trans_eq (mul_comm _ _)
  obtain ⟨ψ, hψ, C₀, -, hball⟩ :=
    exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L2
    Hs ts ys R hR hRlim (fun k => 1 / (4 * ((Cst : ℝ) + 1) * Q k)) hτs0 hτs1 htr hr₀ hw hseed hκ
    (fun _ => 0) (fun _ _ _ _ => Eventually.of_forall fun _ _ _ _ _ _ _ _ hr'' hρ _ =>
      (lt_irrefl (0 : ℝ) (hr''.trans_le hρ)).elim) hPhi hpinch hε hεN hqsN hwitB
  have hQ₀ : 2 ≤ max C₀ 2 := le_max_right _ _
  have hstep₀ : 4 * (Cst : ℝ) * max C₀ 2 * (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) ≤ 1 := by
    rw [show 4 * (Cst : ℝ) * max C₀ 2 * (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) =
      (Cst : ℝ) / ((Cst : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  have hbase : DepthExtendable Hs ts ys R ψ (1 / (4 * ((Cst : ℝ) + 1) * max C₀ 2)) := by
    intro A hA
    obtain ⟨K, hK, hev⟩ := hsurvive A _ (max C₀ 2) hA (by positivity) hQ₀ hstep₀
    refine ⟨K, hK, ?_⟩
    filter_upwards [hball A hA, hψ.tendsto_atTop.eventually hev] with i hi hn
    exact hn fun z hz => (hi z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR (ψ i)).le)
  -- (3) maximal-depth 二分（`CrossingContinuationLeaf:130` 的驱动段）
  obtain ⟨ψ', hψ', hdich⟩ := exists_strictMono_maximal_depth
    (fun σ T => DepthExtendable Hs ts ys R σ T)
    (fun _ _ _ hT' hle h => DepthExtendable.mono_depth h hR hT' hle)
    (fun _ _ _ hψ h => DepthExtendable.comp h hψ)
    (fun _ _ _ hσ h => DepthExtendable.congr h hσ) id
    ⟨ψ, hψ, _, by positivity, hbase⟩
  rcases hdich with hall | ⟨Tstar, hT, hall, hmax⟩
  · exact ⟨id ∘ ψ', strictMono_id.comp hψ', hall⟩
  · -- Tstar 分支：已控深度（`< Tstar`）的 window anchor（G2 `:555_P6L`）+ 延伸 ⇒ 与极大性矛盾
    exfalso
    obtain ⟨ψ₂, hψ₂, M, hM, hanc⟩ :=
      exists_subseq_windowAnchorBound_of_depthExtendable_kappaC_P6KA
      Hs ts ys R hR hRlim (strictMono_id.comp hψ') hT hall hr₀ hw hseed hκ ρnc hradii hkappaC hPhi
      hpinch hε hεX hqs hwitC hqcan hderivC hbcadC
    refine hmax ψ₂ hψ₂ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))
      (lt_add_of_pos_right _ (by positivity)) ?_
    exact hextend ((id ∘ ψ') ∘ ψ₂) ((strictMono_id.comp hψ').comp hψ₂) Tstar M hT hM
      (fun T hT0 hTT => DepthExtendable.comp (hall T hT0 hTT) hψ₂) hanc

/-- **consumer（`_P6KA`）**：原 driver 签名**逐字**（全局 `hkappa`）⇒ 原结论，经 driver 孪生
（全局 κ ⇒ 条件形：丢掉 traced-region 前提，沿子列 `φ` 搬运）。 -/
theorem exists_subseq_forall_depthExtendable_bcadC_viaKappaC_P6KA
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n)
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  exact exists_subseq_forall_depthExtendable_kappaC_P6KA Hs ts ys R hR hRlim hsurvive hanchor0
    hextend hr₀ hw hseed hκ ρnc hradii
    (fun φ hφ D T _ hD hT _ _ =>
      Filter.eventually_map.mpr (hφ.tendsto_atTop.eventually (hkappa D T hD hT)))
    hPhi hpinch hε hεX hεN hqs hwitC hqcan hderivC hbcadC

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
