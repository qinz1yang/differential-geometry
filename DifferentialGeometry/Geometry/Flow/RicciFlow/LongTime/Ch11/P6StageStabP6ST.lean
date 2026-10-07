import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunDecoupledP6P

/-!
# S-c（stage 时刻类）sequence-level stability contract `hstabSeq`（O-CH11-STAB G1，后缀 `_P6ST`）

R-C11-5 D-13 S-c。P6BND2 的 per-history binder `hstab`（左邻域全 Good ⇒ post 点同常数 witness）是**错误形状**：
(a) 单个 history 无 blow-up，ancient-limit 用不上；(b) 树内唯一的 witness 扰动引理
`SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance` 丢常数（`neckModelTolerance α` +
`HasMargins m` ⇒ `2α`、`2C1`、`C2' ≥ 1000C2`），单层常数的 selection 无法同常数闭环；(c) collar 点的 pre-witness
domain 会被 surgery 切掉。crossing 本身无损（survivor 等距 + `SpatialCanonicalWitness.pushforward`），损失只在
pre（`v < σ`）→ terminal 的 `C^k` 扰动。

本文件的合同形 `hstabSeq`：**在 stage 时刻 post 点上直接做 KL 式 blow-up**。`false_of_rerun_decoupled_P6P`
对 `t n` 无 slab 内部限制（`hwit` / `hderiv` 只消费 `time (activeStage v) < v` 的 regular-slab
点），`t n := stageTime (j n)` 即得 `witnessStability_P6ST`。D-13 三要素的精确对应：
* 共同邻域 / surviving footprint = stage 时刻的 `htraced`：`footprint_of_tracedRegion_P6ST`——`τ > 0` 时
  post ball 的每个点都是 `(H.event i).RegularCrossing` 的新侧像（trace 必经 event `i`），且 crossing 前点在
  `terminalRegularOpen` 里、terminal 度量 Rm 界 `≤ K²`（`isRmBoundedBy` 第二分量）；
* pre/post `C^k` 收敛 = terminal 分量 + ancient-limit 的 Cheeger–Gromov 收敛（P6P 内部）；
* 更细 witness = `hwit` 精度 `εin`（与 `ηout` 解耦），`C(ηout)` 由撇常数 `max` 容纳
  （`goodConstants_accommodate_P6P`）。
不需要新 compactness 论证；剩余是 stage 时刻 producer 的接线（见 G2 binder 清单）。无新 def / structure / 具名 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

universe u

/-- stage 时刻左侧：`a < time i.succ` ⇒ `activeStage a ≤ i.castSucc`。 -/
theorem activeStage_le_castSucc_of_lt_P6ST (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {a : Icc (0 : ℝ) H.horizon} (ha : (a : ℝ) < H.time i.succ) :
    H.activeStage a ≤ i.castSucc := by
  have h1 : H.time (H.activeStage a) < H.time i.succ := (H.activeStage_time_le a).trans_lt ha
  exact Fin.le_castSucc_iff.mpr (H.time_strictMono.lt_iff_lt.mp h1)

/-- **footprint（stage 时刻 traced region 的 crossing 内容）**：`t = stageTime i.succ`、深度 `τ > 0` 的 traced
region 里，post ball 的每个点 `x` 都是 event `i` 的 `RegularCrossing` 新侧像 `q`（`HEq x q`），crossing 前点 `p'`
在 `terminalRegularOpen` 里且 terminal 度量 Rm 界 `≤ K²`——即 D-13 的 "共同邻域 / surviving footprint" 与
crossing 处的 `C^k` 数据都已含在 stage 时刻的 `htraced` 里。 -/
theorem footprint_of_tracedRegion_P6ST (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier} {ρ τ K : ℝ}
    (h : H.isTracedRegion (H.stageTime i.succ) y ρ τ K) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage (H.stageTime i.succ))
        (H.stageTime i.succ)) y ρ,
      ∃ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
        HEq x q ∧ (H.event i).RegularCrossing p' q ∧
        ∃ hp : p' ∈ (H.event i).incoming.terminalRegularOpen,
          normSq0S (H.event i).terminal.metric ⟨p', hp⟩ 4
            (metricRm04At (H.event i).terminal.metric ⟨p', hp⟩) ≤ K ^ 2 := by
  obtain ⟨-, hτ, a, hat, ha, htr⟩ := h
  intro x hx
  obtain ⟨A, hA⟩ := htr x hx
  have hlt : (a : ℝ) < H.time i.succ := by
    have : ((H.stageTime i.succ : Icc (0 : ℝ) H.horizon) : ℝ) = H.time i.succ := rfl
    rw [ha, this]
    linarith
  have hf : H.activeStage a ≤ i.castSucc := activeStage_le_castSucc_of_lt_P6ST H i hlt
  have hj : H.activeStage (H.stageTime i.succ) = i.succ := H.activeStage_stageTime i.succ
  have hl : i.succ ≤ H.activeStage (H.stageTime i.succ) := hj.symm.le
  have key : ∀ (k : Fin (H.eventCount + 1)) (hk : k = i.succ) (h1 : H.activeStage a ≤ k)
      (h2 : k ≤ H.activeStage (H.stageTime i.succ)),
      HEq (A.point k h1 h2) (A.point i.succ (hf.trans Fin.castSucc_lt_succ.le) hl) := by
    intro k hk h1 h2
    subst hk
    rfl
  refine ⟨A.point i.castSucc hf (Fin.castSucc_lt_succ.le.trans hl),
    A.point i.succ (hf.trans Fin.castSucc_lt_succ.le) hl, ?_, A.crossing i hf hl,
    (A.crossing i hf hl).mem_terminalRegularRegion (H.event i), hA.2 i hf hl⟩
  exact (heq_of_eq A.endpoint_eq.symm).trans (key _ hj _ le_rfl)

/-- **`witnessStability_P6ST`（S-c 的 sequence-level 合同 `hstabSeq`）**：stage 时刻坏点序列
`y n`（`t n = stageTime (j n)`；S 类即 `j n = (i n).succ`）在 `(stageTime (j n), y n)` 满足 P6P 的完整输入
（`htraced` = surviving footprint，见 `footprint_of_tracedRegion_P6ST`；`hseed`、trace-local κ、pinching、
精度 `εin` 的 `hwit`、`hderiv`、`R → ∞`）且 (O1) 容纳 `ηout ≤ εsel`、`C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'`
⇒ `False`。不经左侧二分、不需要 per-history `hstab`。 -/
theorem witnessStability_P6ST :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ηout : ℝ, 0 < ηout → ηout < 1 / 11 →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {εsel C1' C2' : ℝ} {Ctime' : ℝ≥0}, ηout ≤ εsel → εsel < 1 / 11 →
      C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' → ∀ εin : ℝ, 0 < εin → εin ≤ epsW →
      ∀ (H : ℕ → ObservedHistory.{u}) (j : ∀ n, Fin ((H n).eventCount + 1))
      (y : ∀ n, ((H n).stageAt ((H n).stageTime (j n))).Carrier) (R : ℕ → ℝ) (_hR : ∀ n, 0 < R n),
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
          ((H n).stageTime (j n))) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion ((H n).stageTime (j n)) (y n) (A / Real.sqrt (R n)) (T / R n)
          (K * R n)) →
      ∀ {r₀ w : ℝ}, 0 < r₀ → 0 < w →
      (∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel
            ((H n).stageAt ((H n).stageTime (j n))).Carrier
            ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n))) ((H n).stageTime (j n)))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
              ((H n).stageTime (j n))) (y n)
              (r₀ / Real.sqrt (R n)))) →
      ∀ {κ : ℝ}, 0 < κ → ∀ ρnc : ℕ → ℝ,
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
            ((H n).stageTime (j n))) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ (H n).stageTime (j n)),
          (H n).time (j n) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
          ((H n).activeStage ((H n).stageTime (j n)))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
            ((H n).stageTime (j n))) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ (H n).stageTime (j n)),
          (H n).time (j n) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
          ((H n).activeStage ((H n).stageTime (j n)))
          ((H n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
            ((H n).stageTime (j n))) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ (H n).stageTime (j n)),
          (H n).time (j n) - T / R n ≤ v →
        (v : ℝ) < (H n).time (j n) → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
          ((H n).activeStage ((H n).stageTime (j n)))
          ((H n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) εin C1s C2s
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart εin) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage ((H n).stageTime (j n)))
            ((H n).stageTime (j n))) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ (H n).stageTime (j n)),
          (H n).time (j n) - T / R n ≤ v →
        (v : ℝ) < (H n).time (j n) → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
          ((H n).activeStage ((H n).stageTime (j n)))
          ((H n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) →
      (∀ n, ¬ (H n).HasSpatialCanonicalTimeControl εsel C1' C2' Ctime'
        ((H n).stageTime (j n)) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_rerun_decoupled_P6P.{u}
  refine ⟨epsW, hepsW, fun ηout h1 h2 => ?_⟩
  obtain ⟨C, hC, hB⟩ := hB ηout h1 h2
  exact ⟨C, hC, fun hηs hss hC1 hC2 hCt εin hεin hεW H j y R hR =>
    hB hηs hss hC1 hC2 hCt εin hεin hεW H (fun n => (H n).stageTime (j n)) y R hR⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
