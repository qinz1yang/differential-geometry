import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HdistQCWireP6HQ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WitnessConditionalP6M2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistCFinalP6DC2

/-!
# 深度归纳期 1：hPN 帧的条件形 `hwitC` / `hderivC`（O-CH11-DEPTH1 G1，后缀 `_P6DP`）

设计依据：`docs/geometrization/chapter8/out/P6-CORE-INDUCTION-DESIGN-20261008.md` §6 / §8 期 1
（lead 裁定：kernel body 槽形不动；(SEP-ρ) = 已登记显式 repair target，owner HNOT-LOCALDT）。
联合深度归纳的同深度一环 `P(T) ⇒ Hdist(T) ⇒ Hder(T)`：traced region `(2D, T, K)` ⇒ 跨 slab 相对
hdist `(D, T)`（C11G3：I.8.3(b) + surgery no-shortcut）⇒ selection `hgood` 给 trace 点的 witness / Dt。

* **`hwitC_hderivC_of_hPN_C11G3`**（event 支）：`hdistQC_of_C11G3_eventually_P6HQ`（P6HQ:121，C11G3 的
  eventually 版）的结论直接喂 `hwitC_hderivC_of_hdistC_P6M2`（P6M2:38）的 `hdistC` binder。
* **`hwitC_hderivC_of_hPN_final_C11G3`**（final 支）：`hdistC_final_P6DC2`（HDISTC2，FINCOND final 孪生）
  经尾平移（P6HQ Reindex 节）降为 eventually 前提后同样喂 P6M2:38。
* consumer：把 event 支的输出喂进条件形 driver `exists_subseq_forall_depthExtendable_P6L2`
  （`qs = qcan = 4R`、`Cs = Cq = 4`，照 P6M2:138）。

前提 = HDISTQC / DC2 前提逐字（`hR` 取 P6M2 的 `∀ n` 形）+ P6M2 的 `hgood`（4R）/ `hwin`；结论 = P6M2:38
结论逐字（`Kh := (K n).toHistory`）。**PROVISIONAL[`hsepWK`（(SEP-ρ) 型，event 支带 `i < j`）、`hpin`（HI
沿 history，固定 `a₀`）]**；其余前提是 hPN 帧的结构数据（seed / records / 精度 / 晚时刻）。无新具名 Prop。
陈述由 `build-logs/scratch/O-CH11-DEPTH1/gen/gen1.py` 从三个 tracked 上游逐字拼接（sha256 断言）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **event 支（`_P6DP`，PROVISIONAL[hsepWK, hpin]）**：hPN 帧（`Kh = (K n).toHistory`，坏点 `(σ, y)` 落在
event slab `j n` 的 `t n` 之前）上，C11G3 的 eventually 前提 + selection 的 `hgood` / `hwin` ⇒ 条件形
`hwitC` ∧ `hderivC`（P6M2:38 结论逐字：traced region `(2D, T, K)` ⇒ 深度 `T` 的 trace 点在 `4R` 以上有
witness 与 `|∂ₜR| ≤ Ctime'·R²`）。证明 = HDISTQC 结论直接作 P6M2 的 `hdistC`。 -/
theorem hwitC_hderivC_of_hPN_C11G3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
      (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ),
      (∀ᶠ n in atTop, (K n).time (j n).castSucc < t n) →
      (∀ᶠ n in atTop, t n < (K n).time (j n).succ) →
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeed n)) ((K n).toHistory.activeStage (Tn n))
        ((K n).toHistory.activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, (σ n : ℝ) ≤ t n) →
      (∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) →
      (∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ n, 0 < R n) → Tendsto L atTop atTop →
      (∀ᶠ n in atTop,
        GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) → (∀ᶠ n in atTop, 2 ≤ (q n).modelOrder) →
      (∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  obtain ⟨ε₀, hε₀, hQC⟩ := hdistQC_of_C11G3_eventually_P6HQ.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' K j t hjt htj Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hσt
    hhalf htime hR hL hsmall hclock hRr a₀ ha₀ hpin q T₀ recordsK hcan hacc hord hrad hsep hT₀
    hgood hwin
  exact ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1') (C2' := C2')
    (Ctime' := Ctime') Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hL hgood hwin
    (hQC K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime
      (Filter.Eventually.of_forall hR) hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc
      hord hrad hsep hT₀)

/-- **final 支（`_P6DP`，PROVISIONAL[hsepWK, hpin]）**：坏点在最后一个 event 之后（`time last < t < horizon`）。
`hdistC_final_P6DC2` 要逐 `n` 的前提；这里照 HDISTQC 的尾平移（`exists_shift_forall_of_eventually_P6HQ` +
`eventually_map_of_shift_P6HQ`，子列 `φ′ m := φ (m + N) − N`）降为 eventually，再喂 P6M2:38。
(SEP) 对全部 event（无 `i < j`），与 DC2 合同同形。 -/
theorem hwitC_hderivC_of_hPN_final_C11G3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
      (K : ℕ → RetainedCoreHistory.{u}) (t : ℕ → ℝ),
      (∀ᶠ n in atTop, (K n).time (Fin.last (K n).eventCount) < t n) →
      (∀ᶠ n in atTop, t n < (K n).horizon) →
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeed n)) ((K n).toHistory.activeStage (Tn n))
        ((K n).toHistory.activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, (σ n : ℝ) ≤ t n) →
      (∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) →
      (∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ n, 0 < R n) → Tendsto L atTop atTop →
      (∀ᶠ n in atTop,
        GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) → (∀ᶠ n in atTop, 2 ≤ (q n).modelOrder) →
      (∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_final_P6DC2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' K t htl htK Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hσt
    hhalf htime hR hL hsmall hclock hRr a₀ ha₀ hpin q T₀ recordsK hcan hacc hord hrad hsep hT₀
    hgood hwin
  refine ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1') (C2' := C2')
    (Ctime' := Ctime') Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hL hgood hwin ?_
  intro φ hφ D T Kc hD hT hKc htr
  obtain ⟨N, hN⟩ := exists_shift_forall_of_eventually_P6HQ (htl.and (htK.and (hσt.and
    (hhalf.and (htime.and (hsmall.and (hclock.and (hpin.and (hcan.and (hacc.and
    (hord.and hrad)))))))))))
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  refine eventually_map_of_shift_P6HQ hφ N (fun h => ?_) htr
  exact hC (fun n => K (n + N)) (fun n => t (n + N)) (fun n => (hN n).1)
    (fun n => (hN n).2.1) (fun n => σ (n + N)) (fun n => y (n + N)) (fun n => R (n + N))
    (fun n => r (n + N)) (fun n => L (n + N)) (fun n => Tn (n + N)) (fun n => aSeed (n + N))
    (fun n => haT (n + N)) (fun n => hsT (n + N)) (fun n => has (n + N)) (fun n => pT (n + N))
    (fun n => seedTrace (n + N)) (fun n => (hN n).2.2.1) (fun n => (hN n).2.2.2.1)
    (fun n => (hN n).2.2.2.2.1) (Filter.Eventually.of_forall fun n => hR (n + N))
    (hL.comp hsh) (fun n => (hN n).2.2.2.2.2.1) (fun n => (hN n).2.2.2.2.2.2.1) (hRr.comp hsh)
    ha₀ (fun n => (hN n).2.2.2.2.2.2.2.1) (fun n => q (n + N)) (fun n => T₀ (n + N))
    (fun n => recordsK (n + N)) (fun n => (hN n).2.2.2.2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.2.2.2.1) (fun n => (hN n).2.2.2.2.2.2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.2.2.2.2.2) (fun T hT C hC => hsh.eventually (hsep T hT C hC))
    (fun T hT => hsh.eventually (hT₀ T hT)) (fun m => φ (m + N) - N)
    (strictMono_shiftSub_P6HQ hφ N) D T Kc hD hT hKc h

namespace ObservedHistory

/-- **consumer（§2.3，喂 P6M2 消费点）**：P6M2:138 `exists_subseq_forall_depthExtendable_of_hdistC_P6M2`
的 binder 逐字，只把 `hdistC` 换成 event 支 C11G3 数据（`Hs = (K n).toHistory`）；event 支的 `hwitC` /
`hderivC` 直接进条件形 driver `exists_subseq_forall_depthExtendable_P6L2`。精度阈值 `ε₀` 由引理给出，故结论为
`∃ ε₀, 0 < ε₀ ∧ (精度 eventually ≤ ε₀ → ∃ σ ↑, ∀ T > 0, DepthExtendable)`。 -/
example (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ᶠ n in atTop, (K n).time (j n).castSucc < t n)
    (htj : ∀ᶠ n in atTop, t n < (K n).time (j n).succ)
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
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (p : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
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
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
    (hKh : Hs = fun n => (K n).toHistory) (r : ℕ → ℝ)
    (hσt : ∀ᶠ n in atTop, (ts n : ℝ) ≤ t n)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (ts n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion
        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ') (a₀ + τ') x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hcan : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      ((recordsK n i hi).static b).hasCanonicalWindow)
    (hord : ∀ᶠ n in atTop, 2 ≤ (q n).modelOrder)
    (hrad : ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        (ts n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - T / R n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ((∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hW⟩ := hwitC_hderivC_of_hPN_C11G3.{u}
  refine ⟨ε₀, hε₀, fun hacc => ?_⟩
  obtain ⟨hwC, hdC⟩ := hW K j t hjt htj ts ys R r L Tn aSeed haT hsT has p seedTrace hσt hhalf
    htime hR hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc hord hrad hsep hT₀ hgood hwin
  exact exists_subseq_forall_depthExtendable_P6L2 _ ts ys R hR hRlim hsurvive hanchor0 hextend
    hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch hε hεX hεN (Cs := 4) (qs := fun n => 4 * R n)
    (fun _ => le_rfl) hwC (Cq := 4) (qcan := fun n => 4 * R n) (fun _ => le_rfl) hdC hbcad

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
