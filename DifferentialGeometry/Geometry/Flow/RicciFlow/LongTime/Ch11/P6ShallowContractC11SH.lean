import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingDepthExtension2C_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BcadSliceOpenCond_P6L3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AlphaSecondScaleC11AL

/-!
# 浅窗 SLT 的合同骨架（O-CH11-SHALLOW，后缀 `_C11SH`）

设计：`docs/geometrization/chapter8/design-C11-shallow-20261007.md`。依据 R-C11-10 D-17–D-20、
alpha addendum3 R1–R10、DD10 B-REPORT B4–B6。**本文件不证浅窗 SLT**（D-18：SHALLOW 设计先行），
只登记 `def … : Prop` 合同与无占位证明的接线；都不是闭合声明，端点口径不变（`{A12′}`）。

* `ShallowBcadC_C11SH`（目标 T0）= driver `exists_subseq_forall_depthExtendable_bcadC_P6L2` 的
  `hbcadC` binder 逐字：`C = C(A, Dd)` 在 `φ σ′ Dw T K` 之前，余量 `T + σ′ > 0` 任意小。
  consumer `depthExtendable_of_shallowBcadC_C11SH`：把它喂 driver（INTEGRATION-ONLY）。
* `ShallowSliceRC_C11SH`（目标 T1）= `hbcadC_of_slice_dichotomy_open_P6L3` 的 `hsliceRC` 前件逐字；
  `shallowBcadC_of_sliceRC_C11SH`：T1 ⇒ T0（P6L3 已证，INTEGRATION-ONLY）。
* `HgoodCg_C11SH Cg`：P6R2 `hgood` 的阈值 `4 R` 换成 `Cg R`；`HgoodCg_C11SH.mono`（`Cg ≤ Cg′`）。
  `SecondScaleCg_C11SH Cg` = G1 结论（`max 1 (Cg/η)`）。`Cg = 4` 由 G1 `hgood_secondScale_C11AL`
  给出（`secondScaleCg_four_C11SH`）；**`Cg = 8` 未付**（G1 在 L147 写死 `4 R`，须另实例化）。
* `SliceLocalization_C11SH`（输入 I1 的切片层：driver 已控 traced region 上的 seed-distance 闭合，
  余量 `Lsmall`，下游要 `2 Lsmall ≤ L`）。
* `SecondScaleSurvival_C11SH Cg θ`（输入 I2 的存活部分 = A3 的 b → 0 义务）：坏点 `w`
  （`q = R(v, w) ≥ 2 Cg R_n`，离低曲率 trace 点 `< Dd/√R_n`）有**实际** backward trace 到
  `v − θ/q`，或落在 cap alternative `capAlt`。前件**不含** `b·q/R_n ≥ B`（D-18 (i)）。
  `SecondScaleSurvival_C11SH.mono`：`θ ≤ θ′` 时深的推浅的。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

section DriverSlot

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **目标 T0（`_C11SH`）**：driver `exists_subseq_forall_depthExtendable_bcadC_P6L2` 的 `hbcadC`
binder 逐字（`Local/CrossingDepthExtension2C_P6L2.lean:132–153`）。量词序
`∀ A Dd ∃ C ∀ φ σ′ Dw T K`：`C` 在余量 `T + σ′` 与 traced bound `K` 之前。 -/
def ShallowBcadC_C11SH (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) : Prop :=
  ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
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
            (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n

/-- **consumer（INTEGRATION-ONLY）**：driver 的其余 binder 逐字 + `ShallowBcadC_C11SH` ⇒ 任意深度
depth-extendable 子列。证明 = driver 本身（`hbcadC := hS`，定义展开）。 -/
theorem depthExtendable_of_shallowBcadC_C11SH
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
    (hS : ShallowBcadC_C11SH Hs ts ys R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T :=
  exists_subseq_forall_depthExtendable_bcadC_P6L2 Hs ts ys R hR hRlim hsurvive hanchor0 hextend
    hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch hε hεX hεN hqs hwitC hqcan hderivC hS

/-- **输入 I2 的存活部分（`_C11SH`；A3 的 b → 0 义务，PROVISIONAL 合同）**：对 driver 的每个 traced
配置（与 T0 同一量词序，`θ` 在最前），切片 `v = σ + σ′/R` 上离低曲率 trace 点（`R ≤ A R_n`）
`< Dd/√R_n` 的每个坏点 `w`（`q = R(v, w) ≥ 2 Cg R_n`），要么有**实际** backward trace 到
`v − θ/q`（二次尺度历史深度 `q (v − a) ≥ θ`），要么 `capAlt n v w`（records / 年龄 / 空间窗口的
cap alternative；`capAlt` 须实例化为 `CapWindowPoint` 形，不得取平凡谓词）。前件不含
`b·q/R_n ≥ B`；`b = T + σ′` 只在 `∀ᶠ n` 的门槛里出现。 -/
def SecondScaleSurvival_C11SH (Cg θ : ℝ) (Hs : ℕ → ObservedHistory.{u})
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    (R : ℕ → ℝ)
    (capAlt : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon), ((Hs n).stageAt v).Carrier → Prop) :
    Prop :=
  ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∀ φ : ℕ → ℕ, StrictMono φ →
    ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
    (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
      (T / R n) (K * R n)) →
    ∀ᶠ n in map φ atTop,
    ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (Dw / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
    ∀ tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x₁,
      metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
    ∀ w : ((Hs n).stageAt v).Carrier,
      riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) w <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) →
      2 * Cg * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) w →
      (∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hav : a ≤ v),
          (a : ℝ) ≤ v - θ / metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) w ∧
          Nonempty (BackwardPointTrace (Hs n) ((Hs n).activeStage a) ((Hs n).activeStage v)
            ((Hs n).activeStage_mono hav) w)) ∨
        capAlt n v w

/-- **深推浅（`_C11SH`）**：`θ ≤ θ′` 时 `SecondScaleSurvival_C11SH Cg θ′ ⇒ … Cg θ`（`0 < Cg`、
`0 < R n`）。浅窗 kernel 只需固定的 `θ_*`；保留 TP:55 深窗则需 `∀ θ`（设计 §3）。 -/
theorem SecondScaleSurvival_C11SH.mono {Cg θ θ' : ℝ} {Hs : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier}
    {R : ℕ → ℝ}
    {capAlt : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon), ((Hs n).stageAt v).Carrier → Prop}
    (hCg : 0 < Cg) (hR : ∀ n, 0 < R n) (hθ : θ ≤ θ')
    (h : SecondScaleSurvival_C11SH Cg θ' Hs ts ys R capAlt) :
    SecondScaleSurvival_C11SH Cg θ Hs ts ys R capAlt := by
  intro A Dd hA hDd φ hφ σ' hσ' Dw hDw T K hT hK htr
  filter_upwards [h A Dd hA hDd φ hφ σ' hσ' Dw hDw T K hT hK htr] with n hn
  intro x₁ hx₁ v hvt hv tr₁ hA₁ w hw hq
  rcases hn x₁ hx₁ v hvt hv tr₁ hA₁ w hw hq with ⟨a, hav, ha, htrw⟩ | hcap
  · have hq0 := lt_of_lt_of_le (mul_pos (mul_pos two_pos hCg) (hR n)) hq
    exact Or.inl ⟨a, hav, ha.trans (by linarith [div_le_div_of_nonneg_right hθ hq0.le]), htrw⟩
  · exact Or.inr hcap

end DriverSlot

section SliceSlot

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

/-- **目标 T1（`_C11SH`）**：`hbcadC_of_slice_dichotomy_open_P6L3` 的 `hsliceRC` 前件逐字
（`Local/BcadSliceOpenCond_P6L3.lean:37–73`；`QB Dcap D₂` 只依赖 `(A, Dd)`，在 `φ σ₁ σ₂ Dw T Kc`
之前）。 -/
def ShallowSliceRC_C11SH (η₃ Lc : ℝ) (Kh : ℕ → ObservedHistory.{u})
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) : Prop :=
  ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ T Kc : ℝ, -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)

/-- **T1 ⇒ T0（INTEGRATION-ONLY）**：= `hbcadC_of_slice_dichotomy_open_P6L3`（定义展开）。 -/
theorem shallowBcadC_of_sliceRC_C11SH :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      (∀ n, (σ n : ℝ) < (Kh n).time (Fin.last (Kh n).eventCount)) →
      ShallowSliceRC_C11SH η₃ Lc Kh σ y R → ShallowBcadC_C11SH Kh σ y R :=
  hbcadC_of_slice_dichotomy_open_P6L3.{u}

end SliceSlot

section HgoodSlot

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

/-- **`Cg`-参数化的 selection `hgood`（`_C11SH`）**：P6R2 / G1 的 `hgood` 合取项逐字，只把阈值
`4 * R n` 换成 `Cg * R n`（D-18：新分析定理须明确覆盖 `Cg ∈ {4, 8}`）。 -/
def HgoodCg_C11SH (Cg : ℝ) (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (eps C1 C2 : ℝ) (Ctime : ℝ≥0) :
    Prop :=
  ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
    (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
    ∀ z : ((Kh n).stageAt v).Carrier,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
          ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z

/-- **G1 结论的 `Cg` 版（`_C11SH`）**：`hgood_secondScale_C11AL` 的结论逐字，只把二次尺度下界
`max 1 (4 / η)` 换成 `max 1 (Cg / η)`。 -/
def SecondScaleCg_C11SH (Cg : ℝ) (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (eps C1 C2 : ℝ) (Ctime : ℝ≥0) :
    Prop :=
  ∀ T K η : ℝ, 0 < η → ∀ᶠ n in atTop,
    ∀ q : ℝ, max 1 (Cg / η) * R n ≤ q →
    ∀ (s : Icc (0 : ℝ) (Kh n).horizon) (has' : aSeed n ≤ s) (hsσ : s ≤ σ n)
      (x : ((Kh n).stageAt s).Carrier),
      (σ n : ℝ) - T / R n ≤ (s : ℝ) →
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
          ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
            ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
    ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s),
      (s : ℝ) - K / q ≤ (v : ℝ) →
    ∀ z : ((Kh n).stageAt v).Carrier,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
          ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
            ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
              ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x +
          ENNReal.ofReal (K / Real.sqrt q) →
      η * q ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z

/-- **输入 I1 的切片层（`_C11SH`，PROVISIONAL 合同）**：driver 已控的 traced region 上，切片
`v = σ + σ′/R` 处离 trace 点 `< Dd/√R_n` 的点 `w` 的 seed-distance 闭合，余量 `Lsmall n`
（下游要 `Lsmall → ∞`、`2 Lsmall ≤ L`，即 `L_small < L_good`）。只用 traced region，不用 hscalU。 -/
def SliceLocalization_C11SH (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R Lsmall : ℕ → ℝ) : Prop :=
  ∀ Dd : ℝ, 0 < Dd → ∀ φ : ℕ → ℕ, StrictMono φ →
    ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
    (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
      (T / R n) (K * R n)) →
    ∀ᶠ n in map φ atTop,
    ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (Dw / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvt : v ≤ σ n),
      (v : ℝ) = σ n + σ' / R n →
    ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x₁,
    ∀ w : ((Kh n).stageAt v).Carrier,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) →
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
          ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono (hvt.trans (hsT n)))) w ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (Lsmall n / Real.sqrt (R n))

variable {Kh : ℕ → ObservedHistory.{u}} {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
    ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((Kh n).stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ} {Ctime : ℝ≥0}

/-- **阈值单调（`_C11SH`）**：`Cg ≤ Cg′`、`0 ≤ R n` ⇒ `HgoodCg Cg ⇒ HgoodCg Cg′`（阈值越高，前提越弱）。
故 `Cg = 8` 的输入比 `Cg = 4` 弱：对 `Cg = 8` 证出的分析定理覆盖 `Cg = 4`，反之不然。 -/
theorem HgoodCg_C11SH.mono {Cg Cg' : ℝ} (hCg : Cg ≤ Cg') (hR : ∀ n, 0 ≤ R n)
    (h : HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    HgoodCg_C11SH Cg' Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  fun n v hav hvs hvL z hz hRz =>
    h n v hav hvs hvL z hz ((mul_le_mul_of_nonneg_right hCg (hR n)).trans hRz)

/-- **consumer（`Cg = 4`，INTEGRATION-ONLY）**：G1 `hgood_secondScale_C11AL` 即
`HgoodCg_C11SH 4 ⇒ SecondScaleCg_C11SH 4`（定义展开）。`Cg = 8` 无对应 producer（OPEN）。 -/
theorem secondScaleCg_four_C11SH (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (h : HgoodCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    SecondScaleCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  hgood_secondScale_C11AL Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hL h

/-- **consumer（`Cg`：4 ⇒ 8）**：P6R2 输出（`Cg = 4`）蕴含 `Cg = 8` 版的 `hgood`。 -/
theorem hgoodCg_eight_of_four_C11SH (hR : ∀ n, 0 ≤ R n)
    (h : HgoodCg_C11SH 4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime) :
    HgoodCg_C11SH 8 Kh Tn aSeed σ haT hsT has pT seedTrace y R L eps C1 C2 Ctime :=
  HgoodCg_C11SH.mono (by norm_num) hR h

end HgoodSlot

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
