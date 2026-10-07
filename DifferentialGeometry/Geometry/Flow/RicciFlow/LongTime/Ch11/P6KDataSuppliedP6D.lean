import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureNoRtP6S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSupplyP6D

/-!
# P6 收口主形：K 层数据前提 (a) 的树内供给版（S-CH11-P6DATA G3，后缀 `_P6D`）

`false_of_selection_eventSlab_Kdata_ctrl_noRt_P6S`（P6ANCH2 G1 `hctrl` + P6BND G2 `hRt` 均已去掉）
的 (a) 组 binder `hinit hrecK hqcan hpar hscaleK hθcap hpinchK0 hslabK hqR hnotK` 与隐式
`{phi hphi D θcap qcan p recordsK}` 换成更原始的数据（`P6KDataSupplyP6D` 的 adapter 逐项 discharge）：

* `hinit` ⇐ `hinitK`（full-history 的 initial identification，
  `nonempty_initialIdentification_prefixAt_P6D`）；
  `p / recordsK / hrecK` ⇐ `hcanon : hasCanonicalCutoffRecords`（choose）；
* `qcan n := max (n+1) (Q n)`、`θcap n := 1 − 1/(n+2)`、`D n := n+1`（`exists_params_P6D`）：
  `hqcan` / `hθcap` 及 `hpar` 里的 `n+1 ≤ D n` 消失；`hpar` 余下四条明文事实 `hacc hrad hord hδ`；
* `hscaleK` ⇐ `hscaleK_of_family_P6D`（`hΛδ`、`hρ`：`ρb n > 0` 且 `(n+1)·qcan n·2ρb n² ≤ 1`）；
* `phi / hpinchK0` ⇐ `exists_phi_eventSlabsPinched_P6D`（Hamilton–Ivey，`phi` 只依赖 `P₀ g₀`）；
* `hslabK` 只需在阈值 `Q n` 处给（`eventSlabsDerivative_mono_P6D` 抬到 `qcan n`）；chain 的
  `TimeDerivativeControl_C11W` 经 `eventSlabsDerivative_of_timeDerivativeControl_P6D`；
* 留作 binder（归 P6ANCH2 selection）：`hqR`（`max (n+1) (Q n) < R n`）与 `hnotK`（records 通用形：
  对任意满足 `IsCanonicalCutoffRecordFamily` 的 records，坏点不是 cap-window 点；`D n`、`θcap n` 取上面
  的最弱值——`CapWindowPoint` 对 `Dcap`、`θcap` 单调，故这是最弱的 `hnotK`）。

**未供给（显式 binder，精确缺口见 DELIVERIES 块）**：`hacc hrad hord hδ`（全体 events 的 records family 的
参数界）+ `hcanon` + `hρ`：narrow tuple 的 `F.tower.history n` 对这些**不成立**（early events 的
`q.delta (time i.succ) > 1/(n+1)`、model window 被 `pBase` 钉死），需要 late-records 形主形
（`*_late_P6N` 内核已带 `T₀`）+ ch12 P5L 供给，或 K n 取 late tail。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **P6 收口主形，K 层数据前提 (a) 树内供给版**：见文件头。 -/
theorem false_of_selection_eventSlab_Kdata_supplied_P6D :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0},
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q : ℕ → ℝ} → {p₀ : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hinitK : ∀ n, Nonempty (InitialIdentification P₀ g₀ (K n).toHistory)) →
      (hcanon : ∀ n, (K n).hasCanonicalCutoffRecords (p₀ n) (δb n) (ρb n)) →
      (hΛδ : ∀ n, (p₀ n).recenterConstant * δb n ≤ 1 / 2) →
      (hacc : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p₀ n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p₀ n).modelOrder) →
      (hδ : ∀ n : ℕ, δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hρ : ∀ n : ℕ, 0 < ρb n ∧
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) * (2 * ρb n ^ 2) ≤ 1) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnotK : ∀ (n : ℕ) (p : CutoffParameters)
        (records : ∀ i, GeometricCutoffRecord (K n).toHistory i p),
        (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) records →
        ¬ (K n).CapWindowPoint records (j n).castSucc (yG n) (t n) ((n : ℝ) + 1)
          (1 - 1 / ((n : ℝ) + 2))) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslice : ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
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
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW, hB⟩ :=
    false_of_selection_eventSlab_Kdata_ctrl_noRt_P6S.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime K j t hjt htj Q p₀ δb ρb yG hinitK hcanon hΛδ hacc hrad hord hδ hρ hslabK hqR
    hnotK Kh hKh σ y R hσ hyG hRn hRpos d Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist
    hslice hsel
  obtain ⟨qcan, θcap, D, hqc, hθ, hD, hqcan, hQq, hθcap, hDn⟩ := exists_params_P6D Q
  have hρ' : ∀ n : ℕ, 0 < ρb n ∧ ((n : ℝ) + 1) * qcan n * (2 * ρb n ^ 2) ≤ 1 := fun n => by
    rw [hqc n]
    exact hρ n
  obtain ⟨phi, hphi, p, recordsK, hinit, hrecK, hscaleK, hpinchK0⟩ :=
    exists_Kdata_P6D j hinitK hcanon hΛδ hρ'
  have hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, hδ n⟩
  have hslabK' : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount) :=
    fun n => RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslabK n) (hQq n)
  have hqR' : ∀ n, qcan n <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hqc n]
    exact hqR n
  have hnotK' : ∀ n, ¬ (K n).CapWindowPoint (recordsK n) (j n).castSucc (yG n) (t n) (D n)
      (θcap n) := fun n => by
    rw [hD n, hθ n]
    exact hnotK n (p n) (recordsK n) (hrecK n)
  exact hB' hC1 hC2 hCt hphi hjt htj hinit hrecK hqcan hpar hscaleK hθcap hpinchK0 hslabK' hqR'
    hnotK' Kh hKh σ y R hσ hyG hRn hRpos d Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist
    hslice hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
