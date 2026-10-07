import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedOrCapLate_P6LL

/-!
# `hsurvive` 核心（`CrossingTracedRegion:70`）的 late-records + hybrid 形（O-CH11-P6LATE G1 (1)，`_P6LL`）

`exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces` 的局部化副本：
* records late（`T₀ n ≤ time i.succ`）、`hcan` / `hscale` / `hnot`（`CapWindowPoint` 展开形）late，
  `p₀` 去掉（`hpar` 直接在 `p` 上，δb 一项给 full family `recordsF` 的 late delta 界 `hδF`）；
  新增 `hT₀ : ∀ B, ∀ᶠ n, T₀ n ≤ t n − B / R n`（B5 的窗口起点 `uu = t − T/R` 在 `T₀` 之后）；
* `hinit`（固定 `P₀ g₀` 的 initial identification）换成它唯一被消费的数据：时刻 0 的 fixed
  Hamilton–Ivey `a₀`（`hHI`，与 `exists_pos_fixedHamiltonIveyRegion_for_identified_histories` 输出同形）
  ——这样 rescale 后的 history（D-17 normalization adapter）也能喂；
* `exists_capWindow_persistence_inputs_eventually` 换成 `persistence_inputs_eventually_late_P6LL`
  （只留被用到的合取项，birth 比较只对 late records）；`capWindowPoint_extendHorizon_iff` 换成
  `lateCWP_of_extendHorizon_P6LL`（late 展开形的 extendHorizon 回拉，定义等）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- `exists_capWindow_persistence_inputs_eventually` 的 late 版（`_P6LL`）：HI 常数 `a₀` 由调用者给；
只留 B5 用到的合取项；birth 比较只对 late records。 -/
theorem persistence_inputs_eventually_late_P6LL {D qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {δb : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) :
    ∀ (Rw ζ₀ δ₀ Cbirth : ℝ) (m₀ : ℕ), 0 < ζ₀ → 0 < δ₀ → 0 < Cbirth → ∀ᶠ n in atTop,
      δb n ≤ δ₀ ∧ Rw ≤ (p n).modelRadius ∧ m₀ ≤ (p n).modelOrder ∧ (p n).modelAccuracy ≤ ζ₀ ∧
      (∀ i hi b, qcan n ≤ Cbirth * ((records n i hi).static b).neck.scale ∧
        1 ≤ a₀ * ((records n i hi).static b).neck.scale) ∧ 0 < qcan n := by
  intro Rw ζ₀ δ₀ Cbirth m₀ hζ₀ hδ₀ hC
  have hinv : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ c := by
    intro c hc
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hc).mp hN
    nlinarith
  have hbig : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) + 1 := by
    intro c
    obtain ⟨N, hN⟩ := exists_nat_gt c
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  filter_upwards [hinv δ₀ hδ₀, hinv ζ₀ hζ₀, hbig Rw, eventually_ge_atTop m₀, hbig (1 / Cbirth),
    hbig (1 / a₀)] with n hδ hζ hR hm hCb ha
  obtain ⟨hacc, hD, hrad, hord, hdel⟩ := hpar n
  have hq := hqcan n
  have hq0 : 0 < qcan n := lt_of_lt_of_le (by positivity) hq
  refine ⟨hdel.trans hδ, hR.trans (hD.trans hrad), le_trans hm (by omega), hacc.trans hζ,
    fun i hi b => ?_, hq0⟩
  have hs := hscale n i hi b
  have hCb' : 1 ≤ Cbirth * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hC] at hCb
    linarith
  have ha' : 1 ≤ a₀ * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ ha₀] at ha
    linarith
  constructor
  · calc qcan n ≤ Cbirth * ((n : ℝ) + 1) * qcan n := le_mul_of_one_le_left hq0.le hCb'
      _ = Cbirth * (((n : ℝ) + 1) * qcan n) := by ring
      _ ≤ Cbirth * ((records n i hi).static b).neck.scale := mul_le_mul_of_nonneg_left hs hC.le
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * qcan n := by nlinarith
    calc (1 : ℝ) ≤ a₀ * ((n : ℝ) + 1) := ha'
      _ ≤ a₀ * (((n : ℝ) + 1) * qcan n) := mul_le_mul_of_nonneg_left hsq ha₀.le
      _ ≤ a₀ * ((records n i hi).static b).neck.scale := mul_le_mul_of_nonneg_left hs ha₀.le

/-- `capWindowPoint_extendHorizon_iff`（→ 方向）的 late 展开形版（`_P6LL`）：`extendHorizon` 上的 late
cap window point（records 逐个 `extendHorizon`）回到原 history 的最后 stage（stage 指标 `= last`、
`HEq` 点）。 -/
theorem lateCWP_of_extendHorizon_P6LL (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p) {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {k : Fin ((H.extendHorizon T hT S hS).eventCount + 1)} (hk : k = Fin.last H.eventCount)
    {y' : ((H.extendHorizon T hT S hS).stage k).Carrier}
    {y : (H.stage (Fin.last H.eventCount)).Carrier} (hy : HEq y' y) {t D θ : ℝ}
    (h : ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (A : BackwardPointTrace (H.extendHorizon T hT S hS).toHistory j.succ k hl y')
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl =
          (((records j hj).extendHorizon T hT S hS).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - H.time j.succ ≤
          θ * ((((records j hj).extendHorizon T hT S hS).static b).neck.scale)⁻¹) :
    ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
      (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - H.time j.succ ≤ θ * (((records j hj).static b).neck.scale)⁻¹ := by
  subst hk
  cases hy
  obtain ⟨j, hj, hl, A, b, x, h1, h2, h3⟩ := h
  exact ⟨j, hj, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, x, h1, h2, h3⟩

/-- **`_P6LL`（(1)：`hsurvive` 核心，late records + hybrid）**：`CrossingTracedRegion:70` 的副本，
见文件头。 -/
theorem exists_eventually_isTracedRegion_extendAt_late_P6LL
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ : 1 ≤ Q) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      ∀ ŷ : (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageAt
          ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))).Carrier,
      HEq ŷ (y n) →
      ∀ uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon,
        (uu : ℝ) = t n - T / (G n).flow.scalar (t n) (y n) →
      (∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) ŷ
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (w : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (_ : uu ≤ w) (hwt : w ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))
          (B : BackwardPointTrace ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage w)
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
              hwt) x)
          (v : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (hwv : w ≤ v) (hvt : v ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)),
          metricScalarAt
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
                (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
                v)
            (B.point
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hwv)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hvt)) ≤
            2 * (Q * (G n).flow.scalar (t n) (y n))) →
      ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.isTracedRegion
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) ŷ
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
        (T / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨c, hc, hB5⟩ := exists_isTracedRegion_or_capWindowPoint_at_scale_late_P6LL.{u}
  have hφ0 := hphi.pos 0
  have hφ1 := hphi.pos 1
  have hTQ : 0 < 8 * T * Q := by positivity
  set θ₁ : ℝ := max (1 / 4) (1 - c / (8 * T * Q)) with hθ₁def
  have hθ₁ : θ₁ < 1 := max_lt (by norm_num) (by have := div_pos hc hTQ; linarith)
  have hΘ0 : 0 < (θ₁ + 1) / 2 := by
    have := le_max_left (1 / 4 : ℝ) (1 - c / (8 * T * Q))
    linarith
  obtain ⟨Cbirth, hCb, hB5⟩ := hB5 ((θ₁ + 1) / 2) hΘ0 (by linarith) (2 * Ctime)
  set Dcap : ℝ := 2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
    Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A + 1 with hDcap
  have hDs : StandardCap.transitionEnd < Dcap := by
    have := StandardCap.transitionEnd_pos
    have : 0 ≤ Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A := by positivity
    linarith
  obtain ⟨Rrad, -, m₀, -, ζ₀, δ₀, hζ₀, -, hδ₀, hB5⟩ := hB5 Dcap hDs
  have hev := persistence_inputs_eventually_late_P6LL ha₀ hqcan hpar hscale
  have hDev : ∀ᶠ n : ℕ in atTop, Dcap ≤ D n := by
    obtain ⟨N, hN⟩ := exists_nat_ge Dcap
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(hpar n).2.1]
  have hθev : ∀ᶠ n : ℕ in atTop, θ₁ ≤ θcap n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - θ₁))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 0 < 1 - θ₁ := by linarith
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 - θ₁ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hN
      nlinarith
    linarith [hθcap n]
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Q, by positivity, ?_⟩
  filter_upwards [hev Rrad ζ₀ δ₀ (Cbirth / 2) m₀ hζ₀ hδ₀ (half_pos hCb), hDev, hθev, hT₀ T]
    with n hn hDn hθn hTn
  obtain ⟨hδn, hRn, hmn, hζn, hbirth, hq0⟩ := hn
  intro ŷ hŷ uu huu hscal
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := hq0.trans (hqR n)
  have hq1 : 1 ≤ qcan n := le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (hqcan n)
  have hlast : ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) =
        Fin.last (H n).eventCount :=
    (H n).activeStage_extendHorizon_eq_last ((hend n) ▸ (hat n).le)
      ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n)
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) (hat n).le
  have hut : uu ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) := by
    change (uu : ℝ) ≤ t n
    rw [huu]
    linarith [div_pos hT hR0]
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    (by linarith) (hslab n) (hderG n)
  rcases hB5 ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n))
      (fun i hi => (records n i hi).extendHorizon (t n) ((hend n) ▸ (hat n).le)
        ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n))
      (fun i hi b => hcan n i hi b) hRn hmn hζn
      (fun i => (recordsF n i).extendHorizon (t n) ((hend n) ▸ (hat n).le)
        ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n))
      (δb n) (fun i hi => hδF n i hi) hδn (2 * qcan n) a₀ (by linarith)
      (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (fun i hi b => le_of_le_of_eq (show 2 * qcan n ≤
        Cbirth * ((records n i hi).static b).neck.scale by linarith [(hbirth i hi b).1]) rfl)
      (fun i hi b => (hbirth i hi b).2) phi hphi
      (hpinch n).1 uu
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) hut (by rw [huu]; exact hTn)
      (fun _ => extendHorizon_finalSlab_phiAlmostNonnegative (H := H n)
        (hHT := (hend n) ▸ (hat n).le) (hpinch n).2)
      hdin.1 hdin.2.1 hdin.2.2 ŷ
      ((G n).flow.scalar (t n) (y n)) A T Q Dcap θ₁ hR0 hA hT
      (by nlinarith [hqR n]) huu
      (le_max_left _ _) (le_max_right _ _) (by linarith) le_rfl hscal
      (by rw [hDcap]; linarith) with htr | hcw
  · rw [mul_assoc]
    exact htr
  · obtain ⟨j, hj, hl, B, b, x, hx, hxn, hage⟩ := lateCWP_of_extendHorizon_P6LL (H n) (records n)
      ((hend n) ▸ (hat n).le) ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n) hlast hŷ hcw
    exact absurd ⟨j, hj, hl, B, b, x, hx, by linarith, hage.trans (mul_le_mul_of_nonneg_right hθn
      (inv_nonneg.mpr ((records n j hj).static b).neck.scale_pos.le))⟩ (hnot n)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
