import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedDepthHIP6LT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteLateP6LT

/-!
# late 主形 prefix 层的逐 n HI + 窗口 pinching 版（O-CH11-P6LATE G3，后缀 `_P6LT`）

`P6KRouteLateP6LT`（G2）的副本：`exists_hctrl_lateHI_P6LT`、
`false_of_selection_eventSlab_lateHI_prefix_P6LT`。
prefix 形数据前提块的两处改动（D-17 选项 (A)）：`{a₀ : ℕ → ℝ} (hHI)` 逐 n + `hbirthA`；`hpinch` 改窗口形
（prefix 的各 slab 与 incoming slab 都 `∩ Ici (T₀ n)`）。底层换 `P6TracedDepthHIP6LT` 的 `lateHI` 版。
证明其余逐字（private 小引理照抄，后缀 `_P6LTH`）。
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

/-- 标量按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、`HEq` 点）。 -/
private theorem scalar_congr_P6LTH (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier) (hp : HEq p p') :
    metricScalarAt g p = metricScalarAt (H.stageMetric m' v) p' := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  rfl

/-- 基点标量：E（`K.eventPrefix j T`）层 = K 层（同实时刻、`HEq` 点）。 -/
private theorem scalar_eq_of_eventPrefix_P6LTH (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {T : ℝ} (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') :
    metricScalarAt ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) p =
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' := by
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmet
  rw [hττ]
  exact scalar_congr_P6LTH K.toHistory hidx τ' _ hmet p p' hp

/-- **`_P6LT`（`hctrl` ⇐ 基点 anchor，late records）**：`exists_hctrl_of_anchor0_P6M2` 的副本，
survival 换成 `hsurvive_of_extendAt_lateHI_P6LT`（逐 n HI + 窗口 pinching）。 -/
theorem exists_hctrl_lateHI_P6LT
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap qcan T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n))
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x,
      InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x)
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ᶠ n in atTop,
      (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r / Real.sqrt (R n)) := by
  subst hKh
  -- E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）的基点对象（同 K-route）
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  -- 1. anchor 搬到 E 层（`A = 1`）
  obtain ⟨Q, hQ, hball⟩ := hanchor0_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj hanchor0
    Hs ts ys R rfl HEq.rfl hys hRn 1 one_pos
  -- 2. survival：E 层 traced region
  have hC0 : (0 : ℝ) ≤ 4 * (Ctime : ℝ) * Q := by
    have := Ctime.coe_nonneg
    have : (0 : ℝ) ≤ Q := by linarith
    positivity
  have hT : 0 < 1 / (4 * (Ctime : ℝ) * Q + 1) := by positivity
  have hstep : 4 * (Ctime : ℝ) * Q * (1 / (4 * (Ctime : ℝ) * Q + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  obtain ⟨K₀, hK₀, hev⟩ := hsurvive_of_extendAt_lateHI_P6LT
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hδF hqcan hpar
    hscale hbirthA hθcap hpinch hslab hjt htj hderG hqR hnot hT₀ hRt Hs ts ys R rfl HEq.rfl hys hRn
    1 _ Q one_pos hT hQ hstep
  -- 3. 受控球半径
  have hm : 0 < min 1 (min (1 / (4 * (Ctime : ℝ) * Q + 1)) (1 / (K₀ + 1))) := by
    have : 0 < 1 / (K₀ + 1) := by positivity
    exact lt_min one_pos (lt_min hT this)
  refine ⟨Real.sqrt (min 1 (min (1 / (4 * (Ctime : ℝ) * Q + 1)) (1 / (K₀ + 1)))),
    Real.sqrt_pos.2 hm, fun r hr hrm => ?_⟩
  filter_upwards [hev, hball] with n hn hb
  have hR : 0 < R n := by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  obtain ⟨h1, h2, h3⟩ := controlledBall_radius_arith_P6M2 hK₀ hR hr hrm
  have htr := hn hb
  have hE : (Hs n).isParabolicallyRmControlledBall (ts n) (ys n) (r / Real.sqrt (R n)) :=
    ((Hs n).isParabolicallyRmControlledBall_iff_isTracedRegion (ts n) (ys n) _).2
      (htr.mono (by positivity) h1 (by positivity) h2 (by positivity) h3)
  exact (K n).isParabolicallyRmControlledBall_of_eventPrefix_P6M (j n) (hjt n) (htj n) (ts n)
    (σ n) (hσ' n) (ys n) (y n) (hysK n) hE

/-- **`_P6LT`（K-route 收口，late records，prefix 形数据）**：`false_of_selection_eventSlab_P6M` 的副本，
`htraced` 换成 `exists_subseq_htraced_extendAt_late_P6LT`。 -/
theorem false_of_selection_eventSlab_lateHI_prefix_P6LT :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
              (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {Phi : ℝ → ℝ} → (hPhi : Perelman.AdmissiblePinchingFunction Phi) →
      (hpinchK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
      {C1s C2s Cs Cq : ℝ} → {Ctr : ℝ≥0} → {qs qd : ℕ → ℝ} →
      (hqs : ∀ n, qs n ≤ Cs * R n) → (hqd : ∀ n, qd n ≤ Cq * R n) →
      (hwit : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hderivK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qd n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctr * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) →
      (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW
  refine ⟨C, hC, fun hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ
    hyG hRn r₀
    w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinchK C1s C2s Cs Cq Ctr qs qd hqs hqd hwit
    hderivK hbcad hsel
  subst hKh
  -- E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）的基点对象
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  -- 1. P6D2 G3 在 E 上给 htraced（E 层 trace-local 前提由 G3 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_lateHI_P6LT
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hδF hqcan hpar
    hscale hbirthA hθcap hpinch hslab hjt htj hderG hqR hnot hT₀ hRt hanchor0 Hs ts ys R rfl
    HEq.rfl hys
    hRn
    hr₀ hw (hseed_seq_of_eventPrefix_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_of_eventPrefix_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwit_seq_of_eventPrefix_P6M hHs' hσ' hysK hwit)
    (hbcad_seq_of_eventPrefix_P6M hHs' hσ' hysK hbcad)
  -- 2. htraced 回 K
  have hallK : ∀ T : ℝ, 0 < T → DepthExtendable (fun n => (K n).toHistory) σ y R ψ T :=
    fun T hT => depthExtendable_of_eventPrefix_P6M hHs' hσ' hysK (hall T hT)
  -- 3. P6D G2 直接在 K 上
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hRlim : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [hRn n]
    linarith [hqcan n, hqR n]
  have hscalE := scal_of_extendAt_P6D2 (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys R rfl HEq.rfl hys hRn
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) = R n := fun n =>
    (scalar_eq_of_eventPrefix_P6LTH (K n) (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n) (ys n) (y n)
      (hysK n)).symm.trans (hscalE n)
  obtain ⟨-, ψ', hψ', hev⟩ := hB' (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m))
    (fun m => y (ψ m)) (fun m => R (ψ m)) (fun m => hR (ψ m)) (fun m => hscal (ψ m))
    (hRlim.comp hψ.tendsto_atTop) (fun A T hA hT => hallK T hT A hA) hr₀ hw
    (hψ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (ψ m)) (hradii.comp hψ.tendsto_atTop)
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hkappa D T hD hT)) hPhi
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hpinchK D T hD hT)) (fun m => hqs (ψ m))
    (fun m => hqd (ψ m)) (fun D T hD hT => hψ.tendsto_atTop.eventually (hwit D T hD hT))
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hderivK D T hD hT))
  -- 4. AD-good
  exact false_of_not_good_of_eventually_good_P6L hC1 hC2 hCt (fun m => (K (ψ m)).toHistory)
    (fun m => σ (ψ m)) (fun m => y (ψ m)) (fun m => hsel (ψ m)) ⟨ψ', hψ', hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
