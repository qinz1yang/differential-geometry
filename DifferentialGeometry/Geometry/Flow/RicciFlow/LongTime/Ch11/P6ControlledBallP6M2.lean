import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureKDataP6M

/-!
# 基点受控球 `hctrl` 的生产（O-CH11-P6ANCH2 G1，后缀 `_P6M2`）

`false_of_selection_eventSlab_Kdata_P6M`（G4c，P6 收口当前最终形）的 `hctrl`：
`∀ᶠ n, (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r₀ / √R n)`。生产链（**无循环**：
`hsurvive_of_extendAt_P6D2` 不吃 `hseed` / `hkappa` / `hwit`）：
1. 基点 anchor `hanchor0`（G 形）⇒ E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）ball 标量界
   （`hanchor0_of_extendAt_P6D2`，`A = 1`，得 `Q ≥ 2`）；
2. `hsurvive_of_extendAt_P6D2` 在 `T := 1 / (4·Ctime·Q + 1)`（`4·Ctime·Q·T ≤ 1`）⇒ E 层
   `isTracedRegion (ts n) (ys n) (1/√R) (T/R) (K₀·R)`；
3. `isParabolicallyRmControlledBall_iff_isTracedRegion`（半径 `r`、深度 `r²`、界 `(r²)⁻¹`）+
   `isTracedRegion.mono`，`r ≤ r₀ := √(min 1 (min T (1/(K₀+1))))` ⇒ E 层受控球；
4. G3 桥 `isParabolicallyRmControlledBall_of_eventPrefix_P6M` ⇒ K 层 `hctrl`。

`exists_hctrl_of_anchor0_P6M2`：prefix 形数据前提 + `hanchor0` ⇒ `hctrl`（`∀ r ∈ (0, r₀]`）。
`exists_hctrl_of_Kdata_P6M2`：K 层数据前提 + selection + `Pre841` ⇒ `hctrl`（`hanchor0` 照 G1y
`false_of_selection_eventSlab_final_P6M` 的证明由 SLT 窗口版生产）。
consumer `false_of_selection_eventSlab_Kdata_ctrl_P6M2`：G4c 主形去掉 `r₀` / `hr₀` / `hctrl` 三个 binder。
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

/-- 受控球半径的初等算术：E 层 traced region `(1/√R, T/R, K₀R)` 在 `r ≤ √m`、
`m = min 1 (min T (1/(K₀+1)))` 时包含受控球 `(r/√R, (r/√R)², ((r/√R)²)⁻¹)` 所需的三个不等式。 -/
theorem controlledBall_radius_arith_P6M2 {T K₀ R r : ℝ} (hK₀ : 0 ≤ K₀) (hR : 0 < R)
    (hr : 0 < r) (hrm : r ≤ Real.sqrt (min 1 (min T (1 / (K₀ + 1))))) :
    r / Real.sqrt R ≤ 1 / Real.sqrt R ∧ (r / Real.sqrt R) ^ 2 ≤ T / R ∧
      K₀ * R ≤ ((r / Real.sqrt R) ^ 2)⁻¹ := by
  have hm1 : min 1 (min T (1 / (K₀ + 1))) ≤ 1 := min_le_left _ _
  have hr1 : r ≤ 1 :=
    hrm.trans ((Real.sqrt_le_sqrt hm1).trans_eq Real.sqrt_one)
  have hr2 : r ^ 2 ≤ min 1 (min T (1 / (K₀ + 1))) := by
    have hm0 : 0 ≤ min 1 (min T (1 / (K₀ + 1))) := by
      by_contra hneg
      have : Real.sqrt (min 1 (min T (1 / (K₀ + 1)))) = 0 :=
        Real.sqrt_eq_zero'.2 (le_of_lt (not_le.1 hneg))
      linarith
    calc r ^ 2 ≤ Real.sqrt (min 1 (min T (1 / (K₀ + 1)))) ^ 2 :=
          pow_le_pow_left₀ hr.le hrm 2
      _ = _ := Real.sq_sqrt hm0
  have hrT : r ^ 2 ≤ T := hr2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrK : r ^ 2 ≤ 1 / (K₀ + 1) := hr2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsq : (r / Real.sqrt R) ^ 2 = r ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR.le]
  refine ⟨?_, ?_, ?_⟩
  · gcongr
  · rw [hsq]
    gcongr
  · rw [hsq, inv_div, le_div_iff₀ (by positivity)]
    have hK1 : 0 < K₀ + 1 := by linarith
    have h1 : r ^ 2 * (K₀ + 1) ≤ 1 := by
      rw [le_div_iff₀ hK1] at hrK
      exact hrK
    have h2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith

/-- **`hctrl` ⇐ 基点 anchor**（prefix 形数据前提，与 `false_of_selection_eventSlab_P6M` /
`exists_subseq_htraced_extendAt_P6D2` 逐字同形）：存在 `r₀ > 0`，对每个 `r ∈ (0, r₀]`，K 层基点
`(σ n, y n)` 处 `r/√R n` 受控球 eventually 成立。 -/
theorem exists_hctrl_of_anchor0_P6M2
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap qcan : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {records : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
      ((K n).prefixAt (j n).castSucc).toHistory))
    (hrec : ∀ n, ((K n).prefixAt (j n).castSucc).IsCanonicalCutoffRecordFamily (p₀ n) (δb n)
      (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hnot : ∀ n, ¬ ((K n).prefixAt (j n).castSucc).CapWindowPoint (records n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (yG n) (t n) (D n) (θcap n))
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
  obtain ⟨K₀, hK₀, hev⟩ := hsurvive_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi hinit
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hrec hqcan hpar
    hscale hθcap hpinch hslab hjt htj hderG hqR hnot hRt Hs ts ys R rfl HEq.rfl hys hRn
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

/-- **`hctrl` ⇐ K 层数据前提 + selection 输出 + `Pre841`**（前提与 G4c
`false_of_selection_eventSlab_Kdata_P6M` 逐字，去掉 `r₀` / `hr₀` / `hctrl` 与 `hslice` / `hsel`）：
K 层数据经 `RetainedCoreHistoryPrefixTransport` 换成 prefix 形；`hanchor0` 照 G1y
（`hanchor0_of_closure_data_window_q_P6M`，`q = 4R`、`Cq = 4`；`hW` / `hgrad` ⇐ selection，窗口 `hnc` ⇐
`Pre841` κ）；再 `exists_hctrl_of_anchor0_P6M2`。 -/
theorem exists_hctrl_of_Kdata_P6M2 {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy)
    (hC20 : 0 ≤ C2') :
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (j n).castSucc).toHistory)) →
      (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnotK : ∀ n, ¬ (K n).CapWindowPoint (recordsK n) (j n).castSucc (yG n) (t n) (D n)
        (θcap n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
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
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ᶠ n in atTop,
        (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r / Real.sqrt (R n)) := by
  intro P₀ g₀ Ctime phi hphi K j t hjt htj D θcap qcan p₀ p δb ρb recordsK yG hinit hrecK hqcan
    hpar hscaleK hθcap hpinchK0 hslabK hqR hnotK hRt Kh hKh σ y R hσ hyG hRn hRpos d Tn aSeed haT
    hsT has pT seedTrace L hL hgood hwin hdist
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n) := fun n x v hv hR => by
    have hlt : qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x := by
      have := hq0 n
      linarith
    have h := hslabK n (j n) (Fin.castSucc_lt_last _) x v ⟨hv.1, hv.2.trans (htj n)⟩ hlt
    rw [hctime]
    have h0 : 0 ≤ (Ctime : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 :=
      mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
    linarith
  -- prefix 形数据前提（同 G4c 的证明）
  have hrec : ∀ n, ((K n).prefixAt (j n).castSucc).IsCanonicalCutoffRecordFamily (p₀ n) (δb n)
      (ρb n) ((K n).prefixRecords (j n).castSucc (recordsK n)) := fun n =>
    (K n).isCanonicalCutoffRecordFamily_prefixAt _ (hrecK n)
  have hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi := fun n =>
    ⟨(K n).eventSlabsPinched_prefixAt _ (hpinchK0 n), hpinchK0 n (j n)⟩
  have hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) := fun n =>
    (K n).eventSlabsDerivative_prefixAt _ (fun i _ => hslabK n i (Fin.castSucc_lt_last i))
  have hnot : ∀ n, ¬ ((K n).prefixAt (j n).castSucc).CapWindowPoint
      ((K n).prefixRecords (j n).castSucc (recordsK n))
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (yG n) (t n) (D n) (θcap n) :=
    fun n h => hnotK n ((K n).capWindowPoint_of_prefixAt (j n) (recordsK n) h)
  -- `hanchor0`（照 G1y `false_of_selection_eventSlab_final_P6M` 的证明）
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 d.volume_ge
  subst hKh
  have hnc := hnc_window_of_tracedKappa_P6M hjt htj σ hσ y yG hyG R hRpos hRn d.kappa_pos ρnc
    hkappa
  have hρ : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_of_selection_P6M hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_P6M hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT
    has pT seedTrace L hL hgood hwin hdist
  have hq2 : ∀ n, 2 * qcan n ≤ 4 * R n := fun n => by
    have h1 := hqR n
    have h2 := hqcan n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [hRn n]
    linarith
  have hqC : ∀ n, 4 * R n ≤
      4 * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  have hanchor0 := RetainedCoreHistory.hanchor0_of_closure_data_window_q_P6M
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := ρnc) hεcone d.kappa_pos hphi
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hrec hqcan hpar
    hθcap hpinch hslab hjt htj hderG hqR hnot hRt (Cq := 4) (fun n => 4 * R n) hq2 hqC hW hgrad
    hnc hρ
  exact exists_hctrl_of_anchor0_P6M2
    (records := fun n => (K n).prefixRecords (j n).castSucc (recordsK n)) hphi hjt htj hinit hrec
    hqcan hpar (fun n i b => hscaleK n _ b) hθcap hpinch hslab hderG hqR hnot hRt hanchor0
    (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn

/-- **consumer：P6 收口主形去掉 `hctrl`**（G4c `false_of_selection_eventSlab_Kdata_P6M` 去掉
`r₀` / `hr₀` / `hctrl` 三个 binder；`hctrl` 由 `exists_hctrl_of_Kdata_P6M2` 逐字给出）。 -/
theorem false_of_selection_eventSlab_Kdata_ctrl_P6M2 :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (j n).castSucc).toHistory)) →
      (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnotK : ∀ n, ¬ (K n).CapWindowPoint (recordsK n) (j n).castSucc (yG n) (t n) (D n)
        (θcap n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
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
    false_of_selection_eventSlab_Kdata_P6M.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K j t hjt htj D θcap qcan p₀ p δb ρb recordsK yG hinit hrecK hqcan
    hpar hscaleK hθcap hpinchK0 hslabK hqR hnotK hRt Kh hKh σ y R hσ hyG hRn hRpos d Tn aSeed haT
    hsT has pT seedTrace L hL hgood hwin hdist hslice hsel
  have hC20 : 0 ≤ C2' := (zero_le_one.trans hC).trans hC2
  obtain ⟨r₀, hr₀, hctrl⟩ := exists_hctrl_of_Kdata_P6M2 hεcone hC20 hphi hjt htj hinit hrecK hqcan
    hpar hscaleK hθcap hpinchK0 hslabK hqR hnotK hRt Kh hKh σ y R hσ hyG hRn hRpos d Tn aSeed haT
    hsT has pT seedTrace L hL hgood hwin hdist
  exact hB' hC1 hC2 hCt hphi hjt htj hinit hrecK hqcan hpar hscaleK hθcap hpinchK0 hslabK hqR
    hnotK hRt Kh hKh σ y R hσ hyG hRn hr₀ hRpos d (hctrl r₀ hr₀ le_rfl) Tn aSeed haT hsT has pT
    seedTrace L hL hgood hwin hdist hslice hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
