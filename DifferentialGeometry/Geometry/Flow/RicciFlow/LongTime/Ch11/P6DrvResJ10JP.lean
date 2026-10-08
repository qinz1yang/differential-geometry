import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvJ10HelpJP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10RXHSX

/-!
# J10PAY G2：`J10ResE2_DJ`（更小残余）与 `j10ResE_of_2_JP`（PROVED）

`J10ResE_DJ`（`P6DrvResJ10DJ`）的 (A) 类项在桥内付清，残余 `J10ResE2_DJ`：
* (A′) `0 < a₀K n`（`hpin_kernel_A6K` / HI 传播的正性前提；`DrvResE_DW` 的 `a₀K` 只带 HI）；
* (B) `hDmX`（K 帧 `transitionEnd + 10 < modelRadius`）、`hT₀X`（K 帧 `T₀K n ≤ σ n − (1/100)²`）：
  `∀ᶠ → ∀` 尾平移缺口（与 HFIN 同机制）；
* (C) `hsepX`（K 帧形，窗口 `σ − 10⁻⁴`）、`hnot`（prefix 帧，`D := n + 1`、`θcap := 1 − 1/(n+2)`、
  records = `prefixLateRecords_P6N recordsK`）：留给 HSEPX / HNOTF。
`j10ResE_of_2_JP`：K 帧数据（records 包、Q / a₀K / phi 同元组、seed、hgood）+ `J10ResE2_DJ` ⇒ `J10ResE_DJ`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **更小残余（`_JP`，逐字缩写 def，非合同 Prop）**：见文件头。 -/
def J10ResE2_DJ (K : ℕ → RetainedCoreHistory.{u})
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)) (a₀K : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a₀K n) ∧
  (∀ n, StandardCap.transitionEnd + 10 < (qK n).modelRadius) ∧
  (∀ n, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2) ∧
  ∀ (j : ∀ n, Fin (K n).eventCount) (_hjt : ∀ n, (K n).time (j n).castSucc < (σ n : ℝ))
    (_htj : ∀ n, (σ n : ℝ) < (K n).time (j n).succ)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier), (∀ n, HEq (yK n) (yG n)) →
    ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀K n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (qK n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) *
            ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale)⁻¹

/-- **`j10ResE_of_2_JP`（PROVED）**：K 帧数据（records 包、Q / a₀K / phi 同元组、seed、`hgood`）+
`J10ResE2_DJ` ⇒ `J10ResE_DJ`。 -/
theorem j10ResE_of_2_JP {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    {Ctime : ℝ≥0} {ε C1 C2 Cg : ℝ} (hC2 : 0 ≤ C2)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    (hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n)
    {pF : ℕ → CutoffParameters}
    (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Q a₀K : ℕ → ℝ}
    (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
      -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthAK : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time i.succ) (Tn n : ℝ)))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) (h1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (hsm : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) 1)
    (hhalf : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hgoodK : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v)
      (hvs : v ≤ σ n), (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (yK n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z
          →
        (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hRdef : ∀ n, R n = metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n))
    (hRpos : ∀ n, 0 < R n) (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (yK n) ≠ ⊤)
    (hres : J10ResE2_DJ K σ yK qK T₀K recordsK a₀K) :
    J10ResE_RX_HSX K σ yK R qK T₀K := by
  obtain ⟨ha₀pos, hDmK, hT₀Kσ, hres'⟩ := hres
  intro j hjt htj yG hyG H s t G yy hend hGi hat hts Hs ts qX T₀X ys hys
  have hnotK := hres' j hjt htj yG hyG
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (σ n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun _ => rfl
  have hysK : ∀ n, HEq (ys n) (yK n) := fun n => (hys n).trans (hyG n).symm
  -- E seed
  obtain ⟨aE, haTE, pTE, seedE, haa, hseedE, hsmE, hclockE⟩ :=
    ObservedHistory.exists_seedSeq_hsmall_eventPrefix_P6JA hHs' hσ' Tn aSeed haT hsT has pT
      seedTrace hclock hsm hhalf
  have hgoodE := ObservedHistory.hgood_seq_of_eventPrefix_P6JA (haTK := haT) (hsTK := hsT) (hasK :=
    has) (haTE := haTE)
    (hsTE := fun _ => le_rfl) (hasE := haTE)
    hHs' hσ' hysK haa hseedE hgoodK
  have hwinE := ObservedHistory.hwinE_of_clock_P6JA (TnE := ts) (aE := aE)
    (fun _ => le_rfl) (fun _ => rfl) (by norm_num : (0 : ℝ) < 1 / 100) hclockE hRlim
  -- base-point scalar
  have hscalE := ObservedHistory.scal_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n)) rfl
    HEq.rfl hys (fun _ => rfl)
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans ((ObservedHistory.scalar_eq_of_eventPrefix_P6JGH (K n) (j n) (hjt n)
      (htj n) (ts n) (σ n) (hσ' n) (ys n) (yK n) (hysK n)).symm.trans (hscalE n))
  have hσ1 : ∀ n, 1 ≤ (σ n : ℝ) := fun n => by
    have := hhalf n; have := h1 n; have := hclock n; linarith
  have hq0 : ∀ n : ℕ, 0 ≤ max ((n : ℝ) + 1) (Q n) := fun n =>
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1).trans (le_max_left _ _)
  refine ⟨Ctime, phi, hphi, fun n => (n : ℝ) + 1, fun n => 1 - 1 / ((n : ℝ) + 2),
    fun n => max ((n : ℝ) + 1) (Q n), T₀K, qK, pF, fun n => 1 / ((n : ℝ) + 1),
    fun n => (K n).prefixLateRecords_P6N (j n).castSucc (recordsK n),
    fun n i => (K n).geometricCutoffRecordOfPrefix (j n).castSucc
      (recordsFK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i)),
    a₀K, fun n x => hHIK n x,
    fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n),
    fun n i hi => hδFK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi,
    fun n => le_max_left _ _, fun n => ⟨hacc n, le_rfl, hrad n, hord n, le_rfl⟩,
    fun n i hi b => hscaleK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b,
    hbirthAK.mono fun n h i hi b => h (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b,
    fun n => le_rfl,
    fun n => ⟨fun i => hpinchK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK n (j n)⟩,
    fun n => (K n).prefix_eventSlabsDerivative_JP (j n).castSucc (le_max_right _ _)
      (fun i => le_trans (((K n).prefixAt (j n).castSucc).toHistory.time_le_horizon_at i.succ)
        (le_trans (hjt n).le (hsT n))) (hslabT n),
    fun n => (K n).slabJ_derivativeBound_JP (j n) (le_max_right _ _) (hq0 n) (htj n).le (hsT n)
      (hslabT n),
    hnotK, ?_, ?_, ε, C1, C2, Cg, Ctime, ts, aE, haTE, fun _ => le_rfl, haTE, pTE, seedE, L, hL,
    hgoodE, hwinE, 1 / 100, hC2, by norm_num, hsmE, hclockE, a₀K, fun n => (ha₀pos n).le, ?_, ?_,
    ?_, fun n e _ => rfl, hDmK, ?_, trivial⟩
  · -- hT₀
    intro B
    filter_upwards [hT₀K (max B 1) (lt_of_lt_of_le one_pos (le_max_right _ _))] with n hn
    change T₀K n ≤ (σ n : ℝ) -
      B / ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n)
    rw [← hRn n]
    have : B / R n ≤ max B 1 / R n :=
      div_le_div_of_nonneg_right (le_max_left _ _) (hRpos n).le
    linarith
  · -- hRt
    change Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) *
      (σ n : ℝ)) atTop atTop
    have hfun : (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) *
        (σ n : ℝ)) = fun n => R n * (σ n : ℝ) := funext fun n => by rw [← hRn n]
    rw [hfun]
    refine tendsto_atTop_mono (fun n => ?_) hRlim
    have := hRpos n; have := hσ1 n
    nlinarith
  · -- hpinX
    intro n τ x
    exact (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n)
      (ObservedHistory.hpin_kernel_A6K K recordsFK ha₀pos hHIK n) τ x
  · -- hRa
    intro n
    have h1' : (1 : ℝ) ≤ aE n := (h1 n).trans (haa n)
    have hR1 : (1 : ℝ) ≤ R n := by
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith [hRr n]
    exact one_le_mul_of_one_le_of_one_le hR1 h1'
  · -- hT₀X
    intro n
    rw [hclockE n]
    exact hT₀Kσ n
  · -- hfinX
    intro n
    exact (K n).hfinX_of_eventPrefix_JP (j n) (hjt n) (htj n) (Hs n) (hHs' n) (ts n) (σ n) (hσ' n)
      (ys n) (yK n) (hysK n) (Tn n) (aSeed n) (haT n) (hsT n) (has n) (pT n) (seedTrace n)
      (aE n) (haTE n) le_rfl (haTE n) (pTE n) (seedE n) (hseedE n) (hfinK n)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
