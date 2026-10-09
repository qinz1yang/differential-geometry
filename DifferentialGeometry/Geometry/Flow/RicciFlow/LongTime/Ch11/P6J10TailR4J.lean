import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TailJT

/-!
# R4J10 G1：J10 块三引理的 `hRr` 孪生（`_R4J`）

R4 中心 `(t, y′)` 的归一化是 `R_c := scalar(t, y′)`，`R/2 < R_c < 2R`，故 `(n : ℝ) + 1 ≤ R_c` 不成立。
`hRr` 在 J10PAY / J10TAIL 中只用于 `Tendsto R atTop atTop` 与 `1 ≤ R n`；三个孪生把它换成这两项
（尾平移版取 `∀ᶠ 1 ≤ R`、`∀ᶠ hhalf`，并入同一个 `N₁`）：
* `j10ResE_of_2_R4J` ← `j10ResE_of_2_JP`；
* `j10Blk_of_J10ResE_R4J` ← `j10Blk_of_J10ResE_JT`；
* `j10Blk_of_tail_R4J` ← `j10Blk_of_tail_JT`。
陈述与原件逐字相同，唯一差异是上述 `hRr` / `hhalf` 的弱化；证明由 `build-logs/scratch/R4J10/gen/g1.py`
从 tracked 文本机械生成。无新顶层 binder。
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

open ObservedHistory (DepthExtendable)

/-- **`j10ResE_of_2_R4J`（`_R4J`，PROVED）**：`hRr` 换为 `hRlim` + `1 ≤ R`。
K 帧数据（records 包、Q / a₀K / phi 同元组、seed、`hgood`）+
`J10ResE2_DJ` ⇒ `J10ResE_DJ`。 -/
theorem j10ResE_of_2_R4J {K : ℕ → RetainedCoreHistory.{u}}
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
    (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop) (hR1all : ∀ n, 1 ≤ R n)
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
    have hR1 : (1 : ℝ) ≤ R n := hR1all n
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

/-- **J10 块（`_R4J`，PROVED）**：`hRr` 换为 `hRlim`。
`J10ResE_RX_HSX` + DrvResE 合取 1/3/4/6 + `hev` ⇒ `J10Blk_JT`
（`drvResE_DW_of_RX_HSX` 的 J10 段逐字抽出）。 -/
theorem j10Blk_of_J10ResE_R4J {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    (recK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n))
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK n i hi).static b).neck.scale)
    (hcanK : ∀ n i hi b, ((recK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    (hRdef : ∀ n, R n = metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n))
    (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hev : ∀ n, ∃ j : Fin (K n).eventCount, (K n).time j.castSucc < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).time j.succ)
    (hJ : J10ResE_RX_HSX K σ y R qK T₀K) :
    J10Blk_JT K σ y R := by
  choose j hjt htj using hev
  have hact : ∀ n, (K n).toHistory.activeStage (σ n) = (j n).castSucc := fun n =>
    activeStage_eq_of_mem_slab_HSX (K n) (j n) (σ n) (hjt n).le (htj n)
  let yG : ∀ n, ((K n).stage (j n).castSucc).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (y n)
  have hyG : ∀ n, HEq (y n) (yG n) := fun n => (cast_heq _ _).symm
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (σ n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun _ => rfl
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (σ n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  obtain ⟨Ctime_e, phi_e, hphi_e, D_e, θcap_e, qcan_e, T₀_e, p_e, pF_e, δb_e, records_e, recordsF_e,
    a₀_e, hHI_e, hcan_e, hδF_e, hqcan_e, hpar_e, hscale_e, hbirthA_e, hθcap_e, hpinch_e,
    hslab_e, hderG_e, hnot_e, hT₀_e, hRt_e, eps_e, C1'_e, C2'_e, Cg_e, Ctime'_e, Tn_e,
    aSeed_e, haT_e, hsT_e, has_e, pT_e, seedTrace_e, L_e, hL_e, hgood_e, hwin_e, r_e, hC2_e,
    hr_e, hsmall_e, hclock_e, a₀X_e, ha₀X_e, hpinX_e, hRa_e, hT₀X_e,
    hOldX_e, hDmX_e, hfinX_e, -⟩ := hJ j hjt htj yG hyG ys hys
  have hscalE := ObservedHistory.scal_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n)) rfl
    HEq.rfl hys (fun _ => rfl)
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans ((ObservedHistory.scalar_eq_of_eventPrefix_P6JGH (K n) (j n) (hjt n)
      (htj n) (ts n) (σ n) (hσ' n) (ys n) (y n) (hysK n)).symm.trans (hscalE n))
  have hsepT_b := ObservedHistory.hsepT_eventPrefix_of_drvSep_HSX hr_e
    K j (fun n => (σ n : ℝ)) hjt htj σ R (hRlim.eventually_ge_atTop 1) ts hσ' recK hsep
  exact ObservedHistory.drvSlots_K_of_J10_sepT_HSX
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (t := fun n => (σ n : ℝ)) (y := yG)
    (Ctime := Ctime_e) (phi := phi_e) (hphi := hphi_e) (D := D_e) (θcap := θcap_e) (qcan := qcan_e)
    (T₀ := T₀_e) (p := p_e) (pF := pF_e) (δb := δb_e) (records := records_e)
    (recordsF := recordsF_e) (a₀ := a₀_e) (hHI := hHI_e) (hcan := hcan_e) (hδF := hδF_e)
    (hqcan := hqcan_e) (hpar := hpar_e) (hscale := hscale_e) (hbirthA := hbirthA_e)
    (hθcap := hθcap_e) (hpinch := hpinch_e) (hslab := hslab_e) (hderG := hderG_e) (hnot := hnot_e)
    (hT₀ := hT₀_e) (hRt := hRt_e) (eps := eps_e) (C1' := C1'_e) (C2' := C2'_e) (Cg := Cg_e)
    (Ctime' := Ctime'_e) (Tn := Tn_e) (aSeed := aSeed_e) (haT := haT_e) (hsT := hsT_e)
    (has := has_e) (pT := pT_e) (seedTrace := seedTrace_e) (L := L_e) (hL := hL_e)
    (hgood := hgood_e) (hwin := hwin_e) (r := r_e) (hC2 := hC2_e) (hr := hr_e) (hsmall := hsmall_e)
    (hclock := hclock_e) (a₀X := a₀X_e) (ha₀X := ha₀X_e) (hpinX := hpinX_e) (hRa := hRa_e)
    (qX := qK) (T₀X := T₀K) (hT₀X := hT₀X_e)
    (recordsX := fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recK n))
    (hOldX := hOldX_e)
    (hcanX := fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recK n) (hcanK n))
    (hDmX := hDmX_e) (haccX := hacc) (hmX := fun n => (Nat.le_add_left 2 n).trans (hord n))
    (hsepT := hsepT_b)
    (hfinX := hfinX_e)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys R rfl HEq.rfl hys hRn hRpos hRlim
    K j (fun n => (σ n : ℝ)) hjt htj hHs' σ y hσ' hysK

/-- **J10 块 ⇐ 尾平移（`_R4J`，PROVED）**：`hRr` 换为 `hRlim` + `∀ᶠ 1 ≤ R`，
`hhalf` 换为 `∀ᶠ`。
`j10ResE_of_2_R4J` 前提（原族）+ DrvResE 合取 1 + `hev` +
`J10ResE3_JT` + `0 < a₀K` + `∀ᶠ hT₀X` ⇒ `J10Blk_JT`。取 `N = N₀ + N₁`（`N₀ > transitionEnd + 10`、
`∀ n ≥ N₁` 有 `hT₀X`），平移族上 `j10ResE_of_2_R4J` + `j10Blk_of_J10ResE_R4J`，再 `j10Blk_of_shift_JT`。 -/
theorem j10Blk_of_tail_R4J {K : ℕ → RetainedCoreHistory.{u}}
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
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n)
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
    (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (yK n) ≠ ⊤)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hev : ∀ n, ∃ j : Fin (K n).eventCount, (K n).time j.castSucc < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).time j.succ)
    (ha₀ : ∀ n, 0 < a₀K n) (hT₀X : ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (h3 : J10ResE3_JT K σ yK qK T₀K recordsK) :
    J10Blk_JT K σ yK R := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hT₀X.and (hR1.and hhalf))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
  have hNd : StandardCap.transitionEnd + 10 < ((N₀ + N₁ : ℕ) : ℝ) := by
    have : (N₀ : ℝ) ≤ ((N₀ + N₁ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N₀ N₁
    linarith
  have hJ2 := j10ResE2_shift_of_3_JT (a₀K := a₀K) (N₀ + N₁) hNd hrad ha₀
    (fun n => (hN₁ (n + (N₀ + N₁)) (by omega)).1) h3
  have hJ := j10ResE_of_2_R4J (K := fun n => K (n + (N₀ + N₁)))
    (σ := fun n => σ (n + (N₀ + N₁))) (yK := fun n => yK (n + (N₀ + N₁)))
    (R := fun n => R (n + (N₀ + N₁))) (Ctime := Ctime) (ε := ε) (C1 := C1) (C2 := C2) (Cg := Cg)
    hC2 (qK := fun n => qK (n + (N₀ + N₁))) (T₀K := fun n => T₀K (n + (N₀ + N₁)))
    (recordsK := fun n => recordsK (n + (N₀ + N₁)))
    (fun n => hcanK (n + (N₀ + N₁)))
    (fun n => (hacc (n + (N₀ + N₁))).trans (shiftInv_JT n (N₀ + N₁)))
    (fun n => (shiftLe_JT n (N₀ + N₁)).trans (hrad (n + (N₀ + N₁))))
    (fun n => le_trans (by omega) (hord (n + (N₀ + N₁))))
    (fun T hT => eventually_add_JT (N₀ + N₁) (hT₀K T hT))
    (pF := fun n => pF (n + (N₀ + N₁))) (fun n => recordsFK (n + (N₀ + N₁)))
    (fun n i hi => (hδFK (n + (N₀ + N₁)) i hi).trans (shiftInv_JT n (N₀ + N₁)))
    hphi (Q := fun n => Q (n + (N₀ + N₁))) (a₀K := fun n => a₀K (n + (N₀ + N₁)))
    (fun n => hHIK (n + (N₀ + N₁)))
    (fun n i hi b => (shiftScale_JT n (N₀ + N₁) (Q (n + (N₀ + N₁)))).trans
      (hscaleK (n + (N₀ + N₁)) i hi b))
    (eventually_add_JT (N₀ + N₁) hbirthAK) (fun n => hpinchK (n + (N₀ + N₁)))
    (fun n => Tn (n + (N₀ + N₁))) (fun n => aSeed (n + (N₀ + N₁))) (fun n => haT (n + (N₀ + N₁)))
    (fun n => hsT (n + (N₀ + N₁))) (fun n => has (n + (N₀ + N₁))) (fun n => pT (n + (N₀ + N₁)))
    (fun n => seedTrace (n + (N₀ + N₁))) (fun n => hslabT (n + (N₀ + N₁)))
    (fun n => hclock (n + (N₀ + N₁))) (fun n => h1 (n + (N₀ + N₁)))
    (fun n => hsm (n + (N₀ + N₁))) (fun n => (hN₁ (n + (N₀ + N₁)) (by omega)).2.2)
    (L := fun n => L (n + (N₀ + N₁))) (hL.comp (tendsto_add_atTop_nat (N₀ + N₁)))
    (fun n => hgoodK (n + (N₀ + N₁))) (fun n => hRdef (n + (N₀ + N₁)))
    (fun n => hRpos (n + (N₀ + N₁)))
    (hRlim.comp (tendsto_add_atTop_nat (N₀ + N₁)))
    (fun n => (hN₁ (n + (N₀ + N₁)) (by omega)).2.1)
    (fun n => hfinK (n + (N₀ + N₁))) hJ2
  exact j10Blk_of_shift_JT (N₀ + N₁) (j10Blk_of_J10ResE_R4J (fun n => recordsK (n + (N₀ + N₁)))
    (fun T hT C hC => eventually_add_JT (N₀ + N₁) (hsep T hT C hC))
    (fun n => hcanK (n + (N₀ + N₁)))
    (fun n => (hacc (n + (N₀ + N₁))).trans (shiftInv_JT n (N₀ + N₁)))
    (fun n => le_trans (by omega) (hord (n + (N₀ + N₁))))
    (fun n => hRdef (n + (N₀ + N₁))) (fun n => hRpos (n + (N₀ + N₁)))
    (hRlim.comp (tendsto_add_atTop_nat (N₀ + N₁)))
    (fun n => hev (n + (N₀ + N₁))) hJ)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
