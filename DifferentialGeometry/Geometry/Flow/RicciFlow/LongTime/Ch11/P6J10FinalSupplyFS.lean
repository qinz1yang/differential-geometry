import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSlotsFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalAuxFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10JP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteBridgeP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6JA

/-!
# FSUP W2-C：final 帧 `Cst hsurv hext` 的引擎供给（`j10ResE_of_2_JP` 的 final 孪生，`_FS`）

`finalSurvExt_of_engine_FS`（PROVED）：K 帧数据（records 包 `qK T₀K recordsK`、`Q / a₀K / phi` 同元组、
seed、`hgood`、final 帧 `hnot`（`hnotK_final_cww_P6HN` 形）、event / final slab 的 Dt 与 pinching）
⇒ `∃ Cst, hsurvive ∧ hextend`（K 帧，`DrvResF_DT` 的 `Cst hsurv hext` 三项逐字）。
证明：`H := K.prefixAt last`、`G := finalSlab.restrictIncoming`、`s := horizon`、`t := σ`、
`Hs := finalE_FS`；J10 包各项由 K 帧数据经 final 搬运件供给（seed：
`exists_seedSeq_hsmall_final_P6JA` / `hgood_seq_final_P6JA`；scalar：`scalar_eq_final_P6JAH` +
`scal_of_extendAt_P6D2`；HI / records / `hfinX` / `hsepT`：`P6J10FinalAuxFS`；`hnot`：
`capNot_mono_HNF` + `not_capWindowPoint_prefix_of_late_P6N` 于 `Fin.last`），再经
`drvSlots_Hs_of_J10_sepT_FS`（HSEPX producer）与 `hsurvive/hextend_K_of_final_FS`。
无新 binder；PROVED 相对列出的 K 帧前提（全部为引擎 / T0K 供给形，无 `∀ records` 槽）。
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

namespace ObservedHistory

/-- **final 帧 `Cst hsurv hext` 引擎供给（`_FS`，PROVED 相对 K 帧前提）**。 -/
theorem finalSurvExt_of_engine_FS
    {K : ℕ → RetainedCoreHistory.{u}} {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    (hevF : ∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).horizon)
    {Ctime : ℝ≥0} {ε C1 C2 Cg : ℝ} (hC2 : 0 ≤ C2)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    (hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n)
    (hT₀Kσ : ∀ n, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recordsK n i hi).static b).neck.scale)
    {pF : ℕ → CutoffParameters}
    (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Q a₀K : ℕ → ℝ}
    (ha₀pos : ∀ n, 0 < a₀K n)
    (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
      -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthAK : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi)
    (hpinchFK : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab ((hevF n).1.trans (hevF n).2)).restrictIncoming le_rfl
        ((hevF n).1.trans (hevF n).2) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phi)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time i.succ) (Tn n : ℝ)))
    (hderT : ∀ n, (((K n).finalSlab ((hevF n).1.trans (hevF n).2)).restrictIncoming le_rfl
        ((hevF n).1.trans (hevF n).2) le_rfl).DerivativeBoundBefore Ctime (Q n)
        (min (K n).horizon (Tn n : ℝ)))
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
    (hDmK : ∀ n, StandardCap.transitionEnd + 10 < (qK n).modelRadius)
    (hnot : ∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
      HEq (yK n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (qK n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹)) :
    ∃ (Cst : ℝ≥0),
    (∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric
            ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n) (A / Real.sqrt (R n)),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            z ≤ Q * R n) →
        (K n).toHistory.isTracedRegion (σ n) (yK n) (A / Real.sqrt (R n)) (T / R n) (Kc * R n)) ∧
    (∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable (fun n => (K n).toHistory) σ yK R σs T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σs i)).toHistory.stageMetric
          ((K (σs i)).toHistory.activeStage (σ (σs i))) (σ (σs i))) (yK (σs i))
          (A / Real.sqrt (R (σs i))),
      ∀ (w : Icc (0 : ℝ) (K (σs i)).toHistory.horizon),
        (w : ℝ) = σ (σs i) - T' / R (σs i) →
      ∀ (hwt : w ≤ σ (σs i))
        (Bt : BackwardPointTrace (K (σs i)).toHistory ((K (σs i)).toHistory.activeStage w)
          ((K (σs i)).toHistory.activeStage (σ (σs i)))
          ((K (σs i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σs i)).toHistory.stageMetric ((K (σs i)).toHistory.activeStage w) w)
          (Bt.point ((K (σs i)).toHistory.activeStage w) le_rfl
            ((K (σs i)).toHistory.activeStage_mono hwt)) ≤
          M * R (σs i)) →
      DepthExtendable (fun n => (K n).toHistory) σ yK R σs
        (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) := by
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hevF n).1.trans (hevF n).2
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hact : ∀ n, (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount := fun n =>
    le_antisymm (Fin.le_last _) ((K n).toHistory.le_activeStage (σ n) _ (hevF n).1.le)
  let yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (yK n)
  have hyG : ∀ n, HEq (yK n) (yG n) := fun n => (cast_heq _ _).symm
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).finalE_FS (hfin n) (hevF n).1 (hevF n).2).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime ((K n).prefixAt_time_last _)
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
      ((K n).final_initial (hfin n)) (hevF n).1 (hevF n).2
  have hHs' : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((hevF n).1.trans (hevF n).2)).restrictIncoming
        le_rfl ((hevF n).1.trans (hevF n).2) le_rfl)
      ((K n).final_initial ((hevF n).1.trans (hevF n).2)) (hevF n).1 (hevF n).2).toHistory :=
    fun _ => rfl
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun _ => rfl
  have hAτ : ∀ n, @Eq (Fin ((K n).toHistory.eventCount + 1)) ((Hs n).activeStage (ts n))
      ((K n).toHistory.activeStage (σ n)) := fun n =>
    (K n).activeStage_final_P6M (hfin n) (hevF n).1 (hevF n).2 (ts n) (σ n) (hσ' n)
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hAτ n).symm) (yK n)
  have hysK : ∀ n, HEq (ys n) (yK n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  -- E seed
  obtain ⟨aE, haTE, pTE, seedE, haa, hseedE, hsmE, hclockE⟩ :=
    exists_seedSeq_hsmall_final_P6JA hHs' hσ' Tn aSeed haT hsT has pT seedTrace hclock hsm hhalf
  have hgoodE := hgood_seq_final_P6JA (haTK := haT) (hsTK := hsT) (hasK := has) (haTE := haTE)
    (hsTE := fun _ => le_rfl) (hasE := haTE) hHs' hσ' hysK haa hseedE hgoodK
  have hwinE := hwinE_of_clock_P6JA (TnE := ts) (aE := aE) (fun _ => le_rfl) (fun _ => rfl)
    (by norm_num : (0 : ℝ) < 1 / 100) hclockE hRlim
  -- 基点标量
  have hscalE := scal_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    (s := fun n => (K n).horizon) (t := fun n => (σ n : ℝ)) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial (hfin n))
    (fun n => (hevF n).1) (fun n => (hevF n).2) Hs ts ys
    (fun n => (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow.scalar
      (σ n) (yG n)) rfl HEq.rfl hys (fun _ => rfl)
  have hRn : ∀ n, R n =
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow.scalar
        (σ n) (yG n) := fun n =>
    (hRdef n).trans ((scalar_eq_final_P6JAH (K n) (hfin n) (hevF n).1 (hevF n).2 (ts n) (σ n)
      (hσ' n) (ys n) (yK n) (hysK n)).symm.trans (hscalE n))
  have hσ1 : ∀ n, 1 ≤ (σ n : ℝ) := fun n => by
    have := hhalf n; have := h1 n; have := hclock n; linarith
  have hq0 : ∀ n : ℕ, 0 ≤ max ((n : ℝ) + 1) (Q n) := fun n =>
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1).trans (le_max_left _ _)
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n := hRlim.eventually_ge_atTop 1
  have hsum := drvSlots_Hs_of_J10_sepT_FS (Ctime := Ctime) (phi := phi) hphi
    (D := fun n => (n : ℝ) + 1) (θcap := fun n => 1 - 1 / ((n : ℝ) + 2))
    (qcan := fun n => max ((n : ℝ) + 1) (Q n)) (s := fun n => (K n).horizon)
    (t := fun n => (σ n : ℝ)) (T₀ := T₀K) (p := qK) (pF := pF)
    (δb := fun n => 1 / ((n : ℝ) + 1))
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (records := fun n => (K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n))
    (fun n i => (K n).geometricCutoffRecordOfPrefix (Fin.last (K n).eventCount)
      (recordsFK n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i)))
    (G := fun n => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    (y := yG) (a₀ := a₀K) (fun n x => hHIK n x)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial (hfin n))
    (fun n => (K n).prefixLateRecords_hcan_P6N (Fin.last (K n).eventCount) (recordsK n)
      (hcanK n))
    (fun n i hi => hδFK n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i) hi)
    (fun n => le_max_left _ _) (fun n => ⟨hacc n, le_rfl, hrad n, hord n, le_rfl⟩)
    (fun n i hi b => hscaleK n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i)
      hi b)
    (hbirthAK.mono fun n h i hi b =>
      h (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i) hi b)
    (fun n => le_rfl)
    (fun n => ⟨fun i => hpinchK n (Fin.castLE (Nat.le_of_lt_succ
      (Fin.last (K n).eventCount).isLt) i), hpinchFK n⟩)
    (fun n => (K n).prefix_eventSlabsDerivative_JP (Fin.last (K n).eventCount) (le_max_right _ _)
      (fun i => le_trans (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.time_le_horizon_at
        i.succ) (le_trans (hevF n).1.le (hsT n))) (hslabT n))
    (fun n => (hevF n).1) (fun n => (hevF n).2)
    (fun n => (K n).finalSlab_derivativeBound_FS (hfin n) (le_max_right _ _) (hq0 n)
      (hevF n).2.le (hsT n) (hderT n))
    (fun n => RetainedCoreHistory.capNot_mono_HNF ((K n).prefixAt (Fin.last (K n).eventCount))
      (Fin.last _) _ (yG n) le_rfl le_rfl
      ((K n).not_capWindowPoint_prefix_of_late_P6N (Fin.last (K n).eventCount) (recordsK n)
        (yG n) (hnot n (yG n) (hyG n))))
    (by
      intro B
      filter_upwards [hT₀K (max B 1) (lt_of_lt_of_le one_pos (le_max_right _ _))] with n hn
      change T₀K n ≤ (σ n : ℝ) - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).flow.scalar (σ n) (yG n)
      rw [← hRn n]
      have : B / R n ≤ max B 1 / R n :=
        div_le_div_of_nonneg_right (le_max_left _ _) (hRpos n).le
      linarith)
    (by
      change Tendsto (fun n => (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).flow.scalar (σ n) (yG n) * (σ n : ℝ)) atTop atTop
      have hfun : (fun n => (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
          le_rfl).flow.scalar (σ n) (yG n) * (σ n : ℝ)) = fun n => R n * (σ n : ℝ) :=
        funext fun n => by rw [← hRn n]
      rw [hfun]
      refine tendsto_atTop_mono (fun n => ?_) hRlim
      have := hRpos n; have := hσ1 n
      nlinarith)
    Hs ts ys R rfl HEq.rfl hys hRn hRpos hRlim ((fun n => aE n) |> fun _ => ts) aE haTE
    (fun _ => le_rfl) haTE pTE seedE L hL hgoodE hwinE hC2 (by norm_num) hsmE hclockE a₀K
    (fun n => (ha₀pos n).le)
    (fun n τ x => (K n).inFixedHI_final_FS (hfin n) (hevF n).1 (hevF n).2
      (hpin_kernel_A6K K recordsFK ha₀pos hHIK n) τ x)
    (fun n => by
      have h1' : (1 : ℝ) ≤ aE n := (h1 n).trans (haa n)
      have hR1' : (1 : ℝ) ≤ R n := by
        have : (0 : ℝ) ≤ n := n.cast_nonneg
        linarith [hRr n]
      exact one_le_mul_of_one_le_of_one_le hR1' h1')
    qK T₀K (fun n => by rw [hclockE n]; exact hT₀Kσ n)
    (fun n => (K n).finalPrefixRecords_FS (hfin n) (hevF n).1 (hevF n).2 (recordsK n))
    (fun n e _ => rfl)
    (fun n => (K n).finalPrefixRecords_hcan_FS (hfin n) (hevF n).1 (hevF n).2 (recordsK n)
      (hcanK n))
    hDmK hacc (fun n => (Nat.le_add_left 2 n).trans (hord n))
    (hsepT_final_FS (r := 1 / 100) (by norm_num) K (fun n => (σ n : ℝ)) (fun n => (hevF n).1)
      (fun n => (hevF n).2) σ R hR1 ts hσ' recordsK hsepK)
    (fun n => (K n).hfinX_final_FS (hfin n) (hevF n).1 (hevF n).2 (Hs n) rfl (ts n) (σ n)
      (hσ' n) (ys n) (yK n) (hysK n) (Tn n) (aSeed n) (haT n) (hsT n) (has n) (pT n)
      (seedTrace n) (aE n) (haTE n) le_rfl (haTE n) (pTE n) (seedE n) (hseedE n) (hfinK n))
  obtain ⟨Cst, hsurvE, hextE⟩ := hsum
  exact ⟨Cst, hsurvive_K_of_final_FS hHs' hσ' hysK hsurvE,
    hextend_K_of_final_FS hHs' hσ' hysK hextE⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
