import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardAlignedA2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDiagonalP6D2

/-!
# body 帧 anchor：G9″ guarded 孪生的 FRESH → body `hvolK` 替换（O-CH11-KERNB-A6 / W7 G3a，`_A6K`）

BCBD-A2 G6 `sliceBCBD_kernel_fresh_{theta_ev,sep}_noProtC_alignedG_A2B`（无 `hdistW`）逐字孪生，只做：
FRESH 族（`nr Aκ κ Tκ hκ hWK hTκ htimeS hvolS hnrS`）与 `hwinF` / `hgate` 删除，换成 kernel body 字段
`κd hκd hvolK`（NotKBodyT 逐字形）；`hnc` 由 `exists_tracedKappa_of_kseq_P6D2 hvolK` →
`hnc_window_sameStageG_A2B`（guard 前提弃用）付，`ρ := ρnc`。结论逐字（rings 层 `hanchor0` 形）。
生成：`build-logs/scratch/O-CH11-KERNB-A6/gen/gen3a.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **G5″ body 帧孪生（`_A6K`）**：`sliceBCBD_kernel_fresh_theta_ev_noProtC_alignedG_A2B` 逐字，
FRESH / `hwinF` / `hgate` 换 body `hκd hvolK`。 -/
theorem ObservedHistory.sliceBCBD_kernel_body_theta_ev_alignedG_A6K
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hnotK : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le) hnat
  have hRlimG : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨-, -, Dp, -, -, hD, -, -, -, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot' : ∀ᶠ n in atTop, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θ₀ *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    hnotK.mono fun n hn => by
      rw [hD n]
      exact (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n) (yG n) hn
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hslabs := hslabs_of_sepRho_prefixDt_P6SB3 hC20 (by linarith) hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hcanK hacc hrad hord hT₀ ρs hsepρ hpre1 hpre2
  have hCg1 : (1 : ℝ) ≤ Cg := by linarith
  have hCg0' : (0 : ℝ) ≤ Cg := by linarith
  have hdistWG := ObservedHistory.hdistWStar_of_firstExit_A2B (Ctime' := Ctime') hC20 hCg1 hjt
    htj σ hσ y R hRpos hR1 Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀
    hpin hRa recordsK hcanK hacc hrad hT₀ T₀X hT₀X hOldX hdσ
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 hvolK
  have hnc := ObservedHistory.hnc_window_sameStageG_A2B (Ctime' := Ctime') hCg0' hjt htj σ hσ y yG
    hyG R hRpos hRn hκd ρnc
    (fun D T hD hT => (hkappa D T hD hT).mono fun _ hn x hx v hvt hvT _ _ => hn x hx v hvt hvT)
  have hρ : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgradG_of_selection_sameSlab_Cg_A2B hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hder := hderSelG_of_selection_sameSlab_Cg_A2B hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hR0 : ∀ n, 0 < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_starG_theta_ev_A2B (θcap := fun _ => θ₀)
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := ρnc) hεcone hκd hphi hθ₀
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    (fun _ => le_rfl) hpinch hjt htj hnot' hT₀' hRt hRlimG hR0 (Cq := Cg)
    (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

/-- **G9″ body 帧孪生（`_A6K`）**：`sliceBCBD_kernel_fresh_sep_noProtC_alignedG_A2B` 逐字，
FRESH / `hwinF` / `hgate` 换 body `hκd hvolK`。PROVISIONAL[G9″ 原清单 − hdistW − FRESH − kernel 帧
`hwinF / hgate`]。 -/
theorem ObservedHistory.sliceBCBD_kernel_body_sep_alignedG_A6K
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad2 : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale)
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_sep_P6SB2 hC20 hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hsepT hθ₀ hRlt hcanK hacc hrad2 hord hsep4
  have haccE : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (hacc n).trans hn
  have hnotKev : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    filter_upwards [hceil, haccE] with n hc ha
    rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
    have hx : ‖x.val‖ < (p n).modelRadius := lt_of_lt_of_le h2 (hrad2 n)
    have hS := hlow ((K n).toHistory.event i) ha (le_trans (by omega) (hord n))
      ((recordsK n i hi).static b) (hcanK n i hi b) x hx
    rw [← h1] at hS
    have hC := hc i hi hl A b h3
    have hP := hsep4 n i hi b hl h3
    linarith
  exact sliceBCBD_kernel_body_theta_ev_alignedG_A6K (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj) (hcanK := hcanK) (hacc := hacc)
    (hrad := fun n => le_trans (by linarith) (hrad2 n)) (hord := hord) (hpinchK0 := hpinchK0)
    (hnotK := hnotKev) (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y)
    (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀) (Tn := Tn)
    (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace)
    (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin) (hr := hr)
    (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀) (hpin := hpin) (hRa := hRa)
    (T₀X := T₀X) (hT₀X := hT₀X) (hOldX := hOldX) (hdσ := hdσ) (hκd := hκd) (hvolK := hvolK)
    (ρs := ρs) (hsepρ := hsepρ) (hpre1 := hpre1)
    (hpre2 := hpre2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
