import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDShiftFinalG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDiagonalP6D2

/-!
# final body 帧 anchor：G9″ final guarded 孪生的 FRESH → body `hvolK`（O-CH11-KFPROD G4a，`_KFP`）

KERNB-A6 G3a / G3b（`P6SliceBCBDBody{Anchor,Shift}A6K`）的 final 帧对应，底座换 G9SHIFT final 链：
* `sliceBCBD_final_fresh_{theta_ev,sep}_noProtC_alignedG_seq_G9S`（σ 在 final slab，无 `hdistW`）逐字孪生，
  逐 n FRESH 族（`nr Tκ Aκ κ hκ hWK hTκ htimeS hvolS hnrS`）与 `hwinF` / `hgate` 换 kernel body 字段
  `κd hκd hvolK`；`hnc` 由 `exists_tracedKappa_of_kseq_P6D2 hvolK` →
  `hnc_window_sameStageGF_G9S` 付，`ρ := ρnc`；
* ∀n 平移孪生（`…_seq_ev_G9S`）：同上替换，`hdσ` 改 eventually（并入平移阈值 N，取代原 `hTκ` 的位置）。
结论逐字（final rings 层 `hanchor0` 形）。生成：`build-logs/scratch/O-CH11-KFPROD/gen/gen4.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **final G5″ body 帧孪生（`_KFP`）**：见文件头。 -/
theorem ObservedHistory.sliceBCBD_final_body_theta_ev_alignedG_KFP
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (hnotK : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (Fin.last (K n).eventCount))
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
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
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le) hnat
  have hRlimG : Tendsto (fun n => (G n).flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨-, -, Dp, -, -, hD, -, -, -, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot' : ∀ᶠ n in atTop, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static
              b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤ θ₀ *
          ((((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static
              b).neck.scale
            )⁻¹ :=
    hnotK.mono fun n hn => by
      rw [hD n]
      exact (K n).not_capWindowPoint_prefix_of_late_P6N (Fin.last (K n).eventCount) (recordsK n) (yG
          n) hn
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / (G n).flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt)
        i),
      hpinchF n⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (Fin.last (K n).eventCount) (recordsK n)
      (hcanK n)
  have hslabs := ObservedHistory.hslabs_of_sepRho_prefixDtF_G9S hC20 (by linarith) htl htK G hG σ hσ
      y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hcanK hacc hrad hord hT₀ ρs hsepρ hpre1 hpre2
  have hCg1 : (1 : ℝ) ≤ Cg := by linarith
  have hCg0' : (0 : ℝ) ≤ Cg := by linarith
  have hdistWG := ObservedHistory.hdistWStarF_of_firstExit_G9S (Ctime' := Ctime') hC20 hCg1 htK σ hσ
      y R hRpos hR1 Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀
    hpin hRa recordsK hcanK hacc hrad hT₀ T₀X hT₀X hOldX hdσ
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 hvolK
  have hnc := ObservedHistory.hnc_window_sameStageGF_G9S (Ctime' := Ctime') hCg0' htl htK G hG σ hσ
    y yG hyG R hRpos hRn hκd ρnc
    (fun D T hD hT => (hkappa D T hD hT).mono fun _ hn x hx v hvt hvT _ _ => hn x hx v hvt hvT)
  have hρ : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := ObservedHistory.hW_final_Cg_G9S (fun n => (htl n).trans (htK n)) hG htl σ hσ y yG hyG R
      hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgradGF_of_selection_sameSlab_Cg_G9S hC20 htl htK G hG σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hder := hderSelGF_of_selection_sameSlab_Cg_G9S htl htK G hG σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hR0 : ∀ n, 0 < (G n).flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * (G n).flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_starG_theta_ev_A2B (θcap := fun _ => θ₀)
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := G)
    (s := fun n => (K n).horizon) (y := yG) (ρ := ρnc) hεcone hκd hphi hθ₀
    (fun n => (K n).prefixAt_time_last _) (fun n => by rw [hG n]; exact (K n).final_initial ((htl
        n).trans (htK n))) hcan hpar
    (fun _ => le_rfl) hpinch htl htK hnot' hT₀' hRt hRlimG hR0 (Cq := Cg)
    (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

/-- **final G9″ body 帧孪生（`_KFP`）**：见文件头。 -/
theorem ObservedHistory.sliceBCBD_final_body_sep_alignedG_KFP
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad2 : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale)
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_sep_final_P6HK hC20 (fun n => (htl n).trans
      (htK n)) htl htK
    σ hσ y yG hyG R hRpos hR1 (fun n => by rw [hRn n, hG n]) Tn aSeed haT hsT has pT seedTrace L hL
        hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hsepT hθ₀ hRlt hcanK hacc hrad2 hord hsep4
  have haccE : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (hacc n).trans hn
  have hnotKev : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (Fin.last (K n).eventCount))
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
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
  exact sliceBCBD_final_body_theta_ev_alignedG_KFP (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (htl := htl) (htK := htK) (G := G) (hG := hG) (hcanK := hcanK) (hacc
        := hacc)
    (hrad := fun n => le_trans (by linarith) (hrad2 n)) (hord := hord) (hpinchK0 := hpinchK0)
        (hpinchF := hpinchF)
    (hnotK := hnotKev) (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y)
    (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀) (Tn := Tn)
    (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace)
    (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin) (hr := hr)
    (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀) (hpin := hpin) (hRa := hRa)
    (T₀X := T₀X) (hT₀X := hT₀X) (hOldX := hOldX) (hdσ := hdσ) (hκd := hκd) (hvolK := hvolK)
    (ρs := ρs) (hsepρ := hsepρ) (hpre1 := hpre1)
    (hpre2 := hpre2)

namespace ObservedHistory

/-- **final G9″ body 帧 ∀n 平移孪生（`_KFP`）**：见文件头。 -/
theorem sliceBCBD_final_body_sep_alignedG_ev_KFP
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ᶠ n : ℕ in atTop, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ᶠ n : ℕ in atTop, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hRle : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
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
    (hdσ : ∀ᶠ n in atTop, riemannianEDistOf ((Kh n).stageMetric
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
    (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hsepEv := hsepT_hsep4_ev_of_sepRhoF_G9S (Ctime' := Ctime') (Cg := Cg) (θ₀ := θ₀)
    (recordsK := recordsK) R hRpos ρs hceil hsepρ
  obtain ⟨N0, hN⟩ := Filter.eventually_atTop.1
    (hsepEv.and (hacc.and (hrad.and (hord.and hdσ))))
  set N : ℕ := N0 + 1 with hNN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    rw [hNN]
    push_cast
    linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  have hsh : Tendsto (fun m : ℕ => m + N) atTop atTop := tendsto_add_atTop_nat N
  have hHN : ∀ m : ℕ, N0 ≤ m + N := fun m => by omega
  have hcast : ∀ m : ℕ, (m : ℝ) + 1 + 1 ≤ ((m + N : ℕ) : ℝ) + 1 := fun m => by
    push_cast
    linarith
  have hcast0 : ∀ m : ℕ, (m : ℝ) + 1 ≤ ((m + N : ℕ) : ℝ) + 1 := fun m => by
    linarith [hcast m]
  have hinv : ∀ m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := fun m =>
    one_div_le_one_div_of_le (by positivity) (hcast0 m)
  have hXpos : ∀ (m : ℕ) (s : ℝ),
      0 < max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hρinv : ∀ (m : ℕ) (s : ℝ),
      ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s => by
    rw [inv_pow, Real.sq_sqrt (hXpos m s).le, inv_inv]
  have hmax : ∀ (m : ℕ) (s : ℝ),
      max ((m : ℝ) + 1) ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1)
        (ρs (m + N) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s => by
    rw [hρinv]
    exact max_eq_right ((hcast0 m).trans (le_max_left _ _))
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := sliceBCBD_final_body_sep_alignedG_KFP
    (K := fun m => K (m + N)) (t := fun m => t (m + N))
    (T₀ := fun m => T₀ (m + N)) (p := fun m => p (m + N))
    (recordsK := fun m => recordsK (m + N)) (yG := fun m => yG (m + N))
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀)
    (htl := fun m => htl (m + N)) (htK := fun m => htK (m + N)) (G := fun m => G (m + N))
    (hG := fun m => hG (m + N))
    (hcanK := fun m => hcanK (m + N))
    (hacc := fun m => (hN (m + N) (hHN m)).2.1.trans (hinv m))
    (hrad2 := fun m => le_trans (hcast m) (hN (m + N) (hHN m)).2.2.1)
    (hord := fun m => le_trans (by omega) (hN (m + N) (hHN m)).2.2.2.1)
    (hpinchK0 := fun m => hpinchK0 (m + N)) (hpinchF := fun m => hpinchF (m + N)) (Kh := fun m => (K
        (m + N)).toHistory) (hKh := rfl)
    (σ := fun m => σ (m + N)) (hσ := fun m => hσ (m + N)) (y := fun m => y (m + N))
    (hyG := fun m => hyG (m + N)) (R := fun m => R (m + N)) (hRpos := fun m => hRpos (m + N))
    (hRn := fun m => hRn (m + N))
    (hRlt := fun m => lt_of_lt_of_le (by linarith [hcast m]) (hRle (m + N)))
    (hT₀ := fun B => hsh.eventually (hT₀ B)) (Tn := fun m => Tn (m + N))
    (aSeed := fun m => aSeed (m + N)) (haT := fun m => haT (m + N)) (hsT := fun m => hsT (m + N))
    (has := fun m => has (m + N)) (pT := fun m => pT (m + N))
    (seedTrace := fun m => seedTrace (m + N)) (L := fun m => L (m + N)) (hL := hL.comp hsh)
    (hCg := hCg) (hgood := fun m => hgood (m + N)) (hwin := fun T hT => hsh.eventually (hwin T hT))
    (hr := hr)
    (hsmall := fun m => hsmall (m + N)) (hclock := fun m => hclock (m + N))
    (a₀ := fun m => a₀ (m + N)) (ha₀ := fun m => ha₀ (m + N)) (hpin := fun m => hpin (m + N))
    (hRa := fun m => hRa (m + N)) (T₀X := fun m => T₀X (m + N)) (hT₀X := fun m => hT₀X (m + N))
    (hOldX := fun m => hOldX (m + N)) (hdσ := fun m => (hN (m + N) (hHN m)).2.2.2.2)
    (hκd := hκd) (hvolK := fun D L' B hD hL' hB => hsh.eventually (hvolK D L' B hD hL' hB))
    (hsepT := fun m i hi b hl hage => ((hN (m + N) (hHN m)).1 i hi b hl hage).1)
    (hsep4 := fun m i hi b hl hage => ((hN (m + N) (hHN m)).1 i hi b hl hage).2)
    (ρs := fun m s => (Real.sqrt (max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹))⁻¹)
    (hsepρ := fun B hB => (hsh.eventually (hsepρ B hB)).mono fun m hm i hi b hij hor => by
      have h := hm i hi b hij hor
      rw [hmax]
      refine le_trans (mul_le_mul_of_nonneg_right (hcast0 m) (hXpos m _).le) h)
    (hpre1 := fun m => by
      have h := hpre1 (m + N)
      change (K (m + N)).EventSlabsDerivative Ctime' (max ((m : ℝ) + 1) ((Real.sqrt (max
        (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (Fin.last (K (m +
            N)).eventCount)
      rw [hmax]
      exact h)
    (hpre2 := fun m => by
      have h := hpre2 (m + N)
      change (G (m + N)).DerivativeBoundBefore Ctime'
        (max ((m : ℝ) + 1) ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1)
          (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (t (m + N))
      rw [hmax]
      exact h) A hA
  exact ⟨Q, hQ, eventually_of_shift_G9S (P := fun n =>
    ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (yG n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      (G n).flow.scalar (t n) z ≤
        Q * (G n).flow.scalar (t n) (yG n)) N hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
