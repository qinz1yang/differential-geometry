import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorHPNFrameFinalG9S

/-!
# final 版 hPN 帧 `hanchor0`：hgood 阈值 Cg 参数化（DRVFINAL，`_DF`）

G9SHIFT `hanchor0_hPN_frame_final_G9S` 的孪生：hgood 的 `4` → `Cg`，底层 final slice 核的 `hCg` 由 `2 ≤ Cg`
供（原版 `2 ≤ 4`）。前提 / 结论其余逐字。**无新 binder**。
生成器 `build-logs/scratch/DRVFINAL/gen/g6.py`。
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

/-- **final 版 hPN 帧 `hanchor0`，阈值 `Cg·R` 版（`_G9S_Cg_DF`）**：
`hanchor0_hPN_frame_final_G9S` 的 hgood `4` → `Cg`，`hCg : 2 ≤ Cg` 供底层核（原版 `2 ≤ 4`）。前提 / 结论其余逐字。 -/
theorem hanchor0_hPN_frame_final_G9S_Cg_DF {Cg : ℝ} (hCg : 2 ≤ Cg)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hεcone : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (T₀o : ℕ → ℝ)
    (hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    {A : ℝ} (hA : 1 < A) (ind : ℕ → ℕ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ (2 : ℕ) < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ (2 : ℕ)
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (pow_pos (hr k) 2)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k =>
      (Ho k).rescaleTime_P6X (pow_pos (hr k) 2) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (pow_pos (hr k) 2) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀o k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
      Tendsto L atTop atTop →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
        ∀ z : ((Kh k).stageAt v).Carrier,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
              ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k))
                  ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (L k / Real.sqrt (R k)) →
          Cg * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
          (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (pow_pos (hr k) 2)).neckRadius (Tn k) ^ (2 : ℕ))⁻¹) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (p : ℕ → CutoffParameters)
      (recordsK : ∀ k (i : Fin (K k).eventCount),
        (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K k).time i.succ →
        GeometricCutoffRecord (K k).toHistory i (p k))
      (_hcanK : ∀ k i hi b, ((recordsK k i hi).static b).hasCanonicalWindow)
      (_hacc : ∀ᶠ k : ℕ in atTop, (p k).modelAccuracy ≤ 1 / ((k : ℝ) + 1))
      (_hrad : ∀ᶠ k : ℕ in atTop, (k : ℝ) + 1 ≤ (p k).modelRadius)
      (_hord : ∀ᶠ k : ℕ in atTop, k + 2 ≤ (p k).modelOrder)
    (_hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi)
      (htl : ∀ k, (K k).time (Fin.last (K k).eventCount) < (σ k : ℝ))
      (htK : ∀ k, (σ k : ℝ) < (K k).horizon)
      (_hpinchF : ∀ k, Perelman.PhiAlmostNonnegative
        (((K k).finalSlab ((htl k).trans (htK k))).restrictIncoming le_rfl
          ((htl k).trans (htK k)) le_rfl).flow
        (Ico ((K k).time (Fin.last (K k).eventCount)) (K k).horizon ∩
          Ici ((Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi)
      (_hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K
              n).eventCount) →
          ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
            (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
          ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (pow_pos (hr n) 2)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale),
      ∀ A' : ℝ, 0 < A' → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A' / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n := by
  intro Ho Tno pTo r hr hNT htime hsmallo hvolo c K Kh Tn pT aSeed haT hclock ha1 hsmallK hT₀o
    seedTrace σ y R hsT has L hRdef hRpos hRle hL hgood hwin hwinF hceil hyball hgate
    p recordsK hcanK hacc hrad hord hpinchK0 htl htK hpinchF hsepρ
  have hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRle n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hTn : ∀ n, c n * (Tn n : ℝ) = (Tno n : ℝ) := fun n =>
    (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)
  have hc2 : ∀ n, c n = r n ^ 2 := fun _ => rfl
  have hTn2 : ∀ n, 2 < (Tn n : ℝ) := fun n => by
    by_contra hle0
    have hle := not_lt.mp hle0
    have hrp : 0 < r n ^ 2 := pow_pos (hr n) 2
    have h3 := mul_le_mul_of_nonneg_left hle hrp.le
    have h4 := hTn n
    have h5 := htime n
    rw [hc2 n] at h4
    linarith
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (htl n).trans (htK n)
  have hact : ∀ n, (Kh n).activeStage (σ n) = Fin.last (K n).eventCount := fun n =>
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) (htl n).le
  obtain ⟨yG, hyG⟩ : ∃ yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier,
      ∀ n, HEq (y n) (yG n) :=
    ⟨fun n => cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (y n),
      fun n => (cast_heq _ _).symm⟩
  obtain ⟨G, hG⟩ : ∃ G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon,
      ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl :=
    ⟨fun n => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl, fun n => rfl⟩
  have hRn : ∀ n, R n = (G n).flow.scalar (σ n) (yG n) := fun n => by
    rw [hRdef n]
    exact (K n).scalar_final_G9S (hfin n) (G n) (hG n) (hact n).symm (σ n) (yG n) (y n) (hyG n)
  obtain ⟨hpre1, hpre2⟩ := hpre_Tn_final_G9S hder hanti ind hc (t := fun n => (σ n : ℝ))
    hfin htl htK (fun n => (Tn n : ℝ)) (fun n => Subtype.coe_le_coe.mpr (hsT n))
  obtain ⟨κ, hκ, Tf, hsup⟩ := hsupA A hA
  have hTκ : ∀ᶠ n in atTop, Tf / c n ≤ (Tn n : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt Tf
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [div_le_iff₀ (hc n)]
    have h1 := hNT n
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h3 := hTn n
    calc Tf ≤ c n * (Tn n : ℝ) := by linarith
      _ = (Tn n : ℝ) * c n := mul_comm _ _
  have hvolS : ∀ n, ENNReal.ofReal ((A + 7)⁻¹ * 1 ^ 3) ≤ ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) 1 := by
    intro n
    have hrs : r n / Real.sqrt (c n) = 1 := by
      rw [hc2 n, Real.sqrt_sq (hr n).le]
      exact div_self (hr n).ne'
    have h := ((Ho n).le_ballVolume_castRescale_iff_CXSP (hc n) (v := Tno n) (p := pTo n)
      (κ := A⁻¹) (r := r n)).mpr (hvolo n)
    rw [hrs] at h
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
    have hA0 : 0 < A := by linarith
    have h7 : (A + 7)⁻¹ ≤ A⁻¹ := inv_anti₀ hA0 (by linarith)
    exact mul_le_mul_of_nonneg_right h7 (by positivity)
  have hS := ObservedHistory.sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_ev_G9S
    (K := K)
    (t := fun n => (σ n : ℝ)) (T₀ := fun n => (Tn n : ℝ) - 1 ^ 2 / 2) (p := p)
    (recordsK := recordsK) (yG := yG) (hεcone := hεcone) (hC20 := hC2) (hphi := hphi)
    (hθ₀ := hθ₀) (htl := htl) (htK := htK) (G := G) (hG := hG) (hcanK := hcanK) (hacc := hacc) (hrad
        := hrad)
    (hord := hord) (hpinchK0 := hpinchK0) (hpinchF := fun n => by rw [hG n]; exact hpinchF n) (Kh :=
        Kh) (hKh := rfl) (σ := σ)
    (hσ := fun _ => rfl) (y := y) (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn)
    (hRle := hRle)
    (hT₀ := hT₀_seed_G9S (Tn := fun n => (Tn n : ℝ)) (σ := fun n => (σ n : ℝ)) hRpos hwinF)
    (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT)
    (seedTrace := seedTrace) (L := L) (hL := hL) (hCg := hCg)
    (hgood := hgood) (hwin := hwin) (hr := one_pos)
    (hsmall := hsmallK) (hclock := hclock) (a₀ := fun _ => 0) (ha₀ := fun _ => le_rfl)
    (hpin := fun n s x =>
      ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n s x)
    (hRa := hRa_of_hPN_A2B R (fun n => (aSeed n : ℝ)) hRle ha1)
    (T₀X := fun n => T₀o n / c n)
    (hT₀X := hT₀X_of_hPN_A2B T₀o c (fun n => (aSeed n : ℝ)) hc hT₀o)
    (hOldX := fun _ _ _ => rfl) (hdσ := fun n => ne_top_of_lt (hyball n)) (hκ := hκ)
    (nr := fun n w => q.neckRadius (4 * (c n * w) / 3) / Real.sqrt (c n))
    (Tκ := fun n => Tf / c n) (Aκ := A + 7) (hWK := fun n => hsup ind c hc n) (hTκ := hTκ)
    (htimeS := fun n => by have := hTn2 n; linarith) (hvolS := hvolS)
    (hnrS := fun n w h1 _ => nr_le_one_G9S hanti (hc n) (hTn2 n) h1 (hR1 n) (hceil n))
    (hwinF := hwinF)
    (hgate := hgate.mono fun n h => h.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    (ρs := fun n _ => (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n)) (hceil := hceil)
    (hsepρ := hsepρ) (hpre1 := hpre1) (hpre2 := fun n => by rw [hG n]; exact hpre2 n)
  exact ObservedHistory.hanchor0_driver_of_final_G9S htl htK G hG σ (fun _ => rfl) y yG hyG R
    hRn hS

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
