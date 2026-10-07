import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallScaleSeedC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFwdWideC11FR

/-!
# 小尺度 `hsmall` / window-zero 的前向版（O-CH11-FRESH G2a，后缀 `_C11FR`）

SMALLVOL5 三步（assembly `HsmallAssemblySeedScaleC11V5`、`HsmallScaleSeedC11V5`、glue
`WindowGlueSeedScaleC11V5`）的前向版：shift 种子尺度前提 `nr v ≤ r`（crossing seed 的 R3 来源）全部换成
`nr (4(t − r²/2)/3) ≤ r`（前向时刻 `≥ t`，由 `nr t ≤ r` + antitone 给出，G1c）。证明体逐字；
B 类用法（`hcan` 的 `s < nr v/50`、glue 的 `ρ' ≷ nr v/100` 分界）不变。
`epsilon0_C11FR`：assembly 重证带来的 GAP-2 常数（与 `epsilon0_C11V5` 同源同型，`Classical.choose` 不可比）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. assembly -/

/-- **assembly（前向）**：`hsmall_of_wide_window_late_seedScale_C11V5` 的证明体逐字；`hW` 与结论里每个 `v` 的
前提 `nr v ≤ r` 换成前向形 `nr (4(t − r²/2)/3) ≤ r`（只在 `nr v/50 ≤ (A+1)r` 支原样传给 `hK`）。
`hcan`（`s < nr v/50` 的 canonical 阈值，B 类）不变。`ε₀` 同取 `contact_volume_trichotomy_C11V2`。 -/
theorem hsmallFwd_of_wide_window_late_C11FR (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      (∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, T₀ ≤ (v' : ℝ) → v' ≤ v →
          ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ κ' : ℝ, 0 < κ' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) →
          2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨ε₀, κU, hε₀, hκU, hU⟩ := contact_volume_trichotomy_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F nr A κ M hA hκ hnrM hW hcapS hcan hdeg
  obtain ⟨T, hT, hK⟩ := hW
  obtain ⟨T₀, hcan⟩ := hcan
  set κC : ℝ := A⁻¹ * Real.exp (-57) / 512 / (100 * (A + 1)) ^ 3 with hκC
  have hκCpos : 0 < κC := by rw [hκC]; positivity
  set κR : ℝ := min κ κC with hκR
  have hκRpos : 0 < κR := lt_min hκ hκCpos
  refine ⟨min κU (κR / (8 * Real.exp 6)), lt_min hκU (by positivity),
    max (max T (2 * (M / 50) ^ 2)) (4 * T₀), lt_max_of_lt_left (lt_max_of_lt_left hT), ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv hnrv x hx ρ' hρ'
    hρnr hρr hball
  have hr0 : 0 < r := hsm.1
  have hnrpos : 0 < nr v := by linarith
  set R : ℝ := min (nr v / 50) ((A + 1) * r) with hRdef
  have hρR : ρ' < R := lt_min (by linarith) (by nlinarith)
  have hRnr : R ≤ nr v / 50 := min_le_left _ _
  have hRv : R ^ 2 ≤ (v : ℝ) := by
    have hR0 : 0 ≤ R := hρ'.le.trans hρR.le
    have hRM : R ≤ M / 50 := hRnr.trans (by linarith [hnrM v])
    have hsq : R ^ 2 ≤ (M / 50) ^ 2 := pow_le_pow_left₀ hR0 hRM 2
    have hTM : 2 * (M / 50) ^ 2 ≤ (t : ℝ) :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hTt
    nlinarith
  have hθ := seedRatio_lt_one_C11V2 hA
  have hseed : ∀ q : ℝ, max (1 / 2) ((A + 1 / 100) / (A + 1)) * R ≤ q → q < R →
      H.isParabolicallyRmControlledBall v x q →
      ENNReal.ofReal κR * ENNReal.ofReal q ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) x q) := by
    intro q hθq hqR hc
    have hq0 : 0 < q := hc.1
    rw [ofReal_mul_ofReal_cube_C11V2 κR hq0.le]
    have hR0 : 0 ≤ R := hρ'.le.trans hρR.le
    by_cases hcase : nr v / 50 ≤ (A + 1) * r
    · have hRe : R = nr v / 50 := min_eq_left hcase
      have hlow : nr v / 100 ≤ q := by
        have h1 : 1 / 2 * R ≤ max (1 / 2) ((A + 1 / 100) / (A + 1)) * R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
        rw [hRe] at h1 hθq
        linarith
      have hup : q ≤ (A + 1) * r := hqR.le.trans (min_le_right _ _)
      have h := hK n t p r (((le_max_left _ _).trans (le_max_left _ _)).trans hTt) hr hsm hvol
        aSeed haT hclock seedTrace
        v hav hvt hv hnrv x hx q hlow hup hc
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg hq0.le 3))).trans h
    · have hRe : R = (A + 1) * r := min_eq_right (le_of_lt (lt_of_not_ge hcase))
      have hlow : (A + 1 / 100) * r ≤ q := by
        have h1 : (A + 1 / 100) / (A + 1) * R ≤ max (1 / 2) ((A + 1 / 100) / (A + 1)) * R :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hR0
        have he : (A + 1 / 100) / (A + 1) * R = (A + 1 / 100) * r := by
          rw [hRe]
          field_simp
        linarith
      have hup : q ≤ (A + 1) * r := hRe ▸ hqR.le
      have hshift := earlier_seed_on_half_depth_P6B haT p r A hr hclock hsm hvol seedTrace v hav
        hvt hv
      have h := seed_volume_of_containment_C11V2 hA hr0 hx hlow hup hshift.2.1
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg hq0.le 3))).trans h
  have hmain := hU H v x hball hρR hRv (fun i _ _ => rfl)
    (fun i b _ _ => hcapS n i b)
    (fun v' hv'v w s hs hsR hvs hcont => by
      have hsM : s ≤ M / 50 := (hsR.trans_le hRnr).le.trans (by linarith [hnrM v])
      have hs2 : s ^ 2 ≤ (M / 50) ^ 2 := pow_le_pow_left₀ hs.le hsM 2
      have hT0t : 4 * T₀ ≤ (t : ℝ) := (le_max_right _ _).trans hTt
      have hTM : 2 * (M / 50) ^ 2 ≤ (t : ℝ) :=
        ((le_max_right _ _).trans (le_max_left _ _)).trans hTt
      have hT0 : T₀ ≤ (v' : ℝ) := by nlinarith [sq_nonneg r]
      exact hcan n v v' hT0 hv'v w s hs (hsR.trans_le hRnr) hvs hcont)
    (hdeg n) hθ hκRpos.le hseed
  rw [ofReal_mul_ofReal_cube_C11V2 _ hρ'.le] at hmain
  exact hmain

/-! ## 2. `hsmallSeed`（native `nr`）与 GAP-2 常数 -/

/-- 前向 wide 供给对 `nr` 钳位不变（前向时刻 `T ≥ t ≥ 0`，`max T 0 = T`）。 -/
theorem localKappaWideFwdSupply_clamp_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : LocalKappaWideFwdSupply_C11FR F δ α nr) :
    LocalKappaWideFwdSupply_C11FR F δ α (fun s => nr (max s 0)) := by
  intro A L hA hL
  obtain ⟨κ, hκ, hK⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ρ' hlow hup hball
  have hmax : max (t : ℝ) 0 = t := max_eq_left t.2.1
  obtain ⟨T, hT1, hT2, hT3⟩ := hscale
  have hmaxT : max T 0 = T := max_eq_left (t.2.1.trans hT1)
  exact hK n t p r hr hacc hsmall hvol ⟨T, hT1, hT2, by simpa only [hmaxT] using hT3⟩ x hx ρ'
    (by simpa only [hmax] using hlow) hup hball

/-- **`hsmallSeed_of_wideScaledSupply_C11V5` 的前向版**：前向 wide 供给 + S7 + P3 / hprof + records 的
canonical window + `HistoryCanonicalSupply` ⇒ `hsmall`（`nr = q.neckRadius`），每个 `v` 的前提为
`q.neckRadius (4(t − r²/2)/3) ≤ r`（不再是 `q.neckRadius v ≤ r`）。证明体逐字。 -/
theorem hsmallSeedFwd_of_wideFwdSupply_C11FR (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A : ℝ}, 0 < A →
      CollarWindowSupply_C11E.{u} q → ModelConstraintsSupply_C11E q εProf_C11E.{u} →
      q.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, CanonicalWindowsSupply_C11S records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      ∃ κ' : ℝ, 0 < κ' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) →
          2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
            q.neckRadius (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < q.neckRadius v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨N, hN, hdeg⟩ := exists_stageDegreeBound_uniform_C11V4.{u} P
  obtain ⟨ε₀, hε₀, hE⟩ := hsmallFwd_of_wide_window_late_C11FR.{u}
    (4 * StandardCap.transitionEnd + 6) le_rfl ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F q A hA hP3 hprof hq records hwin hδanti hρanti hcanon hwide
  have hD : 4 * StandardCap.transitionEnd + 6 ≤ q.modelRadius :=
    four_transitionEnd_le_modelRadius_C11V3 hP3
  have hS7 := largerBallAccuracySupply_diagonal_C11S q hδanti
  obtain ⟨c, c', hc, hc', hHI, hlow⟩ := history_HI_and_lower_of_records_C11V3 records
  have hcomp := hcomp_late_of_HI_C11V3 (nr := q.neckRadius) (M := q.neckRadius 0)
    (q.neckRadius_pos 0 le_rfl) (fun s hs => hρanti (Set.mem_Ici.mpr le_rfl) hs hs) hc hc' hHI hlow
  obtain ⟨T₀, hcan⟩ := hcan_late_of_canonicalSupply_C11V3 hρanti hcanon hcomp
  obtain ⟨κ, hκ, hW⟩ := wideWindowFwd_of_wideFwd_C11FR hS7
    (localKappaWideFwdSupply_clamp_C11FR hwide) hA
  obtain ⟨κ', hκ', T, hT, hK⟩ := hE (nr := fun s => q.neckRadius (max s 0))
    (M := q.neckRadius 0) hA hκ (nr_clamp_le_C11V3 hρanti) hW
    (hcapS_restrict_of_records_C11V4 records hwin hq hprof.2.1 hD)
    ⟨T₀, by
      intro n H v v' hT0 hv'v w s hs hsnr hvs hcont
      have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
      exact hcan n v v' hT0 hv'v w s hs (by simpa only [hmax] using hsnr) hvs hcont⟩
    (hdeg F)
  refine ⟨κ', hκ', T, hT, ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv hnrv x hx ρ' hρ' hρnr hρr
    hball
  have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
  have hmaxT : max (4 * ((t : ℝ) - r ^ 2 / 2) / 3) 0 = 4 * ((t : ℝ) - r ^ 2 / 2) / 3 :=
    max_eq_left (by nlinarith [sq_nonneg r])
  exact hK n t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv
    (by simpa only [hmaxT] using hnrv) x hx ρ' hρ' (by simpa only [hmax] using hρnr) hρr hball

/-- **GAP-2 常数（前向版）`ε₀(ε, C1, C2, N(P))`**：`hsmallSeedFwd_of_wideFwdSupply_C11FR` 的 `ε₀`
（`Classical.choose`）。与 `epsilon0_C11V5` 同源（`contact_volume_trichotomy_C11V2`，
`D = 4·transitionEnd + 6`、`N = exists_stageDegreeBound_uniform_C11V4 P`），同型、同量词序，
只依赖 `(ε, C1, C2, P)`。 -/
def epsilon0_C11FR (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) : ℝ :=
  (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} ε C1 C2 P).choose

theorem epsilon0_pos_C11FR (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    0 < epsilon0_C11FR ε C1 C2 P :=
  (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} ε C1 C2 P).choose_spec.1

/-! ## 3. glue ⇒ CXCW window 形 -/

/-- **glue（前向）**：`localKappaWindow_zero_of_window_and_small_seedScale_C11V5` 的证明体逐字；`hsmall` 的前提
为前向形，输出 window 的种子前提为 `∀ w ∈ [t − r²/2, t], nr (4w/3) ≤ r`——恰是 CXCW
`pre841Data_of_window_seedWindow_CXCW` 在 `nr̃ := fun w => nr (4 * w / 3)` 下的 window 形
（只在 `w = t − r²/2` 处使用）。 -/
theorem localKappaWindow_zero_of_window_and_smallFwd_C11FR {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ κ' : ℝ}
    (hW : LocalKappaWindowAt_P6B F nr A κ)
    (hsmall : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr (4 * w / 3) ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (min κ κ' * ρ' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨T₁, hT₁, hK₁⟩ := hW
  obtain ⟨T₂, hT₂, hK₂⟩ := hsmall
  refine ⟨max T₁ T₂, lt_max_of_lt_left hT₁, ?_⟩
  intro n H t p r hTt hr hcurv hvol hscale aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ'0
    hρ'r hball
  have hρpos : 0 < ρ' := hball.1
  have hρ3 : 0 ≤ ρ' ^ 3 := pow_nonneg hρpos.le 3
  rcases le_or_gt (nr v / 100) ρ' with hge | hlt
  · have h := hK₁ n t p r ((le_max_left _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv x hx ρ' hge hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ3)).trans h
  · have hnrv : nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r :=
      hscale _ le_rfl (by linarith [sq_nonneg r])
    have h := hK₂ n t p r ((le_max_right _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv hnrv x hx ρ' hρpos hlt hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _) hρ3)).trans h

/-- **consumer**：真实 `nr = q.neckRadius` 的 P6B window + 前向 `hsmall` ⇒ CXCW window 形
（`nr̃ = q.neckRadius (4 · / 3)`）。 -/
example (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A κ₁ : ℝ}
    (hA : 0 < A) (hκ₁ : 0 < κ₁) (hP3 : CollarWindowSupply_C11E.{u} q)
    (hprof : ModelConstraintsSupply_C11E q εProf_C11E.{u})
    (hq : q.modelAccuracy ≤ epsilon0_C11FR ε C1 C2 P)
    (records : CutoffRecords_C11S F q) (hwin : CanonicalWindowsSupply_C11S records)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanon : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hwide : LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
    (hW : LocalKappaWindowAt_P6B F q.neckRadius A κ₁) :
    ∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius (4 * w / 3) ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨κ', hκ', hsmall⟩ := (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} ε C1 C2 P).choose_spec.2
    hA hP3 hprof hq records hwin hδanti hρanti hcanon hwide
  exact ⟨min κ₁ κ', lt_min hκ₁ hκ',
    localKappaWindow_zero_of_window_and_smallFwd_C11FR hW hsmall⟩

end GC.LongTime.Ch11
