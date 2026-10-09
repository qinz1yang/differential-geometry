import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WideAlignC11V3

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL3 G2′：`hcan` 限到晚期的 `hsmall` 装配（`_C11V3`，GAP-1）

SMALLVOL2 G2 `hsmall_of_wide_window_C11V2` 的 `hcan` 对**所有** `v v'` 要求（含早期，无来源）。G2 的证明只在
晚期调它：`t ≥ T`、`2r² < t`、`v ≥ t - r²/2` ⇒ `v > 3t/4`；`s < nr v/50 ≤ M/50`、`2(M/50)² ≤ t` ⇒
`v' ≥ v - s² > t/4`。故 `hcan` 只需 `∃ T₀, ∀ v' ≥ T₀`，把 `T` 放大成 `max (max T (2(M/50)²)) (4T₀)`
即可（`hsmall_of_wide_window_late_C11V3`，证明体照抄 G2，只改三处）。
* `hcan_late_of_canonicalSupply_C11V3`：晚期 `hcan` ⇐ `HistoryCanonicalSupply_C11S` + `nr` 单调 + **晚期**
  `hcomp`（`|Rm| = s⁻²`、`s < nr v'/50` ⇒ `s⁻² ≤ 2500·R`，仅 `v' ≥ T₀`）；
* `localKappaWindow_zero_of_narrowTuple_late_C11V3` 及 consumer（喂 `tracedKappa_of_window_P6B`）。
**晚期 `hcomp`（GAP-1′）在本文件仍是显式前提**；其来源（history slice 的 HI + 标量下界 ⇒ 晚期
`s⁻² ≤ 2500 R`）见同目录 `HICompareC11V3.lean`（`hcomp_late_of_HI_C11V3`，metric 级点态引理
`sqrt_normSq_le_of_HI_C11V3`）。
-/

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2′（晚期 `hcan`）**：同 G2 `hsmall_of_wide_window_C11V2`，只把 `hcan` 限到晚期
`T₀ ≤ v'`（`∃ T₀` 紧跟其余前提）。G2 的证明只在 `v ≥ 3t/4`（`2r² < t`、`v ≥ t - r²/2`）与
`s < nr v/50 ≤ M/50` 处调 `hcan`，故取 `T = max (max T (2(M/50)²)) (4T₀)` 后
`v' ≥ v - s² > 3t/4 - t/2 = t/4 ≥ T₀`。其余前提、结论、证明体逐字。 -/
theorem hsmall_of_wide_window_late_C11V3 (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
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
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ' hρnr hρr
    hball
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
        v hav hvt hv x hx q hlow hup hc
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

/-- **端到端（window 形，晚期 `hcan`）**：G2′ ⇒ `∃ κ'' > 0, LocalKappaWindowAt_P6B F (fun _ => 0) A κ''`。 -/
theorem localKappaWindow_zero_of_wide_window_late_C11V3 (D : ℝ)
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
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
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hS⟩ := hsmall_of_wide_window_late_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F nr A κ M hA hκ hnrM hW hcapS hcan hdeg
  obtain ⟨κ', hκ', hsmall⟩ := hS hA hκ hnrM hW hcapS hcan hdeg
  exact ⟨min κ κ', lt_min hκ hκ',
    localKappaWindow_zero_of_window_and_small_C11V (window_of_wide_window_C11V2 hA hW) hsmall⟩

/-- **晚期 `hcan`**：`HistoryCanonicalSupply_C11S` + `nr` 单调不增 + 晚期 `hcomp` ⇒ G2′ 的 `hcan`。 -/
theorem hcan_late_of_canonicalSupply_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {ε C1 C2 : ℝ}
    (hanti : AntitoneOn nr (Ici 0))
    (hcanon : HistoryCanonicalSupply_C11S F nr ε C1 C2)
    (hcomp : ∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
        T₀ ≤ (v' : ℝ) → 0 < s → s < nr v' / 50 →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
          (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
        (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) :
    ∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
      ∀ v v' : Icc (0 : ℝ) H.horizon, T₀ ≤ (v' : ℝ) → v' ≤ v →
        ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
        0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
          (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
          V.capTubeHasNeckChart ε := by
  obtain ⟨T₀, hcomp⟩ := hcomp
  refine ⟨T₀, ?_⟩
  intro n H v v' hT0 hv'v w s hs hsnr hvs hcont
  have hnr : nr v ≤ nr v' := hanti v'.2.1 v.2.1 hv'v
  have hsnr' : s < nr v' / 50 := lt_of_lt_of_le hsnr (by linarith)
  have h1 := hcomp n v' w s hT0 hs hsnr' hcont
  refine hcanon n v' w ?_
  have h50 : 50 * s < nr v' := by linarith
  have hlt : (50 * s) ^ 2 < nr v' ^ 2 := pow_lt_pow_left₀ h50 (by positivity) two_ne_zero
  have hinv : (nr v' ^ 2)⁻¹ < ((50 * s) ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) hlt
  have he : ((50 * s) ^ 2)⁻¹ = (s⁻¹) ^ 2 / 2500 := by
    field_simp
    ring
  rw [he] at hinv
  have hR : (s⁻¹) ^ 2 / 2500 ≤ metricScalarAt (H.stageMetric (H.activeStage v') v') w := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  exact hinv.trans_le hR

/-- **端到端（narrow tuple 形，晚期 `hcan`）**：同 `localKappaWindow_zero_of_narrowTuple_C11V3`，
`hcomp` 与 `hcan` 都只在晚期。 -/
theorem localKappaWindow_zero_of_narrowTuple_late_C11V3 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
          T₀ ≤ (v' : ℝ) → 0 < s → s < q.neckRadius v' / 50 →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wide_window_late_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc' hord records hwin hanti hcanon hcomp hdeg hacc hwide
  obtain ⟨T₀, hcan⟩ := hcan_late_of_canonicalSupply_C11V3 hanti hcanon hcomp
  subst hDq
  obtain ⟨κ, hκ, hL⟩ := wideLate_of_wideSupply_C11V3 hacc
    (localKappaWideSupply_clamp_C11V3 hwide) hA
  exact hE (nr := fun s => q.neckRadius (max s 0)) (M := q.neckRadius 0) hA hκ
    (nr_clamp_le_C11V3 hanti)
    (wideWindow_of_wideLate_C11V2 (F := F) (nr := fun s => q.neckRadius (max s 0)) (κ := κ) hA
      hL)
    (hcapS_of_records_C11V3 records hwin hacc' hord)
    ⟨T₀, by
      intro n H v v' hT0 hv'v w s hs hsnr hvs hcont
      have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
      exact hcan n v v' hT0 hv'v w s hs (by simpa only [hmax] using hsnr) hvs hcont⟩
    hdeg

/-- **端到端 consumer（晚期形）**：K 链 wide 供给 + narrow tuple + 晚期 `hcomp` ⇒ `nr := 0` window ⇒
`tracedKappa_of_window_P6B`。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
          T₀ ≤ (v' : ℝ) → 0 < s → s < q.neckRadius v' / 50 →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_late_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc hord records hwin hanti hcanon hcomp hdeg hS7 hwide
  obtain ⟨κ'', -, hW0⟩ := hE hA hDq hacc hord records hwin hanti hcanon hcomp hdeg hS7 hwide
  have := tracedKappa_of_window_P6B hW0
  trivial

end GC.LongTime.Ch11
