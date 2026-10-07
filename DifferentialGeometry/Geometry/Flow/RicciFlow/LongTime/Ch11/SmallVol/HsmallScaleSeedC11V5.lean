import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueSeedScaleC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaDataSupplyC11KD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL5 G3（续）：KDATA `hsmallScale_of_wideSupply_C11KD` 的种子尺度类比（`_C11V5`）

`hsmallScale_of_wideSupply_C11KD`（Q3 小尺度前提，`nr = q.neckRadius`）的变体：
* 输入的 wide 供给换成 KAPPA3 G7 的 `LocalKappaWideScaledSupply_C11Q4b`
  （例如 `localKappaWideScaled_of_reducedVolumeScaled_C11Q4b` 的结论，K5 由 KAPPA3 G6 / FINEPACK 链给出）；
* 结论是 G1 形的 `hsmall`：每个 `v` 多 `nr v ≤ r`（`nr = q.neckRadius`）。
链同 KDATA（`hsmall_of_wide_window_late_seedScale_C11V5` 代替 `…_C11V3`、
`wideWindowScaled_of_wideScaled_C11Q4b` 代替
`wideWindow_of_wideLate_C11V2` ∘ `wideLate_of_wideSupply_C11V3`），
`nr` 取钳位 `fun s => q.neckRadius (max s 0)` 后换回 `q.neckRadius`（`v ∈ Icc 0 horizon` 处 `max v 0 = v`）。
`ε₀` 只依赖 `(ε, C1, C2, N(P))`，`q.modelAccuracy ≤ ε₀` 是显式 binder（GAP-2 的量词次序同 KDATA）。
-/

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- 尺度 wide 供给对 `nr` 钳位不变（`t : Icc 0 horizon` 处 `max t 0 = t`）。 -/
theorem localKappaWideScaledSupply_clamp_C11V5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : LocalKappaWideScaledSupply_C11Q4b F δ α nr) :
    LocalKappaWideScaledSupply_C11Q4b F δ α (fun s => nr (max s 0)) := by
  intro A L hA hL
  obtain ⟨κ, hκ, hK⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ρ' hlow hup hball
  have hmax : max (t : ℝ) 0 = t := max_eq_left t.2.1
  exact hK n t p r hr hacc hsmall hvol (by simpa only [hmax] using hscale) x hx ρ'
    (by simpa only [hmax] using hlow) hup hball

/-- **`hsmallScale_of_wideSupply_C11KD` 的种子尺度类比**：尺度 wide 供给 + S7（对角 `α`）+ P3 / hprof +
records 的 canonical window + `HistoryCanonicalSupply` ⇒ G1 形 `hsmall`（`nr = q.neckRadius`，
每个 `v` 多 `nr v ≤ r`）。 -/
theorem hsmallSeed_of_wideScaledSupply_C11V5 (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A : ℝ}, 0 < A →
      CollarWindowSupply_C11E.{u} q → ModelConstraintsSupply_C11E q εProf_C11E.{u} →
      q.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, CanonicalWindowsSupply_C11S records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → q.neckRadius v ≤ r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < q.neckRadius v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨N, hN, hdeg⟩ := exists_stageDegreeBound_uniform_C11V4.{u} P
  obtain ⟨ε₀, hε₀, hE⟩ := hsmall_of_wide_window_late_seedScale_C11V5.{u}
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
  obtain ⟨κ, hκ, hW⟩ := wideWindowScaled_of_wideScaled_C11Q4b hS7
    (localKappaWideScaledSupply_clamp_C11V5 hwide) hA
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
  exact hK n t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv
    (by simpa only [hmax] using hnrv) x hx ρ' hρ' (by simpa only [hmax] using hρnr) hρr hball

/-- **GAP-2 的常数 `ε₀(ε, C1, C2, N(P))`**：`hsmallSeed_of_wideScaledSupply_C11V5` 里存在的 `ε₀`
（`Classical.choose`）。显式 binder 写作 `q.modelAccuracy ≤ epsilon0_C11V5 ε C1 C2 P`。 -/
def epsilon0_C11V5 (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) : ℝ :=
  (hsmallSeed_of_wideScaledSupply_C11V5.{u} ε C1 C2 P).choose

theorem epsilon0_pos_C11V5 (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    0 < epsilon0_C11V5 ε C1 C2 P :=
  (hsmallSeed_of_wideScaledSupply_C11V5.{u} ε C1 C2 P).choose_spec.1

/-- **consumer**：真实 `nr = q.neckRadius` 的 window（`LocalKappaWindowAt_P6B F q.neckRadius A κ₁`）
+ 本定理的种子尺度 `hsmall` ⇒ 种子尺度 window-zero（G2）。 -/
example (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A κ₁ : ℝ},
      0 < A → 0 < κ₁ → CollarWindowSupply_C11E.{u} q →
      ModelConstraintsSupply_C11E q εProf_C11E.{u} → q.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, CanonicalWindowsSupply_C11S records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LocalKappaWindowAt_P6B F q.neckRadius A κ₁ →
      ∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
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
  obtain ⟨ε₀, hε₀, hE⟩ := hsmallSeed_of_wideScaledSupply_C11V5.{u} ε C1 C2 P
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F q A κ₁ hA hκ₁ hP3 hprof hq records hwin hδanti hρanti hcanon hwide hW
  obtain ⟨κ', hκ', hsmall⟩ := hE hA hP3 hprof hq records hwin hδanti hρanti hcanon hwide
  exact ⟨min κ₁ κ', lt_min hκ₁ hκ',
    localKappaWindow_zero_of_window_and_small_seedScale_C11V5 hW hsmall⟩

end GC.LongTime.Ch11
