import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallAssemblyLateC11V3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL5 G1：`hsmall` 装配的种子尺度变体（`_C11V5`，KAPPA3 G7 精确形 (i)）

`hsmall_of_wide_window_late_C11V3` 的 `hW`（wide window，seed shift 后的 `(v, O_v, r/100)` 处）改成
KAPPA3 G7 `wideWindowScaled_of_wideScaled_C11Q4b` 的结论形：**每个 `v` 多一个前提 `nr v ≤ r`**
（shift 种子 `(v, O_v, r/100)` 的尺度条件 `nr v/100 ≤ r/100`）；结论 `hsmall`（小尺度
`ρ' < nr v/100`、`ρ' < r/100`）同样带 `nr v ≤ r`。证明体逐字照搬 `hsmall_of_wide_window_late_C11V3`，
只多传 `hnrv` 给 `hW`（唯一一处调用 `hK`）；`contact_volume_trichotomy_C11V2` 与 `hcan` 的晚期限制
不变。其余前提（`hcapS / hcan / hdeg`、`ε₀` 的量词次序）逐字同 V3。
只在 P6 种子路径上被消费（`nr v ≤ r` 由 `seedScale_of_doubling_C11Q4b` 在 `v ∈ [t − r²/2, t]` 上给出），
不改全称合同。
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

/-- **G1（(i)）**：`hsmall_of_wide_window_late_C11V3` 的种子尺度变体：`hW` 每个 `v` 多 `nr v ≤ r`，
结论 `hsmall` 同带 `nr v ≤ r`（位于时钟窗口 `t − r²/2 ≤ v` 之后）。 -/
theorem hsmall_of_wide_window_late_seedScale_C11V5 (D : ℝ)
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
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

/-- **consumer（G1）**：KAPPA3 G7 的尺度 K5 + S7 ⇒ `wideWindowScaled_of_wideScaled_C11Q4b`（seed shift
window，多 `nr v ≤ r`）直接是本定理的 `hW`；`ε₀` 与 `hcapS / hcan / hdeg` 照 V3。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ} {A M : ℝ}, 0 < A → (∀ s, nr s ≤ M) →
      LargerBallAccuracySupply_C11S δ α → SeedReducedVolumeScaled_C11Q4 F δ α nr v →
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
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨ε₀, hε₀, hE⟩ := hsmall_of_wide_window_late_seedScale_C11V5.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α nr v A M hA hnrM hacc hK5 hcapS hcan hdeg
  obtain ⟨κ, hκ, hW⟩ := wideWindowScaled_of_wideScaled_C11Q4b hacc
    (localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5) hA
  exact hE hA hκ hnrM hW hcapS hcan hdeg

end GC.LongTime.Ch11
