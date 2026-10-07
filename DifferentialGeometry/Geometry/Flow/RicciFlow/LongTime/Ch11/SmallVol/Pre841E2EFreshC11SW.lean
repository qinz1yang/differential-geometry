import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBlockBandBridgeC11SW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedWinSelectC11SW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2ESeedWindowCXCW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2ERegionalCXSK

/-!
# Pre841 data 存在定理：`hseedWin` 显式前提消去（O-CH11-SEEDWIN-P G3，后缀 `_C11SW`）

`exists_pre841Data_of_retention_seedWindow_bridge_CXCW` 的同一 tower / native radius（同一证明链，
经 `exists_blockData_nrBand_C11SW` 多导出 band 常值）；`hseedWin` 由 G2 producer 生产：
* `exists_pre841Data_of_retention_fresh_C11SW`：`hseedWin` → 坏点 ceiling `hRle`（P6SEL
  `selection_of_bad_sequence_P6X` 第 4 合取，`q n := N.params`）+ `hfresh`（只约束 crossing 支）；
* `exists_pre841Data_of_retention_large_C11SW`：`hseedWin` → `∀ᶠ n, 1 ≤ r n`（无 seed-window 前提）；
  consumer `exists_pre841Data_of_retention_rbar_C11SW`（hband 的 `r̄√t < r` 形）；
* `exists_pre841Data_regional_of_retention_fresh_C11SW`：CXSK 同源 regional κ consumer 的同一替换。
其余前提（`hradii / hwin / hdist`、seed 数据、retention/KDATA 条件）逐字保留，不在本车道。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **fresh 形**：CXCW bridge 的 `hseedWin` 换成坏点 ceiling `R n ≤ nr(t n)⁻²` 与 `hfresh`
（crossing `t − r²/2 ≤ a_k < t` 时旧块半径 `nr a_k ≤ r`）；同块支由 band 常值 + ratio 支付。 -/
theorem exists_pre841Data_of_retention_fresh_C11SW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      (∀ᶠ n in atTop, ∀ k : ℕ, (t n : ℝ) - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
        (5 / 6 : ℝ) * 3 ^ k < (t n : ℝ) → N.params.neckRadius ((5 / 6 : ℝ) * 3 ^ k) ≤ r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU, hbridge, hband⟩ :=
    exists_blockData_nrBand_C11SW P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle hfresh
  have hle := eventually_native_le_of_ceiling_C11SW (t := fun n => (t n : ℝ))
    (fun n => N.params.neckRadius_pos _ (t n).2.1) hRle hradii
  have hseedWin := eventually_seedWin_of_fresh_C11SW (c := fun k => rad (k + 1)) hband hlate
    htime hle hfresh
  exact nonempty_pre841Data_of_retention_seedWindow_CXCW N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist hseedWin

/-- **large 形**：`hseedWin` 换成 `∀ᶠ n, 1 ≤ r n`（`nr ≤ 1`，无 seed-window / crossing 前提）。 -/
theorem exists_pre841Data_of_retention_large_C11SW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ᶠ n in atTop, 1 ≤ r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU, hbridge, hband⟩ :=
    exists_blockData_nrBand_C11SW P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hlarge
  exact nonempty_pre841Data_of_retention_seedWindow_CXCW N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist
    (eventually_seedWin_of_large_C11SW hnr1 htime hlarge)

/-- **consumer（hband 路线）**：`∃ r̄ > 0, r̄√t < r` ⇒ large 形前提；Pre841 data 无 seed-window 前提。 -/
theorem exists_pre841Data_of_retention_rbar_C11SW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∃ rbar : ℝ, 0 < rbar ∧ ∀ n, rbar * Real.sqrt (t n) < r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, hbridge, hband, h⟩ := exists_pre841Data_of_retention_large_C11SW P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hrbar
  obtain ⟨rb, hrb, hbr⟩ := hrbar
  exact h hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist (eventually_one_le_of_rbar_C11SW hrb hbr hlate)

/-- **regional consumer（CXSK 同源）**：`exists_pre841Data_regional_of_retention_seedWindow_CXSK` 的
`hseedWin` 同样换成 ceiling + `hfresh`；同一 `d` 与 `d.kappa` 的区域 κ 供给。 -/
theorem exists_pre841Data_regional_of_retention_fresh_C11SW (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      (∀ᶠ n in atTop, ∀ k : ℕ, (t n : ℝ) - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
        (5 / 6 : ℝ) * 3 ^ k < (t n : ℝ) → N.params.neckRadius ((5 / 6 : ℝ) * 3 ^ k) ≤ r n) →
      ∃ d : Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR,
      ∀ᶠ n in atTop,
        ∀ (j : Fin (F.tower.history (ind n)).eventCount)
          (c : ((F.tower.history (ind n)).stage j.castSucc).Carrier)
          (U : Set ((F.tower.history (ind n)).stage j.castSucc).Carrier) (a v ρU : ℝ),
        (t n : ℝ) - r n ^ 2 / 2 ≤ a → v ≤ (t n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
          a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
          (F.tower.history (ind n)).time j.castSucc < τ →
          (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
          ∀ z ∈ U,
          ∀ zz cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier,
          HEq zz z → HEq cc c →
            riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage τ) τ) cc zz < ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
          a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
          (F.tower.history (ind n)).time j.castSucc < τ →
          (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ t n),
          ∀ cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
                ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
              ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage τ)
                ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
                ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) cc +
                ENNReal.ofReal ρU ≤ ENNReal.ofReal (A * r n)) →
        RegionalKappa_C11Q3 (F.tower.history (ind n)) j U a v (r n / 200) d.kappa) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU, hbridge, hband⟩ :=
    exists_blockData_nrBand_C11SW P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle hfresh
  have hle := eventually_native_le_of_ceiling_C11SW (t := fun n => (t n : ℝ))
    (fun n => N.params.neckRadius_pos _ (t n).2.1) hRle hradii
  have hseedWin := eventually_seedWin_of_fresh_C11SW (c := fun k => rad (k + 1)) hband hlate
    htime hle hfresh
  exact exists_pre841Data_regional_of_retention_seedWindow_CXSK N rad Df εf cap mf hrad hnr1
    hev hdomK3 hdomE hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock
    seedTrace s hst y R hR hradii hwin hdist hseedWin

end GC.LongTime.Ch11
