import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2ESeedScaleC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBlockDataBridgeC11ND
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaNrDoublingC11ND

/-!
# κ 线端到端：`hnrDoubling` 换成 astra 块半径比（S-CH11-DOUBLE G2 consumer，后缀 `_C11ND`）

SMALLVOL5 终点 `exists_pre841Data_of_retention_seedScale_C11V5` 的变体：显式前提
`hnrDoubling : ∃ C T₀, ∀ τ ≥ T₀, nr(3τ/4) ≤ C·nr τ` **消去**，换成块半径比

  `∃ C' k₀, ∀ j ≥ k₀, rad j ≤ C' * rad (j + 1)`（`rad j = (TW.block j).radius`，
  `rad (j+1) = ℓ_j.rNext`；即 `rNext ≥ 上一块半径 / C'`），

并把 `rad` 与 `N.params.neckRadius` 的联系 `∀ k, N.params.neckRadius (3^k) = rad (k+1)` 作为结论
交出（来自 `exists_blockData_nrBridge_C11ND`）。链：块比 ⇒（桥）`nr` 块比 ⇒（`nrDoubling_of_blockRatio_three_C11ND`，
`nr` 单调正）`hnrDoubling` ⇒ V5 端到端。剩下的唯一 astra 侧缺口 = `hrat`（BlockStep 不含 `rNext` 下界，见
`KappaBlockRadiusC11ND` 文件头）。
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

/-- **tower 版 G1 + G2 合成**：lookahead 下界 + `nr` 单调正 ⇒ 逐字 `hnrDoubling`。 -/
theorem nrDoubling_of_lookahead_C11ND {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (T.toChain.observation n).parameters.neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < q.neckRadius t)
    (hlook : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) :
    ∃ C' T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → q.neckRadius (3 * t / 4) ≤ C' * q.neckRadius t :=
  nrDoubling_of_blockRatio_three_C11ND hanti hpos (nrBlockRatio_of_lookahead_C11ND T q hobs hlook)

/-- **κ 线端到端（块半径比版）**：`hnrDoubling` 消去，换成 `rad j ≤ C' · rad (j+1)`。 -/
theorem exists_pre841Data_of_retention_blockRadius_C11ND (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      ((∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j → rad j ≤ C' * rad (j + 1)) →
      ∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
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
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU, hbridge⟩ :=
    exists_blockData_nrBridge_C11ND P g
  refine ⟨F, N, rad, hbridge, fun hrat => ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle
  have hratio : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      N.params.neckRadius ((3 : ℝ) ^ k) ≤ C' * N.params.neckRadius ((3 : ℝ) ^ (k + 1)) := by
    obtain ⟨C', k₀, h⟩ := hrat
    refine ⟨C', k₀, fun k hk => ?_⟩
    rw [hbridge k, hbridge (k + 1)]
    exact h (k + 1) (by omega)
  exact nonempty_pre841Data_of_retention_seedScale_C11V5 N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist
    (nrDoubling_of_blockRatio_three_C11ND N.radius_antitone
      (fun τ hτ => N.params.neckRadius_pos τ hτ) hratio) hRle

end GC.LongTime.Ch11
