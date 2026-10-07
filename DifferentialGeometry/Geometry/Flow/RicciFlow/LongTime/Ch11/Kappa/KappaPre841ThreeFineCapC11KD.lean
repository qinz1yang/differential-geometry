import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaPre841ThreeC11KD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineEndToEndC11Q5

set_option autoImplicit false

/-!
# 局部 κ 线端到端（fine-cap 版）：只剩 `hW`、`hB`、`hact`、`hfine`（S-CH11-KDATA G4，后缀 `_C11KD`）

FINECAP（`KappaFineEndToEndC11Q5`）的 D-2 contract correction：原 `hscale : KappaWindowScale_C11Q2`
推不出（choose 常数 + 固定 `modelAccuracy`），端到端
`nonempty_pre841Data_of_native_fineCap_C11Q5` 把它换成 `hact`（逐 record 的 actual canonical
insertion）与 `hfine`（只对 `α` 的纯 δ 条件）。本文件把 G3 的 wrapper 搬到这个新端到端：

* `pre841Data_of_three_fineCap_C11KD`：数据 binder（`N / hκ / hδ / hacc / hsmallScale`）仍由 narrow tuple
  + 树内引理给出（G2 / G3 同一套），`hscale` ⇒ `hact + hfine`；`hsmallScale` 吃
  `localKappaWideSupply_of_native_fineCap_C11Q5` 的 wide 供给。
* `pre841Data_of_chain_fineCap_C11KD`：chain 层复合（`tupleData_of_chain_C11KD` ∘ 上一条）；
  `hact` 针对产出的 `records`。
-/

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **fine-cap 版端到端只剩 `hW hB hact hfine`**：`nonempty_pre841Data_of_native_fineCap_C11Q5` 的数据
binder（`N / hκ / hδ / hacc / hsmallScale`）由 narrow tuple 的数据合取项 + 树内引理给出；`hscale`
（D-2 contract correction 后推不出）换成 `hact`（实际 canonical insertion）与 `hfine`（纯 δ 条件）。 -/
theorem pre841Data_of_three_fineCap_C11KD (ε C1 C2 : ℝ) {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {Cw Db : ℝ → ℝ} {Ctime : ℝ≥0}
    (records : CutoffRecords_C11S F q)
    (hP3 : CollarWindowSupply_C11E.{u} q) (hprof : ModelConstraintsSupply_C11E q εProf_C11E.{u})
    (hacc₀ : q.modelAccuracy ≤ epsilon0_C11KD ε C1 C2 P)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hcw : CanonicalWindowsSupply_C11S records)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hrecent : RecentCutoffSupply_C11S records)
    (hP2 : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hW : WeightedMinBound_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius Cw)
    (hB : SeedRegularBlock_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius
      (weightedMinLengthConst_C11Q2 Cw) Db blockKappa_C11KD)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g q (diagonalAccuracy_C11S q.delta)
      (weightedMinLevel_C11Q2 Cw) Ctime)
    {A : ℝ} (hA : 0 < A)
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  have hacc := largerBallAccuracySupply_diagonal_C11S q hδanti
  have hwide := localKappaWideSupply_of_native_fineCap_C11Q5
    (nativeDataOfSupplies_C11KD F q records ε C1 C2 Ctime hρanti hδanti hδlim hconst hcw hcan hP2
      hrecent) hW hB blockKappa_pos_C11KD (fun _ _ => le_rfl) hact hfine
  obtain ⟨κ', hκ', hsmallScale⟩ := (hsmallScale_of_wideSupply_C11KD.{u} ε C1 C2 P).choose_spec.2
    hA hP3 hprof hacc₀ records hcw hδanti hρanti hcan hwide
  exact nonempty_pre841Data_of_native_fineCap_C11Q5
    (nativeDataOfSupplies_C11KD F q records ε C1 C2 Ctime hρanti hδanti hδlim hconst hcw hcan hP2
      hrecent) hW hB blockKappa_pos_C11KD (fun _ _ => le_rfl) hact hfine hacc hA hκ' hsmallScale
    ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

/-! ## chain 层 -/

/-- **chain ⇒ `Pre841Data_C11K`（fine-cap 版），只剩 `hW hB hact hfine`**：`tupleData_of_chain_C11KD` ∘
`pre841Data_of_three_fineCap_C11KD`。除 chain 自身的数据（`S`、P3 / hprof、逐步 retention、GAP-2 的
`ε₀`）与 PRE841 种子数据外，唯一前提是 `hW`、`hB`、`hact`（对产出的 `records`）、`hfine`。 -/
theorem pre841Data_of_chain_fineCap_C11KD {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase Γ P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (hacc₀ : pBase.modelAccuracy ≤
      epsilon0_C11KD Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : CutoffRecords_C11S F q), F.tower = S.tower ∧
      ∀ {Cw Db : ℝ → ℝ},
      WeightedMinBound_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius Cw →
      SeedRegularBlock_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius
        (weightedMinLengthConst_C11Q2 Cw) Db blockKappa_C11KD →
      (∀ n i b, ActualCanonicalInsertion_C11Q5 ((records n i).static b)) →
      KappaFineScale_C11Q5 P g q (diagonalAccuracy_C11S q.delta)
        (weightedMinLevel_C11Q2 Cw) Γ.Ctime →
      ∀ {A : ℝ}, 0 < A → ∀ (ind : ℕ → ℕ)
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
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨F, q, records, hTower, hP3q, hprofq, hq, hconst, hcw, hδanti, hρanti, hδlim, hcan,
    hrecent, hP2⟩ := tupleData_of_chain_C11KD S hP3 hprof εcut Dcut mcut W hshift hoffset hacc₀
  refine ⟨F, q, records, hTower, ?_⟩
  intro Cw Db hW hB hact hfine A hA ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist
  exact pre841Data_of_three_fineCap_C11KD Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) records
    hP3q hprofq hq hconst hcw hδanti hρanti hδlim hcan hrecent hP2 hW hB hact hfine hA ind t p r
    hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

end GC.LongTime.Ch11
