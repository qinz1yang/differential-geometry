import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaDataSupplyC11KD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaUREBlockC11Q3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.TimeDerivativeC12X

set_option autoImplicit false

/-!
# 局部 κ 线端到端：只剩 `hW`、`hB`、`hscale` 三条（S-CH11-KDATA G3，后缀 `_C11KD`）

`pre841Data_of_three_C11KD`：`nonempty_pre841Data_of_native_C11Q2`（`Kappa/KappaEndToEndC11Q2`）
的包装。数据 binder 全部换成 narrow tuple（`exists_w1_params_timeDerivative_C12X` 的合取项）：

* `N` ⇐ `nativeDataOfSupplies_C11KD`；`hδ`：`δ := q.delta`，`le_rfl`；`hacc` ⇐
  `largerBallAccuracySupply_diagonal_C11S`（`α := diagonalAccuracy_C11S q.delta`）；`hκ` ⇐
  `blockKappa_pos_C11KD`（`κ := blockKappa_C11KD`，`hB` 以它陈述，`D` 自由）；
* `hsmallScale` ⇐ `hsmallScale_of_wideSupply_C11KD`（吃 `localKappaWideSupply_of_native_C11Q2` 的
  结论、tuple 的 P3 / hprof / canonical window、GAP-2 `q.modelAccuracy ≤ epsilon0_C11KD …`）；
* 剩下的 K 链前提只有 `hW`（WeightedMinBound，KAPPA2 G1/G2）、`hB`（`SeedRegularBlock`，URE，KAPPA2
  Q3-G3）、`hscale`（δ₀ 尺度，FINECAP）；以及 PRE841 的种子 / 窗口 / 距离数据（调用输入，不属 native 数据）。

`tupleData_of_chain_C11KD`：任一 `PreparedSpatialChain`（+ astra 对角导数的逐步 retention 数据）
给出 wrapper 的全部 tuple 数据 binder（同一个 `(F, q, records)`，`Ctime = Γ.Ctime`，
`C1 C2` 取 `Γ` 的 `max` 形，使 GAP-2 的 `ε₀` 在 `F` 之前确定）；
`pre841Data_of_chain_C11KD`：两者复合，`hW hB hscale` 与种子数据之外无其它前提。
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

/-- block 常数 `blockKappa_C11KD` 逐字就是 KAPPA2 Q3-G3 的 URE 常数 `ureBlockKappa_C11Q3`
（`hB` 的 `κ` 与 URE 产出对齐）。 -/
theorem blockKappa_eq_ure_C11KD : blockKappa_C11KD = ureBlockKappa_C11Q3 :=
  rfl

/-- **端到端只剩 `hW hB hscale`**：`nonempty_pre841Data_of_native_C11Q2` 的数据 binder
（`N / hκ / hδ / hacc / hsmallScale`）由 narrow tuple 的数据合取项 + 树内引理给出。 -/
theorem pre841Data_of_three_C11KD (ε C1 C2 : ℝ) {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hscale : KappaWindowScale_C11Q2 P g q (diagonalAccuracy_C11S q.delta) q.neckRadius
      (weightedMinLevel_C11Q2 Cw) (fun t => (q.neckRadius t ^ 2)⁻¹)
      (fun t => q.neckRadius (t / 2)) Ctime)
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
  have hwide := localKappaWideSupply_of_native_C11Q2
    (nativeDataOfSupplies_C11KD F q records ε C1 C2 Ctime hρanti hδanti hδlim hconst hcw hcan hP2
      hrecent) hW hB blockKappa_pos_C11KD (fun _ _ => le_rfl) hscale
  obtain ⟨κ', hκ', hsmallScale⟩ := (hsmallScale_of_wideSupply_C11KD.{u} ε C1 C2 P).choose_spec.2
    hA hP3 hprof hacc₀ records hcw hδanti hρanti hcan hwide
  exact nonempty_pre841Data_of_native_C11Q2
    (nativeDataOfSupplies_C11KD F q records ε C1 C2 Ctime hρanti hδanti hδlim hconst hcw hcan hP2
      hrecent) hW hB blockKappa_pos_C11KD (fun _ _ => le_rfl) hscale hacc hA hκ' hsmallScale
    ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

/-! ## chain 层：`PreparedSpatialChain` 给出 wrapper 的全部 tuple 数据 binder -/

/-- tuple 里 canonical 常数 `C1`（`w1_of_preparedSpatialChain_C11A` 的取法）。 -/
def chainC1_C11KD (Γ : ClosedBirthConstants) : ℝ :=
  max Γ.C1s Γ.Cbirth

/-- tuple 里 canonical 常数 `C2`。 -/
def chainC2_C11KD (Γ : ClosedBirthConstants) : ℝ :=
  max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))

/-- **chain ⇒ wrapper 的 tuple 数据**：`exists_w1_params_timeDerivative_C12X` 的合取项，
`C1 C2` 取 `chainC1_C11KD / chainC2_C11KD`（所以 GAP-2 的 `epsilon0_C11KD` 在 `F` 之前确定），
GAP-2 条件 `pBase.modelAccuracy ≤ ε₀` 经 `q.modelAccuracy = pBase.modelAccuracy` 传到 `q`。 -/
theorem tupleData_of_chain_C11KD {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
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
      CollarWindowSupply_C11E.{u} q ∧ ModelConstraintsSupply_C11E q εProf_C11E.{u} ∧
      q.modelAccuracy ≤ epsilon0_C11KD Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P ∧
      CanonicalConstantsSupply_C11S Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) ∧
      CanonicalWindowsSupply_C11S records ∧ AntitoneOn q.delta (Ici 0) ∧
      AntitoneOn q.neckRadius (Ici 0) ∧ Tendsto q.delta atTop (𝓝 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon (chainC1_C11KD Γ)
        (chainC2_C11KD Γ) ∧
      RecentCutoffSupply_C11S records ∧ TimeDerivativeSupply_C11E F q.neckRadius Γ.Ctime := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin,
    hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  obtain ⟨hfixed, hrad, hord, hacc, -⟩ := hstatic
  exact ⟨F, q, records, hTower, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
    modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof, hacc.le.trans hacc₀,
    canonicalConstantsSupply_of_closedBirthConstants_C11A Γ, hwin, hδanti, hρanti, hδlim, hcan,
    hrecent,
    timeDerivativeSupply_of_astra_C12X S εcut Dcut mcut W hshift hoffset F hTower q hρanti
      (diagonal_neckRadius_of_prefix_C12X S q (fun n t ht => (hpref n t ht).2.1))⟩

/-- **chain ⇒ `Pre841Data_C11K`，只剩 `hW hB hscale`**：`tupleData_of_chain_C11KD` ∘
`pre841Data_of_three_C11KD`。除 chain 自身的数据（`S`、P3 / hprof、逐步 retention、GAP-2 的
`ε₀`）与 PRE841 种子数据外，唯一前提是 `hW`（WeightedMinBound）、`hB`（block）、`hscale`（δ₀ 尺度）。 -/
theorem pre841Data_of_chain_C11KD {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
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
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = S.tower ∧
      ∀ {Cw Db : ℝ → ℝ},
      WeightedMinBound_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius Cw →
      SeedRegularBlock_C11Q2 F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius
        (weightedMinLengthConst_C11Q2 Cw) Db blockKappa_C11KD →
      KappaWindowScale_C11Q2 P g q (diagonalAccuracy_C11S q.delta) q.neckRadius
        (weightedMinLevel_C11Q2 Cw) (fun t => (q.neckRadius t ^ 2)⁻¹)
        (fun t => q.neckRadius (t / 2)) Γ.Ctime →
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
  refine ⟨F, q, hTower, ?_⟩
  intro Cw Db hW hB hscale A hA ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst
    y R hR hradii hwin hdist
  exact pre841Data_of_three_C11KD Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) records hP3q
    hprofq hq hconst hcw hδanti hρanti hδlim hcan hrecent hP2 hW hB hscale hA ind t p r hlate htime
    hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

end GC.LongTime.Ch11
