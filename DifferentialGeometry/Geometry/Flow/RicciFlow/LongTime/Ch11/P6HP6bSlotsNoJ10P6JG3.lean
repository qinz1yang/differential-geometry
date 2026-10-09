import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestTimeSwitchNoJ10P6JB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersNoJ10P6JB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalNoJ10P6JB

/-!
# J10GEN3 G3：hP6b 时间 jointD 的 hgap 四槽全部由 J10GEN2B producer 付清（切换 example，`_P6JG3`）

J10GEN2B G3（`P6JointTimeSwitchNoJ10P6JB`：只有 `hgapJ` 由 producer 付）与 G3b（`P6HrestTimeSwitchNoJ10P6JB`：
`hgapJ8 hgapJF hgapJF8` 仍是 binder）的合并：time jointD 孪生 `canonicalLateTimeCore_of_jointD_noJ10_P6JB` 的
`hgapJ` 位 ← `hgapJ_noJ10_of_producers_P6JB`；其 `hrestP` 位 ← HP3 孪生
`hrestP_of_jointPrefix_noJ10_P6JB`，后者的 `hgapJ8` ← `hgapJ8_noJ10_of_capBirthBudget_P6JB`、
`hgapJF` ← `hgapJF_noJ10_of_producers_P6JB`、
`hgapJF8` ← `hgapJF8_noJ10_of_producers_P6JB`。`_hcomp` 的 binder（类型由 producer 参数推断）= 切换后
hP6b 时间链的**全部输入**：
* producer 输入（各族一份：KNOM `hP5L`、`hδq`、`records`、chain `S εcut Dcut mcut W hshift hoffset hTower`、
  `hC₀`、`ha₀ hHI hT₀`；J8 另 `hrcs`）；
* **OPEN 族**：`hJ11 hJ15 hOpenJ`（J）、`hJ11₈ hJ15₈ hOpen8BJ`（J8，含 `CapBirthBudget_P6J7`）、
  `hJ11F hJ15F hOpenFJ`（JF）、`hJ11F8 hJ15F8 hOpenF8J`（JF8）；
* HP3 原槽 `hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF`；
* 四个 no-J10 kernel（`hkerJ0 hkerJ hkerF hkerF8`，**BLOCKED**，缺口表见 J10GEN3 G1 块）。
**无任何 J10 / `Q < R` 前提**；不切换任何冻结文本（example 无名）。HP6B 冻结装配
`hP6bTwoLevelTime_of_slots_P6HPB` 走 coarse 链（`outerTwoLevelTime_C11G7B` /
`hrestP_of_jointPrefix_bad_coarse_P6FK`），其孪生需另外 6 层 wrapper（含 `_exp_CXOU2` kernel 前提），列 HANDOVER。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **P5L 形适配（`_P6JG3`，PROVED，INTEGRATION）**：J8 / JF / JF8 producer 吃的展开 P5L 形（带与
`records` 的逐项匹配）⇒ J producer 吃的具名 `LateLinkedRecordsSupply_C11E F q`（丢掉匹配合取）。
供同一 witness 版 example 只用一个 `hP5L`。 -/
theorem lateLinkedRecordsSupply_of_matched_P6JG3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z)) :
    GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q := by
  intro D ζ m hζ
  obtain ⟨T, hT⟩ := hP5L D ζ m hζ
  refine ⟨T, fun k => ?_⟩
  obtain ⟨p, h1, h2, h3, h4, h5, h6, h7, rs, hrs, -⟩ := hT k
  exact ⟨p, h1, h2, h3, h4, h5, h6, h7, rs, hrs⟩

/-- **G3 切换 example（`_P6JG3`）**：见文件头。 -/
example
    (hkerJ0 : ObservedHistory.NotKKernelNoJ10_P6JB.{u})
    (hkerJ : ObservedHistory.NotKKernelDecNoJ10_P6JB.{u})
    (hkerF : ObservedHistory.FinalKernelNoJ10_P6JB.{u})
    (hkerF8 : ObservedHistory.FinalKernelDecNoJ10_P6JB.{u}) :
    True := by
  obtain ⟨_c₀, -, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, -, -, epsH, -, hHP⟩ :=
    (ObservedHistory.hrestP_of_jointPrefix_noJ10_P6JB.{u} hkerJ hkerF hkerF8)
  obtain ⟨_c₀', -, Cb', Rn', ζ', δ₀', m₀', hCb', hζ', hδ₀', -, -, epsJ, -, hJD⟩ :=
    (ObservedHistory.canonicalLateTimeCore_of_jointD_noJ10_P6JB.{u} hkerJ0)
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsH → ε ≤ epsJ →
      ε ≤ Classical.choose ObservedHistory.ancientWitness_decoupled_P6P.{u} →
      ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
      True := by
    intro ε hε hsmall hεH hεJ hεA hεX hεN hεcone
    obtain ⟨CH, -, hHP'⟩ := hHP ε hε hsmall hεH hεA hεX hεN hεcone
    obtain ⟨CJ, -, hJD'⟩ := hJD ε hε hsmall hεJ hεX hεN hεcone
    have _hcomp := fun {P : OrientedThreeStage.{u}} {g : P.Metric}
        {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} hanti hcan hder
        (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) hT₀m hQm pB Cc a₀ pB₈ Cc₈ a₀₈ pBF CcF a₀F pBF8 CcF8 a₀F8
        hP5L hδq records S εcut Dcut mcut W hshift hoffset hTower hC₀ ha₀ hHI hT₀ hJ11 hJ15 hOpenJ
        hδq₈ records₈ hP5L₈ hrcs₈ S₈ εcut₈ Dcut₈ mcut₈ W₈ hshift₈ hoffset₈ hTower₈ hC₀₈ ha₀₈ hHI₈
        hT₀₈ hJ11₈ hJ15₈ hOpen8BJ
        hδqF recordsF hP5LF SF εcutF DcutF mcutF WF hshiftF hoffsetF hTowerF ha₀F hHIF hT₀F hJ11F
        hJ15F hOpenFJ
        hδqF8 recordsF8 hP5LF8 SF8 εcutF8 DcutF8 mcutF8 WF8 hshiftF8 hoffsetF8 hTowerF8 ha₀F8 hHIF8
        hT₀F8 hJ11F8 hJ15F8 hOpenF8J
        hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF =>
      hJD' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
        (le_max_right _ _) (le_max_right _ _) (Real.toNNReal_le_toNNReal (le_max_right _ _))
        (F := F) (q := q) hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm
        (ObservedHistory.hgapJ_noJ10_of_producers_P6JB (pBase := pB) (Cc := Cc) (a₀ := a₀)
          Cb' Rn' ζ' δ₀' m₀' hCb'
          (fun C n => (hζ' C n).1) (fun C n => (hδ₀' C n).1)
          hanti hP5L hδq records S εcut Dcut mcut W hshift hoffset hTower hC₀ ha₀ hHI hT₀ hJ11 hJ15
          hOpenJ)
        (hHP' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
          (le_max_left _ _) (le_max_left _ _) (Real.toNNReal_le_toNNReal (le_max_left _ _))
          (F := F) (q := q) (C1f := 1) (C2f := 1) (m := 1) (kk := 0) Ctime₀ T₀ Qt hanti hT₀m hQm
          (ObservedHistory.hgapJ8_noJ10_of_capBirthBudget_P6JB (pBase := pB₈) (Cc := Cc₈)
            (a₀ := a₀₈)
            Cb Rn ζ δ₀ m₀ hCb
            (fun C n => (hζ C n).1) (fun C n => (hδ₀ C n).1)
            hanti hδq₈ records₈ hP5L₈ hrcs₈ S₈ εcut₈ Dcut₈ mcut₈ W₈ hshift₈ hoffset₈ hTower₈ hC₀₈
            ha₀₈ hHI₈ hT₀₈ hJ11₈ hJ15₈ hOpen8BJ)
          (ObservedHistory.hgapJF_noJ10_of_producers_P6JB (pBase := pBF) (Cc := CcF) (a₀ := a₀F)
            hanti hδqF recordsF hP5LF SF εcutF DcutF mcutF WF hshiftF hoffsetF hTowerF ha₀F hHIF
            hT₀F hJ11F hJ15F hOpenFJ)
          (ObservedHistory.hgapJF8_noJ10_of_producers_P6JB (pBase := pBF8) (Cc := CcF8) (a₀ := a₀F8)
            hanti hδqF8 recordsF8 hP5LF8 SF8 εcutF8 DcutF8 mcutF8 WF8 hshiftF8 hoffsetF8 hTowerF8
            ha₀F8 hHIF8 hT₀F8 hJ11F8 hJ15F8 hOpenF8J)
          hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF)
    trivial
  trivial

/-- **G3 切换 example，同一 witness 版（`_P6JG3`）**：四个 producer 共用 `hδq`、`records`、
chain `S εcut Dcut mcut W hshift hoffset hTower`、`a₀ ha₀ hHI`；P5L：J8 / JF / JF8 共用展开形 `hP5L₈`，
J 吃具名 `LateLinkedRecordsSupply_C11E`（非 defeq；J 位数学上可由
`lateLinkedRecordsSupply_of_matched_P6JG3 records hP5L₈` 付，内联进同一 `_hcomp` 时 JF8 的 `hT₀F8`
元变量作用域报错，留 HANDOVER）；各族只留 `hT₀`、`hC₀`、`hrcs` 与 OPEN 族。 -/
example
    (hkerJ0 : ObservedHistory.NotKKernelNoJ10_P6JB.{u})
    (hkerJ : ObservedHistory.NotKKernelDecNoJ10_P6JB.{u})
    (hkerF : ObservedHistory.FinalKernelNoJ10_P6JB.{u})
    (hkerF8 : ObservedHistory.FinalKernelDecNoJ10_P6JB.{u}) :
    True := by
  obtain ⟨_c₀, -, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, -, -, epsH, -, hHP⟩ :=
    (ObservedHistory.hrestP_of_jointPrefix_noJ10_P6JB.{u} hkerJ hkerF hkerF8)
  obtain ⟨_c₀', -, Cb', Rn', ζ', δ₀', m₀', hCb', hζ', hδ₀', -, -, epsJ, -, hJD⟩ :=
    (ObservedHistory.canonicalLateTimeCore_of_jointD_noJ10_P6JB.{u} hkerJ0)
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsH → ε ≤ epsJ →
      ε ≤ Classical.choose ObservedHistory.ancientWitness_decoupled_P6P.{u} →
      ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
      True := by
    intro ε hε hsmall hεH hεJ hεA hεX hεN hεcone
    obtain ⟨CH, -, hHP'⟩ := hHP ε hε hsmall hεH hεA hεX hεN hεcone
    obtain ⟨CJ, -, hJD'⟩ := hJD ε hε hsmall hεJ hεX hεN hεcone
    have _hcomp := fun {P : OrientedThreeStage.{u}} {g : P.Metric}
        {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} hanti hcan hder
        (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) hT₀m hQm pB Cc a₀
        hP5L hδq records S εcut Dcut mcut W hshift hoffset hTower hC₀ ha₀ hHI hT₀ hJ11 hJ15 hOpenJ
        hP5L₈ hrcs₈ hC₀₈ hT₀₈ hJ11₈ hJ15₈ hOpen8BJ hT₀F hJ11F hJ15F hOpenFJ
        hT₀F8 hJ11F8 hJ15F8 hOpenF8J
        hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF =>
      hJD' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
        (le_max_right _ _) (le_max_right _ _) (Real.toNNReal_le_toNNReal (le_max_right _ _))
        (F := F) (q := q) hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm
        (ObservedHistory.hgapJ_noJ10_of_producers_P6JB (pBase := pB) (Cc := Cc) (a₀ := a₀)
          Cb' Rn' ζ' δ₀' m₀' hCb'
          (fun C n => (hζ' C n).1) (fun C n => (hδ₀' C n).1)
          hanti hP5L hδq records S εcut Dcut mcut W hshift hoffset hTower hC₀ ha₀ hHI hT₀ hJ11 hJ15
          hOpenJ)
        (hHP' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
          (le_max_left _ _) (le_max_left _ _) (Real.toNNReal_le_toNNReal (le_max_left _ _))
          (F := F) (q := q) (C1f := 1) (C2f := 1) (m := 1) (kk := 0) Ctime₀ T₀ Qt hanti hT₀m hQm
          (ObservedHistory.hgapJ8_noJ10_of_capBirthBudget_P6JB (pBase := pB) (Cc := Cc)
            (a₀ := a₀)
            Cb Rn ζ δ₀ m₀ hCb
            (fun C n => (hζ C n).1) (fun C n => (hδ₀ C n).1)
            hanti hδq records hP5L₈ hrcs₈ S εcut Dcut mcut W hshift hoffset hTower hC₀₈
            ha₀ hHI hT₀₈ hJ11₈ hJ15₈ hOpen8BJ)
          (ObservedHistory.hgapJF_noJ10_of_producers_P6JB (pBase := pB) (Cc := Cc) (a₀ := a₀)
            hanti hδq records hP5L₈ S εcut Dcut mcut W hshift hoffset hTower ha₀ hHI
            hT₀F hJ11F hJ15F hOpenFJ)
          (ObservedHistory.hgapJF8_noJ10_of_producers_P6JB (pBase := pB) (Cc := Cc) (a₀ := a₀)
            hanti hδq records hP5L₈ S εcut Dcut mcut W hshift hoffset hTower
            ha₀ hHI hT₀F8 hJ11F8 hJ15F8 hOpenF8J)
          hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF)
    trivial
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
