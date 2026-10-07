import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialProviders
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecursion
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false

/-!
# S-C12X-DIAG (G2)：`pBase` 的参数约束（P3 / hprof）与 astra existence 的对接（后缀 `_C12X`）

`a12Enhanced_of_chain_C11P2` 的 `hP3 : CollarWindowSupply_C11E pBase`、
`hprof : ModelConstraintsSupply_C11E pBase εProf_C11E` 是对**链的 `pBase`** 的约束：

* `ModelConstraintsSupply_C11E pBase ε₀ := pBase.modelAccuracy ≤ ε₀ ∧ 2 ≤ pBase.modelOrder ∧
  transitionEnd + 1 ≤ pBase.modelRadius`；
* `CollarWindowSupply_C11E pBase := collarAdmitsAllOrders_C11E pBase.fixed.collarLength _ ∧
  capWindowRadius_C11E + 1 ≤ pBase.modelRadius`。

astra `exists_prepared_spatial_chains_from_initial` 的 `pBase` 是**输出**（`∃ pBase`，内部由
`prepareInitial` 选出，只暴露 `pBase.fixed = fixed`、`recenter`），不是可选的输入。但同一条构造的
reserve-quality 版
（`exists_prepared_spatial_initial_state_with_distance_scalars_with_reserve_quality`，参数
`Dstar εReserve`）把 `prepared.HasReserveQuality Dstar εReserve`
（`Dstar ≤ modelRadius ∧ modelAccuracy ≤ εReserve ∧ 2 ≤ modelOrder ∧ …`）和
`prepared.parameters = pBase` 留在输出里，`Dstar εReserve` 任意取正。取
`Dstar = capWindowRadius_C11E + 1`、`εReserve = εProf_C11E`：

* `modelConstraints_capRadius_of_reserve_C12X`：reserve quality ⇒ `ModelConstraintsSupply_C11E pBase
  εProf`（hprof **全部**）与 `capWindowRadius + 1 ≤ pBase.modelRadius`（hP3 的第二条）；
* `exists_prepared_spatial_chains_from_initial_pBase_C12X`：
  `exists_prepared_spatial_chains_from_initial`
  的**逐字加强**——同一个 `C`、同一个 `pBase / base`、同一条 chain 存在陈述，另外暴露
  `pBase.fixed = fixed`（`fixed` 在 `P g` 之前选定）与上面两条约束；
* `collarWindowSupply_of_provider_fixed_C12X`：hP3 只剩第一条 `collarAdmitsAllOrders_C11E
  fixed.collarLength`。这一条 astra 的 provider 链没有暴露（`fixed` 在 ∃ 里，约 20 个文件），
  见 `docs/geometrization/chapter8/out/CH12X-PBASE-GAP.md`；这里把它写成**显式前提**。
-/

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- `Dstar := capWindowRadius_C11E + 1`、`εReserve := εProf_C11E` 的 reserve quality ⇒ hprof 的三条
与 hP3 的半径条。 -/
theorem modelConstraints_capRadius_of_reserve_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {B : ℝ}
    (prepared : ClosedBirthPreparedClass pBase C P g B) (hpar : prepared.parameters = pBase)
    (hres : prepared.HasReserveQuality (capWindowRadius_C11E + 1) εProf_C11E.{u}) :
    ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      capWindowRadius_C11E + 1 ≤ pBase.modelRadius := by
  obtain ⟨hD, hacc, hord, -⟩ := hres
  rw [hpar] at hD hacc hord
  refine ⟨⟨hacc, hord, ?_⟩, hD⟩
  have hte := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
  unfold capWindowRadius_C11E at hD
  linarith

/-- hP3 = collar 条 + 半径条；collar 条对 `pBase.fixed = fixed` 沿等式传递。 -/
theorem collarWindowSupply_of_provider_fixed_C12X {pBase : CutoffParameters}
    {fixed : StaticCapScaffold} (hfixed : pBase.fixed = fixed)
    (hcollar : collarAdmitsAllOrders_C11E.{u} fixed.collarLength fixed.collar_pos)
    (hrad : capWindowRadius_C11E + 1 ≤ pBase.modelRadius) :
    CollarWindowSupply_C11E.{u} pBase := by
  have key : ∀ (A A' : ℝ) (hA : 0 < A) (hA' : 0 < A'), A = A' →
      collarAdmitsAllOrders_C11E.{u} A hA → collarAdmitsAllOrders_C11E.{u} A' hA' := by
    intro A A' _ _ e h
    subst e
    exact h
  exact ⟨key _ _ _ _ (congrArg StaticCapScaffold.collarLength hfixed.symm) hcollar, hrad⟩

/-- **astra existence 的逐字加强**：`exists_prepared_spatial_chains_from_initial` 的全部结论
（`C`、`pBase`、`base`、chain 存在），加上 `pBase.fixed = fixed`（`fixed` 先于 `P g`）、
`ModelConstraintsSupply_C11E pBase εProf_C11E`（hprof）与
`capWindowRadius_C11E + 1 ≤ pBase.modelRadius`（hP3 的半径条）。 -/
theorem exists_prepared_spatial_chains_from_initial_pBase_C12X :
    ∃ (fixed : StaticCapScaffold) (C : ClosedBirthConstants),
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      pBase.fixed = fixed ∧ ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      capWindowRadius_C11E + 1 ≤ pBase.modelRadius ∧
      base.history = RetainedCoreHistory.atZero P g ∧ base.radius ≤ 1 ∧
      ∀ (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
      (∀ n L future r, 0 < budget n L future r) →
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  have hD : 0 < capWindowRadius_C11E + 1 := by
    have hte := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    positivity
  obtain ⟨Cdist, hCdist, fixed, recenter, C, -, _, prepareClass, analytic, makeBase⟩ :=
    exists_closedBirthConstants_strong_C12X.{u}
      (capWindowRadius_C11E + 1) εProf_C11E.{u} hD εProf_pos_C11E.{u}
  refine ⟨fixed, C, ?_⟩
  intro P g
  obtain ⟨pBase, prepared, base, hquality, _, hfixed, hrc, hpar, hprepared, hDistance, hS⟩ :=
    makeBase P g
  rcases hS with ⟨hbase, _, _, _, _, _, _, _, _, _, hrbase, _, _⟩
  obtain ⟨hprof, hrad⟩ := modelConstraints_capRadius_of_reserve_C12X prepared hpar hquality
  refine ⟨pBase, base, hfixed, hprof, hrad, hbase, hrbase, ?_⟩
  intro budget hbudget
  obtain ⟨S, hS0, -, hfut⟩ := exists_prepared_spatial_chain_with_distance_scalars Cdist pBase C
    (by simpa only [hfixed, hrc] using prepareClass)
    analytic base hbase hDistance hrbase budget hbudget
  exact ⟨S, hS0, hfut⟩

end GC.LongTime.Ch11
