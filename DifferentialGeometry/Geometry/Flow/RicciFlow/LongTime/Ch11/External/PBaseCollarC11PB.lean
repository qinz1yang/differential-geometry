import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.PBaseC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticCollarAdmitsC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false

/-!
# S-CH11-PBASE (G2)：pBase 的 collar 条（路线 A，后缀 `_C11PB`）

`PBaseC12X` 把 `collarAdmitsAllOrders_C11E fixed.collarLength fixed.collar_pos` 留成显式前提
`hcollar`（`CH12X-PBASE-GAP.md` §3：`∃ A` 的两次 `obtain` 见证不相等）。本文件用 patched-at-path 的
astra ∃ 链（`PreparedSpatialProvidersPortC11P` 等，见 DELIVERIES 块的 15 文件 diff）把
`∃ (A : ℝ) (hA : 0 < A), fixed = StaticCapScaffold.ofCollarLength A hA ∧ StaticCollarAdmits A hA`
一路从 `RecenteredStaticPreparation`（`StaticPinchingInsertion` 的 `hmod`）携带到 provider：

* `collarAdmitsAllOrders_of_staticCollarAdmits_C11PB`：adapter，`StaticCollarAdmits.{0, 0, u} A hA`
  ⇒ `collarAdmitsAllOrders_C11E.{u} A hA`（`E = H = ThreeSpace`，`M : Type u`；同
  `exists_collarLength_P3_C11E` 的转法，只去掉 `δ₀ < 1 / 2`）；
* `exists_prepared_spatial_chains_from_initial_pBaseCollar_C11PB`：`PBaseC12X` 的加强形（同一个
  `C / pBase / base / chain`）多两条：
  `∃ A hA, fixed = ofCollarLength A hA ∧ collarAdmitsAllOrders_C11E A hA`，以及 ch12 的
  `C.epsilon ≤ εStrong_C12X`（provider 换成 `exists_closedBirthConstants_strong_C12X`）；
* `exists_prepared_spatial_chains_from_initial_pBaseSupplies_C11PB`：consumer，`hcollar` 被 discharge，
  `a12Enhanced_of_chain_C11P2` 的 `hP3 / hprof` 对链的 `pBase` 直接成立：
  `CollarWindowSupply_C11E pBase ∧ ModelConstraintsSupply_C11E pBase εProf_C11E`。
-/

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- adapter：宇宙多态的 `StaticCollarAdmits` 在 `.{0, 0, u}` 处就是 `collarAdmitsAllOrders_C11E.{u}`。 -/
theorem collarAdmitsAllOrders_of_staticCollarAdmits_C11PB {A : ℝ} {hA : 0 < A}
    (h : DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticCollarAdmits.{0, 0, u} A hA) :
    collarAdmitsAllOrders_C11E.{u} A hA := by
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, -, hb⟩ := h D hD m ε hε
  exact ⟨δ₀, hδ₀, fun δ' hδ' hle M _ _ _ _ g x₀ d => hb δ' hδ' hle g x₀ d⟩

/-- `fixed = ofCollarLength A hA` 的 collar 条沿等式传到 `fixed.collarLength`。 -/
theorem collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB {fixed : StaticCapScaffold}
    (h : ∃ (A : ℝ) (hA : 0 < A), fixed = StaticCapScaffold.ofCollarLength A hA ∧
      collarAdmitsAllOrders_C11E.{u} A hA) :
    collarAdmitsAllOrders_C11E.{u} fixed.collarLength fixed.collar_pos := by
  obtain ⟨A, hA, rfl, hcol⟩ := h
  exact hcol

/-- **`PBaseC12X` 的 collar 加强形**：`exists_prepared_spatial_chains_from_initial_pBase_C12X` 的全部结论
（同一个 `C / pBase / base / chain`），`fixed` 先于 `P g` 选定，并多一条
`∃ A hA, fixed = ofCollarLength A hA ∧ collarAdmitsAllOrders_C11E A hA`（`hcollar` 不再是前提）。 -/
theorem exists_prepared_spatial_chains_from_initial_pBaseCollar_C11PB :
    ∃ (fixed : StaticCapScaffold) (C : ClosedBirthConstants),
    C.epsilon ≤ εStrong_C12X.{u} ∧
    (∃ (A : ℝ) (hA : 0 < A), fixed = StaticCapScaffold.ofCollarLength A hA ∧
      collarAdmitsAllOrders_C11E.{u} A hA) ∧
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
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, ⟨-, A, hA, hfix, hcol⟩, prepareClass, analytic,
      makeBase⟩ :=
    exists_closedBirthConstants_strong_C12X.{u}
      (capWindowRadius_C11E + 1) εProf_C11E.{u} hD εProf_pos_C11E.{u}
  refine ⟨fixed, C, hεs, ⟨A, hA, hfix, collarAdmitsAllOrders_of_staticCollarAdmits_C11PB hcol⟩,
    ?_⟩
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

/-- **consumer**：`hP3 / hprof` 对链的 `pBase` 直接成立（`PBaseC12X` 里的 `hcollar` 已 discharge）。 -/
theorem exists_prepared_spatial_chains_from_initial_pBaseSupplies_C11PB :
    ∃ C : ClosedBirthConstants, C.epsilon ≤ εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      CollarWindowSupply_C11E.{u} pBase ∧ ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      base.history = RetainedCoreHistory.atZero P g ∧ base.radius ≤ 1 := by
  obtain ⟨fixed, C, hεs, hpkg, hchain⟩ :=
    exists_prepared_spatial_chains_from_initial_pBaseCollar_C11PB.{u}
  refine ⟨C, hεs, fun P g => ?_⟩
  obtain ⟨pBase, base, hfixed, hprof, hrad, hhist, hrbase, -⟩ := hchain P g
  exact ⟨pBase, base,
    collarWindowSupply_of_provider_fixed_C12X hfixed
      (collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB hpkg) hrad,
    hprof, hhist, hrbase⟩

end GC.LongTime.Ch11
