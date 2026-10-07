import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.PBaseAccuracyC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.RecordsCoarsenC11W7

set_option autoImplicit false

/-!
# S-C12X-DIAG (G5)：GAP-2b——`pBase.modelRadius ≥ D` 就够，不需要 `= D`（后缀 `_C12X`）

SMALLVOL3 的入口 `localKappaWindow_zero_of_narrowTuple_records_C11V3` 要 `q.modelRadius = D`；
`pBase.modelRadius` 在 astra 构造里**只有下界**：`PreparedDistanceClassProvider` 给的是
`DcapRequest ≤ p₀.modelRadius`（陈述），证明里 `p₀.modelRadius := max DcapRequest (max DN
(standardCapL + 1))`，`DN` 是 noncollapse 定理的内部 ∃ 见证——所以 `pBase.modelRadius = D`
不可得（要精确半径只能重写 provider 链，OUTER G6 的 (c) 项）。

OUTER G6 的 (b) 项已由 S-CH11-W1L7 G1（`Outer/RecordsCoarsenC11W7`）落地：
`localKappaWindow_zero_of_narrowTuple_records_ge_C11W7` 把 `q.modelRadius = D` 放宽成
`D ≤ q.modelRadius`（records 经 `restrictModelWindow` 粗化到 `D`），并有 chain 层入口
`localKappaWindow_of_chain_C11W7`（吃 `D ≤ pBase.modelRadius`、`pBase.modelAccuracy ≤ ε₀`、
`2 ≤ pBase.modelOrder`）。本文件把它与 G4 的 `…_pBase_acc_C12X` 接成端到端：

* `exists_chain_localKappaWindow_C12X`：`∃ fixed C, ∀ P g, ∃ pBase S, …`——pBase 带 `fixed`、hprof、
  `capWindowRadius + 1 ≤ pBase.modelRadius`，并且（取 `εR := localKappaWindow_of_chain_C11W7` 的 `ε₀`，
  `D := capWindowRadius_C11E + 1`，`N := exists_uniform_stageDegreeBound_C11W7 P`）同一条链 `S` 上有
  narrow tuple 的 `(F, q)`，`q` 的 `delta / neckRadius` 等于对角，且 K 链供给 ⇒ 每个 `A > 0` 的
  `nr := 0` window。K 链 `LocalKappaWideSupply_C11Q …` 仍是显式前提（GAP-3，归 KAPPA）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- `D := capWindowRadius_C11E + 1` 满足 SMALLVOL3 入口的 `4·transitionEnd + 6 ≤ D`。 -/
theorem capWindow_ge_smallvol_C12X :
    4 * StandardCap.transitionEnd + 6 ≤ capWindowRadius_C11E + 1 := by
  have hte := StandardCap.transitionEnd_pos
  unfold capWindowRadius_C11E
  linarith

/-- **G4 + W1L7 端到端**：`pBase`（`fixed`、hprof、`capWindowRadius + 1 ≤ modelRadius`）带一条链 `S`，
其 narrow tuple `(F, q)` 在 K 链供给下给出每个 `A > 0` 的 `nr := 0` window。 -/
theorem exists_chain_localKappaWindow_C12X :
    ∃ (fixed : StaticCapScaffold) (C : ClosedBirthConstants),
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (S : PreparedSpatialChain pBase C P g),
      pBase.fixed = fixed ∧ ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      capWindowRadius_C11E + 1 ≤ pBase.modelRadius ∧
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = S.tower ∧
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) ∧
        (LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
          ∀ A : ℝ, 0 < A → ∃ κ'' : ℝ, 0 < κ'' ∧
            LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') := by
  have hD := capWindow_ge_smallvol_C12X
  let Nof : ∀ P : OrientedThreeStage.{u}, ℕ :=
    fun P => (exists_uniform_stageDegreeBound_C11W7 P).choose
  let ε₀ : ClosedBirthConstants → ∀ P : OrientedThreeStage.{u}, P.Metric → ℝ := fun C P _ =>
    Classical.choose (localKappaWindow_of_chain_C11W7.{u} (capWindowRadius_C11E + 1) hD C (Nof P)
      (exists_uniform_stageDegreeBound_C11W7 P).choose_spec.1)
  have hε₀ : ∀ C P g, 0 < ε₀ C P g := fun C P _ =>
    (Classical.choose_spec (localKappaWindow_of_chain_C11W7.{u} (capWindowRadius_C11E + 1) hD C
      (Nof P) (exists_uniform_stageDegreeBound_C11W7 P).choose_spec.1)).1
  obtain ⟨fixed, C, hex⟩ := exists_prepared_spatial_chains_from_initial_pBase_acc_C12X.{u} ε₀ hε₀
  refine ⟨fixed, C, fun P g => ?_⟩
  obtain ⟨pBase, base, hfixed, hprof, hacc, hrad, -, -, hS⟩ := hex P g
  obtain ⟨S, -, -⟩ := hS (fun _ _ _ _ => 1) (fun _ _ _ _ => one_pos)
  refine ⟨pBase, S, hfixed, hprof, hrad, ?_⟩
  exact (Classical.choose_spec (localKappaWindow_of_chain_C11W7.{u} (capWindowRadius_C11E + 1) hD C
    (Nof P) (exists_uniform_stageDegreeBound_C11W7 P).choose_spec.1)).2 S hrad hacc hprof.2.1
    (fun F n j => (exists_uniform_stageDegreeBound_C11W7 P).choose_spec.2 F n j)

end GC.LongTime.Ch11
