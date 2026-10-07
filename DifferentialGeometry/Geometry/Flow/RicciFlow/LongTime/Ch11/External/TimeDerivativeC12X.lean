import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDiagonalDerivative

set_option autoImplicit false

/-!
# S-C12X-DIAG (G1)：S11 `TimeDerivativeSupply_C11E` ⇐ astra `PreparedSpatialDiagonalDerivative`
（后缀 `_C12X`）

astra `PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold` 已由 FIX9 G5 落地
（`Surgery/History/PreparedSpatialDiagonalDerivative` shim → `…PortC11P`，陈述逐字同 donor）。
ENHSUP 的 `timeDerivativeSupply_of_diagonal_C11P2` 只缺 `hdiag`；本文件把 astra 定理的结论喂给它，
并在 chain 层（不经 outer 的 `BlockTower_C11W`，对照 W1L4 `timeDerivativeSupply_of_blockTower_C11W4`）
给出：

* `diagonal_neckRadius_of_prefix_C12X`：narrow tuple 的 `hpref` ⇒ astra `hdiagonal`（W1L4 同一引理的
  chain 层复述，免 `Outer/` 依赖）；
* `timeDerivativeSupply_of_astra_C12X`（**S11 的 chain 层 producer**）：astra 的链数据
  `(S, εcut, Dcut, mcut, W, hshift, hoffset)`（逐步 retention `W` 与 shift / offset 恒等式不是
  `PreparedSpatialChain` 的字段，由 outer block 构造给）+ `(F, hTower, q, hanti, hdiagonal)` ⇒
  `TimeDerivativeSupply_C11E F q.neckRadius C.Ctime`；常数仍是 Γ 的 `C.Ctime`；
* `exists_w1_params_timeDerivative_C12X`：与 `w1_params_of_preparedSpatialChain_C11P2` 同一个
  `(F, q, κ, records)` 上，在它的全部结论之后再加 S11 合取项（`a12Enhanced_of_chain_C11P2` 的 `hext`
  里 `TimeDerivativeSupply_C11E F q.neckRadius C.Ctime` 一项，逐字）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- narrow tuple 的 `hpref`（`q.neckRadius` 在 `[0, n]` 上等于第 `n` 个观测的 `neckRadius`）⇒
astra 的 `hdiagonal`（`q.neckRadius` 等于对角 `neckRadius`，`v ≥ 0`）。 -/
theorem diagonal_neckRadius_of_prefix_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hpref : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t) :
    ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v :=
  fun v hv => hpref (Nat.ceil v) v ⟨hv, Nat.le_ceil v⟩

/-- **S11 的 chain 层 producer**：astra 对角时间导数定理（binder 逐字取自它）+ ENHSUP 的
`timeDerivativeSupply_of_diagonal_C11P2`。`hdiagonal` 的形同 astra 定理；narrow tuple 给的 `hpref`
经 `diagonal_neckRadius_of_prefix_C12X` 转成它。 -/
theorem timeDerivativeSupply_of_astra_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hdiagonal : ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v) :
    TimeDerivativeSupply_C11E F q.neckRadius C.Ctime :=
  timeDerivativeSupply_of_diagonal_C11P2 F q.neckRadius C.Ctime
    (PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold S εcut Dcut mcut W
      hshift hoffset F hTower q hanti hdiagonal)

/-- **W1 + 参数级 enhanced 字段 + S11**：`w1_params_of_preparedSpatialChain_C11P2` 的全部结论，
外加同一个 `(F, q)` 上的 `TimeDerivativeSupply_C11E F q.neckRadius C.Ctime`。 -/
theorem exists_w1_params_timeDerivative_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      F.tower = S.tower ∧ ε = C.epsilon ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t) ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      CollarWindowSupply_C11E.{u} q ∧ ModelConstraintsSupply_C11E q εProf_C11E.{u} ∧
      ConeEpsilonSupply_C11E ε ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin,
    hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  obtain ⟨hfixed, hrad, hord, hacc, -⟩ := hstatic
  refine ⟨F, q, κ, records, C.epsilon, max C.C1s C.Cbirth,
    max C.C2s (max C.Cbirth (C.Cgrad : ℝ)), hTower, rfl, ⟨hfixed, hrad, hord, hacc⟩, fun t ht => ?_,
    canonicalConstantsSupply_of_closedBirthConstants_C11A C, hκ, hκanti, hδanti, hρanti,
    hcan, hwin, hnc, hδlim, hrecent, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
    modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
    coneEpsilonSupply_of_closedBirth_C11P2 C,
    timeDerivativeSupply_of_astra_C12X S εcut Dcut mcut W hshift hoffset F hTower q hρanti
      (diagonal_neckRadius_of_prefix_C12X S q (fun n t ht => (hpref n t ht).2.1))⟩
  change q.delta t = ((S.observation (Nat.ceil t)).parameters).delta t
  exact (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).1

end GC.LongTime.Ch11
