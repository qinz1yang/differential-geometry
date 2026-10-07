import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWireC11SG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformSuppliesC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryCanonicalSupplyC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A

/-!
# `hfull` and the W1 tuple at the shared strong ceiling, without `hb`（O-CH11-S16CEIL G3）

G2 之后 `PreparedSpatialState` 带 `C1S_le : C1S ≤ strongC1_C11SC C.epsilon C.C1`（Base `1`、Step
`max` 归纳），`hstrong_of_stateStrong_C11SG S` 不再需要 `hb`，常数是 shared ceiling
`C1ceil_C11SC C = C1star_C12X C Ccore Cu`、`C2ceil_C11SC C`（`Ccore Cu` = engine 的闭项，在
`P / g / B / κ` 之前固定）。本文件把它接到：

* `hfull_of_chain_C11SC`：S16C `hfull` 形（`hfull_of_stateStrong_C12X`），`q` 只需满足 GAPTOP 的
  对角条件 `q.neckRadius = (chainDiagonal_C11A S).neckRadius`（`hpref_of_chainDiagonal_C11SC`
  从 chain 的 `parameters_past` 推出 narrow tuple 的 `hpref`）；
* `exists_w1_params_ceiling_C11SC`：`exists_w1_params_strong_C12X` 的结论形，但 `C1 C2` 取 shared
  ceiling（S4 / S5 用 `canonicalConstantsSupply_mono_C11RD` / `historyCanonicalSupply_mono_C12X`
  从旧 ceiling 升上来），且**无 `hstrong` 前提**。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- chain 的对角 `neckRadius` 在 `[0, n]` 上等于第 `n` 个观测的 `neckRadius`（chain successor 的
`parameters_past` + `diagonal_eq_on_prefix`）；故 GAPTOP 的对角条件给出 narrow tuple 的 `hpref`。 -/
theorem hpref_of_chainDiagonal_C11SC {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t := by
  intro n t ht
  rw [hdiag t ht.1]
  refine (CutoffParameters.diagonal_eq_on_prefix (fun m => (S.observation m).parameters)
    (parameter_compat_of_successors_C11RD _ fun m s hs => ?_) n ht).2.1
  have hs' : s ≤ preparedSpatialHorizon (m + 1) := by
    change s ≤ (3 : ℝ) ^ m
    exact hs.trans (nat_lt_three_pow m).le
  exact (S.successor (m + 1)).parameters_past s hs'

/-- **`hfull` at the shared ceiling, no `hb`**：任一 chain、任一满足对角条件的 `(F, q)`。 -/
theorem hfull_of_chain_C11SC {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric C.epsilon (C1ceil_C11SC.{u} C)
          (C2ceil_C11SC.{u} C) x,
        W.capTubeHasNeckChart C.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (s' : ℝ)
            (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
            (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
              G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
            s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G C.epsilon x
              s.time :=
  hfull_of_stateStrong_C12X S F hTower q (hpref_of_chainDiagonal_C11SC S q hdiag) _ _
    (hstrong_of_stateStrong_C11SG S)

/-- S16 v2 supply at the shared ceiling on any diagonal `(F, q)` of the chain, no `hb`. -/
theorem strongCanonicalSupplyV2_ceiling_C11SC {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    StrongCanonicalSupplyV2_C11E F q.neckRadius C.epsilon (C1ceil_C11SC.{u} C)
      (C2ceil_C11SC.{u} C) :=
  strongCanonicalSupplyV2_of_towerFull_C12X (hfull_of_chain_C11SC S F hTower q hdiag)

/-- **W1 + parameter-level enhanced fields + S16 at the shared ceiling**（无 `hstrong` / `hb`）：
`exists_w1_params_strong_C12X` 的结论形，`C1 C2 := C1ceil_C11SC C, C2ceil_C11SC C`，即 CONSTANTS-TABLE
H2 的 hext 共用对。 -/
theorem exists_w1_params_ceiling_C11SC {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u}) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      F.tower = S.tower ∧ ε = C.epsilon ∧ C1 = C1ceil_C11SC.{u} C ∧ C2 = C2ceil_C11SC.{u} C ∧
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
      ConeEpsilonSupply_C11E ε ∧ StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin,
    hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  obtain ⟨hfixed, hrad, hord, hacc, -⟩ := hstatic
  refine ⟨F, q, κ, records, C.epsilon, C1ceil_C11SC.{u} C, C2ceil_C11SC.{u} C, hTower, rfl, rfl,
    rfl, ⟨hfixed, hrad, hord, hacc⟩, fun t ht => ?_,
    canonicalConstantsSupply_mono_C11RD (canonicalConstantsSupply_of_closedBirthConstants_C11A C)
      (oldC1_le_C1ceil_C11SC C) (oldC2_le_C2ceil_C11SC C), hκ, hκanti, hδanti, hρanti,
    historyCanonicalSupply_mono_C12X hcan (oldC1_le_C1ceil_C11SC C) (oldC2_le_C2ceil_C11SC C),
    hwin, hnc, hδlim, hrecent, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
    modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
    coneEpsilonSupply_of_closedBirth_C11P2 C,
    strongCanonicalSupplyV2_of_stateStrong_C12X S F hTower q (fun n t ht => (hpref n t ht).2.1)
      _ _ (hstrong_of_stateStrong_C11SG S)⟩
  change q.delta t = ((S.observation (Nat.ceil t)).parameters).delta t
  exact (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).1

/-- **consumer**：W1 tuple 的 S16 合取与 S5 合取落在同一 shared ceiling 上，可直接作 `hext` 的
S5 / S16 两项（同一 `(F, q, C1, C2)`），中间没有任何显式常数前提。 -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u}) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      HistoryCanonicalSupply_C11S F q.neckRadius C.epsilon (C1ceil_C11SC.{u} C)
        (C2ceil_C11SC.{u} C) ∧
      StrongCanonicalSupplyV2_C11E F q.neckRadius C.epsilon (C1ceil_C11SC.{u} C)
        (C2ceil_C11SC.{u} C) := by
  obtain ⟨F, q, -, -, ε, C1, C2, -, rfl, rfl, rfl, -, -, -, -, -, -, -, hcan, -, -, -, -, -, -,
    -, hS⟩ := exists_w1_params_ceiling_C11SC S hP3 hprof
  exact ⟨F, q, hcan, hS⟩

end GC.LongTime.Ch11

end
