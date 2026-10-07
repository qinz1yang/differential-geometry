import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.PBaseC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false

/-!
# S-C12X-DIAG (G4)：`pBase.modelAccuracy ≤ εR` 依赖 `C`、`(P, g)`（GAP-2，后缀 `_C12X`）

`exists_prepared_spatial_chains_from_initial_pBase_C12X`（PBaseC12X）用 `εReserve := εProf_C11E`，
常数，在 `∃ C` 之前。SMALLVOL3 的 `localKappaWindow_zero_of_narrowTuple_records_C11V3` 要的是
`q.modelAccuracy ≤ ε₀(D, C.epsilon, C1, C2, N(P))`——依赖 `C` 与 `P`（`N = N(P, g)`）。

做法同 O-CH11-OUTER G6（`Outer/ReserveByPointC11W6`）：先在 `εReserve₀ = 1` 处实例化 Providers 的
reserve-quality 初态定理，只取 `Cdist fixed recenter C prepareClass analytic`（它们与 `εReserve` 无关，
证明体里先于 `εReserve` 被选出）；对每个 `(P, g)` 直接调 PCBC
（`exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality`），
取 `εReserve := min εProf_C11E (εR C P g)`，照 Providers 的 record 字面量重组 capacity 1 的 class，
再接 `exists_prepared_spatial_base_with_distance_scalars` 与
`exists_prepared_spatial_chain_with_distance_scalars`（与 astra existence 同一条链）。

**[FROZEN v2]** 量词顺序：`∃ fixed C, ∀ P g, …`——`fixed` 与 `C` 先于 `P g`，`εR` 是定理参数，可依赖
`C`（取值时用 `C` 本身）与 `(P, g)`。简报的 `εR : ∀ P, ℝ` 是特例 `fun _ P _ => εR P`。
`C` 的构造不依赖 `εReserve`，所以这是最强顺序（`εR` 不能依赖 `pBase`：`pBase` 在 `εR` 之后选出）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **astra existence 的逐字加强（按点 accuracy）**：`exists_prepared_spatial_chains_from_initial_pBase_C12X`
的全部结论，另加 `pBase.modelAccuracy ≤ εR C P g`；`εR` 任意正（可依赖 `C`、`P`、`g`）。 -/
theorem exists_prepared_spatial_chains_from_initial_pBase_acc_C12X
    (εR : ClosedBirthConstants → ∀ P : OrientedThreeStage.{u}, P.Metric → ℝ)
    (hεR : ∀ C P g, 0 < εR C P g) :
    ∃ (fixed : StaticCapScaffold) (C : ClosedBirthConstants),
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      pBase.fixed = fixed ∧ ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      pBase.modelAccuracy ≤ εR C P g ∧ capWindowRadius_C11E + 1 ≤ pBase.modelRadius ∧
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
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, -, prepareClass, analytic, -⟩ :=
    exists_closedBirthConstants_strong_C12X.{u} (capWindowRadius_C11E + 1) 1 hD one_pos
  refine ⟨fixed, C, fun P g => ?_⟩
  have hεRes : 0 < min εProf_C11E.{u} (εR C P g) := lt_min εProf_pos_C11E (hεR C P g)
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
      (capWindowRadius_C11E + 1) (min εProf_C11E.{u} (εR C P g)) hD hεRes Cdist fixed recenter
      prepareClass C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth C.Ctime C.Cgrad
      C.epsilon_pos ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos, hεs⟩
      analytic P g
  obtain ⟨pBase, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    hDReserve, hεReserveBound, hmReserve, hscaleReserve, hStrong,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, hQall, hQallPos,
    hcap, hrec, extension, control⟩ := prepareInitial 1 one_pos
  obtain ⟨C1h, C2h, qh, hC1h, hC2h, hC1hb, hC2hb, hqh, hStrongV⟩ := hStrong
  let prepared : ClosedBirthPreparedClass pBase C P g 1 := {
    parameters := pBase
    deltaBound := δb
    radiusBound := ρb
    epsilonClass := εClass
    kappaClass := κClass
    kappa := κ
    qcan := qcan
    qs := qs
    Qzero := Qzero
    Qbirth := Qbirth
    Qall := Qall
    fixed_eq := rfl
    recenter_eq := rfl
    deltaBound_pos := hδb
    radiusBound_pos := hρb
    epsilonClass_pos := hεClass
    epsilonClass_small := hεClass11
    kappaClass_pos := hκClass
    kappa_pos := hκ
    qcan_pos := hqcan
    qcan_le_qs := hqs
    qs_le := hqsC
    Qzero_pos := hQzero
    Qbirth_ge := hQbirth
    Qall_eq := hQall
    Qall_pos := hQallPos
    modelRadius_bound := hcap
    recenter_bound := hrec
    zero_bound := zeroBound
    extension := extension.forget
    control := control
    epsilon_strong := hεs
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := hStrongV }
  have hprepared : prepared.HasDistanceExtension Cdist := extension
  have hprep : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist := by
    rw [hfixed, hrc]
    exact prepareClass
  obtain ⟨base, hDistance, hS⟩ :=
    exists_prepared_spatial_base_with_distance_scalars Cdist pBase C P g prepared rfl hprepared
  rcases hS with ⟨hbase, _, _, _, _, _, _, _, _, _, hrbase, _, _⟩
  obtain ⟨hprof, hrad⟩ := modelConstraints_capRadius_of_reserve_C12X prepared rfl
    ⟨hDReserve, hεReserveBound.trans (min_le_left _ _), hmReserve, hscaleReserve⟩
  refine ⟨pBase, base, hfixed, hprof, hεReserveBound.trans (min_le_right _ _), hrad, hbase,
    hrbase, ?_⟩
  intro budget hbudget
  obtain ⟨S, hS0, -, hfut⟩ := exists_prepared_spatial_chain_with_distance_scalars Cdist pBase C
    hprep analytic base hbase hDistance hrbase budget hbudget
  exact ⟨S, hS0, hfut⟩

end GC.LongTime.Ch11
