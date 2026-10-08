import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadius

/-!
# S-CH11-FIX7 port of astra `PreparedSpatialBase`（`PortC11P`）

来源：donor `PreparedSpatialBase.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 1 个 error；本 port 只做 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `finalMetric_heq` 的 `intro t; rw [add_zero]; exact HEq.rfl`：本树里 `rw [add_zero]` 之后的
  自动 `rfl` 已经关掉 `HEq a a` 目标，多余的 `exact HEq.rfl` 报 "No goals"，删去。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow
universe u

/-- Initialize the recurrence with the supplied prepared class, the original
zero-time marking, and a radius chosen before any fine event request. -/
theorem exists_prepared_spatial_base_with_small_test_margin
    (cMax : ℝ) (hcMax : 0 < cMax)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase) :
    ∃ S : PreparedSpatialState pBase C P g 0 1,
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.radius * Real.sqrt S.prepared.Qall ≤ 100 * cMax ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  classical
  have htransport : ∀ {b b' : ℝ} (h : b = b')
      (K : ClosedBirthPreparedClass pBase C P g b),
      let K' : ClosedBirthPreparedClass pBase C P g b' := h ▸ K
      K'.parameters = K.parameters ∧ K'.Qall = K.Qall ∧ HEq K' K ∧
        K'.qStrong = K.qStrong := by
    intro b b' h K
    cases h
    exact ⟨rfl, rfl, HEq.rfl, rfl⟩
  let prepared₀ : ClosedBirthPreparedClass pBase C P g ((1 : ℝ) - 0) :=
    (sub_zero (1 : ℝ)).symm ▸ prepared
  have hsame := htransport (sub_zero (1 : ℝ)).symm prepared
  have hparameters : prepared₀.parameters = prepared.parameters := hsame.1
  have hQ : prepared₀.Qall = prepared.Qall := hsame.2.1
  have hprepared : HEq prepared₀ prepared := hsame.2.2.1
  have hqStrong : prepared₀.qStrong = prepared.qStrong := hsame.2.2.2
  have hroot : 0 < Real.sqrt prepared.Qall := Real.sqrt_pos.mpr prepared.Qall_pos
  have hmargin : 0 < 100 * cMax / Real.sqrt prepared.Qall :=
    div_pos (mul_pos (by norm_num) hcMax) hroot
  obtain ⟨r, hr, hrceiling, hthreshold⟩ :=
    exists_canonical_radius_below
      (R := min 1 (100 * cMax / Real.sqrt prepared.Qall))
      (lt_min one_pos hmargin) (lt_max_of_lt_left prepared.Qall_pos : 0 < max prepared.Qall
        prepared.qStrong)
  have hrone : r ≤ 1 := hrceiling.trans (min_le_left _ _)
  have hfit : r * Real.sqrt prepared.Qall ≤ 100 * cMax :=
    (le_div_iff₀ hroot).mp (hrceiling.trans (min_le_right _ _))
  let H := RetainedCoreHistory.atZero P g
  let p : CutoffParameters := { prepared.parameters with
    delta := fun _ => (1 : ℝ) / 2
    delta_pos := fun _ _ => by norm_num
    delta_lt_one := fun _ _ => by norm_num
    neckRadius := fun _ => r
    neckRadius_pos := fun _ _ => hr }
  let nativeRecords : ∀ i : Fin H.eventCount,
      GeometricCutoffRecord H.toHistory i prepared.parameters := fun i => Fin.elim0 i
  have hclass : H.IsCanonicalCutoffRecordFamily prepared₀.parameters
      prepared₀.deltaBound prepared₀.radiusBound nativeRecords := by
    unfold RetainedCoreHistory.IsCanonicalCutoffRecordFamily
    rw [hparameters]
    exact ⟨rfl, rfl, rfl, rfl, rfl,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  let S : PreparedSpatialState pBase C P g 0 1 := {
    history := H
    initial := InitialIdentification.atZero P g
    horizon_eq := rfl
    parameters := p
    records := fun i => Fin.elim0 i
    static_eq := by
      change prepared.parameters.fixed = pBase.fixed ∧
        prepared.parameters.modelRadius = pBase.modelRadius ∧
        prepared.parameters.modelOrder = pBase.modelOrder ∧
        prepared.parameters.modelAccuracy = pBase.modelAccuracy ∧
        prepared.parameters.recenterConstant = pBase.recenterConstant
      rw [hbase]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    modelRadius_bound := prepared.modelRadius_bound
    eventControl := fun i => Fin.elim0 i
    windows := fun i => Fin.elim0 i
    linked := fun i => Fin.elim0 i
    radial := fun i => Fin.elim0 i
    kappa := 1
    kappa_pos := one_pos
    noncollapsed := H.noncollapsedBefore_zero 1 C.epsilon
    nativeStage := P
    nativeMetric := g
    native := H
    nativeInitial := InitialIdentification.atZero P g
    nativeParameters := prepared.parameters
    nativeRecords := nativeRecords
    shift := 0
    offset := 0
    prepared := prepared₀
    nativeClass := hclass
    nativeRecordHyp := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    nativeEventControl := fun i => Fin.elim0 i
    affine := {
      count_eq := rfl
      time_eq := fun _ => (add_zero (0 : ℝ)).symm
      stage_eq := fun _ => rfl
      initialMetric_heq := fun _ => HEq.rfl
      event_heq := fun i => Fin.elim0 i }
    horizon_affine := (add_zero (0 : ℝ)).symm
    native_lt_capacity := by change (0 : ℝ) < 1 - 0; norm_num
    finalMetric_heq := by
      intro t
      rw [add_zero]
    radius := r
    radius_pos := hr
    threshold_le := by rw [hQ]; exact (le_max_left _ _).trans hthreshold
    radius_antitone := fun _ _ _ _ _ => le_rfl
    radius_after := fun _ _ => rfl
    delta_antitone := fun _ _ _ _ _ => le_rfl
    canonical := by
      intro t ht
      exact False.elim ((not_lt_of_ge t.2.1) ht)
    C1S := 1
    C2S := 1
    C1S_ge_one := le_rfl
    C2S_ge_one := le_rfl
    C1S_le := one_le_strongC1_C11SC C.C1_ge_one _
    C2S_le := one_le_strongC2_C11SC C.C2_ge_one _ _
    strong_threshold_le := by
      rw [hqStrong]
      exact (le_max_right _ _).trans hthreshold
    strong := by
      intro t ht
      exact False.elim ((not_lt_of_ge t.2.1) ht) }
  have hfitS : S.radius * Real.sqrt S.prepared.Qall ≤ 100 * cMax := by
    change r * Real.sqrt prepared₀.Qall ≤ 100 * cMax
    rw [hQ]
    exact hfit
  exact ⟨S, rfl, HEq.rfl, rfl, HEq.rfl, rfl, HEq.rfl, rfl, hprepared,
    rfl, rfl, hrone, hfitS, rfl, fun _ => rfl⟩

/-- Compatibility projection of the same refined marked zero-state constructor. -/
theorem exists_prepared_spatial_base
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase) :
    ∃ S : PreparedSpatialState pBase C P g 0 1,
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  obtain ⟨S, hHistory, hInitial, hStage, hMetric, hNative, hNativeInitial,
    hParameters, hPrepared, hShift, hOffset, hRadius, _, hDelta, hNeck⟩ :=
    exists_prepared_spatial_base_with_small_test_margin 1 one_pos pBase C P g prepared hbase
  exact ⟨S, hHistory, hInitial, hStage, hMetric, hNative, hNativeInitial,
    hParameters, hPrepared, hShift, hOffset, hRadius, hDelta, hNeck⟩

end GC.GeneralFlow
