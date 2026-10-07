import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

/-!
# CX-CONST：在首次选取 closed-birth constants 时同时满足 P6 accuracy

交接 I / ConstantsTable E5：给定正数 `εP6`，把它加入首次选择 `ε` 的 minimum，
然后在该 `ε` 上重新调用 uniform analytic packet。常数仍在 `P g B κ` 之前选择；
保留 strong selection 的 collar、distance、analytic 和 initial-state 全部结论。
此定理不给 `hwin`、`Q < R` 或 stage witness transfer，也不改变已有 prepared state。

来源复用：`ClosedBirthConstantsStrongC12X.lean:38–185`（C12X S16 D2）及
`UniformClosedBirthObservationEstimatesPortC11P.lean:34–74` 的 `∀ ε` uniform packet。
只改变 ε 的选择和增加 `C.epsilon ≤ εP6` 合取；其余 construction 逐项复用。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

universe u

open private reserve_quality_of_same_prepared_class from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData

/-- CX-CONST：正 accuracy 上界先于所有 geometric data 给出，完整 strong packet 保留。 -/
theorem exists_closedBirthConstants_strong_accuracy_CXCA
    (Dstar εReserve εP6 : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (hεP6 : 0 < εP6) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ) (C : ClosedBirthConstants),
      C.epsilon ≤ εP6 ∧ C.epsilon ≤ εStrong_C12X.{u} ∧
      (4 ≤ recenter ∧ ∃ (A : ℝ) (hA : 0 < A),
        fixed = StaticCapScaffold.ofCollarLength A hA ∧
        StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
      PreparedDistanceClassProvider.{u} fixed recenter Cdist ∧
      (∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon) ∧
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
      ∃ (pBase : CutoffParameters)
        (prepared : ClosedBirthPreparedClass pBase C P g 1)
        (S : PreparedSpatialState pBase C P g 0 1),
        prepared.HasReserveQuality Dstar εReserve ∧
        S.prepared.HasReserveQuality Dstar εReserve ∧
        pBase.fixed = fixed ∧ pBase.recenterConstant = recenter ∧
        prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
        S.DistanceData Cdist ∧
        S.history = RetainedCoreHistory.atZero P g ∧
        HEq S.initial (InitialIdentification.atZero P g) ∧
        S.nativeStage = P ∧ HEq S.nativeMetric g ∧
        S.native = RetainedCoreHistory.atZero P g ∧
        HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
        S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
        S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
        S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
        (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  obtain ⟨Cdist, hCdist, fixed, recenter, hrecenter, prepareClass⟩ :=
    exists_common_prepared_geometric_observation_extension_before_quality_with_distance_scalars.{u}
  obtain ⟨εbar, hεbar, uniform⟩ := exists_uniform_closed_birth_observation_estimate_packet.{u}
  -- P6 accuracy 在选取 analytic constants 之前加入 minimum。
  let ε : ℝ :=
    min (min (min (εbar / 2) (1 / 200)) coneAccuracy) (min εStrong_C12X.{u} εP6)
  have hε : 0 < ε :=
    lt_min (lt_min (lt_min (by positivity) (by norm_num)) coneAccuracy_pos)
      (lt_min εStrong_C12X_pos hεP6)
  have hε100 : ε < 1 / 100 :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))).trans_lt
      (by norm_num)
  have hε11 : ε < 1 / 11 := hε100.trans (by norm_num)
  have hεbar' : ε ≤ εbar :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))).trans (by linarith)
  have hεcone : ε ≤ coneAccuracy := (min_le_left _ _).trans (min_le_right _ _)
  have hstrong : ε ≤ εStrong_C12X.{u} := (min_le_right _ _).trans (min_le_left _ _)
  have hP6 : ε ≤ εP6 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C1, C2, C1s, C2s, Cs, τmin, Cbirth, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, hCbirth, analytic⟩ :=
    uniform ε hε hε11 hεbar'
  let C : ClosedBirthConstants := {
    epsilon := ε
    C1 := C1
    C2 := C2
    C1s := C1s
    C2s := C2s
    Cs := Cs
    tauMin := τmin
    Cbirth := Cbirth
    Ctime := Ctime
    Cgrad := Cgrad
    epsilon_pos := hε
    epsilon_small := hε100
    C1_ge_one := hC1
    C2_ge_one := hC2
    C1s_ge_one := hC1s
    C2s_ge_one := hC2s
    Cs_ge_one := hCs
    tauMin_pos := hτmin
    Cbirth_ge_one := hCbirth
    epsilon_cone := hεcone }
  refine ⟨Cdist, hCdist, fixed, recenter, C, hP6, hstrong, hrecenter,
    prepareClass, analytic, ?_⟩
  intro P g
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
      Dstar εReserve hDstar hεReserve
      Cdist fixed recenter prepareClass
      ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε
      ⟨hC1, hC2, hC1s, hC2s, hτmin, hstrong⟩ analytic P g
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
    epsilon_strong := hstrong
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := hStrongV }
  have hquality : prepared.HasReserveQuality Dstar εReserve :=
    ⟨hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩
  have hprepared : prepared.HasDistanceExtension Cdist := extension
  obtain ⟨S, hDistance, hS⟩ :=
    exists_prepared_spatial_base_with_distance_scalars Cdist pBase C P g prepared rfl hprepared
  have hSquality : S.prepared.HasReserveQuality Dstar εReserve := by
    rcases hS with ⟨_, _, hStage, hMetric, _, _, _, hPrepared, hShift, _⟩
    exact reserve_quality_of_same_prepared_class hStage.symm hMetric.symm
      (by rw [hShift, sub_zero]) hPrepared.symm hquality
  exact ⟨pBase, prepared, S, hquality, hSquality,
    hfixed, hrc, rfl, hprepared, hDistance, hS⟩

/-- Consumer：给任意正 `εP6`，丢弃新增上界后得到完整旧 strong selection 类型。 -/
example (Dstar εReserve εP6 : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (hεP6 : 0 < εP6) :
    type_of% (exists_closedBirthConstants_strong_C12X.{u}
      Dstar εReserve hDstar hεReserve) := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, -, h⟩ :=
    exists_closedBirthConstants_strong_accuracy_CXCA.{u}
      Dstar εReserve εP6 hDstar hεReserve hεP6
  exact ⟨Cdist, hCdist, fixed, recenter, C, h⟩

end GC.GeneralFlow

end
