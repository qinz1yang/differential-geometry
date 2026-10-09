import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedClosedBirthClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.UniformClosedBirthObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData

/-!
# S-CH11-FIX12 port of astra `PreparedSpatialProviders`（`PortC11P`）

来源：donor `PreparedSpatialProviders.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 两处陈述里 `PreparedDistanceClassProvider fixed recenter Cdist` 的 universe 被自动成 `u_1`，而
  证明体全是 `.{u}`（l.105 "Application type mismatch … `.{u}` vs `.{u_1}`"）→ 陈述里写
  `PreparedDistanceClassProvider.{u}`；
* 陈述里只出现、证明不引用的 binder（`I` / `IL`）加 `_` 前缀（unusedVariables；binder 名不改变
  陈述）；
* 两处孤立 `·`（单独一行后接 tactic）合并成 `· tactic`（风格 linter）。

原路径 `PreparedSpatialProviders` 是只 import 本文件的 re-export shim。
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

/-- Choose the genuine common providers and uniform constants before original
initial data, then retain the actual capacity-one class and its reserve quality
in the same marked zero state. -/
theorem exists_prepared_spatial_initial_state_with_distance_scalars_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ) (C : ClosedBirthConstants),
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
  let ε : ℝ := min (min (min (εbar / 2) (1 / 200)) coneAccuracy) εStrong_C12X.{u}
  have hε : 0 < ε :=
    lt_min (lt_min (lt_min (by positivity) (by norm_num)) coneAccuracy_pos) εStrong_C12X_pos
  have hε100 : ε < 1 / 100 :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))).trans_lt
      (by norm_num)
  have hε11 : ε < 1 / 11 := hε100.trans (by norm_num)
  have hεbar' : ε ≤ εbar :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))).trans (by linarith)
  have hεcone : ε ≤ coneAccuracy := (min_le_left _ _).trans (min_le_right _ _)
  have hεstrong : ε ≤ εStrong_C12X.{u} := min_le_right _ _
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
  refine ⟨Cdist, hCdist, fixed, recenter, C, hrecenter, prepareClass, analytic, ?_⟩
  intro P g
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
      Dstar εReserve hDstar hεReserve
      Cdist fixed recenter prepareClass
      ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε
      ⟨hC1, hC2, hC1s, hC2s, hτmin, hεstrong⟩ analytic P g
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
    epsilon_strong := hεstrong
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

/-- Preserve the original provider API by projecting the same strengthened construction. -/
theorem exists_prepared_spatial_initial_state_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ) (C : ClosedBirthConstants),
      4 ≤ recenter ∧
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
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hrecenter, prepareClass, analytic, initial⟩ :=
    exists_prepared_spatial_initial_state_with_distance_scalars_with_reserve_quality.{u}
      1 1 one_pos one_pos
  refine ⟨Cdist, hCdist, fixed, recenter, C, hrecenter.1, prepareClass, analytic, ?_⟩
  intro P g
  obtain ⟨pBase, prepared, S, _, _, hS⟩ := initial P g
  exact ⟨pBase, prepared, S, hS⟩

/-- Forget only the distance certificate from the same genuine initial construction. -/
theorem exists_prepared_spatial_initial_state :
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ) (C : ClosedBirthConstants),
      4 ≤ recenter ∧
      (∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
      ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
      ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
        0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
      ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
        p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
        0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
        p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
        mcapRequest ≤ p₀.modelOrder ∧
        StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
        p₀.recenterConstant * δb ≤ 1 / 2 ∧
        (∀ (L : RetainedCoreHistory.{u}) (_IL : InitialIdentification P g L.toHistory)
          (pL : CutoffParameters)
          (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
          L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          L.NoncollapsedBefore κ ε L.horizon) ∧
        PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb) ∧
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
        pBase.fixed = fixed ∧ pBase.recenterConstant = recenter ∧
        prepared.parameters = pBase ∧
        S.history = RetainedCoreHistory.atZero P g ∧
        HEq S.initial (InitialIdentification.atZero P g) ∧
        S.nativeStage = P ∧ HEq S.nativeMetric g ∧
        S.native = RetainedCoreHistory.atZero P g ∧
        HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
        S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
        S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
        S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
        (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  obtain ⟨_, _, distanceResult⟩ := exists_prepared_spatial_initial_state_with_distance_scalars.{u}
  obtain ⟨fixed, recenter, C, distanceProjectionh1⟩ := distanceResult
  refine ⟨fixed, recenter, C, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2, ?_⟩
  refine ⟨?_, ?_⟩
  · exact PreparedClassProviderWithNative.forget (PreparedDistanceClassProvider.toNative
      distanceProjectionh3.1)
  · obtain ⟨distanceProjectionfield4, distanceProjectionh5⟩ := distanceProjectionh3.2
    refine ⟨distanceProjectionfield4, ?_⟩
    intro P g
    have distanceProjectionh6 := @distanceProjectionh5 P g
    obtain ⟨pBase, prepared, S, distanceProjectionh7⟩ := distanceProjectionh6
    refine ⟨pBase, prepared, S, ?_⟩
    obtain ⟨distanceProjectionfield8, distanceProjectionfield9, distanceProjectionfield10,
      distanceProjectionh11⟩ := distanceProjectionh7
    refine ⟨distanceProjectionfield8, distanceProjectionfield9, distanceProjectionfield10, ?_⟩
    exact (distanceProjectionh11.2).2

end GC.GeneralFlow
