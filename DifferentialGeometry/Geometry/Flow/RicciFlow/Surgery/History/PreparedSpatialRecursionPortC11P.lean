import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceData

/-!
# S-CH11-FIX11 port of astra `PreparedSpatialRecursion`（`PortC11P`）

来源：donor `PreparedSpatialRecursion.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 4 个陈述里 `PreparedDistanceClassProvider pBase.fixed …` → `PreparedDistanceClassProvider.{u}`
  （universe 被自动成 `u_1`，与 `.{u}` 的 `toNative` / `analytic` application mismatch ×4，
  同 `GeometricObservationFineQuality` / `PreparedSpatialStep`）；
* 11 个陈述 binder `I` / `IL` 不被引用 → `_I` / `_IL`（unusedVariables）；
* 2 处孤立 `·`（单独成行）与下一行合并（`linter.style.cdot`）。

原路径 `PreparedSpatialRecursion` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open scoped NNReal

namespace GC.GeneralFlow

open private exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStep
open private reserve_quality_of_same_prepared_class from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData
universe u

/-- Read the scalar threshold of the same prepared class after its index transports. -/
private theorem preparedClass_Qall_eq_of_heq
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P Q : OrientedThreeStage.{u}} {g : P.Metric} {g' : Q.Metric} {B B' : ℝ}
    {K : ClosedBirthPreparedClass pBase C P g B}
    {K' : ClosedBirthPreparedClass pBase C Q g' B'}
    (hP : P = Q) (hg : HEq g g') (hB : B = B') (hK : HEq K K') :
    K.Qall = K'.Qall := by
  cases hP
  cases (eq_of_heq hg)
  cases hB
  cases (eq_of_heq hK)
  rfl

/-- One certified recursion retains the actual model request and buffered native certificate.
The selected future class/radius precede the requested quality and all fine events. -/
private theorem exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin_with_conditional_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseFull : certificate base.history) (hbaseNative : certificate base.native)
    (hbaseExtension : PreparedGeometricObservationExtensionWithNative certificate
      base.nativeStage base.nativeMetric (1 - base.shift)
      base.prepared.epsilonClass base.prepared.kappaClass
      base.prepared.parameters base.prepared.deltaBound base.prepared.radiusBound)
    (hrbase : base.radius ≤ 1)
    (hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (base.prepared.HasReserveQuality Dstar εReserve →
        ∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, certificate (S.state n).history ∧ certificate (S.state n).native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          (S.state n).nativeStage (S.state n).nativeMetric
          (((3 : ℝ) ^ n) - (S.state n).shift)
          (S.state n).prepared.epsilonClass (S.state n).prepared.kappaClass
          (S.state n).prepared.parameters (S.state n).prepared.deltaBound
          (S.state n).prepared.radiusBound) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  classical
  have extension (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n))
      (hL : certificate L.history ∧ certificate L.native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          L.nativeStage L.nativeMetric (((3 : ℝ) ^ n) - L.shift)
          L.prepared.epsilonClass L.prepared.kappaClass
          L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound) :
      ∃ R : PreparedSpatialState pBase C P g
          (preparedSpatialHorizon (n + 1)) ((3 : ℝ) ^ (n + 1)),
        (certificate R.history ∧ certificate R.native ∧
          PreparedGeometricObservationExtensionWithNative certificate
            R.nativeStage R.nativeMetric (((3 : ℝ) ^ (n + 1)) - R.shift)
            R.prepared.epsilonClass R.prepared.kappaClass
            R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ 1 / ((n : ℝ) + 2) ∧
          PreparedSpatialSuccessor L R ((5 / 6 : ℝ) * 3 ^ n)
            (1 / ((n : ℝ) + 2)) d ∧
          ∃ (future : ClosedBirthPreparedClass pBase C
              (L.native.stage (Fin.last L.native.eventCount))
              (L.native.initialMetric (Fin.last L.native.eventCount))
              ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount))) (r : ℝ),
            future.HasReserveQuality Dstar εReserve ∧
            0 < r ∧ R.radius = r ∧ HEq R.prepared future ∧
            R.shift = L.history.time (Fin.last L.history.eventCount) ∧
            R.offset = L.history.eventCount ∧
            R.nativeStage = L.native.stage (Fin.last L.native.eventCount) ∧
            HEq R.nativeMetric (L.native.initialMetric (Fin.last L.native.eventCount)) ∧
            d ≤ L.parameters.delta (preparedSpatialHorizon n) / 4 ∧
            d ≤ (request n L future r).2.2.2 ∧
            R.radius * Real.sqrt R.prepared.Qall ≤ 100 * cMax ∧
            Nonempty (PreparedSpatialStepRetention L R d (1 / ((n : ℝ) + 2))
              (request n L future r).1 (request n L future r).2.1
              (request n L future r).2.2.1) := by
    have hp : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
    have hBB : (3 : ℝ) ^ n < 3 ^ (n + 1) := by
      rw [pow_succ]
      nlinarith
    have hEA : preparedSpatialHorizon n ≤ (5 / 6 : ℝ) * 3 ^ n := by
      cases n with
      | zero => norm_num [preparedSpatialHorizon]
      | succ n =>
        change (3 : ℝ) ^ n ≤ (5 / 6 : ℝ) * 3 ^ (n + 1)
        rw [pow_succ]
        have hpos : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
        nlinarith
    have hAB : (5 / 6 : ℝ) * 3 ^ n < (3 : ℝ) ^ n := by nlinarith
    have heta : 0 < 1 / ((n : ℝ) + 2) := by positivity
    obtain ⟨future, r, hFutureQuality, _, hr, _, _, hFit, make⟩ :=
      exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
        Dstar εReserve hDstar hεReserve certificate joinCertificate
        pBase C cMax hcMax prepareClass analytic L hL.1 hL.2.1 hL.2.2 hBB hEA hAB heta
    obtain ⟨hε, hD, hδ⟩ := hrequest n L future r hr
    have hE : 0 ≤ preparedSpatialHorizon n := L.horizon_eq ▸ L.history.horizon_nonneg
    have hquarter : 0 < L.parameters.delta (preparedSpatialHorizon n) / 4 :=
      div_pos (L.parameters.delta_pos _ hE) (by norm_num)
    let cap := min (1 / ((n : ℝ) + 2))
      (min (request n L future r).2.2.2
        (L.parameters.delta (preparedSpatialHorizon n) / 4))
    have hcap : 0 < cap := lt_min heta (lt_min hδ hquarter)
    obtain ⟨d, hd, hd1, _, hdCap, R, hRradius, hShift, hOffset, hStage, hMetric,
      hRprepared, hRCertificate, hR, hW⟩ :=
      (make (request n L future r).1 (request n L future r).2.1
        (request n L future r).2.2.1 hε hD).2 cap hcap
    have hdQuarter : d ≤ L.parameters.delta (preparedSpatialHorizon n) / 4 :=
      hdCap.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hdRequest : d ≤ (request n L future r).2.2.2 :=
      hdCap.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hRQ : R.prepared.Qall = future.Qall :=
      preparedClass_Qall_eq_of_heq hStage hMetric
        (congrArg (fun s => (3 : ℝ) ^ (n + 1) - s) hShift) hRprepared
    have hRFit : R.radius * Real.sqrt R.prepared.Qall ≤ 100 * cMax := by
      rw [hRradius, hRQ]
      exact hFit
    exact ⟨R, hRCertificate, d, hd, hd1, hdCap.trans (min_le_left _ _), hR,
      future, r, hFutureQuality, hr, hRradius, hRprepared, hShift, hOffset, hStage, hMetric,
      hdQuarter, hdRequest, hRFit, hW⟩
  let Certified (n : ℕ) :=
    {L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n) //
      certificate L.history ∧ certificate L.native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          L.nativeStage L.nativeMetric (((3 : ℝ) ^ n) - L.shift)
          L.prepared.epsilonClass L.prepared.kappaClass
          L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound}
  let baseCertified : Certified 0 := ⟨base, hbaseFull, hbaseNative, hbaseExtension⟩
  let next (n : ℕ) (L : Certified n) : Certified (n + 1) :=
    ⟨Classical.choose (extension n L.1 L.2),
      (Classical.choose_spec (extension n L.1 L.2)).1⟩
  let fine (n : ℕ) (L : Certified n) :=
    Classical.choose ((Classical.choose_spec (extension n L.1 L.2)).2)
  have next_spec (n : ℕ) (L : Certified n) :=
    Classical.choose_spec ((Classical.choose_spec (extension n L.1 L.2)).2)
  let chain : ∀ n : ℕ, Certified n :=
    fun n => Nat.rec baseCertified (fun n L => next n L) n
  let S : PreparedSpatialChain pBase C P g := {
    state := fun n => (chain n).1
    accuracy := fun n => fine n (chain n)
    accuracy_pos := fun n => (next_spec n (chain n)).1
    accuracy_lt_one := fun n => (next_spec n (chain n)).2.1
    accuracy_le := fun n => (next_spec n (chain n)).2.2.1
    successor := fun n => (next_spec n (chain n)).2.2.2.1
    initial_history := hbase
    initial_radius_le := hrbase }
  have retained (n : ℕ) :
      ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        future.HasReserveQuality Dstar εReserve ∧
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount)) ∧
        S.accuracy n ≤ (S.state n).parameters.delta (preparedSpatialHorizon n) / 4 ∧
        S.accuracy n ≤ (request n (S.state n) future r).2.2.2 ∧
        (S.state (n + 1)).radius * Real.sqrt (S.state (n + 1)).prepared.Qall ≤
          100 * cMax ∧
        Nonempty (PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
          (S.accuracy n) (1 / ((n : ℝ) + 2)) (request n (S.state n) future r).1
          (request n (S.state n) future r).2.1
          (request n (S.state n) future r).2.2.1) :=
    (next_spec n (chain n)).2.2.2.2
  choose future r hRetainedWithQuality using retained
  have hFutureQuality : ∀ n, (future n).HasReserveQuality Dstar εReserve :=
    fun n => (hRetainedWithQuality n).1
  have hRetained (n : ℕ) := (hRetainedWithQuality n).2
  have hAllQuality (hbaseQuality : base.prepared.HasReserveQuality Dstar εReserve) :
      ∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve := by
    intro n
    cases n with
    | zero => exact hbaseQuality
    | succ n =>
      obtain ⟨_, _, hPrepared, hShift, _, hStage, hMetric, _, _, _, _⟩ := hRetained n
      exact reserve_quality_of_same_prepared_class hStage.symm hMetric.symm
        (congrArg (fun s => (3 : ℝ) ^ (n + 1) - s) hShift).symm
        hPrepared.symm (hFutureQuality n)
  have hAllFit : ∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤
      100 * cMax := by
    intro n
    cases n with
    | zero => exact hbaseFit
    | succ n =>
      obtain ⟨_, _, _, _, _, _, _, _, _, hFit, _⟩ := hRetained n
      exact hFit
  refine ⟨S, future, r, hFutureQuality, hAllQuality, rfl, hAllFit,
    fun n => (chain n).2, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hr, hRadius, hPrepared, hShift, hOffset, hStage, hMetric, _, _, _, _⟩ := hRetained n
    exact ⟨hr, hRadius, hPrepared, hShift, hOffset, hStage, hMetric⟩
  · intro n
    obtain ⟨_, _, _, _, _, _, _, hQuarter, _, _, _⟩ := hRetained n
    exact hQuarter
  · intro n
    obtain ⟨_, _, _, _, _, _, _, _, hRequest, _, _⟩ := hRetained n
    exact hRequest
  · refine ⟨fun n => ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hW⟩ := hRetained n
    exact Classical.choice hW

/-- Retain all states of this same chain from the supplied base quality. -/
private theorem exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseQuality : base.prepared.HasReserveQuality Dstar εReserve)
    (hbaseFull : certificate base.history) (hbaseNative : certificate base.native)
    (hbaseExtension : PreparedGeometricObservationExtensionWithNative certificate
      base.nativeStage base.nativeMetric (1 - base.shift)
      base.prepared.epsilonClass base.prepared.kappaClass
      base.prepared.parameters base.prepared.deltaBound base.prepared.radiusBound)
    (hrbase : base.radius ≤ 1)
    (hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, certificate (S.state n).history ∧ certificate (S.state n).native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          (S.state n).nativeStage (S.state n).nativeMetric
          (((3 : ℝ) ^ n) - (S.state n).shift)
          (S.state n).prepared.epsilonClass (S.state n).prepared.kappaClass
          (S.state n).prepared.parameters (S.state n).prepared.deltaBound
          (S.state n).prepared.radiusBound) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨S, future, r, hFuture, hStates, hOld⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin_with_conditional_reserve_quality
      Dstar εReserve hDstar hεReserve certificate joinCertificate pBase C cMax hcMax
      prepareClass analytic base hbase hbaseFull hbaseNative hbaseExtension
      hrbase hbaseFit request hrequest
  exact ⟨S, future, r, hFuture, hStates hbaseQuality, hOld⟩

/-- Preserve the arbitrary-base API without asserting any base reserve quality. -/
private theorem exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseFull : certificate base.history) (hbaseNative : certificate base.native)
    (hbaseExtension : PreparedGeometricObservationExtensionWithNative certificate
      base.nativeStage base.nativeMetric (1 - base.shift)
      base.prepared.epsilonClass base.prepared.kappaClass
      base.prepared.parameters base.prepared.deltaBound base.prepared.radiusBound)
    (hrbase : base.radius ≤ 1)
    (hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, certificate (S.state n).history ∧ certificate (S.state n).native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          (S.state n).nativeStage (S.state n).nativeMetric
          (((3 : ℝ) ^ n) - (S.state n).shift)
          (S.state n).prepared.epsilonClass (S.state n).prepared.kappaClass
          (S.state n).prepared.parameters (S.state n).prepared.deltaBound
          (S.state n).prepared.radiusBound) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨S, future, r, _, _, hOld⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin_with_conditional_reserve_quality
      1 1 one_pos one_pos certificate joinCertificate pBase C cMax hcMax
      prepareClass analytic base hbase hbaseFull hbaseNative hbaseExtension
      hrbase hbaseFit request hrequest
  exact ⟨S, future, r, hOld⟩

/-- The original quality interface forgets only the margin on the same recursion. -/
private theorem exists_prepared_spatial_chain_with_quality_and_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseFull : certificate base.history) (hbaseNative : certificate base.native)
    (hbaseExtension : PreparedGeometricObservationExtensionWithNative certificate
      base.nativeStage base.nativeMetric (1 - base.shift)
      base.prepared.epsilonClass base.prepared.kappaClass
      base.prepared.parameters base.prepared.deltaBound base.prepared.radiusBound)
    (hrbase : base.radius ≤ 1)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, certificate (S.state n).history ∧ certificate (S.state n).native ∧
        PreparedGeometricObservationExtensionWithNative certificate
          (S.state n).nativeStage (S.state n).nativeMetric
          (((3 : ℝ) ^ n) - (S.state n).shift)
          (S.state n).prepared.epsilonClass (S.state n).prepared.kappaClass
          (S.state n).prepared.parameters (S.state n).prepared.deltaBound
          (S.state n).prepared.radiusBound) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  let cMax : ℝ := base.radius * Real.sqrt base.prepared.Qall + 1
  have hproduct : 0 ≤ base.radius * Real.sqrt base.prepared.Qall :=
    mul_nonneg base.radius_pos.le (Real.sqrt_nonneg _)
  have hcMax : 0 < cMax := by dsimp only [cMax]; linarith
  have hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax := by
    dsimp only [cMax]
    linarith
  obtain ⟨S, future, r, hInitial, _, hCertificate, hState, hQuarter, hRequest, hW⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin
      certificate joinCertificate pBase C cMax hcMax prepareClass analytic
      base hbase hbaseFull hbaseNative hbaseExtension hrbase hbaseFit request hrequest
  exact ⟨S, future, r, hInitial, hCertificate, hState, hQuarter, hRequest, hW⟩

/-- Preserve the original private interface by projecting the same retained recursion. -/
private theorem exists_prepared_spatial_chain_with_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseFull : certificate base.history) (hbaseNative : certificate base.native)
    (hbaseExtension : PreparedGeometricObservationExtensionWithNative certificate
      base.nativeStage base.nativeMetric (1 - base.shift)
      base.prepared.epsilonClass base.prepared.kappaClass
      base.prepared.parameters base.prepared.deltaBound base.prepared.radiusBound)
    (hrbase : base.radius ≤ 1)
    (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ)
    (hbudget : ∀ n L future r, 0 < budget n L future r) :
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧ (∀ n, (certificate (S.state n).history ∧ certificate (S.state n).native ∧
          PreparedGeometricObservationExtensionWithNative certificate
            (S.state n).nativeStage (S.state n).nativeMetric (((3 : ℝ) ^ n) - (S.state n).shift)
            (S.state n).prepared.epsilonClass (S.state n).prepared.kappaClass
            (S.state n).prepared.parameters (S.state n).prepared.deltaBound (S.state n).prepared.radiusBound)) ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  obtain ⟨S, future, r, hInitial, hCertificate, hState, _, hBudget, _⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate
      certificate joinCertificate pBase C prepareClass analytic
      base hbase hbaseFull hbaseNative hbaseExtension hrbase
      (fun n L future r =>
        (pBase.modelAccuracy, pBase.modelRadius, pBase.modelOrder, budget n L future r))
      (by
        intro n L future r _
        exact ⟨pBase.modelAccuracy_pos, pBase.modelRadius_pos, hbudget n L future r⟩)
  refine ⟨S, hInitial, hCertificate, ?_⟩
  intro n
  obtain ⟨hr, hRadius, hPrepared, _, _, _, _⟩ := hState n
  exact ⟨future n, r n, hr, hRadius, hPrepared, hBudget n⟩

/-- Compatibility through the same engine with the trivial certificate. -/
theorem exists_prepared_spatial_chain
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
      ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
      ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
        0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
      ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
        p₀.fixed = pBase.fixed ∧ p₀.recenterConstant = pBase.recenterConstant ∧
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
        PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hrbase : base.radius ≤ 1)
    (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ)
    (hbudget : ∀ n L future r, 0 < budget n L future r) :
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  have distanceResult := @exists_prepared_spatial_chain_with_native_certificate.{u} (fun _ => True)
    (by intro H K J c hp A hH hK; exact True.intro) pBase C (PreparedClassProviderWithNative.of_weak
      prepareClass) analytic P g base hbase True.intro True.intro base.prepared.extension.withTrue
      hrbase budget hbudget
  obtain ⟨S, distanceProjectionh1⟩ := distanceResult
  refine ⟨S, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2, ?_⟩
  exact (distanceProjectionh3.2)

/-- The same selected successor/chain retaining its actual distance certificates. -/
theorem exists_prepared_spatial_chain_with_distance_scalars
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseDistance : base.DistanceData Cdist)
    (hrbase : base.radius ≤ 1)
    (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ)
    (hbudget : ∀ n L future r, 0 < budget n L future r) :
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧ (∀ n, (S.state n).DistanceData Cdist) ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  have distanceResult := @exists_prepared_spatial_chain_with_native_certificate.{u} (fun K => ∀ i :
    Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist)
    (by
      intro H K J c hp A hH hK
      exact hasUniformDistanceScalar_at_affine_join hp A hH hK) pBase C prepareClass.toNative
        analytic P g base hbase hbaseDistance.full hbaseDistance.native hbaseDistance.extension
        hrbase budget hbudget
  obtain ⟨S, distanceProjectionh1⟩ := distanceResult
  refine ⟨S, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2, ?_⟩
  refine ⟨?_, ?_⟩
  · intro n
    have distanceProjectionh4 := @distanceProjectionh3.1 n
    exact ⟨distanceProjectionh4.1, distanceProjectionh4.2.1, distanceProjectionh4.2.2⟩
  · exact distanceProjectionh3.2


/-- The same requested-quality chain with its actual distance certificates. -/
theorem exists_prepared_spatial_chain_with_quality_and_distance_scalars
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseDistance : base.DistanceData Cdist)
    (hrbase : base.radius ≤ 1)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨S, future, r, hInitial, hCertificate, hState, hQuarter, hRequest, hW⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C prepareClass.toNative analytic base hbase
      hbaseDistance.full hbaseDistance.native hbaseDistance.extension hrbase request hrequest
  exact ⟨S, future, r, hInitial,
    fun n => ⟨(hCertificate n).1, (hCertificate n).2.1, (hCertificate n).2.2⟩,
    hState, hQuarter, hRequest, hW⟩

/-- The same quality/distance chain, with every own-class radius fixed before fine requests. -/
theorem exists_prepared_spatial_chain_with_quality_and_distance_scalars_and_small_test_margin
    (Cdist : ℝ≥0) (cMax : ℝ) (hcMax : 0 < cMax)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseDistance : base.DistanceData Cdist)
    (hrbase : base.radius ≤ 1)
    (hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨S, future, r, hInitial, hFit, hCertificate, hState, hQuarter, hRequest, hW⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C cMax hcMax prepareClass.toNative analytic base hbase
      hbaseDistance.full hbaseDistance.native hbaseDistance.extension hrbase hbaseFit request hrequest
  exact ⟨S, future, r, hInitial, hFit,
    fun n => ⟨(hCertificate n).1, (hCertificate n).2.1, (hCertificate n).2.2⟩,
    hState, hQuarter, hRequest, hW⟩

/-- The same distance-certified chain with its base, future and state quality. -/
theorem exists_prepared_spatial_chain_with_quality_and_distance_scalars_and_small_test_margin_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (Cdist : ℝ≥0) (cMax : ℝ) (hcMax : 0 < cMax)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
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
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (base : PreparedSpatialState pBase C P g 0 1)
    (hbase : base.history = RetainedCoreHistory.atZero P g)
    (hbaseQuality : base.prepared.HasReserveQuality Dstar εReserve)
    (hbaseDistance : base.DistanceData Cdist)
    (hrbase : base.radius ≤ 1)
    (hbaseFit : base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax)
    (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ)
    (hrequest : ∀ n L future r, 0 < r →
      0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
      0 < (request n L future r).2.2.2) :
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨S, future, r, hFutureQuality, hStateQuality,
    hInitial, hFit, hCertificate, hState, hQuarter, hRequest, hW⟩ :=
    exists_prepared_spatial_chain_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
      Dstar εReserve hDstar hεReserve (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C cMax hcMax prepareClass.toNative analytic base hbase hbaseQuality
      hbaseDistance.full hbaseDistance.native hbaseDistance.extension hrbase hbaseFit request hrequest
  exact ⟨S, future, r, hFutureQuality, hStateQuality, hInitial, hFit,
    fun n => ⟨(hCertificate n).1, (hCertificate n).2.1, (hCertificate n).2.2⟩,
    hState, hQuarter, hRequest, hW⟩

end GC.GeneralFlow
