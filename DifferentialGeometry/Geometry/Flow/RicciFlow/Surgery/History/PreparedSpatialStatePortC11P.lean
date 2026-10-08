import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullCanonicalC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullLeafDefsC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingC11SC

/-!
O-CH11-FIX3B port（astra `History/PreparedSpatialState` 的 elaboration 修补；陈述/定义逐字不变）：
本树 Lean 4.35 把 structure 里 `a b c : T` 解析成带 binder 的单字段，三处多名字段行加括号
`(epsilon C1 … : ℝ)`、`(Ctime Cgrad : ℝ≥0)`、`(deltaBound … Qall : ℝ)`。
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

/-- One choice of the uniform coefficients, shared by every native restart. -/
structure ClosedBirthConstants where
  (epsilon C1 C2 C1s C2s Cs tauMin Cbirth : ℝ)
  (Ctime Cgrad : ℝ≥0)
  epsilon_pos : 0 < epsilon
  epsilon_small : epsilon < 1 / 100
  C1_ge_one : 1 ≤ C1
  C2_ge_one : 1 ≤ C2
  C1s_ge_one : 1 ≤ C1s
  C2s_ge_one : 1 ≤ C2s
  Cs_ge_one : 1 ≤ Cs
  tauMin_pos : 0 < tauMin
  Cbirth_ge_one : 1 ≤ Cbirth
  epsilon_cone : epsilon ≤ coneAccuracy

/-- A selected native class with its actual extension and combined analytic
callback. This is recursive state, supplied by the paid class preparer. -/
structure ClosedBirthPreparedClass (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) where
  parameters : CutoffParameters
  (deltaBound radiusBound epsilonClass kappaClass kappa qcan qs Qzero Qbirth Qall : ℝ)
  fixed_eq : parameters.fixed = pBase.fixed
  recenter_eq : parameters.recenterConstant = pBase.recenterConstant
  deltaBound_pos : 0 < deltaBound
  radiusBound_pos : 0 < radiusBound
  epsilonClass_pos : 0 < epsilonClass
  epsilonClass_small : epsilonClass < 1 / 11
  kappaClass_pos : 0 < kappaClass
  kappa_pos : 0 < kappa
  qcan_pos : 0 < qcan
  qcan_le_qs : qcan ≤ qs
  qs_le : qs ≤ C.Cs * qcan
  Qzero_pos : 0 < Qzero
  Qbirth_ge : max 1 (max qcan qs) ≤ Qbirth
  Qall_eq : Qall = max Qbirth Qzero
  Qall_pos : 0 < Qall
  modelRadius_bound : StandardCap.transitionEnd < parameters.modelRadius + 1
  recenter_bound : parameters.recenterConstant * deltaBound ≤ 1 / 2
  zero_bound : ∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
    ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero
  extension : PreparedGeometricObservationExtension P g B epsilonClass kappaClass
    parameters deltaBound radiusBound
  control : ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
    (pV : CutoffParameters)
    (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
    V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily parameters deltaBound radiusBound records →
    V.NoncollapsedBefore kappa C.epsilon V.horizon ∧
    NativeEstimates V C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
    ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
      (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
      V.toHistory.activeStage t ≠ 0 →
      ∀ y : (V.toHistory.stageAt t).Carrier,
        Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
        ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
          C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y,
          W.capTubeHasNeckChart C.epsilon
  epsilon_strong : C.epsilon ≤ εStrong_C12X.{u}
  (C1strong C2strong qStrong : ℝ)
  C1strong_ge_one : 1 ≤ C1strong
  C2strong_ge_one : 1 ≤ C2strong
  /-- S16 shared bound (O-CH11-S16CEIL)：class 的 strong 常数不超过 uniform engine 常数
  `strongC1_C11SC C.epsilon C.C1`（只依赖 `C`，在 `P/g/B/κ` 之前固定的闭项）。 -/
  C1strong_le : C1strong ≤ strongC1_C11SC.{u} C.epsilon C.C1
  C2strong_le : C2strong ≤ strongC2_C11SC.{u} C.epsilon C.C2 C.Cgrad
  qs_le_qStrong : qs ≤ qStrong
  strongControl : ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
    (pV : CutoffParameters)
    (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
    V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily parameters deltaBound radiusBound records →
    RecordHypFar_C12X (5 / 4) V records →
    V.EventSlabsStronglyCanonicalFull_C12X C.epsilon C.epsilon C1strong C2strong qStrong
      (Fin.last V.eventCount) ∧
    ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
      V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
        ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl)
        C.epsilon C.epsilon C1strong C2strong qStrong V.horizon

/-- Full marked history and the precise prepared native tail used for its next
extension. The radius and class precede the next fine accuracy request. Physical
control is stored below the full horizon; the next buffered extension pays the
old endpoint, including surgery births and the original zero-time metric. -/
structure PreparedSpatialState (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (E B : ℝ) where
  history : RetainedCoreHistory.{u}
  initial : InitialIdentification P g history.toHistory
  horizon_eq : history.horizon = E
  parameters : CutoffParameters
  records : ∀ i : Fin history.eventCount,
    GeometricCutoffRecord history.toHistory i parameters
  static_eq : parameters.fixed = pBase.fixed ∧ parameters.modelRadius = pBase.modelRadius ∧
    parameters.modelOrder = pBase.modelOrder ∧ parameters.modelAccuracy = pBase.modelAccuracy ∧
    parameters.recenterConstant = pBase.recenterConstant
  modelRadius_bound : StandardCap.transitionEnd < parameters.modelRadius + 1
  eventControl : HistoryEventControl history
  windows : ∀ i b, ((records i).static b).hasCanonicalWindow
  linked : ∀ i b, ((records i).static b).hasLinkedCanonicalWindow_C12X
  radial : RadialWindows_C12X history records
  kappa : ℝ
  kappa_pos : 0 < kappa
  noncollapsed : history.NoncollapsedBefore kappa C.epsilon history.horizon
  nativeStage : OrientedThreeStage.{u}
  nativeMetric : nativeStage.Metric
  native : RetainedCoreHistory.{u}
  nativeInitial : InitialIdentification nativeStage nativeMetric native.toHistory
  nativeParameters : CutoffParameters
  nativeRecords : ∀ i : Fin native.eventCount,
    GeometricCutoffRecord native.toHistory i nativeParameters
  shift : ℝ
  offset : ℕ
  prepared : ClosedBirthPreparedClass pBase C nativeStage nativeMetric (B - shift)
  nativeClass : native.IsCanonicalCutoffRecordFamily prepared.parameters
    prepared.deltaBound prepared.radiusBound nativeRecords
  nativeRecordHyp : RecordHypFar_C12X (5 / 4) native nativeRecords
  nativeEventControl : HistoryEventControl native
  affine : AffineEventPrefix native history shift offset (Fin.last native.eventCount)
  horizon_affine : history.horizon = native.horizon + shift
  native_lt_capacity : native.horizon < B - shift
  finalMetric_heq : ∀ t : ℝ,
    HEq (history.toHistory.stageMetric (Fin.last history.eventCount) (t + shift))
      (native.toHistory.stageMetric (Fin.last native.eventCount) t)
  radius : ℝ
  radius_pos : 0 < radius
  threshold_le : prepared.Qall ≤ (radius ^ 2)⁻¹
  radius_antitone : AntitoneOn parameters.neckRadius (Ici 0)
  radius_after : ∀ t : ℝ, E ≤ t → parameters.neckRadius t = radius
  delta_antitone : AntitoneOn parameters.delta (Ici 0)
  canonical : ∀ t : Icc (0 : ℝ) history.toHistory.horizon, (t : ℝ) < E →
    ∀ x : (history.toHistory.stageAt t).Carrier,
      (parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
        (history.toHistory.stageMetric (history.toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        (history.toHistory.stageMetric (history.toHistory.activeStage t) t)
        C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
        W.capTubeHasNeckChart C.epsilon
  (C1S C2S : ℝ)
  C1S_ge_one : 1 ≤ C1S
  C2S_ge_one : 1 ≤ C2S
  /-- S16 shared bound (O-CH11-S16CEIL)：沿 recursion 保持的同一上界（Base `1`，Step `max`）。 -/
  C1S_le : C1S ≤ strongC1_C11SC.{u} C.epsilon C.C1
  C2S_le : C2S ≤ strongC2_C11SC.{u} C.epsilon C.C2 C.Cgrad
  strong_threshold_le : prepared.qStrong ≤ (radius ^ 2)⁻¹
  strong : ∀ t : Icc (0 : ℝ) history.toHistory.horizon, (t : ℝ) < E →
    history.time (history.toHistory.activeStage t) < (t : ℝ) →
    ∀ x : (history.toHistory.stageAt t).Carrier,
      (parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
        (history.toHistory.stageMetric (history.toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
          (history.toHistory.stageMetric (history.toHistory.activeStage t) t)
          C.epsilon C1S C2S x,
        W.capTubeHasNeckChart C.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (s' : ℝ) (G : (history.stage (history.toHistory.activeStage t)).IncomingSlab
              (history.time (history.toHistory.activeStage t)) s'),
            (∀ τ ∈ Icc (history.time (history.toHistory.activeStage t)) (t : ℝ),
              G.flow.base.metric τ = history.toHistory.stageMetric
                (history.toHistory.activeStage t) τ) ∧
            history.toHistory.HistoryStrongNeckFull_C12X (history.toHistory.activeStage t) G
              C.epsilon x t

/-- Exact full-history compatibility, with the quantitative budgets chosen for
this extension. Native reserved records are retained separately in the state. -/
structure PreparedSpatialSuccessor {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (R : PreparedSpatialState pBase C P g B Bnext) (activation eta d : ℝ) : Prop where
  initial_prefix : L.initial.IsPrefixOf R.initial
  count_le : L.history.eventCount ≤ R.history.eventCount
  parameters_past : ∀ t : ℝ, t ≤ E →
    R.parameters.delta t = L.parameters.delta t ∧
    R.parameters.neckRadius t = L.parameters.neckRadius t ∧
    R.parameters.protectedRadius t = L.parameters.protectedRadius t
  records_preserved : ∀ i : Fin L.history.eventCount,
    HEq (R.records (i.castLE count_le)).nominalRadius (L.records i).nominalRadius ∧
    HEq (R.records (i.castLE count_le)).delta (L.records i).delta ∧
    HEq (R.records (i.castLE count_le)).order (L.records i).order ∧
    HEq (R.records (i.castLE count_le)).neck (L.records i).neck ∧
    HEq (R.records (i.castLE count_le)).static (L.records i).static
  radius_le : R.radius ≤ L.radius
  radius_before_activation : ∀ t : ℝ, t ≤ activation →
    R.parameters.neckRadius t = L.parameters.neckRadius t
  radius_after_activation : ∀ t : ℝ, activation < t →
    R.parameters.neckRadius t = R.radius
  delta_after : ∀ t : ℝ, E < t → R.parameters.delta t = d
  recent_records : ∀ i : Fin R.history.eventCount, E < R.history.time i.succ →
    ∀ h, (R.records i).nominalRadius h ≤ eta * R.radius

end GC.GeneralFlow
