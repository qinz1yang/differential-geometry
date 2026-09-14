import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KappaSeedFrontierConsolidation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersMinimalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance seedCollapseInputTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance seedCollapseInputCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance seedCollapseInputSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance seedCollapseInputC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance seedCollapseInputT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance seedCollapseInputSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance seedCollapseInputTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance seedCollapseInputMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance seedCollapseInputBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

omit [I.Boundaryless] in
def KLimAlmostAncientCollapseBallBound (kappa eps A L : ℝ) : Prop :=
  ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
    KLim (I := I) kappa F → ∀ (x : F.M) (Q r : ℝ),
    0 < Q → F.S.scalar 0 x = Q → 0 < r →
    (∀ t : ℝ, t ≤ 0 → ∀ z : F.M,
      z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r →
        F.S.scalar t z ≤ 2 * Q) →
    L ≤ r ^ 2 * Q →
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q)) ≤
      ENNReal.ofReal eps * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)

omit [I.Boundaryless] in
def KLimAlmostAncientCollapseEpsilonWitness (kappa eps : ℝ) : Prop :=
  ∃ A L : ℝ, 1 ≤ A ∧ A ^ 2 ≤ L ∧
    KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L

omit [I.Boundaryless] in
def KLimAlmostAncientCollapseFields (kappa : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    KLimAlmostAncientCollapseEpsilonWitness.{u, uE, uH} (I := I) kappa eps

omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapse_iff_fields {kappa : ℝ} :
    KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa ↔
      KLimAlmostAncientCollapseFields.{u, uE, uH} (I := I) kappa := by
  constructor
  · intro h eps heps
    obtain ⟨A, L, hA, hAL, hbound⟩ := h eps heps
    exact ⟨A, L, hA, hAL, hbound⟩
  · intro h eps heps
    obtain ⟨A, L, hA, hAL, hbound⟩ := h eps heps
    exact ⟨A, L, hA, hAL, hbound⟩

omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapseFields_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimAlmostAncientCollapseFields.{u, uE, uH} (I := I) kappa :=
  (kLimAlmostAncientCollapse_iff_fields (I := I)).1
    (kLimAlmostAncientCollapse_of_nonpos (I := I) h)

omit [I.Boundaryless] in
def KLimSeedAncientLimitSequence (kappa : ℝ)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  X.D = ancientTimeInterval ∧ (∀ i, KLim (I := I) kappa (X.term i)) ∧
    Module.finrank ℝ E = 3 ∧
    (∀ i, seedTerminalUnitVolume (X.term i) = euclideanUnitBallVolume 3 / 2)

omit [I.Boundaryless] in
def PointedCGHFlowLimitConvergence (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ) : Prop :=
  StrictMono phi ∧
  ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
    (let _ : TopologicalSpace L.M := L.topology
     ConnectedSpace L.M) ∧
    (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
    ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) ∧
        (∀ k,
          let D := C.domain k
          let _ : TopologicalSpace
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
          let _ : ChartedSpace H
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
          let _ : IsManifold I ∞
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
          D.referenceMetric = D.limitMetric)

omit [I.Boundaryless] in
def PointedCGHFlowLimit (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
    PointedCGHFlowLimitConvergence.{u, uE, uH} (I := I) X L phi

omit [I.Boundaryless] in
def KLimSeedAncientLimitFields (kappa : ℝ) : Prop :=
  ∀ X : PointedFlowSeq.{u, uE, uH} (I := I),
    KLimSeedAncientLimitSequence.{u, uE, uH} (I := I) kappa X →
      PointedCGHFlowLimit.{u, uE, uH} (I := I) X

omit [I.Boundaryless] in
theorem kLimSeedAncientLimit_iff_fields {kappa : ℝ} :
    KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa ↔
      KLimSeedAncientLimitFields.{u, uE, uH} (I := I) kappa := by
  constructor
  · intro h X hX
    exact h X hX.1 hX.2.1 hX.2.2.1 hX.2.2.2
  · intro h X hD hK hdim hvolume
    exact h X ⟨hD, hK, hdim, hvolume⟩

omit [I.Boundaryless] in
def KLimAncientKappaSeedSequence (kappa : ℝ)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  X.D = ancientTimeInterval ∧
    (∀ i, IsAncientKappaSolution (I := I) kappa (X.term i)) ∧
    Module.finrank ℝ E = 3 ∧
    (∀ i, seedTerminalUnitVolume (X.term i) = euclideanUnitBallVolume 3 / 2)

theorem kLimSeedAncientLimitSequence_of_ancientKappaSeedSequence {kappa : ℝ}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (h : KLimAncientKappaSeedSequence.{u, uE, uH} (I := I) kappa X) :
    KLimSeedAncientLimitSequence.{u, uE, uH} (I := I) kappa X := by
  obtain ⟨hD, hAncient, hdim, hvolume⟩ := h
  exact ⟨hD, fun i => ancientKappaThree_toKLim (I := I) (X.term i) (hAncient i) hdim,
    hdim, hvolume⟩

omit [I.Boundaryless] in
theorem kLimSeedAncientLimit_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa := by
  intro X _hD hK _hdim _hvolume
  exact absurd (hK 0).kappa_pos (not_lt.mpr h)

omit [I.Boundaryless] in
theorem kLimSeedAncientLimitFields_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimSeedAncientLimitFields.{u, uE, uH} (I := I) kappa :=
  (kLimSeedAncientLimit_iff_fields (I := I)).1 (kLimSeedAncientLimit_of_nonpos (I := I) h)

omit [I.Boundaryless] in
def KLimExceptFlatness {D : RealTimeInterval} (kappa : ℝ)
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  2 ≤ Module.finrank ℝ E ∧ 0 < kappa ∧ D.carrier = Set.Iic 0 ∧
  D.regular = Set.Iio 0 ∧
  (let _ : TopologicalSpace F.M := F.topology
   ConnectedSpace F.M) ∧
  (∀ t ∈ D.carrier, MetricComplete (I := I) (F.atTime (I := I) t)) ∧
  (∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t) ∧
  PointedFlowNoncollapsedAllScales (I := I) F kappa ∧
  (∀ t ∈ D.carrier, ∀ (x : F.M) (V : TangentSpace I x),
    0 ≤ derivWithin (fun s : ℝ => F.S.scalar s x) D.carrier t +
      2 * (F.S.base.metric t).inner x
        (gradientAt (I := I) (flowG (I := I) F.S) t (F.S.scalar t) x) V +
      2 * metricRicci (I := I) (M := F.M) (F.S.base.metric t) x (vec2 V V))

omit [I.Boundaryless] in
theorem kLimExceptFlatness_of_kLim {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (hK : KLim (I := I) kappa F) : KLimExceptFlatness.{u, uE, uH} (I := I) kappa F :=
  ⟨hK.dimension_ge_two, hK.kappa_pos, hK.carrier_eq, hK.regular_eq, hK.connected,
    hK.complete, hK.nonnegativeCurvatureOperator, hK.noncollapsed, hK.traceHarnack⟩

omit [I.Boundaryless] in
theorem kLim_of_kLimExceptFlatness_and_notFlat {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (h : KLimExceptFlatness.{u, uE, uH} (I := I) kappa F)
    (hnotflat : PointedFlowNotFlat (I := I) F) : KLim (I := I) kappa F where
  dimension_ge_two := h.1
  kappa_pos := h.2.1
  carrier_eq := h.2.2.1
  regular_eq := h.2.2.2.1
  connected := h.2.2.2.2.1
  complete := h.2.2.2.2.2.1
  nonnegativeCurvatureOperator := h.2.2.2.2.2.2.1
  noncollapsed := h.2.2.2.2.2.2.2.1
  notFlat := hnotflat
  traceHarnack := h.2.2.2.2.2.2.2.2

omit [I.Boundaryless] in
theorem kLim_iff_kLimExceptFlatness_and_notFlat {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ} :
    KLim (I := I) kappa F ↔
      KLimExceptFlatness.{u, uE, uH} (I := I) kappa F ∧
        PointedFlowNotFlat (I := I) F :=
  ⟨fun hK => ⟨kLimExceptFlatness_of_kLim hK, hK.notFlat⟩,
    fun h => kLim_of_kLimExceptFlatness_and_notFlat h.1 h.2⟩

theorem euclideanFlatFlow_kLimExceptFlatness {kappa : ℝ} (hkappa : 0 < kappa)
    (hvolume : ENNReal.ofReal kappa ≤ euclideanUnitBallVolume 3) :
    KLimExceptFlatness.{0, 0, 0} (I := I3) kappa euclideanFlatFlow := by
  refine ⟨?_, hkappa, rfl, rfl, inferInstance, ?_, ?_, ?_, ?_⟩
  · norm_num [finrank_euclideanSpace, Fintype.card_fin]
  · exact fun _t _ht => (euclideanMetric_complete (E := ThreeSpace)).complete
  · exact fun t _ht => euclideanFlatFlow_nonnegativeCurvatureOperator t
  · exact euclideanFlatFlow_noncollapsed hkappa hvolume
  · exact fun t ht x V => euclideanFlatFlow_traceHarnack t ht x V

theorem euclideanFlatFlow_seedTerminalUnitVolume :
    seedTerminalUnitVolume (I := I3) euclideanFlatFlow = euclideanUnitBallVolume 3 := by
  rw [seedTerminalUnitVolume, euclideanFlatFlow_metric]
  rw [euclideanMetric_ball_volume (0 : ThreeSpace) (r := 1) one_pos]
  simp

theorem kLimLocalCurvatureBound_of_seedAncientLimit_and_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa :=
  kLimLocalCurvatureBound_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse
      (I := I) hdim hseed hcollapse)

theorem kLimLocalCurvatureBound_of_seedAncientLimit_and_almostAncientCollapse_of_nonpos
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (h : kappa ≤ 0) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa :=
  kLimLocalCurvatureBound_of_seedAncientLimit_and_almostAncientCollapse (I := I) hdim
    (kLimSeedAncientLimit_of_nonpos (I := I) h)
    (kLimAlmostAncientCollapse_of_nonpos (I := I) h)

theorem kLimTerminalDerivativeBound_of_seedAncientLimit_and_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa :=
  kLimTerminalDerivativeBound_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse
      (I := I) hdim hseed hcollapse)

theorem kLimTerminalDerivativeBound_of_seedAncientLimit_and_almostAncientCollapse_of_nonpos
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (h : kappa ≤ 0) :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa :=
  kLimTerminalDerivativeBound_of_seedAncientLimit_and_almostAncientCollapse (I := I) hdim
    (kLimSeedAncientLimit_of_nonpos (I := I) h)
    (kLimAlmostAncientCollapse_of_nonpos (I := I) h)

theorem boundedAtDistanceShell_of_seedAncientLimit_and_almostAncientCollapse_and_blowupBridge
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hseed : KLimSeedAncientLimit.{u, 0, 0} (I := I3) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, 0, 0} (I := I3) kappa)
    (hbridge : KLimBlowupLimitBridge.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_terminalDerivativeBoundProducer
    (terminalDerivativeBoundProducer_of_kLimTerminalDerivativeBound_and_blowupBridge
      (kLimTerminalDerivativeBound_of_seedAncientLimit_and_almostAncientCollapse
        (I := I3) (by simp [ThreeSpace]) hseed hcollapse) hbridge)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem boundedAtDistanceShell_of_modelCurvatureBoundNearBase_and_noSubsequenceCurvatureEscape
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hescape : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, r, hepsStar, hr, hbound⟩ :=
    exists_pos_curvatureBoundedWithin_of_modelScale hmod
  exact boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell
    ⟨epsStar, r, hepsStar, hr, fun eps heps hle X =>
      hbound eps heps hle sigma hsigma Phi hPhi X⟩ hescape

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
