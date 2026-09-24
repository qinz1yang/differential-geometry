import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalPropagationOfHarnackCollapse

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.DifferentialGeometry.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance seedFrontierTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance seedFrontierCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance seedFrontierSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance seedFrontierC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
private local instance seedFrontierT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance seedFrontierSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance seedFrontierTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance seedFrontierMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance seedFrontierBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

theorem exists_klim_seed_volume_of_seedAncientLimit
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa) :
    ∃ v : ℝ, 0 < v ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
          ENNReal.ofReal v ≤
            riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
              (riemannianBallOf (I := I) (F.S.base.metric 0) x 1) :=
  kLimSeedVolumeBound_of_seedAncientLimit (I := I) hdim h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_anchored_scalar_bound_of_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa)
    (v D : ℝ) (hv : 0 < v) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ p : F.M,
        ENNReal.ofReal v ≤
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) p 1) →
        ∀ q : F.M, q ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p D →
          F.S.scalar 0 q ≤ C :=
  kLimAnchoredScalarBound_of_almostAncientCollapse (I := I) hdim h v D hv hD

theorem kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  ⟨kLimSeedVolumeBound_of_seedAncientLimit (I := I) hdim hseed,
    kLimAnchoredScalarBound_of_almostAncientCollapse (I := I) hdim hcollapse⟩

theorem modelCurvatureBoundNearBase_of_seedAncientLimit_and_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa :=
  CanonicalNeighborhood.FiniteHorn.modelCurvatureBoundNearBase_of_harnackCollapseBound
    (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse
      (I := I) hdim hseed hcollapse)

theorem exists_klim_seed_volume_of_nonpos
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (hkappa : kappa ≤ 0) :
    ∃ v : ℝ, 0 < v ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
          ENNReal.ofReal v ≤
            riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
              (riemannianBallOf (I := I) (F.S.base.metric 0) x 1) :=
  (kLimHarnackCollapseBound_of_nonpos (I := I) hdim hkappa).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_anchored_scalar_bound_of_nonpos
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (hkappa : kappa ≤ 0)
    (v D : ℝ) (hv : 0 < v) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ p : F.M,
        ENNReal.ofReal v ≤
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) p 1) →
        ∀ q : F.M, q ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p D →
          F.S.scalar 0 q ≤ C :=
  (kLimHarnackCollapseBound_of_nonpos (I := I) hdim hkappa).2 v D hv hD

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
