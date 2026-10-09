import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeLocalCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.DifferentialGeometry.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open scoped _root_.DifferentialGeometry.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance klimBoundTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance klimBoundCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance klimBoundSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance klimBoundC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance klimBoundC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance klimBoundT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance klimBoundSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

def KLimTerminalDerivativeBound (kappa : ℝ) : Prop :=
  ∃ K : ℝ → ℝ, (∀ A, 0 < K A) ∧
    ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
      KLim (I := I) kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, 0 ≤ A → ∀ m : ℕ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          curvDerivNorm (I := I) m (F.S.base.metric 0) y ≤
            shiLocalUniformBound (Module.finrank ℝ E) m (K A) (Real.sqrt (K A)) * K A

omit [I.Boundaryless] in
theorem kLim_terminal_curvDerivNorm_zero_le_sqrt_three_mul_scalar
    (hdim : Module.finrank ℝ E = 3)
    {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    {t : ℝ} (ht : t ∈ D.carrier) (y : F.M) :
    curvDerivNorm (I := I) 0 (F.S.base.metric t) y ≤
      Real.sqrt 3 * F.S.scalar t y := by
  have h := pointedFlow_rmNormLeScalar_of_nonnegativeOperator (I := I) F hdim
    hK.nonnegativeCurvatureOperator t ht y
  change Real.sqrt (curvDerivNormSq (I := I) 0 (F.S.base.metric t) y) ≤
    Real.sqrt 3 * F.S.scalar t y at h
  simpa only [curvDerivNorm] using h

theorem kLimTerminalDerivativeBound_of_localCurvatureBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa) :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_normalized_klim_spatial_jet_constants_of_localCurvatureBound
      (I := I) hdim kappa h
  refine ⟨K, hK, fun D F hKL hbase A hA m y hy => ?_⟩
  have hb := hbound D F hKL hbase A hA 0 (le_refl (0 : ℝ)) m y hy
  simpa only [hdim] using hb

theorem kLimTerminalDerivativeBound_of_harnackCollapseBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa :=
  kLimTerminalDerivativeBound_of_localCurvatureBound (I := I) hdim
    (kLimLocalCurvatureBound_of_harnackCollapseBound (I := I) hdim h)

end General

section ThreeSpace

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private local instance klimBridgeC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance klimBridgeC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

def KLimBlowupLimitBridge (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∀ K : ℝ → ℝ, (∀ A, 0 < K A) →
    (∀ (D : RealTimeInterval) (F : PointedFlowData.{u, 0, 0} (I := I3) D),
        KLim (I := I3) kappa F → F.S.scalar 0 F.basepoint = 1 →
          ∀ A : ℝ, 0 ≤ A → ∀ m : ℕ, ∀ y : F.M,
            riemannianEDistOf (I := I3) (F.S.base.metric 0) F.basepoint y ≤
              ENNReal.ofReal A →
            curvDerivNorm (I := I3) m (F.S.base.metric 0) y ≤
              shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K A)
                (Real.sqrt (K A)) * K A) →
      ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, TerminalDerivativeBounds X

theorem terminalDerivativeBoundProducer_of_kLimTerminalDerivativeBound_and_blowupBridge
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hK : KLimTerminalDerivativeBound.{u, 0, 0} (I := I3) kappa)
    (hb : KLimBlowupLimitBridge.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hKpos, hKbound⟩ := hK
  exact hb K hKpos fun D F hKL hbase A hA m y hy =>
    hKbound D F hKL hbase A hA m y hy

theorem terminalDerivativeBoundProducer_of_harnackCollapseBound_and_blowupBridge
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (hb : KLimBlowupLimitBridge.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_kLimTerminalDerivativeBound_and_blowupBridge
    (kLimTerminalDerivativeBound_of_harnackCollapseBound (I := I3)
      (by simp [ThreeSpace]) h) hb

end ThreeSpace

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
