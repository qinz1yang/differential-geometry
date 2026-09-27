import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff _root_.Manifold
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
attribute [local instance] pointedScalarManifoldOne pointedScalarLimitTopology
  pointedScalarLimitCharted pointedScalarLimitSmooth pointedScalarLimitT2 pointedScalarLimitSigma
section NormalizedTerminalSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance pointedScalarFlowTopology : TopologicalSpace F.M := F.topology
local instance pointedScalarFlowCharted : ChartedSpace H F.M := F.charted
local instance pointedScalarFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance pointedScalarFlowT2 : T2Space F.M := F.t2
local instance pointedScalarFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    metricScalarAt (I := I) L.metric L.basepoint = 1 := by
  apply pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
  intro k
  exact terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ (subseq k)

theorem terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (C : CanonicalMetricCompactness (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I))) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = 1 :=
  scalar_base_eq_in_canonicalMetricCompactness C
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)

end NormalizedTerminalSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
