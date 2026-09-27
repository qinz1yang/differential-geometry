import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.PointedFlowData

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open Bundle
open scoped _root_.Manifold ContDiff

universe u v uE uH uE' uH'
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {D : RealTimeInterval}
  (F : PointedFlowData.{v, uE', uH'} (I := J) D)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local instance pullbackTargetTopology : TopologicalSpace F.M := F.topology
local instance pullbackTargetCharted : ChartedSpace H' F.M := F.charted
local instance pullbackTargetSmooth : IsManifold J ∞ F.M := F.smooth
local instance pullbackTargetT2 : T2Space F.M := F.t2
local instance pullbackTargetSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

def pullback (Phi : M ≃ₘ⟮I, J⟯ F.M) : PointedFlowData.{u, uE, uH} (I := I) D where
  M := M
  topology := inferInstance
  charted := inferInstance
  smooth := inferInstance
  sigmaCompact := inferInstance
  t2 := inferInstance
  t2TangentBundle := inferInstance
  basepoint := Phi.symm F.basepoint
  S := F.S.pullback Phi
  isSolution := F.isSolution.pullback F.S Phi

theorem pullback_rmNormSq (Phi : M ≃ₘ⟮I, J⟯ F.M) (t : ℝ) (x : M) :
    (F.pullback Phi).rmNormSq t x = F.rmNormSq t (Phi x) := by
  exact riemannNormSq_cross (F.S.base.metric t) Phi x

theorem pullback_complete (Phi : M ≃ₘ⟮I, J⟯ F.M) (t : ℝ)
    (hF : MetricComplete (F.atTime t)) :
    MetricComplete ((F.pullback Phi).atTime t) := by
  have hg : RiemannianMetricComplete (F.S.base.metric t) := ⟨hF⟩
  exact (RiemannianMetricComplete.pullbackCross (F.S.base.metric t) Phi hg).complete

end DifferentialGeometry.CheegerGromovCompactness.PointedFlowData
