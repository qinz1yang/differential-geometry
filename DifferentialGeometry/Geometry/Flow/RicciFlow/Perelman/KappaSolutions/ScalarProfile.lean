import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance scalarProfileTopology : TopologicalSpace F.M := F.topology
local instance scalarProfileCharted : ChartedSpace H F.M := F.charted
local instance scalarProfileSmooth : IsManifold I ∞ F.M := F.smooth
local instance scalarProfileC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance scalarProfileT2 : T2Space F.M := F.t2
local instance scalarProfileSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem scalar_profile_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    ∀ t : ℝ, t ≤ 0 → ∃ R : ℝ, 0 < R ∧ ∀ x : F.M, F.S.scalar t x = R := by
  intro t ht
  obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
  obtain ⟨R, hRpos, hR⟩ := exists_roundSphereQuotient_metricScalarAt_const Dq
  have hscale : 0 < 4 * (T - t) := by
    have hdiff : 0 < T - t := by linarith
    positivity
  refine ⟨(4 * (T - t))⁻¹ * R, ?_, ?_⟩
  · positivity
  · intro x
    rw [show F.S.scalar t x = metricScalarAt (I := I) (F.S.base.metric t) x by rfl]
    have hm : F.S.base.metric t = scaleMetric (4 * (T - t)) hscale
        (Diffeomorph.pullbackMetricCross Dq.gQuot e) := by
      simpa only [SolutionOn.family] using hmetric t ht
    rw [hm, metricScalarAt_scaleMetric, metricScalar_cross, hR]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
