import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.LocalDiffeomorph
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem liftedMetric_eq_localPullMetric
    (g : SmoothRiemannianMetric I M) :
    liftedMetric (I := I) g = localPullMetric g
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      (proj_localDiffeo (I := I)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, (hasMFDerivAt_proj (I := I) x).mfderiv]
  rfl

theorem normalizedGradientRicciSoliton_liftedMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    normalizedGradientRicciSoliton (I := I) (liftedMetric (I := I) g)
      (f.comp ⟨proj, proj_contMDiff (I := I)⟩) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hc := liftedMetric_complete g h.1
  rw [liftedMetric_eq_localPullMetric] at hc ⊢
  exact normalizedGradientRicciSoliton_localPullMetric h (proj_localDiffeo (I := I)) hc

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
