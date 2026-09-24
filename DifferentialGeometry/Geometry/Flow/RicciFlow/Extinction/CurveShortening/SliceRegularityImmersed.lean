import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SliceRegularityFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampAngleWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAngleEvolution

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve

variable (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_continuous_of_immersedOn {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Continuous (fun x => c.speed g lambda x t) :=
  (speed_contDiff_of_immersedOn c g lambda hlambda hc hi t ht).continuous

omit [CompleteSpace E] in
theorem sliceRegularity_of_projectionImmersedOn [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    c.SliceRegularity g lambda t :=
  ProductCurve.sliceRegularity c g lambda hlambda hc hi t ht

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

omit [CompactSpace Q] [ConnectedSpace Q] in
theorem CurveShorteningSliceRegularity.of_projectionImmersedOn
    (B : RicciBackground (I := I) (M := Q) D a b) {L₀ : ℝ}
    (hdepth : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      c.projection.ImmersedOn (I := I) (Icc a b)) :
    CurveShorteningSliceRegularity (I := I) (Q := Q) (D := D) (a := a) (b := b) B L₀ :=
  fun lambda hlambda hlambda_one c hsol hlen t ht =>
    ProductCurve.sliceRegularity c B.family.metric lambda hlambda hsol
      (hdepth lambda hlambda hlambda_one c hsol hlen) t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
