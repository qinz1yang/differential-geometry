import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M]

theorem hamilton_ancient_trace_harnack_at_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Set.Iic 0) (hregular : D.regular = Set.Iio 0)
    (hcomplete : ∀ t ∈ D.carrier,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ D.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : M,
        Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.carrier, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) (V : TangentSpace I x) :
    0 ≤ derivWithin (fun s : ℝ => S.scalar s x) D.carrier 0 +
      2 * (S.base.metric 0).inner x
        (gradientAt (I := I) (flowG (I := I) S) 0 (S.scalar 0) x) V +
      2 * metricRicci (I := I) (M := M) (S.base.metric 0) x (vec2 V V) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
