import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ricciFlow_additive_distance_bound_of_ricci_upper [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    (hconnected : ConnectedSpace M) {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ s ∈ Icc a b,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hRic : ∀ s ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      0 ≤ S.ricciAt s x (vec2 v v) ∧
        S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ E : ℝ) - 1) * K * (S.base.metric s).inner x v v)
    (x y : M) :
    0 ≤ (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
      (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
        (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ≤
      (10 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * Real.sqrt K * (b - a) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
