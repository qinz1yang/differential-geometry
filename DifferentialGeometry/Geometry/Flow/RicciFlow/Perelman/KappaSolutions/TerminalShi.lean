import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

local instance upstreamTerminalShiC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem shi_local_curvDerivNorm_terminal_inclusive
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {a b K R : ℝ} (hab : a < b) (hK : 0 < K) (hR : 0 < R)
    (hcarrier : Set.Icc a b ⊆ D.carrier) (hregular : Set.Ico a b ⊆ D.regular)
    (p : M)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hcurv : ∀ t ∈ Set.Icc a b, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc a b, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K)) →
          curvDerivNorm (I := I) m (S.base.metric t) y ≤
            shiLocalUniformBound (Module.finrank ℝ E) m (K * (b - a)) R * K /
              Real.sqrt (t - a) ^ m := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
