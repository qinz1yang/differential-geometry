import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}

theorem complete_forward_flatness
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {a b : Real} (hab : a < b)
    (hcarrier : Set.Icc a b ⊆ D.carrier)
    (hregular : Set.Ico a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Set.Icc a b, MetricComplete (I := I) (F.atTime (I := I) t))
    (hcurv : ∃ K : Real, ∀ t ∈ Set.Icc a b, ∀ x : F.M,
      F.rmNormSq (I := I) t x ≤ K)
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) a x = 0) :
    ∀ t ∈ Set.Icc a b, ∀ x : F.M, F.rmNormSq (I := I) t x = 0 := by
  sorry

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
