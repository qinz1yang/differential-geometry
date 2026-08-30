import DifferentialGeometry.Geometry.Curvature.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Operator.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_scaleMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (c : Real) (hc : 0 < c) :
    gradientRicciSoliton (I := I) (scaleMetric (I := I) c hc g) f (σ / c) := by
  intro x v w
  rw [Curvature.ricciTensor_scaleMetric, Operator.hessFun_scaleMetric,
    scaleMetric_inner, h x v w]
  field_simp [ne_of_gt hc]

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M] [I.Boundaryless] [T2Space N] [J.Boundaryless]

theorem gradientRicciSoliton_pullbackCross
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := J) g f σ)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    gradientRicciSoliton (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
      (f.comp Φ.toContMDiffMap) σ := by
  intro x v w
  rw [Curvature.ricciTensor_pullbackCross, Operator.hessFun_pullbackCross,
    Diffeomorph.pullbackMetricCross_inner]
  exact h (Φ x) (mfderiv I J (Φ : M → N) x v)
    (mfderiv I J (Φ : M → N) x w)

end DifferentialGeometry.Geometry
