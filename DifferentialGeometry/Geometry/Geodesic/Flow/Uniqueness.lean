import DifferentialGeometry.Analysis.ODE.Flow.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction

open Bundle Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isMIntegralCurveOn_geodesicVectorFieldChart_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {K : Set ℝ}
    (hsrc : ∀ t ∈ K, (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) K ↔
      IsMIntegralCurveOn f (geodesicVectorField (I := I) g) K := by
  constructor <;> intro hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht

theorem integralCurve_eqOn [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    {f₁ f₂ : ℝ → TangentBundle I M} {K : Set ℝ} {t₀ : ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hf₁ : IsMIntegralCurveOn f₁ (geodesicVectorField (I := I) g) K)
    (hf₂ : IsMIntegralCurveOn f₂ (geodesicVectorField (I := I) g) K)
    (heq : f₁ t₀ = f₂ t₀) : EqOn f₁ f₂ K :=
  isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless hK hconn ht₀
    ((geodesicVF_smooth g).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hf₁ hf₂ heq

end DifferentialGeometry.Geometry.Riemannian.Geodesic
