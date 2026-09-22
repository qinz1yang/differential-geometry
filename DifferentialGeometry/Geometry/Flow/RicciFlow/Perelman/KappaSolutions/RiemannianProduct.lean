import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Measure.Product

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Curvature

variable [CompleteSpace E]
variable [I.Boundaryless] [T2Space M]

private local instance upstreamRiemannianProductC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

set_option backward.isDefEq.respectTransparency false in
theorem metricRm04At_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ) (v : Fin 4 → TangentSpace I y) (a : Fin 4 → ℝ) :
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) (fun i => (v i, a i)) =
      metricRm04At (I := I) h y v := by
  have heq : gP = h.prod (euclideanMetric (E := ℝ)) := by
    refine SmoothRiemannianMetric.ext_inner (I := I.prod 𝓘(ℝ, ℝ)) ?_
    intro x u w
    obtain ⟨y', s'⟩ := x
    rw [SmoothRiemannianMetric.prod_inner]
    change gP.inner (y', s') u w = h.inner y' u.1 w.1 + inner ℝ u.2 w.2
    have hu : u = ((u.1, u.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    have hw : w = ((w.1, w.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    rw [hu, hw]
    rw [hproduct y' s' u.1 w.1 u.2 w.2]
    simp [inner, mul_comm]
  rw [heq]
  rw [metricRm04At_productMetric_apply]
  rw [metricRm04At_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ))
    (by simp) s]
  simp

end Curvature

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
