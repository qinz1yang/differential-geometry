import DifferentialGeometry.Geometry.Exponential.LocalAddition.SecondDerivative.Hessian
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

theorem secondDerivativeRemainder_eq_blocks
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E) :
    secondDerivativeRemainder (I := I) g p v z a b =
      fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (a, 0) (b, 0) +
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (a, 0) (0, fderiv ℝ v z b) +
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z a) (b, 0) +
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z a) (0, fderiv ℝ v z b) := by
  simpa only [secondDerivativeRemainder] using
    fderiv_fderiv_prod_apply (F := targetCoordinates (I := I) g p)
      (p := z) (x := v z) (a := a) (b := b)
      (u := fderiv ℝ v z a) (v := fderiv ℝ v z b)

end DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

end
