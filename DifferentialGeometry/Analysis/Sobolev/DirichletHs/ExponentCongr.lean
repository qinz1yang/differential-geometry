import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

def dirichletHsCongr
    (g : SmoothRiemannianMetric (I_half n) M) {a b : ℝ}
    (h : a = b) : dirichletHs g a ≃ₗᵢ[ℝ] dirichletHs g b := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

def dirichletHsCongrL
    (g : SmoothRiemannianMetric (I_half n) M) {a b : ℝ}
    (h : a = b) : dirichletHs g a →L[ℝ] dirichletHs g b :=
  (dirichletHsCongr g h).toLinearIsometry.toContinuousLinearMap

@[simp] theorem dirichletHsCongr_coeff
    {g : SmoothRiemannianMetric (I_half n) M} {a b : ℝ}
    (h : a = b) (u : dirichletHs g a)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsCongr g h u).coeff i = u.coeff i := by
  cases h
  rfl

@[simp] theorem dirichletHsCongrL_coeff
    {g : SmoothRiemannianMetric (I_half n) M} {a b : ℝ}
    (h : a = b) (u : dirichletHs g a)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsCongrL g h u).coeff i = u.coeff i := by
  exact dirichletHsCongr_coeff h u i

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
