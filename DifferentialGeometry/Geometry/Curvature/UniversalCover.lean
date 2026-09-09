import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M] [Inhabited M]

set_option backward.isDefEq.respectTransparency false in
private theorem normSq0S_lifted_eq
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M) (s : ℕ)
    (A : Tensor0SSpace s I x) :
    normSq0S (liftedMetric (I := I) g) x s A = normSq0S g (proj x) s A := by
  classical
  obtain ⟨b, hb⟩ := exists_gOrthonormalBasis (I := I) g (proj x)
  have hb' : ∀ i j, (liftedMetric (I := I) g).inner x (b i) (b j) =
      if i = j then (1 : ℝ) else 0 := hb
  have hi := metricInverseInBasis_identity_of_orthonormal g b hb
  have hi' := metricInverseInBasis_identity_of_orthonormal (liftedMetric (I := I) g) b hb'
  rw [normSq0S_identity_eq_sum_sq _ x s b hi',
    normSq0S_identity_eq_sum_sq g (proj x) s b hi]
  rfl

variable [I.Boundaryless] [T2Space M]

theorem metricRm04At_liftedMetric_apply
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M) (v : Fin 4 → E) :
    metricRm04At (I := I) (liftedMetric (I := I) g) x v =
      metricRm04At (I := I) g (proj x) v := by
  exact metricRm_lifted (I := I) g x (v 0) (v 1) (v 2) (v 3)

theorem metricRm04At_liftedMetric
    (g : SmoothRiemannianMetric I M)
    (x : UniversalCover M) :
    metricRm04At (I := I) (liftedMetric (I := I) g) x =
      metricRm04At (I := I) g (proj x) := by
  ext v
  exact metricRm04At_liftedMetric_apply (I := I) g x v

theorem normSq0S_metricRm04At_liftedMetric
    (g : SmoothRiemannianMetric I M)
    (x : UniversalCover M) :
    normSq0S (I := I) (liftedMetric (I := I) g) x 4
        (metricRm04At (I := I) (liftedMetric (I := I) g) x) =
      normSq0S (I := I) g (proj x) 4 (metricRm04At (I := I) g (proj x)) := by
  rw [normSq0S_lifted_eq, metricRm04At_liftedMetric]

theorem metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M) :
    metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (I := I) g) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := UniversalCover M) ↔
    metricAlgebraicCurvatureTensorAt (I := I) g (proj x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff,
    metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  constructor
  · intro h n c v w
    have h' := h n c v w
    have heq : ∀ i j : Fin n,
        metricRm04StdAt (I := I) (M := UniversalCover M) (liftedMetric (I := I) g) x
          (v i) (w i) (w j) (v j) =
        metricRm04StdAt (I := I) (M := M) g (proj x)
          (v i) (w i) (w j) (v j) := by
      intro i j
      exact metricRm04At_liftedMetric_apply (I := I) g x (vec4 (v i) (w i) (w j) (v j))
    simpa only [heq] using h'
  · intro h n c v w
    have h' := h n c v w
    have heq : ∀ i j : Fin n,
        metricRm04StdAt (I := I) (M := UniversalCover M) (liftedMetric (I := I) g) x
          (v i) (w i) (w j) (v j) =
        metricRm04StdAt (I := I) (M := M) g (proj x)
          (v i) (w i) (w j) (v j) := by
      intro i j
      exact metricRm04At_liftedMetric_apply (I := I) g x (vec4 (v i) (w i) (w j) (v j))
    simpa only [heq] using h'

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
