import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.SurfaceFlatOrPositive
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

/-!
# SF2 on surfaces modelled on `ℝ²`, and on the round two-sphere

`flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two` specialised to closed connected surfaces
with the model `𝓡 2`, and run on an actual manifold: the round two-sphere
`roundTwoSphereShrinkerMetric` on `S² ⊂ ℝ³` (scalar curvature `1`) has `K ≥ 0`, is not flat, and
SF2 returns its positive branch.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

/-- **SF2 on `𝓡 2` surfaces.** A smooth metric with `K ≥ 0` on a closed connected surface
modelled on `ℝ²` is flat, or the surface carries a smooth metric with `R > 0` everywhere. -/
theorem flat_or_exists_scalar_pos_of_sectional_nonneg_euclidean_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 2) M) (hg : SectionalBoundedBelow g 0) :
    (∀ x (v w z u : TangentSpace (𝓡 2) x),
        metricRm04StandardAt (I := 𝓡 2) (M := M) g x v w z u = 0) ∨
      ∃ h : SmoothRiemannianMetric (𝓡 2) M, ∀ x, 0 < metricScalarAt (I := 𝓡 2) h x :=
  flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two finrank_euclideanSpace_fin g hg

/-- The round two-sphere is connected. -/
theorem connectedSpace_sphere_euclideanSpace_three :
    ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  exact isConnected_iff_connectedSpace.mp (isConnected_sphere hrank _ zero_le_one)

/-- The round two-sphere has nonnegative sectional curvature. -/
theorem roundTwoSphereShrinkerMetric_sectionalBoundedBelow_zero :
    SectionalBoundedBelow (I := 𝓡 2) roundTwoSphereShrinkerMetric 0 :=
  (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two finrank_euclideanSpace_fin).2
    fun x => by rw [roundTwoSphereShrinkerMetric_scalarCurvature x]; norm_num

/-- The round two-sphere is not flat. -/
theorem roundTwoSphereShrinkerMetric_not_flat :
    ¬ ∀ x (v w z u : TangentSpace (𝓡 2) x),
      metricRm04StandardAt (I := 𝓡 2)
        (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        roundTwoSphereShrinkerMetric x v w z u = 0 := by
  intro hflat
  have := connectedSpace_sphere_euclideanSpace_three
  have : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ConnectedSpace.toNonempty
  let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := Classical.arbitrary _
  obtain ⟨v, w, hvw⟩ :=
    exists_linearIndependent_pair_of_finrank_eq_two (I := 𝓡 2) finrank_euclideanSpace_fin x
  have hden := sectionalCurvatureDenominator_pos_of_linearIndependent
    roundTwoSphereShrinkerMetric x v w hvw
  have h := metricRm04StandardAt_sectional_eq_of_finrank_eq_two
    roundTwoSphereShrinkerMetric finrank_euclideanSpace_fin x v w
  rw [hflat x v w w v, roundTwoSphereShrinkerMetric_scalarCurvature x] at h
  have hz : sectionalCurvatureDenominator (I := 𝓡 2) roundTwoSphereShrinkerMetric x v w = 0 := by
    linarith
  exact hden.ne' hz

/-- **Consumer.** SF2 run on the round two-sphere lands in the positive branch. -/
theorem exists_scalar_pos_roundTwoSphere_of_flat_or_positive :
    ∃ h : SmoothRiemannianMetric (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      ∀ x, 0 < metricScalarAt (I := 𝓡 2) h x :=
  have := connectedSpace_sphere_euclideanSpace_three
  (flat_or_exists_scalar_pos_of_sectional_nonneg_euclidean_two roundTwoSphereShrinkerMetric
    roundTwoSphereShrinkerMetric_sectionalBoundedBelow_zero).resolve_left
    roundTwoSphereShrinkerMetric_not_flat

end DifferentialGeometry.PDE.RicciFlow
