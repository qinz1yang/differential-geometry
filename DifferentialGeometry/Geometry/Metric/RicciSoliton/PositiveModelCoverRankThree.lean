import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover ∧
      IsQuotientCoveringMap cover (coveringDeckGroup cover) := by
  apply exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_sectional_pos
    (I := I) (M := M) h hdim
  intro x v w hvw
  apply metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
    (I := I) (M := M) g x
      (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim)
      (hrank x) (hcone x) v w hvw

theorem exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover := by
  obtain ⟨cover, hcover, _⟩ :=
    exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
      (I := I) (M := M) h hdim hcone hrank
  exact ⟨cover, hcover⟩

end DifferentialGeometry.Geometry
