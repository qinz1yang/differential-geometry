import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceCompactness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceMorse

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) :
    (∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover) ∨
      ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M,
        solitonModelCovering roundTwoSphereShrinkerMetric
            roundTwoSphereShrinkerPotential g f cover ∧
          IsQuotientCoveringMap cover (coveringDeckGroup cover) ∧
          ((∃ e : Metric.sphere
              (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ M,
              ∀ x, e x = cover x) ∨
            (∃ e : RealProjectivePlane ≃ₜ M,
              ∀ x, e (realProjectivePlaneQuotientMap x) = cover x)) := by
  by_cases hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1
  · left
    exact exists_solitonModelCovering_of_isGaussianGradientRicciSoliton h hGaussian
  · right
    let _ : CompactSpace M :=
      normalizedGradientRicciSoliton_compactSpace_of_finrank_eq_two_of_not_isGaussian
        (I := I) h hdim hGaussian
    have hscalar :=
      normalizedGradientRicciSoliton_scalar_eq_one_of_compact_of_finrank_eq_two
        (I := I) (E := E) h hdim
    exact
      exists_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_compact_of_finrank_eq_two_of_scalar_eq_one
        (I := I) h hdim hscalar

end DifferentialGeometry.Geometry
