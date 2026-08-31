import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveRoundness
import DifferentialGeometry.Geometry.Metric.Sphere.PositiveSpaceForm

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

open Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

theorem exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover := by
  have hround :=
    gradientRicciSoliton_constant_sectional_curvature_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h.2.1 hdim hsec
  obtain ⟨cover, hcoverCont, hcoverSurj, hcovering, hcoverMetric⟩ :=
    exists_round_three_sphere_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) inferInstance inferInstance inferInstance hdim g
        (1 / 4) (by norm_num) (by simpa using hround)
  have hpotential :=
    normalizedGradientRicciSoliton_potential_eq_three_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h hdim hsec
  refine ⟨cover, normalizedGradientRicciSoliton_roundThreeSphere, h,
    hcoverCont, hcoverSurj, hcovering, ?_, ?_⟩
  · intro x v w
    have hmetric := hcoverMetric x v w
    rw [scaleMetric_inner] at hmetric
    rw [roundThreeSphereShrinkerMetric, roundSphereShrinkerMetric,
      scaleMetric_inner]
    norm_num [roundSphereShrinkerRadius] at hmetric ⊢
    linarith
  · intro x
    rw [roundThreeSphereShrinkerPotential_apply, hpotential (cover x)]

end DifferentialGeometry.Geometry
