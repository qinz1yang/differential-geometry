import DifferentialGeometry.Topology.ThreeManifold.Closed
import DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold
open scoped Manifold ContDiff

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

structure SphericalSpaceFormQuotientModel
    (I : ModelWithCorners ℝ E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Type _ where
  quotient : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3
  equiv : N ≃ₘ⟮I, 𝓡 3⟯ quotient.Q

def isSphericalSpaceFormQuotient
    (I : ModelWithCorners ℝ E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Prop :=
  Nonempty (SphericalSpaceFormQuotientModel I N)

def isSphericalSpaceForm : Prop :=
  isSphericalSpaceFormQuotient I M

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem constant_positive_sectional_curvature_implies_spherical_space_form
    (hM : isClosedThreeManifold (I := I) (M := M))
    (hconst : admitsConstantPositiveSectionalCurvature (I := I) (M := M)) :
    isSphericalSpaceForm (I := I) (M := M) := by
  obtain ⟨hcompact, hconn, hbdry, hdim⟩ := hM
  obtain ⟨g, c, hc, hsec⟩ := hconst
  let model :=
    constPosQuotient
      (I := I) (M := M) hcompact hconn hbdry hdim g c hc hsec
  exact ⟨⟨model.1, model.2⟩⟩

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem spherical_space_form_admits_constant_positive_sectional_curvature
    (model : isSphericalSpaceFormQuotient I M) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  obtain ⟨S⟩ := model
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  obtain ⟨c, hc, hsec⟩ := S.quotient.gQuot_constPosSec
  refine ⟨Diffeomorph.pullbackMetricCross S.quotient.gQuot S.equiv, c, hc, fun x X Y => ?_⟩
  rw [metricRm04Standard_pullbackCross S.quotient.gQuot S.equiv x X Y Y X, hsec,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x X X,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x Y Y,
    ← Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x X Y]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem spherical_space_form_implies_constant_positive_sectional_curvature
    (hsph : isSphericalSpaceForm (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) :=
  spherical_space_form_admits_constant_positive_sectional_curvature
    (I := I) (M := M) hsph

omit [NeZero (Module.finrank ℝ E)] in
theorem constant_positive_sectional_curvature_iff_spherical_space_form
    (hM : isClosedThreeManifold (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) ↔
      isSphericalSpaceForm (I := I) (M := M) := by
  let : I.Boundaryless := hM.2.2.1
  constructor
  · exact constant_positive_sectional_curvature_implies_spherical_space_form
      (I := I) (M := M) hM
  · exact spherical_space_form_implies_constant_positive_sectional_curvature
      (I := I) (M := M)

end DifferentialGeometry.Geometry
