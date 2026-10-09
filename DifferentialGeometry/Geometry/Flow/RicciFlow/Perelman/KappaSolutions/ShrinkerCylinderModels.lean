import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderModelEvolution

section
set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} I)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem cylinder_antipodal_scalar_one (x : CylinderAntipodalQuotient) :
    metricScalarAt cylinderAntipodalQuotientMetric x = 1 := by
  obtain ⟨y, rfl⟩ := cylinderAntipodalQuotientMap_surjective x
  rw [← metricScalarAt_localPull cylinderAntipodalQuotientMetric
    cylinderAntipodalQuotientMap cylinderAntipodalQuotientMap_isLocalDiffeomorph,
    localPullMetric_cylinderAntipodalQuotientMetric]
  exact roundThreeCylinderShrinkerMetric_scalarCurvature y

private theorem cylinder_diagonal_scalar_one (x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient) :
    metricScalarAt cylinderDiagonalQuotientMetric x = 1 := by
  obtain ⟨y, rfl⟩ := cylinderDiagonalQuotientMap_surjective x
  rw [← metricScalarAt_localPull cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph,
    localPullMetric_cylinderDiagonalQuotientMetric]
  exact roundThreeCylinderShrinkerMetric_scalarCurvature y

theorem NoncompactShrinkerIsometryModels.scalar_eq_one
    {g : SmoothRiemannianMetric I L.M} {f : C^∞⟮I, L.M; ℝ⟯}
    (h : NoncompactShrinkerIsometryModels L g f) (x : L.M) : metricScalarAt g x = 1 := by
  rcases h with ⟨e, he, _hf⟩ | ⟨e, he, _hf⟩ | ⟨e, he, _hf⟩
  · have hh := metricScalar_cross g e (e.symm x)
    rw [e.apply_symm_apply, he] at hh
    exact hh.symm.trans (roundThreeCylinderShrinkerMetric_scalarCurvature _)
  · let d := cylinderAntipodalQuotientDiffeomorph.trans e
    have hd : Diffeomorph.pullbackMetricCross g d = cylinderAntipodalQuotientMetric := by
      rw [← Diffeomorph.pullbackMetricCross_trans, he,
        cylinderAntipodalQuotientDiffeomorph_pullbackMetric]
    have hh := metricScalar_cross g d (d.symm x)
    rw [d.apply_symm_apply, hd] at hh
    exact hh.symm.trans (cylinder_antipodal_scalar_one _)
  · have hh := metricScalar_cross g e (e.symm x)
    rw [e.apply_symm_apply, he] at hh
    exact hh.symm.trans (cylinder_diagonal_scalar_one _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} I)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

omit [CompleteSpace E] in
theorem NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models
    {g : ℝ → SmoothRiemannianMetric I L.M} {f : C^∞⟮I, L.M; ℝ⟯}
    (h : NoncompactShrinkerIsometryModels L (g 0) f)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : L.M, ∀ v w : TangentSpace I x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w) :
    (∃ d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0, Diffeomorph.pullbackMetricCross (g t) d =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : SpatialNeckCylinder, f (d x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ d : (DifferentialGeometry.RealProjectivePlane × ℝ) ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (g t)
          (cylinderAntipodalQuotientDiffeomorph.trans d)) cylinderAntipodalQuotientMap
          cylinderAntipodalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : DifferentialGeometry.RealProjectivePlane × ℝ, f (d x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ d : DifferentialGeometry.Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (g t) d) cylinderDiagonalQuotientMap
          cylinderDiagonalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
        f (d x) = cylinderDiagonalQuotientPotential x) := by
  rcases h with ⟨d, hd, hf⟩ | ⟨d, hd, hf⟩ | ⟨d, hd, hf⟩
  · exact Or.inl ⟨d, fun t ht =>
      pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci g hflow d hd t ht, hf⟩
  · refine Or.inr (Or.inl ⟨d, ?_, hf⟩)
    have hzero : Diffeomorph.pullbackMetricCross (g 0)
        (cylinderAntipodalQuotientDiffeomorph.trans d) = cylinderAntipodalQuotientMetric := by
      rw [← Diffeomorph.pullbackMetricCross_trans, hd,
        cylinderAntipodalQuotientDiffeomorph_pullbackMetric]
    exact fun t ht => pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci
      g hflow (cylinderAntipodalQuotientDiffeomorph.trans d) hzero t ht
  · exact Or.inr (Or.inr ⟨d, fun t ht =>
      pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci g hflow d hd t ht, hf⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
