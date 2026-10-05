import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralMetric
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.LocalPullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Sectional
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Product
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds

/-!
Curvature derivative bounds on the actual dihedral quotient metric are uniform in the
positive line length. The bound is supplied by the compact scaled spherical factor.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.Endpoint GC.Geometry.SphericalProduct
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] DifferentialGeometry.Geometry.Collapse.sphereDimension
  DifferentialGeometry.Geometry.Collapse.cylinderDimension
  DifferentialGeometry.Geometry.Collapse.sphereCompact

namespace DifferentialGeometry.Geometry.Collapse

universe u

private theorem dihedralThinCylinderMetric_sectional_nonneg
    (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (x : sphereCylinder) :
    SectionalBoundedBelowAt (dihedralThinCylinderMetric ε L hε hL) x 0 := by
  let c : ℝ := 2 * L / ε
  have hc : 0 < c := div_pos (mul_pos (by norm_num) hL) hε
  let Φ := (Diffeomorph.refl ((𝓡 2))
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne').toContinuousLinearEquiv.toDiffeomorph
  have hscale : ε ^ 2 * c ^ 2 = (2 * L) ^ 2 := by
    dsimp [c]
    field_simp
  have hmetric : Diffeomorph.pullbackMetricCross
      (scaleMetric (ε ^ 2) (pow_pos hε 2) slimSphereMetric) Φ =
      dihedralThinCylinderMetric ε L hε hL := by
    rw [Diffeomorph.pullbackMetricCross_scaleMetric]
    change scaleMetric (ε ^ 2) (pow_pos hε 2)
      (Diffeomorph.pullbackMetricCross
        ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prod
          (DifferentialGeometry.euclideanMetric (E := ℝ))) Φ) = _
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    dsimp only [Φ]
    rw [Diffeomorph.pullbackMetric_prod_euclidean_smul]
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    dsimp only [dihedralThinCylinderMetric]
    rw [scaleMetric_inner, SmoothRiemannianMetric.prod_inner,
      SmoothRiemannianMetric.prod_inner]
    dsimp only [scaleMetric]
    change ε ^ 2 *
      ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 v.1 w.1 +
        c ^ 2 * (DifferentialGeometry.euclideanMetric (E := ℝ)).inner y.2 v.2 w.2) =
      ε ^ 2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 v.1 w.1 +
        (2 * L) ^ 2 * (DifferentialGeometry.euclideanMetric (E := ℝ)).inner y.2 v.2 w.2
    rw [mul_add, ← mul_assoc, hscale]
  rw [← hmetric]
  apply Geometry.Riemannian.sectionalBoundedBelowAt_pullbackMetricCross
  apply (sectionalBoundedBelowAt_scaleMetric_iff (pow_pos hε 2)).mpr
  simpa only [zero_mul] using slimSphereMetric_sectional_nonneg (Φ x)

theorem dihedralMetric_sectional_nonneg (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (x : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) :
    SectionalBoundedBelowAt (dihedralMetric ε L hε hL) x 0 := by
  obtain ⟨z, rfl⟩ := dihedralProjection_surjective x
  have hs : SectionalBoundedBelowAt (dihedralRechartedMetric ε L hε hL) z 0 :=
    Geometry.Riemannian.sectionalBoundedBelowAt_pullbackMetricCross _ _ z
      (dihedralThinCylinderMetric_sectional_nonneg ε L hε hL _)
  rw [← dihedralMetric_pullback] at hs
  intro v w
  let D := dihedralProjection_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by decide) z
  have hv : mfderiv (𝓡 3) (𝓡 3) dihedralProjection z (D.symm v) = v :=
    D.apply_symm_apply v
  have hw : mfderiv (𝓡 3) (𝓡 3) dihedralProjection z (D.symm w) = w :=
    D.apply_symm_apply w
  have h := hs (D.symm v) (D.symm w)
  simp only [zero_mul] at h ⊢
  rw [Curvature.metricRm04StandardAt_localPullMetric, hv, hw] at h
  exact h

theorem exists_dihedralCurvatureDerivative_bound (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L : ℝ) (hL : 0 < L), ∀ k ≤ K,
    ∀ x : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier,
      CheegerGromovCompactness.curvDerivNorm k (dihedralMetric ε L hε hL) x ≤ A := by
  let gS := scaleMetric (ε ^ 2) (pow_pos hε 2)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  obtain ⟨B, hB⟩ := CheegerGromovCompactness.exists_curvDerivNorm_bound_of_isCompact
    gS K (C := Set.univ) isCompact_univ
  refine ⟨max B 1, lt_of_lt_of_le (by norm_num) (le_max_right B 1), ?_⟩
  intro L hL k hk x
  obtain ⟨z, rfl⟩ := dihedralProjection_surjective x
  have hquot := CheegerGromovCompactness.curvDerivNorm_localPullMetric
    (dihedralMetric ε L hε hL) dihedralProjection dihedralProjection_localDiffeomorph k z
  rw [dihedralMetric_pullback] at hquot
  rw [← hquot, dihedralRechartedMetric,
    PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross]
  change CheegerGromovCompactness.curvDerivNorm k
    (gS.prod (scaleMetric ((2 * L) ^ 2) (pow_pos (mul_pos (by norm_num) hL) 2)
      (DifferentialGeometry.euclideanMetric (E := ℝ))))
    (sphereCylinderRechartDiffeomorph.symm z) ≤ max B 1
  rw [PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_prod_real]
  exact (hB k hk _ (Set.mem_univ _)).trans (le_max_left B 1)

end DifferentialGeometry.Geometry.Collapse
