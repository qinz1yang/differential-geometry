import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff

private local instance shrinkingCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩


def scalarOneShrinkingCylinderMetric (s : ℝ) (hs : s < 1) :
    SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder :=
  DifferentialGeometry.Diffeomorph.pullbackMetric
    (scaleMetric (2 * (1 - s)) (mul_pos (by norm_num) (sub_pos.mpr hs)) unitCylinderMetric)
    (cylinderAxialScale (Real.sqrt (2 * (1 - s)))
      (ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) (sub_pos.mpr hs))))).symm


theorem scalarOneShrinkingCylinderMetric_inner (s : ℝ) (hs : s < 1)
    (y : SpatialNeckSphere) (z : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    (scalarOneShrinkingCylinderMetric s hs).inner (y, z) (v, a) (w, b) =
      2 * (1 - s) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        a * b := by
  let c : ℝ := 2 * (1 - s)
  have hc : 0 < c := mul_pos (by norm_num) (sub_pos.mpr hs)
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hcoefficient : c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) = 1 := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hc.le, mul_inv_cancel₀ hc.ne']
  have hpull := DifferentialGeometry.Diffeomorph.pullbackMetric_inner
    (scaleMetric c hc unitCylinderMetric) (cylinderAxialScale (Real.sqrt c) hsqrt).symm
      (y, z) (v, a) (w, b)
  have hdiff (V : TangentSpace SpatialNeckCylinderModel (y, z)) :
      mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale (Real.sqrt c) hsqrt).symm (y, z) V =
        (V.1, (Real.sqrt c)⁻¹ * V.2) := by
    have heq := congrArg
      (fun Phi : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
          SpatialNeckCylinder =>
        (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel Phi (y, z) V :
          EuclideanSpace ℝ (Fin 2) × ℝ))
      (cylinderAxialScale_symm (Real.sqrt c) hsqrt)
    exact heq.trans (cylinderAxialScale_mfderiv (Real.sqrt c)⁻¹ (inv_ne_zero hsqrt) (y, z) V)
  have hinner := congrArg₂
    (fun V W : EuclideanSpace ℝ (Fin 2) × ℝ =>
      unitCylinderMetric.inner (y, (Real.sqrt c)⁻¹ * z) V W)
    (hdiff (v, a)) (hdiff (w, b))
  have hformula := hinner.trans
    (unitCylinderMetric_inner y ((Real.sqrt c)⁻¹ * z) v w
      ((Real.sqrt c)⁻¹ * a) ((Real.sqrt c)⁻¹ * b))
  apply hpull.trans
  simp only [scaleMetric_inner]
  apply (congrArg (fun r : ℝ => c * r) hformula).trans
  calc
    c * ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        ((Real.sqrt c)⁻¹ * a) * ((Real.sqrt c)⁻¹ * b)) =
      c * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        (c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) * (a * b) := by ring
    _ = _ := by rw [hcoefficient]; ring


theorem scalarOneShrinkingCylinderMetric_zero :
    scalarOneShrinkingCylinderMetric 0 (by norm_num) = doubleSphereCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, z⟩ ⟨v, a⟩ ⟨w, b⟩
  apply (scalarOneShrinkingCylinderMetric_inner 0 (by norm_num) y z v w a b).trans
  apply Eq.trans _ (doubleSphereCylinderMetric_inner y z v w a b).symm
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
