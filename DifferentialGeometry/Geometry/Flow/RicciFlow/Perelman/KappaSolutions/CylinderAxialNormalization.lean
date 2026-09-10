import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology

private local instance cylinderAxialSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def cylinderAxialScale (c : ℝ) (hc : c ≠ 0) :
    SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
      SpatialNeckCylinder where
  toEquiv :=
    { toFun := fun x => (x.1, c * x.2)
      invFun := fun x => (x.1, c⁻¹ * x.2)
      left_inv := by
        intro x
        apply Prod.ext
        · rfl
        · change c⁻¹ * (c * x.2) = x.2
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · change c * (c⁻¹ * x.2) = x.2
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] }
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)

@[simp] theorem cylinderAxialScale_apply (c : ℝ) (hc : c ≠ 0)
    (x : SpatialNeckCylinder) : cylinderAxialScale c hc x = (x.1, c * x.2) := rfl


theorem cylinderAxialScale_symm (c : ℝ) (hc : c ≠ 0) :
    (cylinderAxialScale c hc).symm = cylinderAxialScale c⁻¹ (inv_ne_zero hc) := by
  apply _root_.Diffeomorph.ext
  intro x
  rfl

@[simp] theorem cylinderAxialScale_central (c : ℝ) (hc : c ≠ 0)
    (y : SpatialNeckSphere) : cylinderAxialScale c hc (y, 0) = (y, 0) := by
  simp only [cylinderAxialScale_apply, mul_zero]


theorem cylinderAxialScale_mfderiv (c : ℝ) (hc : c ≠ 0)
    (x : SpatialNeckCylinder) (V : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale c hc) x V = (V.1, c * V.2) := by
  have hd : HasFDerivAt (fun z : ℝ => c * z)
      (c • ContinuousLinearMap.id ℝ ℝ) x.2 :=
    (hasFDerivAt_id x.2).const_smul c
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => c * z) x.2 :=
    hd.differentiableAt.mdifferentiableAt
  have hfun : (cylinderAxialScale c hc : SpatialNeckCylinder → SpatialNeckCylinder) =
      Prod.map (id : SpatialNeckSphere → SpatialNeckSphere) (fun z : ℝ => c * z) := rfl
  rw [hfun, mfderiv_prodMap mdifferentiableAt_id hm, mfderiv_id]
  change (V.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => c * z) x.2 V.2) = _
  rw [mfderiv_eq_fderiv, hd.fderiv]
  rfl

def doubleSphereCylinderMetric :
    SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder :=
  DifferentialGeometry.Diffeomorph.pullbackMetric
    (scaleMetric 2 (by norm_num) unitCylinderMetric)
    (cylinderAxialScale (Real.sqrt 2) (by positivity)).symm

theorem doubleSphereCylinderMetric_inner (y : SpatialNeckSphere) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    doubleSphereCylinderMetric.inner (y, s) (v, a) (w, b) =
      2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hcoefficient : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hs)
    calc
      (Real.sqrt 2) ^ 2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) =
          (Real.sqrt 2 * (Real.sqrt 2)⁻¹) *
            (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hs]; norm_num
      _ = (Real.sqrt 2) ^ 2 * (1 / 2 : ℝ) := by rw [hsquare]; norm_num
  have hpull := DifferentialGeometry.Diffeomorph.pullbackMetric_inner
    (scaleMetric 2 (by norm_num) unitCylinderMetric)
    (cylinderAxialScale (Real.sqrt 2) (by positivity)).symm (y, s) (v, a) (w, b)
  have hdiff (V : TangentSpace SpatialNeckCylinderModel (y, s)) :
      mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale (Real.sqrt 2) hs).symm (y, s) V =
      (V.1, (Real.sqrt 2)⁻¹ * V.2) := by
    have heq := congrArg
      (fun Φ : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
          SpatialNeckCylinder =>
        (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel Φ (y, s) V :
          EuclideanSpace ℝ (Fin 2) × ℝ))
      (cylinderAxialScale_symm (Real.sqrt 2) hs)
    exact heq.trans (cylinderAxialScale_mfderiv (Real.sqrt 2)⁻¹ (inv_ne_zero hs) (y, s) V)
  have hinner := congrArg₂
    (fun V Z : EuclideanSpace ℝ (Fin 2) × ℝ =>
      unitCylinderMetric.inner (y, (Real.sqrt 2)⁻¹ * s) V Z)
    (hdiff (v, a)) (hdiff (w, b))
  have hformula := hinner.trans
    (unitCylinderMetric_inner y ((Real.sqrt 2)⁻¹ * s) v w
      ((Real.sqrt 2)⁻¹ * a) ((Real.sqrt 2)⁻¹ * b))
  apply hpull.trans
  simp only [scaleMetric_inner]
  apply (congrArg (fun z : ℝ => 2 * z) hformula).trans
  calc
    2 * ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        ((Real.sqrt 2)⁻¹ * a) * ((Real.sqrt 2)⁻¹ * b)) =
      2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (a * b) := by ring
    _ = _ := by rw [hcoefficient]; ring

theorem cylinderAxialScale_pullback_doubleSphereCylinderMetric :
    DifferentialGeometry.Diffeomorph.pullbackMetric doubleSphereCylinderMetric
        (cylinderAxialScale (Real.sqrt 2) (by positivity)) =
      scaleMetric 2 (by norm_num) unitCylinderMetric := by
  rw [doubleSphereCylinderMetric, DifferentialGeometry.Diffeomorph.pullbackMetric_trans,
    _root_.Diffeomorph.self_trans_symm, DifferentialGeometry.Diffeomorph.pullbackMetric_refl]

theorem cylinderAxialScale_normalized_doubleSphereCylinderMetric :
    scaleMetric (1 / 2) (by norm_num)
        (DifferentialGeometry.Diffeomorph.pullbackMetric doubleSphereCylinderMetric
          (cylinderAxialScale (Real.sqrt 2) (by positivity))) = unitCylinderMetric := by
  rw [cylinderAxialScale_pullback_doubleSphereCylinderMetric]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
