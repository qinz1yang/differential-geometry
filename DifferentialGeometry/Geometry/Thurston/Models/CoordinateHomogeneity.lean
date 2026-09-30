import DifferentialGeometry.Geometry.Thurston.Models.CoordinateMetrics

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Geometry

private abbrev proj (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def coordinateShiftLinear (k : CoordinateModel) (a b : ModelCoordinates) :
    ModelCoordinates →L[ℝ] ModelCoordinates :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (match k with
      | .hyperbolic => ![Real.exp (b 2 - a 2) • proj 0,
          Real.exp (b 2 - a 2) • proj 1, proj 2]
      | .hyperbolicProduct | .universalSL2 =>
          ![Real.exp (b 1 - a 1) • proj 0, proj 1, proj 2]
      | .nil => ![proj 0, proj 1, proj 2 + (b 0 - a 0) • proj 1]
      | .sol => ![Real.exp (a 2 - b 2) • proj 0,
          Real.exp (b 2 - a 2) • proj 1, proj 2]))

theorem coordinateShiftLinear_inverse (k : CoordinateModel)
    (a b v : ModelCoordinates) :
    coordinateShiftLinear k b a (coordinateShiftLinear k a b v) = v := by
  cases k <;> ext i <;> fin_cases i <;>
    simp [coordinateShiftLinear, proj, Real.exp_sub] <;> field_simp
  all_goals ring

def coordinateShift (k : CoordinateModel) (a b x : ModelCoordinates) : ModelCoordinates :=
  b + coordinateShiftLinear k a b (x - a)

@[simp] theorem coordinateShift_self (k : CoordinateModel) (a b : ModelCoordinates) :
    coordinateShift k a b a = b := by simp [coordinateShift]

theorem coordinateShift_inverse (k : CoordinateModel) (a b x : ModelCoordinates) :
    coordinateShift k b a (coordinateShift k a b x) = x := by
  simp only [coordinateShift, add_sub_cancel_left, coordinateShiftLinear_inverse,
    add_sub_cancel]

theorem coordinateShift_contDiff (k : CoordinateModel) (a b : ModelCoordinates) :
    ContDiff ℝ ∞ (coordinateShift k a b) :=
  contDiff_const.add ((coordinateShiftLinear k a b).contDiff.comp
    (contDiff_id.sub contDiff_const))

theorem coordinateShift_hasFDerivAt (k : CoordinateModel) (a b x : ModelCoordinates) :
    HasFDerivAt (coordinateShift k a b) (coordinateShiftLinear k a b) x := by
  convert! ((coordinateShiftLinear k a b).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a)).const_add b using 1

def coordinateShiftDiffeomorph (k : CoordinateModel) (a b : ModelCoordinates) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := coordinateShift k a b
  invFun := coordinateShift k b a
  left_inv := coordinateShift_inverse k a b
  right_inv := coordinateShift_inverse k b a
  contMDiff_toFun := (coordinateShift_contDiff k a b).contMDiff
  contMDiff_invFun := (coordinateShift_contDiff k b a).contMDiff

theorem coordinateShift_preserves_coframe (k : CoordinateModel)
    (a b x v : ModelCoordinates) :
    coordinateCoframe k (coordinateShift k a b x) (coordinateShiftLinear k a b v) =
      coordinateCoframe k x v := by
  cases k <;> ext i <;> fin_cases i <;>
    simp [coordinateCoframe, coordinateShift, coordinateShiftLinear, proj,
      Real.exp_sub, Real.exp_add, Real.exp_neg] <;> field_simp
  all_goals ring

theorem coordinateShift_preserves_inner (k : CoordinateModel)
    (a b x v w : ModelCoordinates) :
    coordinateInner k (coordinateShift k a b x)
      (coordinateShiftLinear k a b v) (coordinateShiftLinear k a b w) =
        coordinateInner k x v w := by
  simp only [coordinateInner, coordinateShift_preserves_coframe]

theorem coordinateModelMetric_homogeneous (k : CoordinateModel) :
    HomogeneousMetric (coordinateModelMetric k) := by
  intro a b
  refine ⟨coordinateShiftDiffeomorph k a b, coordinateShift_self k a b, ?_⟩
  intro x v w
  change (coordinateModelMetric k).inner (coordinateShift k a b x)
    (mfderiv (𝓡 3) (𝓡 3) (coordinateShift k a b) x v)
    (mfderiv (𝓡 3) (𝓡 3) (coordinateShift k a b) x w) = _
  rw [mfderiv_eq_fderiv, (coordinateShift_hasFDerivAt k a b x).fderiv]
  change coordinateBilinear k (coordinateShift k a b x)
    (coordinateShiftLinear k a b v) (coordinateShiftLinear k a b w) =
      coordinateBilinear k x v w
  exact (coordinateBilinear_apply k _ _ _).trans
    ((coordinateShift_preserves_inner k a b x v w).trans
      (coordinateBilinear_apply k x v w).symm)

theorem coordinateModelMetric_locallyHomogeneous (k : CoordinateModel) :
    LocallyHomogeneousMetric (coordinateModelMetric k) :=
  (coordinateModelMetric_homogeneous k).locallyHomogeneous

end GC.Geometry
