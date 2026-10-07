import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection

namespace DifferentialGeometry.Horospherical

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open MobiusBoundary (ptInfty ptInfty_val_castSucc horoVec_castSucc horizOf)
open AsymptoticRays (rayTo)
open ProjectiveOrthogonalGroup (PO)

variable {m : ℕ}

theorem rayTo_ofCoords (x : Horizontal m) (h : ℝ) (hh : 0 < h) (t : ℝ) :
    rayTo (ofCoords x h hh) ptInfty t =
      ofCoords x (h * Real.exp t) (mul_pos hh (Real.exp_pos t)) := by
  have he : Real.exp (-t) * h⁻¹ = (h * Real.exp t)⁻¹ := by
    rw [Real.exp_neg, mul_inv_rev]
  apply ext_of_horizOf_vHeight
  · ext i
    simp only [HorosphereProjection.rayTo_val_exp, ofCoords, ofCoordsVec, horizOf,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, horoVec_castSucc,
      ptInfty_val_castSucc, mul_zero, add_zero]
    rw [← mul_assoc, he]
  · rw [HorosphereProjection.rayTo_val_exp, vHeight_add, vHeight_smul,
      vHeight_smul, vHeight_ptInfty]
    change Real.exp (-t) * vHeight (ofCoordsVec x h) + _ * 0 =
      vHeight (ofCoordsVec x (h * Real.exp t))
    rw [vHeight_ofCoordsVec, vHeight_ofCoordsVec, mul_zero, add_zero, he]

theorem rayTo_inv_smul_ofCoords_exp (ξ : BoundaryH (m + 1)) (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty)
    (x : Horizontal m) (ℓ t : ℝ) :
    rayTo ((poMulAction (Nat.le_add_left 1 m)).smul a⁻¹
      (ofCoords x (Real.exp ℓ) (Real.exp_pos ℓ))) ξ t =
        (poMulAction (Nat.le_add_left 1 m)).smul a⁻¹
          (ofCoords x (Real.exp (ℓ + t)) (Real.exp_pos (ℓ + t))) := by
  let _ := poMulAction (Nat.le_add_left 1 m)
  let _ := poBoundaryMulAction (Nat.le_add_left 1 m)
  change a • ξ = ptInfty at ha
  have hi : a⁻¹ • (ptInfty : BoundaryH (m + 1)) = ξ := by
    rw [← ha, inv_smul_smul]
  have h := BoundaryExtension.po_smul_rayTo (Nat.le_add_left 1 m) a⁻¹
    (ofCoords x (Real.exp ℓ) (Real.exp_pos ℓ)) ptInfty t
  rw [hi, rayTo_ofCoords] at h
  change rayTo (a⁻¹ • ofCoords x (Real.exp ℓ) (Real.exp_pos ℓ)) ξ t =
    a⁻¹ • ofCoords x (Real.exp (ℓ + t)) (Real.exp_pos (ℓ + t))
  rw [← h]
  congr 1
  apply HUpper.ext
  simp only [ofCoords, Real.exp_add]

end DifferentialGeometry.Horospherical
