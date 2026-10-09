import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierLinear
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProduct

/-!
# Extendable arithmetic normal forms for genus-one lens parameters

A nonzero lower-left entry gives a positive lens parameter. The coordinate change on the source
solid torus preserves its meridian and is upper triangular; the new matching matrix is A U.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

theorem exists_meridianPreserving_lens_normalForm (A : GL (Fin 2) ℤ)
    (hc : A.val 1 0 ≠ 0) :
    ∃ p : ℕ, 0 < p ∧ ∃ q : ℤ, ∃ hpq : IsCoprime (p : ℤ) q,
      ∃ U : GL (Fin 2) ℤ, U • meridianSlope = meridianSlope ∧
        A * U = lensMatrixUnit p q hpq ∧ p = (A.val 1 0).natAbs ∧
        U.val 1 0 = 0 ∧ (U.val 0 0 = 1 ∨ U.val 0 0 = -1) ∧
        (U.val 1 1 = 1 ∨ U.val 1 1 = -1) := by
  let p := (A.val 1 0).natAbs
  have hp : 0 < p := Nat.pos_of_ne_zero (by
    intro h
    exact hc (Int.natAbs_eq_zero.mp h))
  have hcol : IsPrimitive (A.val 0 0, A.val 1 0) := by
    have h := isPrimitive_smulVec (Matrix.isUnits_det_units A)
      (v := (1, 0)) (by decide)
    simpa only [smulVec, mul_one, mul_zero, add_zero] using h
  have hcp : IsCoprime (A.val 0 0) (A.val 1 0) :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcol
  have hnormal : ∃ q : ℤ, ∃ hpq : IsCoprime (p : ℤ) q,
      lensMatrixUnit p q hpq • meridianSlope = A • meridianSlope := by
    by_cases hc0 : 0 ≤ A.val 1 0
    · have hcast : (p : ℤ) = A.val 1 0 := by
        rw [Int.natCast_natAbs, abs_of_nonneg hc0]
      have hpq : IsCoprime (p : ℤ) (-A.val 0 0) := by
        rw [hcast]
        exact hcp.symm.neg_right
      refine ⟨-A.val 0 0, hpq, ?_⟩
      change _ • PrimitiveSlope.mk (1, 0) (by decide) =
        _ • PrimitiveSlope.mk (1, 0) (by decide)
      rw [PrimitiveSlope.smul_mk, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
      left
      simp only [smulVec, lensMatrixUnit_val, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, add_zero, neg_neg, hcast]
    · have hcast : (p : ℤ) = -A.val 1 0 := by
        rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hc0)]
      have hpq : IsCoprime (p : ℤ) (A.val 0 0) := by
        rw [hcast]
        exact hcp.symm.neg_left
      refine ⟨A.val 0 0, hpq, ?_⟩
      change _ • PrimitiveSlope.mk (1, 0) (by decide) =
        _ • PrimitiveSlope.mk (1, 0) (by decide)
      rw [PrimitiveSlope.smul_mk, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
      right
      simp only [smulVec, lensMatrixUnit_val, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, add_zero, Prod.neg_mk, hcast, neg_neg]
  obtain ⟨q, hpq, hnormal⟩ := hnormal
  let U := A⁻¹ * lensMatrixUnit p q hpq
  have hU : U • meridianSlope = meridianSlope := by
    rw [mul_smul, hnormal, inv_smul_smul]
  have hAU : A * U = lensMatrixUnit p q hpq := mul_inv_cancel_left A _
  obtain ⟨h10, h00, h11⟩ := meridianStabilizer_entries U hU
  exact ⟨p, hp, q, hpq, U, hU, hAU, rfl, h10, h00, h11⟩

def lensZeroMatrixUnit : GL (Fin 2) ℤ :=
  PrimitiveSlope.unitOfDet !![-1, 0; 0, 1] (Or.inr (by
    rw [Matrix.det_fin_two_of]
    norm_num))

theorem lensZeroMatrixUnit_meridian : lensZeroMatrixUnit • meridianSlope = meridianSlope := by
  change _ • PrimitiveSlope.mk (1, 0) (by decide) = PrimitiveSlope.mk (1, 0) (by decide)
  rw [PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
  right
  simp [lensZeroMatrixUnit, PrimitiveSlope.val_unitOfDet, smulVec]

theorem exists_meridianPreserving_product_normalForm (A : GL (Fin 2) ℤ)
    (hc : PrimitiveSlope.delta (A • meridianSlope) meridianSlope = 0) :
    ∃ U : GL (Fin 2) ℤ, U • meridianSlope = meridianSlope ∧
      A * U = lensZeroMatrixUnit ∧ U.val 1 0 = 0 ∧
      (U.val 0 0 = 1 ∨ U.val 0 0 = -1) ∧ (U.val 1 1 = 1 ∨ U.val 1 1 = -1) := by
  have hA : A • meridianSlope = meridianSlope := (PrimitiveSlope.delta_eq_zero_iff _ _).mp hc
  let U := A⁻¹ * lensZeroMatrixUnit
  have hU : U • meridianSlope = meridianSlope := by
    calc
      U • meridianSlope = A⁻¹ • (lensZeroMatrixUnit • meridianSlope) := mul_smul _ _ _
      _ = A⁻¹ • meridianSlope := congrArg (A⁻¹ • ·) lensZeroMatrixUnit_meridian
      _ = A⁻¹ • (A • meridianSlope) := congrArg (A⁻¹ • ·) hA.symm
      _ = meridianSlope := inv_smul_smul A meridianSlope
  obtain ⟨h10, h00, h11⟩ := meridianStabilizer_entries U hU
  exact ⟨U, hU, mul_inv_cancel_left A _, h10, h00, h11⟩

def lensSwapMatrixUnit : GL (Fin 2) ℤ :=
  PrimitiveSlope.unitOfDet !![0, 1; 1, 0] (Or.inr (by
    rw [Matrix.det_fin_two_of]
    norm_num))

theorem lensSwapMatrixUnit_distances :
    PrimitiveSlope.delta (lensSwapMatrixUnit • meridianSlope) fiberSlope = 0 ∧
      PrimitiveSlope.delta (lensSwapMatrixUnit • fiberSlope) meridianSlope = 0 ∧
      PrimitiveSlope.delta (lensSwapMatrixUnit • meridianSlope) meridianSlope = 1 := by
  rw [delta_smul_meridian_fiber, delta_smul_fiber_meridian, delta_smul_meridian_meridian]
  norm_num [lensSwapMatrixUnit, PrimitiveSlope.val_unitOfDet]

theorem lensIdentityMatrix_distances :
    PrimitiveSlope.delta ((1 : GL (Fin 2) ℤ) • meridianSlope) fiberSlope = 1 ∧
      PrimitiveSlope.delta ((1 : GL (Fin 2) ℤ) • fiberSlope) meridianSlope = 1 ∧
      PrimitiveSlope.delta ((1 : GL (Fin 2) ℤ) • meridianSlope) meridianSlope = 0 := by
  rw [delta_smul_meridian_fiber, delta_smul_fiber_meridian, delta_smul_meridian_meridian]
  norm_num

end GC.Seifert
