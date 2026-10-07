/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Hyperbolic.Horospherical

private def coordinate (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

def point (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![(1 / 2) * x 0 + (1 / 2) * (x 0)⁻¹ + (1 / 8) * x 0 * ((x 1)^2 + (x 2)^2),
    (-1 / 2) * x 0 + (1 / 2) * (x 0)⁻¹ + (1 / 8) * x 0 * ((x 1)^2 + (x 2)^2),
    (1 / 2) * x 0 * x 1, (1 / 2) * x 0 * x 2]

def differential (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi
    ![(1 / 2 - (1 / 2) * ((x 0)^2)⁻¹ + ((x 1)^2 + (x 2)^2) / 8) • coordinate 0 +
        (x 0 * x 1 / 4) • coordinate 1 + (x 0 * x 2 / 4) • coordinate 2,
      (-1 / 2 - (1 / 2) * ((x 0)^2)⁻¹ + ((x 1)^2 + (x 2)^2) / 8) • coordinate 0 +
        (x 0 * x 1 / 4) • coordinate 1 + (x 0 * x 2 / 4) • coordinate 2,
      (x 1 / 2) • coordinate 0 + (x 0 / 2) • coordinate 1,
      (x 2 / 2) • coordinate 0 + (x 0 / 2) • coordinate 2]

theorem hasFDerivAt_point (x : Fin 3 → ℝ) (hx : x 0 ≠ 0) :
    HasFDerivAt point (differential x) x := by
  have dh : HasFDerivAt (fun y : Fin 3 → ℝ => y 0) (coordinate 0) x :=
    (coordinate 0).hasFDerivAt
  have da : HasFDerivAt (fun y : Fin 3 → ℝ => y 1) (coordinate 1) x :=
    (coordinate 1).hasFDerivAt
  have db : HasFDerivAt (fun y : Fin 3 → ℝ => y 2) (coordinate 2) x :=
    (coordinate 2).hasFDerivAt
  have hi : HasFDerivAt (fun y : Fin 3 → ℝ => (y 0)⁻¹)
      (-((x 0)^2)⁻¹ • coordinate 0) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x dh
  apply hasFDerivAt_pi.mpr
  intro k
  fin_cases k
  · change HasFDerivAt
      (fun y : Fin 3 → ℝ => (1 / 2) * y 0 + (1 / 2) * (y 0)⁻¹ +
        (1 / 8) * y 0 * ((y 1)^2 + (y 2)^2)) _ x
    refine (((dh.const_mul (1 / 2)).add (hi.const_mul (1 / 2))).add
      (((dh.const_mul (1 / 8)).mul ((da.pow 2).add (db.pow 2))))).congr_fderiv ?_
    ext v
    simp [coordinate, smul_eq_mul]
    ring
  · change HasFDerivAt
      (fun y : Fin 3 → ℝ => (-1 / 2) * y 0 + (1 / 2) * (y 0)⁻¹ +
        (1 / 8) * y 0 * ((y 1)^2 + (y 2)^2)) _ x
    refine (((dh.const_mul (-1 / 2)).add (hi.const_mul (1 / 2))).add
      (((dh.const_mul (1 / 8)).mul ((da.pow 2).add (db.pow 2))))).congr_fderiv ?_
    ext v
    simp [coordinate, smul_eq_mul]
    ring
  · change HasFDerivAt (fun y : Fin 3 → ℝ => (1 / 2) * y 0 * y 1) _ x
    refine ((dh.const_mul (1 / 2)).mul da).congr_fderiv ?_
    ext v
    simp [coordinate, smul_eq_mul]
    ring
  · change HasFDerivAt (fun y : Fin 3 → ℝ => (1 / 2) * y 0 * y 2) _ x
    refine ((dh.const_mul (1 / 2)).mul db).congr_fderiv ?_
    ext v
    simp [coordinate, smul_eq_mul]
    ring

def lorentzPair (u v : Fin 4 → ℝ) : ℝ :=
  -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

theorem lorentzPair_differential (x u v : Fin 3 → ℝ) (hx : x 0 ≠ 0) :
    lorentzPair (differential x u) (differential x v) =
      u 0 * v 0 / (x 0)^2 + (x 0)^2 / 4 * (u 1 * v 1 + u 2 * v 2) := by
  simp [lorentzPair, differential, coordinate, smul_eq_mul]
  field_simp [hx]
  ring

theorem lorentzPair_fderiv_point (x u v : Fin 3 → ℝ) (hx : x 0 ≠ 0) :
    lorentzPair (fderiv ℝ point x u) (fderiv ℝ point x v) =
      u 0 * v 0 / (x 0)^2 + (x 0)^2 / 4 * (u 1 * v 1 + u 2 * v 2) := by
  rw [(hasFDerivAt_point x hx).fderiv]
  exact lorentzPair_differential x u v hx

theorem lorentzPair_normalized (h a b r u v s w z : ℝ) (hh : h ≠ 0) :
    lorentzPair (differential ![h, a, b] ![-h * r / 2, u, v])
      (differential ![h, a, b] ![-h * s / 2, w, z]) =
        (1 / 4) * (r * s + h^2 * (u * w + v * z)) := by
  rw [lorentzPair_differential _ _ _ hh]
  change (-h * r / 2) * (-h * s / 2) / h^2 + h^2 / 4 * (u * w + v * z) =
    (1 / 4) * (r * s + h^2 * (u * w + v * z))
  field_simp [hh]
  ring

theorem exp_height_sq (r : ℝ) : Real.exp (-r / 2)^2 = Real.exp (-r) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem lorentzPair_cusp_normalized (t a b r u v s w z : ℝ) :
    lorentzPair
      (differential ![Real.exp (-t / 2), a, b] ![-Real.exp (-t / 2) * r / 2, u, v])
      (differential ![Real.exp (-t / 2), a, b] ![-Real.exp (-t / 2) * s / 2, w, z]) =
        (1 / 4) * (r * s + Real.exp (-t) * (u * w + v * z)) := by
  rw [lorentzPair_normalized _ _ _ _ _ _ _ _ _ (Real.exp_ne_zero _), exp_height_sq]

def warpCoordinates (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Real.exp (-x 0 / 2), x 1, x 2]

def warpDifferential (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi
    ![(-Real.exp (-x 0 / 2) / 2) • coordinate 0, coordinate 1, coordinate 2]

theorem hasFDerivAt_warpCoordinates (x : Fin 3 → ℝ) :
    HasFDerivAt warpCoordinates (warpDifferential x) x := by
  have dh : HasFDerivAt (fun y : Fin 3 → ℝ => y 0) (coordinate 0) x :=
    (coordinate 0).hasFDerivAt
  have hr : HasFDerivAt (fun y : Fin 3 → ℝ => -y 0 / 2)
      ((-1 / 2 : ℝ) • coordinate 0) x := by
    convert dh.const_mul (-1 / 2) using 1
    funext y
    ring
  apply hasFDerivAt_pi.mpr
  intro k
  fin_cases k
  · change HasFDerivAt (fun y : Fin 3 → ℝ => Real.exp (-y 0 / 2)) _ x
    refine ((Real.hasDerivAt_exp _).comp_hasFDerivAt x hr).congr_fderiv ?_
    ext v
    simp [coordinate, smul_eq_mul]
    ring
  · exact (coordinate 1).hasFDerivAt
  · exact (coordinate 2).hasFDerivAt

def warpedPoint : (Fin 3 → ℝ) → (Fin 4 → ℝ) := point ∘ warpCoordinates

theorem fderiv_warpedPoint (x : Fin 3 → ℝ) :
    fderiv ℝ warpedPoint x =
      (differential (warpCoordinates x)).comp (warpDifferential x) := by
  exact ((hasFDerivAt_point (warpCoordinates x) (Real.exp_ne_zero _)).comp x
    (hasFDerivAt_warpCoordinates x)).fderiv

theorem lorentzPair_fderiv_warpedPoint (x u v : Fin 3 → ℝ) :
    lorentzPair (fderiv ℝ warpedPoint x u) (fderiv ℝ warpedPoint x v) =
      (1 / 4) * (u 0 * v 0 + Real.exp (-x 0) * (u 1 * v 1 + u 2 * v 2)) := by
  rw [fderiv_warpedPoint]
  simp only [ContinuousLinearMap.comp_apply]
  have hu : warpDifferential x u = ![-Real.exp (-x 0 / 2) * u 0 / 2, u 1, u 2] := by
    ext k
    fin_cases k <;> simp [warpDifferential, coordinate, smul_eq_mul]
    ring
  have hv : warpDifferential x v = ![-Real.exp (-x 0 / 2) * v 0 / 2, v 1, v 2] := by
    ext k
    fin_cases k <;> simp [warpDifferential, coordinate, smul_eq_mul]
    ring
  rw [hu, hv]
  exact lorentzPair_cusp_normalized (x 0) (x 1) (x 2) (u 0) (u 1) (u 2)
    (v 0) (v 1) (v 2)

end DifferentialGeometry.Geometry.Hyperbolic.Horospherical
