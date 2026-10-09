/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real

open Set Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def sphereProdIccHomeomorphAnnulus (a b : ℝ) (ha : 0 < a) :
    (sphere (0 : E) 1 × Icc a b) ≃ₜ {x : E | ‖x‖ ∈ Icc a b} where
  toFun p := ⟨(p.2 : ℝ) • (p.1 : E), by
    change ‖(p.2 : ℝ) • (p.1 : E)‖ ∈ Icc a b
    have hr : 0 < (p.2 : ℝ) := ha.trans_le p.2.property.1
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one] using p.2.property⟩
  invFun x := (⟨‖(x : E)‖⁻¹ • (x : E), by
    exact mem_sphere_zero_iff_norm.mpr
      (norm_smul_inv_norm (norm_ne_zero_iff.mp (ha.trans_le x.property.1).ne'))⟩,
    ⟨‖(x : E)‖, x.property⟩)
  left_inv p := by
    let q : sphere (0 : E) 1 × Ioi (0 : ℝ) :=
      (p.1, ⟨p.2, ha.trans_le p.2.property.1⟩)
    have h := (homeomorphUnitSphereProd E).apply_symm_apply q
    apply Prod.ext
    · apply Subtype.ext
      simpa only [homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_symm_apply_coe, q] using
        congrArg (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => (z.1 : E)) h
    · apply Subtype.ext
      simpa only [homeomorphUnitSphereProd_apply_snd_coe,
        homeomorphUnitSphereProd_symm_apply_coe, q] using
        congrArg (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => (z.2 : ℝ)) h
  right_inv x := by
    apply Subtype.ext
    let z : ({0}ᶜ : Set E) :=
      ⟨x, norm_ne_zero_iff.mp (ha.trans_le x.property.1).ne'⟩
    simpa only [homeomorphUnitSphereProd_symm_apply_coe,
      homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe, z] using
      congrArg (fun w : ({0}ᶜ : Set E) => (w : E))
        ((homeomorphUnitSphereProd E).symm_apply_apply z)
  continuous_toFun := by
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_norm.comp continuous_subtype_val).inv₀
        (fun x => (ha.trans_le x.property.1).ne')).smul continuous_subtype_val
    · exact (continuous_norm.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem sphereProdIccHomeomorphAnnulus_apply_coe (a b : ℝ) (ha : 0 < a)
    (p : sphere (0 : E) 1 × Icc a b) :
    (sphereProdIccHomeomorphAnnulus a b ha p : E) = (p.2 : ℝ) • (p.1 : E) := rfl

@[simp]
theorem sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe (a b : ℝ) (ha : 0 < a)
    (x : {x : E | ‖x‖ ∈ Icc a b}) :
    ((sphereProdIccHomeomorphAnnulus a b ha).symm x).1.val = ‖(x : E)‖⁻¹ • (x : E) := rfl

@[simp]
theorem sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe (a b : ℝ) (ha : 0 < a)
    (x : {x : E | ‖x‖ ∈ Icc a b}) :
    ((sphereProdIccHomeomorphAnnulus a b ha).symm x).2.val = ‖(x : E)‖ := rfl

theorem interior_norm_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    interior {x : E | ‖x‖ ∈ Icc a b} = {x : E | ‖x‖ ∈ Ioo a b} := by
  have heq : {x : E | ‖x‖ ∈ Icc a b} = closedBall (0 : E) b ∩ (ball 0 a)ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, mem_inter_iff, mem_closedBall, mem_compl_iff,
      mem_ball, dist_zero_right, not_lt]
    exact and_comm
  rw [heq, interior_inter, interior_closedBall (0 : E) (ha.trans hab).ne',
    interior_compl, closure_ball (0 : E) ha.ne']
  ext x
  simp only [mem_inter_iff, mem_ball, mem_compl_iff, mem_closedBall, dist_zero_right,
    not_le, mem_ofPred_eq, mem_Ioo]
  exact and_comm

theorem isCompact_norm_band [FiniteDimensional ℝ E] (a b : ℝ) :
    IsCompact {x : E | ‖x‖ ∈ Icc a b} := by
  apply (isCompact_closedBall (0 : E) b).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm)
  exact fun x hx => mem_closedBall_zero_iff.mpr hx.2

end DifferentialGeometry.Topology
