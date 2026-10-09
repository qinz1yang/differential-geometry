import DifferentialGeometry.Topology.Manifold.ClosedDiskRotation
import DifferentialGeometry.Topology.Algebra.Group.TorusMatrix

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

def closedSolidTorusAction (q p : ℤ) (t : Circle) :
    (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      (ClosedCell 2 × Circle) where
  toFun x := (closedDiskRotation (t ^ q) x.1, t ^ p * x.2)
  invFun x := ((closedDiskRotation (t ^ q)).symm x.1, (t ^ p)⁻¹ * x.2)
  left_inv x := by simp
  right_inv x := by simp
  contMDiff_toFun := ((closedDiskRotation (t ^ q)).contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.mul contMDiff_snd)
  contMDiff_invFun := ((closedDiskRotation (t ^ q)).symm.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.mul contMDiff_snd)

theorem closedSolidTorusAction_apply (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    closedSolidTorusAction q p t x = (closedDiskRotation (t ^ q) x.1, t ^ p * x.2) := rfl

@[simp] theorem closedSolidTorusAction_one (q p : ℤ) (x : ClosedCell 2 × Circle) :
    closedSolidTorusAction q p 1 x = x := by
  simp [closedSolidTorusAction_apply]

@[simp] theorem closedSolidTorusAction_mul (q p : ℤ) (t s : Circle)
    (x : ClosedCell 2 × Circle) :
    closedSolidTorusAction q p (t * s) x =
      closedSolidTorusAction q p t (closedSolidTorusAction q p s x) := by
  simp only [closedSolidTorusAction_apply, mul_zpow, closedDiskRotation_mul, mul_assoc]

@[simp] theorem closedSolidTorusAction_inv (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    closedSolidTorusAction q p t⁻¹ x = (closedSolidTorusAction q p t).symm x := by
  apply (closedSolidTorusAction q p t).injective
  change closedSolidTorusAction q p t (closedSolidTorusAction q p t⁻¹ x) =
    closedSolidTorusAction q p t ((closedSolidTorusAction q p t).symm x)
  rw [← closedSolidTorusAction_mul, mul_inv_cancel, closedSolidTorusAction_one,
    Diffeomorph.apply_symm_apply]

theorem closedSolidTorusAction_contMDiff (q p : ℤ) :
    ContMDiff ((𝓡 1).prod ((𝓡∂ 2).prod (𝓡 1))) ((𝓡∂ 2).prod (𝓡 1)) ∞
      (fun x : Circle × (ClosedCell 2 × Circle) => closedSolidTorusAction q p x.1 x.2) := by
  have h : ContMDiff ((𝓡 1).prod ((𝓡∂ 2).prod (𝓡 1)))
      ((𝓡 1).prod (𝓡 1)) ∞
      (fun x : Circle × (ClosedCell 2 × Circle) => Circle.slopeMap ![q, p] x.1) :=
    (Circle.slopeMap_contMDiff ![q, p]).comp contMDiff_fst
  exact (closedDiskRotation_contMDiff.comp
    ((contMDiff_fst.comp h).prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      ((contMDiff_snd.comp h).mul (contMDiff_snd.comp contMDiff_snd))

theorem closedSolidTorusAction_symm_contMDiff (q p : ℤ) :
    ContMDiff ((𝓡 1).prod ((𝓡∂ 2).prod (𝓡 1))) ((𝓡∂ 2).prod (𝓡 1)) ∞
      (fun x : Circle × (ClosedCell 2 × Circle) =>
        (closedSolidTorusAction q p x.1).symm x.2) := by
  have h := (closedSolidTorusAction_contMDiff q p).comp
    (contMDiff_fst.inv.prodMk contMDiff_snd)
  exact h.congr (fun x => (closedSolidTorusAction_inv q p x.1 x.2).symm)

theorem closedSolidTorusAction_complex (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    Complex.orthonormalBasisOneI.repr.symm (closedSolidTorusAction q p t x).1.val =
      ((t ^ q : Circle) : ℂ) * Complex.orthonormalBasisOneI.repr.symm x.1.val :=
  closedDiskRotation_complex (t ^ q) x.1

@[simp] theorem closedSolidTorusAction_norm (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    ‖(closedSolidTorusAction q p t x).1.val‖ = ‖x.1.val‖ :=
  closedDiskRotation_norm (t ^ q) x.1

theorem closedSolidTorusAction_eq_self_iff (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    closedSolidTorusAction q p t x = x ↔ (t ^ q = 1 ∨ x.1.val = 0) ∧ t ^ p = 1 := by
  rw [closedSolidTorusAction_apply, Prod.mk.injEq, closedDiskRotation_eq_self_iff]
  exact and_congr_right (fun _ => mul_eq_right)

theorem closedSolidTorusAction_eq_self_iff_of_eq_zero (q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) (hx : x.1.val = 0) :
    closedSolidTorusAction q p t x = x ↔ t ^ p = 1 := by
  simp only [closedSolidTorusAction_eq_self_iff, hx, or_true, true_and]

theorem closedSolidTorusAction_eq_self_iff_of_ne_zero (q p : ℤ) (hqp : IsCoprime q p)
    (t : Circle) (x : ClosedCell 2 × Circle) (hx : x.1.val ≠ 0) :
    closedSolidTorusAction q p t x = x ↔ t = 1 := by
  constructor
  · intro h
    obtain ⟨h, hp⟩ := (closedSolidTorusAction_eq_self_iff q p t x).mp h
    have hq := h.resolve_right hx
    apply Circle.slopeMap_injective ![q, p] hqp
    simp only [Circle.slopeMap, Matrix.cons_val_zero, Matrix.cons_val_one,
      hq, hp, one_zpow]
  · rintro rfl
    exact closedSolidTorusAction_one q p x

end DifferentialGeometry.Topology.Manifold
