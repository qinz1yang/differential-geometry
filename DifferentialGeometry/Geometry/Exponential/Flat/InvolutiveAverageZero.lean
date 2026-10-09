import DifferentialGeometry.Geometry.Exponential.Flat.InvolutiveHolonomy
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Zero trace of an actual finite orthogonal matrix average forces the average to be zero by
its Gram identity. An actual faithful positive four-element involutive SO3 group supplies
that zero trace internally and has zero vector average, without a trace relation premise.
-/

set_option autoImplicit false

noncomputable section

open Module
open scoped ComplexOrder

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem finite_orthogonal_sum_eq_zero (K : Type*) [instG : Group K] [instF : Fintype K]
    (rho : K →* Matrix (Fin 3) (Fin 3) ℝ)
    (ho : ∀ g, (rho g).transpose * rho g = 1)
    (ht : (∑ g : K, (rho g).trace) = 0) : (∑ g : K, rho g) = 0 := by
  let S : Matrix (Fin 3) (Fin 3) ℝ := ∑ g : K, rho g
  have hleft (g : K) : (rho g).transpose * S = S := by
    have hi : (rho g).transpose = rho g⁻¹ :=
      Matrix.left_inv_eq_left_inv (ho g) (by rw [← map_mul, inv_mul_cancel, map_one])
    rw [hi]
    change rho g⁻¹ * (∑ h : K, rho h) = _
    rw [Finset.mul_sum]
    simp_rw [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (by intro h; rfl)
  have hS : S.transpose * S = (Fintype.card K : ℝ) • S := by
    change (∑ g : K, rho g).transpose * S = _
    rw [Matrix.transpose_sum, Finset.sum_mul]
    simp_rw [hleft]
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have htr : S.trace = 0 := by rw [Matrix.trace_sum]; exact ht
  have hg : (S.conjTranspose * S).trace = 0 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hS, Matrix.trace_smul, htr, smul_zero]
  change S = 0
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hg

theorem positive_involutive_four_sum_zero (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Fintype H] (hc : Fintype.card H = 4)
    (hpos : ∀ a : H, 0 < LinearMap.det a.val.toLinearMap)
    (htwo : ∀ a : H, a.val ^ 2 = 1) : ∀ u : E3, (∑ a : H, a.val u) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let rhoL : (E3 ≃ₗᵢ[ℝ] E3) →* Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun := fun a => LinearMap.toMatrix e.toBasis e.toBasis a.toLinearMap
      map_one' := by
        change LinearMap.toMatrix e.toBasis e.toBasis (1 : E3 →ₗ[ℝ] E3) = 1
        exact LinearMap.toMatrix_one e.toBasis
      map_mul' := by
        intro a b
        change LinearMap.toMatrix e.toBasis e.toBasis (a.toLinearMap * b.toLinearMap) = _
        exact LinearMap.toMatrix_mul e.toBasis a.toLinearMap b.toLinearMap }
  have hrhoL : Function.Injective rhoL := by
    intro a b h
    have he := (LinearMap.toMatrix e.toBasis e.toBasis).injective h
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E3 →ₗ[ℝ] E3 => f x) he
  let rho := rhoL.comp H.subtype
  have hrho : Function.Injective rho := hrhoL.comp Subtype.val_injective
  have ho (a : H) : (rho a).transpose * rho a = 1 := by
    have hu := a.val.toMatrix_mem_unitaryGroup e e
    have hs := Unitary.star_mul_self_of_mem hu
    change (LinearMap.toMatrix e.toBasis e.toBasis a.val.toLinearMap).transpose *
      LinearMap.toMatrix e.toBasis e.toBasis a.val.toLinearMap = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs
  have hp (a : H) : rho a ^ 2 = 1 := by
    change rhoL a.val ^ 2 = 1
    have he := congrArg rhoL (htwo a)
    simpa only [map_pow, map_one] using he
  have hd (a : H) : (rho a).det = 1 := by
    have hdp : 0 < (rho a).det := by
      change 0 < (LinearMap.toMatrix e.toBasis e.toBasis a.val.toLinearMap).det
      rw [LinearMap.det_toMatrix]
      exact hpos a
    exact (pow_eq_one_iff_of_nonneg hdp.le (by decide : (2 : ℕ) ≠ 0)).mp
      (by rw [← Matrix.det_pow, hp, Matrix.det_one])
  have hi : (rho (1 : H)).trace = 3 := by rw [map_one, Matrix.trace_one]; norm_num
  have htrace (a : H) (ha : a ≠ 1) : (rho a).trace = -1 := by
    have hne : rho a ≠ 1 := by intro he; exact ha (hrho (he.trans rho.map_one.symm))
    exact orthogonal_nontrivial_involution_trace (rho a) (ho a) (hd a) (hp a) hne
  have hrest : (∑ a ∈ Finset.univ.erase (1 : H), (rho a).trace) = -3 := by
    calc
      _ = ∑ a ∈ Finset.univ.erase (1 : H), (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact htrace a (Finset.ne_of_mem_erase ha)
      _ = _ := by simp [Finset.card_erase_of_mem, hc]
  have ht : (∑ a : H, (rho a).trace) = 0 := by
    have he := Finset.sum_erase_add Finset.univ (fun a : H => (rho a).trace)
      (Finset.mem_univ (1 : H))
    rw [hrest, hi] at he
    norm_num at he
    exact he.symm
  have hsum := finite_orthogonal_sum_eq_zero H rho ho ht
  have hlin : (∑ a : H, a.val.toLinearMap) = 0 := by
    apply (LinearMap.toMatrix e.toBasis e.toBasis).injective
    rw [map_sum, map_zero]
    exact hsum
  intro u
  change (∑ a : H, a.val.toLinearMap u) = 0
  have he := congrArg (fun f : E3 →ₗ[ℝ] E3 => f u) hlin
  simpa only [LinearMap.sum_apply, LinearMap.zero_apply] using he

end DifferentialGeometry.Geometry.FlatSurface
