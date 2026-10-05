import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalTraceEnds
import DifferentialGeometry.Geometry.Exponential.Flat.CrystallographicTrace

/-!
Every actual rotation of a free oriented affine lattice group has order one, two, three,
four or six. The integral trace is produced from the same lattice, and the orthogonal
cubic and endpoint trace kernels produce actual powers. A faithful orthonormal matrix
representation transports these powers back to the original linear isometry.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_linear_power_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap) :
    γ.val.linearIsometryEquiv = 1 ∨ γ.val.linearIsometryEquiv ^ 2 = 1 ∨
    γ.val.linearIsometryEquiv ^ 3 = 1 ∨ γ.val.linearIsometryEquiv ^ 4 = 1 ∨
    γ.val.linearIsometryEquiv ^ 6 = 1 := by
  let L := γ.val.linearIsometryEquiv
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let rho : (E3 ≃ₗᵢ[ℝ] E3) →* Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun := fun K => LinearMap.toMatrix e.toBasis e.toBasis K.toLinearMap
      map_one' := by
        change LinearMap.toMatrix e.toBasis e.toBasis (1 : E3 →ₗ[ℝ] E3) = 1
        exact LinearMap.toMatrix_one e.toBasis
      map_mul' := by
        intro K T
        change LinearMap.toMatrix e.toBasis e.toBasis (K.toLinearMap * T.toLinearMap) = _
        exact LinearMap.toMatrix_mul e.toBasis K.toLinearMap T.toLinearMap }
  have hrho : Function.Injective rho := by
    intro K T h
    have he := (LinearMap.toMatrix e.toBasis e.toBasis).injective h
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E3 →ₗ[ℝ] E3 => f x) he
  have hu := L.toMatrix_mem_unitaryGroup e e
  have ho : (rho L).transpose * rho L = 1 := by
    have hs := Unitary.star_mul_self_of_mem hu
    change (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap).transpose *
      LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs
  obtain ⟨T, hT, hdT, z, hz⟩ := exists_affineLinear_integerMatrix G b hb γ hpos
  have hdL : LinearMap.det L.toLinearMap = 1 := by
    rw [← LinearMap.det_toMatrix b, ← hT]
    change (T.map fun n : ℤ => (n : ℝ)).det = 1
    rw [← Int.cast_det, hdT]
    norm_num
  have hdet : (rho L).det = 1 := (LinearMap.det_toMatrix e.toBasis L.toLinearMap).trans hdL
  have htrace : (rho L).trace = LinearMap.trace ℝ E3 L.toLinearMap :=
    (LinearMap.trace_eq_matrix_trace ℝ e.toBasis L.toLinearMap).symm
  have hpow (n : ℕ) (h : rho L ^ n = 1) : L ^ n = 1 := by
    apply hrho
    rw [map_pow, map_one]
    exact h
  have hcases : (rho L).trace = -1 ∨ (rho L).trace = 0 ∨ (rho L).trace = 1 ∨
      (rho L).trace = 2 ∨ (rho L).trace = 3 := by
    rw [htrace]
    exact affineFree_trace_cases G b hb hfree γ hpos
  rcases hcases with h | h | h | h | h
  · right; left
    exact hpow 2 (orthogonal_trace_neg_one_sq _ ho hdet h)
  · right; right; left
    exact hpow 3 (orthogonal_trace_zero_pow _ ho hdet h)
  · right; right; right; left
    exact hpow 4 (orthogonal_trace_one_pow _ ho hdet h)
  · right; right; right; right
    exact hpow 6 (orthogonal_trace_two_pow _ ho hdet h)
  · left
    apply hrho
    rw [map_one]
    exact orthogonal_trace_three_eq_one _ ho h

theorem affineFree_linear_order_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap) :
    orderOf γ.val.linearIsometryEquiv = 1 ∨ orderOf γ.val.linearIsometryEquiv = 2 ∨
    orderOf γ.val.linearIsometryEquiv = 3 ∨ orderOf γ.val.linearIsometryEquiv = 4 ∨
    orderOf γ.val.linearIsometryEquiv = 6 := by
  let L := γ.val.linearIsometryEquiv
  have aux (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) (hp : L ^ n = 1) :
      orderOf L = 1 ∨ orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6 := by
    have hdiv := orderOf_dvd_of_pow_eq_one hp
    have hnpos : 0 < n := by rcases hn with h | h | h | h <;> omega
    have hkpos := Nat.pos_of_dvd_of_pos hdiv hnpos
    have hkle : orderOf L ≤ 6 := by
      have hle := Nat.le_of_dvd hnpos hdiv
      rcases hn with h | h | h | h <;> omega
    rcases hn with rfl | rfl | rfl | rfl <;>
      generalize hk : orderOf L = k at hdiv hkpos hkle ⊢ <;>
      interval_cases k <;> norm_num at hdiv <;> norm_num
  rcases affineFree_linear_power_cases G b hb hfree γ hpos with h | h | h | h | h
  · simp [h]
  · exact aux 2 (by decide) h
  · exact aux 3 (by decide) h
  · exact aux 4 (by decide) h
  · exact aux 6 (by decide) h

end DifferentialGeometry.Geometry.FlatSurface
