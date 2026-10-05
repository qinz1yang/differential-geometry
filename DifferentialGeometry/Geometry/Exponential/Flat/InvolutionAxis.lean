import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalFiniteTrace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

/-!
The fixed space of an actual nontrivial positive three-dimensional orthogonal involution
is the line spanned by any nonzero fixed vector. Its averaging projector has trace and
rank one. A commuting isometry preserves that actual line and sends its vector to itself
or its negative, without a supplied common direction or axis-uniqueness premise.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem involution_fixedVector_uniqueLine (L : E3 ≃ₗᵢ[ℝ] E3) (hp : L ^ 2 = 1)
    (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap) (q v : E3)
    (hq : q ≠ 0) (hfixq : L q = q) (hfixv : L v = v) : ∃ a : ℝ, v = a • q := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let A := LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap
  have hlin : L.toLinearMap ^ 2 = 1 :=
    congrArg (fun K : E3 ≃ₗᵢ[ℝ] E3 => K.toLinearMap) hp
  have hA2 : A ^ 2 = 1 := by
    change (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap) ^ 2 = 1
    rw [LinearMap.toMatrix_pow, hlin, LinearMap.toMatrix_one]
  have hu := L.toMatrix_mem_unitaryGroup e e
  have horth : A.transpose * A = 1 := by
    have hs := Unitary.star_mul_self_of_mem hu
    change (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap).transpose *
      LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs
  have hdetpos : 0 < A.det := by
    change 0 < (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap).det
    rw [LinearMap.det_toMatrix]
    exact hpos
  have hdet : A.det = 1 :=
    (pow_eq_one_iff_of_nonneg hdetpos.le (by decide : (2 : ℕ) ≠ 0)).mp
      (by rw [← Matrix.det_pow, hA2, Matrix.det_one])
  have hAn : A ≠ 1 := by
    intro he
    apply hne
    have hl : L.toLinearMap = 1 :=
      (LinearMap.toMatrix e.toBasis e.toBasis).injective
        (he.trans (LinearMap.toMatrix_one e.toBasis).symm)
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E3 →ₗ[ℝ] E3 => f x) hl
  have htrace : LinearMap.trace ℝ E3 L.toLinearMap = -1 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ e.toBasis]
    exact orthogonal_nontrivial_involution_trace A horth hdet hA2 hAn
  have hLL (x : E3) : L (L x) = x := congrArg (fun K : E3 ≃ₗᵢ[ℝ] E3 => K x) hp
  let P : E3 →ₗ[ℝ] E3 := (1 / 2 : ℝ) • (L.toLinearMap + 1)
  have hP : IsIdempotentElem P := by
    change P * P = P
    apply LinearMap.ext
    intro x
    change (1 / 2 : ℝ) • (L ((1 / 2 : ℝ) • (L x + x)) +
      (1 / 2 : ℝ) • (L x + x)) = (1 / 2 : ℝ) • (L x + x)
    simp only [map_smul, map_add, hLL]
    module
  have htr : LinearMap.trace ℝ E3 P = 1 := by
    change LinearMap.trace ℝ E3 ((1 / 2 : ℝ) • (L.toLinearMap + 1)) = 1
    rw [map_smul, map_add, htrace, LinearMap.trace_one]
    norm_num
  have hrank : finrank ℝ P.range = 1 := by
    have he := ((LinearMap.isProj_range_iff_isIdempotentElem P).mpr hP).trace
    rw [htr] at he
    exact_mod_cast he.symm
  have hqm : q ∈ P.range := (LinearMap.IsIdempotentElem.mem_range_iff hP).mpr (by
    change (1 / 2 : ℝ) • (L q + q) = q
    rw [hfixq]
    module)
  have hvm : v ∈ P.range := (LinearMap.IsIdempotentElem.mem_range_iff hP).mpr (by
    change (1 / 2 : ℝ) • (L v + v) = v
    rw [hfixv]
    module)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hrank hqm hq] at hvm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvm
  exact ⟨a, ha.symm⟩

theorem commuting_involution_preserves_axis (L K : E3 ≃ₗᵢ[ℝ] E3)
    (hp : L ^ 2 = 1) (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap)
    (hc : Commute L K) (q : E3) (hq : q ≠ 0) (hfixq : L q = q) : K q = q ∨ K q = -q := by
  have he := congrArg (fun T : E3 ≃ₗᵢ[ℝ] E3 => T q) hc.eq
  change L (K q) = K (L q) at he
  rw [hfixq] at he
  obtain ⟨a, ha⟩ := involution_fixedVector_uniqueLine L hp hne hpos q (K q) hq hfixq he
  have hm : |a| * ‖q‖ = 1 * ‖q‖ := by
    have hn := K.norm_map q
    rw [ha, norm_smul, Real.norm_eq_abs] at hn
    simpa only [one_mul] using hn
  have habs : |a| = 1 := mul_right_cancel₀ (norm_ne_zero_iff.mpr hq) hm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    rw [h, one_smul] at ha
    exact ha
  · right
    rw [h, neg_one_smul] at ha
    exact ha

end DifferentialGeometry.Geometry.FlatSurface
