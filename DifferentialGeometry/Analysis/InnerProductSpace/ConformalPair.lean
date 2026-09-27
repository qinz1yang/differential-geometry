import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LinearMap

theorem IsPosSemidef.apply_self_le_sum_sub_smul_of_orthogonal
    {K V : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] {B : V →ₗ[K] V →ₗ[K] K}
    (hB : B.IsPosSemidef) {v w : V} (horth : B v w = 0)
    (heq : B v v = B w w) (t : V) (a b : K) :
    B v v ≤ B (v - a • t) (v - a • t) + B (w - b • t) (w - b • t) := by
  by_cases hab : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp only [ha, hb, zero_smul, sub_zero]
    exact le_add_of_nonneg_right (hB.nonneg w)
  · have habpos : 0 < a ^ 2 + b ^ 2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg a) (sq_nonneg b)) (Ne.symm hab)
    have hid :
        B (a • v + b • w - (a ^ 2 + b ^ 2) • t)
            (a • v + b • w - (a ^ 2 + b ^ 2) • t) =
          (a ^ 2 + b ^ 2) *
            (B (v - a • t) (v - a • t) + B (w - b • t) (w - b • t) - B v v) := by
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [show B w v = B v w from hB.eq w v, horth, heq]
      ring
    have hnonneg := hB.nonneg (a • v + b • w - (a ^ 2 + b ^ 2) • t)
    rw [hid] at hnonneg
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left habpos).mp hnonneg)

theorem IsPosSemidef.apply_eq_zero_of_conformal_smul
    {K V : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] {B : V →ₗ[K] V →ₗ[K] K}
    (hB : B.IsPosSemidef) {v t : V} {a : K}
    (horth : B (a • t) v = 0) (heq : B (a • t) (a • t) = B v v) :
    B t v = 0 := by
  by_cases ha : a = 0
  · have hv : B v v = 0 := by simpa only [ha, zero_smul, map_zero, LinearMap.zero_apply] using heq.symm
    have hh := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le B hB.nonneg t v
    rw [show B v t = B t v from hB.eq v t, hv, mul_zero] at hh
    nlinarith only [hh, sq_nonneg (B t v)]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at horth
    exact (mul_eq_zero.mp horth).resolve_left ha

theorem IsPosSemidef.eq_neg_div_of_conformal_smul
    {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] {B : V →ₗ[K] V →ₗ[K] K}
    (hB : B.IsPosSemidef) {v t : V} {a b : K} (ht : B t t ≠ 0)
    (horth : B (a • t) (v + b • t) = 0)
    (heq : B (a • t) (a • t) = B (v + b • t) (v + b • t)) :
    b = -(B t v) / B t t := by
  have hh := hB.apply_eq_zero_of_conformal_smul horth heq
  simp only [map_add, map_smul, smul_eq_mul] at hh
  apply (eq_div_iff ht).mpr
  linarith


end LinearMap
