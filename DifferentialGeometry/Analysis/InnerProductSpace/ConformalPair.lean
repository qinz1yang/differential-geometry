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

end LinearMap
