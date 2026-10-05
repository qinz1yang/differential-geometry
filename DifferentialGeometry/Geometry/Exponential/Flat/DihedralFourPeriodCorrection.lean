import DifferentialGeometry.Geometry.Exponential.Flat.QuarterTurnPlane
import Mathlib.Algebra.Ring.Int.Parity

/-!
Actual parallel lattice periods admit a translation correction for one of the two dihedral
half-turns. The parity of the integer coefficient selects the corrected half-turn.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem dihedral_four_period_norm_correction (T : Submodule ℤ E3)
    (K L : E3 ≃ₗᵢ[ℝ] E3) (u w t : E3) (m n : ℤ)
    (hu : u ∈ T) (hw : w ∈ T) (ht : t ∈ T) (hKu : K u = u)
    (hKw : K w = L w) (hL2w : (L ^ 2) w = -w) (hKLt : K (L t) = -L t)
    (hum : u = m • t) (hwn : w + K w = n • t) :
    ∃ x : E3, x ∈ T ∧ (u + x + K x = 0 ∨ w + x + K (L x) = 0) := by
  have hLn : L w - w = n • L t := by
    have he := congrArg L hwn
    rw [map_add, map_zsmul, hKw] at he
    change L w + L (L w) = n • L t at he
    have hLLw : L (L w) = -w := hL2w
    rw [hLLw] at he
    simpa only [sub_eq_add_neg] using he
  have h2w : (2 : ℤ) • w = n • (t - L t) := by
    rw [smul_sub, ← hwn, ← hLn, hKw]
    abel
  obtain ⟨j, hn | hn⟩ := Int.even_or_odd' n
  · have hdouble : (2 : ℤ) • w = (2 : ℤ) • (j • (t - L t)) := by
      rw [h2w, hn, smul_smul]
    have hreal : (2 : ℝ) • w = (2 : ℝ) • (j • (t - L t)) := by
      simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_ofNat] using hdouble
    have hz : (2 : ℝ) • (w - j • (t - L t)) = 0 := by
      rw [smul_sub, hreal, sub_self]
    have he : w = j • (t - L t) :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
    let x := (-j) • t
    refine ⟨x, T.smul_mem (-j) ht, Or.inr ?_⟩
    change w + (-j) • t + K (L ((-j) • t)) = 0
    rw [map_zsmul, map_zsmul, hKLt, he, smul_sub]
    simp only [neg_smul, smul_neg]
    abel
  · let x := (-(j + 1)) • u + m • w
    refine ⟨x, T.add_mem (T.smul_mem (-(j + 1)) hu) (T.smul_mem m hw), Or.inl ?_⟩
    have he : u + x + K x = u + (2 * -(j + 1)) • u + m • (w + K w) := by
      dsimp only [x]
      rw [map_add, map_zsmul, map_zsmul, hKu]
      module
    rw [he, hum, hwn, hn]
    simp only [smul_smul]
    module

end DifferentialGeometry.Geometry.FlatSurface
