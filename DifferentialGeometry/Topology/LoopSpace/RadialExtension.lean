import DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric



noncomputable section

open Set NormedSpace Metric
open scoped NNReal

namespace DifferentialGeometry.Topology


def radialExtension (F : Circle → Circle) (z : ℂ) : ℂ := ‖z‖ • (F (radialDirection z) : ℂ)

@[simp] theorem radialExtension_zero (F : Circle → Circle) : radialExtension F 0 = 0 := by
  simp [radialExtension]

@[simp] theorem radialExtension_norm (F : Circle → Circle) (z : ℂ) :
    ‖radialExtension F z‖ = ‖z‖ := by
  rw [radialExtension, norm_smul, Circle.norm_coe, mul_one]
  exact norm_norm z

theorem radialExtension_circle (F : Circle → Circle) (z : Circle) :
    radialExtension F (z : ℂ) = (F z : ℂ) := by
  rw [radialExtension, Circle.norm_coe, one_smul, radialDirection_unit]

theorem radialDirection_radialExtension (F : Circle → Circle) {z : ℂ} (hz : z ≠ 0) :
    radialDirection (radialExtension F z) = F (radialDirection z) :=
  radialDirection_pos_smul (norm_pos_iff.mpr hz) _

theorem radialExtension_id (z : ℂ) : radialExtension id z = z := radialDirection_reconstruct z

theorem radialExtension_comp (F G : Circle → Circle) (z : ℂ) :
    radialExtension (F ∘ G) z = radialExtension F (radialExtension G z) := by
  by_cases hz : z = 0
  · simp [hz]
  · change ‖z‖ • (F (G (radialDirection z)) : ℂ) =
      ‖radialExtension G z‖ • (F (radialDirection (radialExtension G z)) : ℂ)
    rw [radialExtension_norm, radialDirection_radialExtension G hz]



theorem radialExtension_lipschitz {F : Circle → Circle} {L : ℝ≥0}
    (hF : LipschitzWith L F) : LipschitzWith (2 * L + 1) (radialExtension F) := by
  have hordered (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖) :
      dist (radialExtension F x) (radialExtension F y) ≤ (2 * (L : ℝ) + 1) * dist x y := by
    by_cases hx : x = 0
    · subst x
      rw [radialExtension_zero, dist_zero_left, radialExtension_norm, dist_zero_left]
      nlinarith [L.coe_nonneg, norm_nonneg y]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : y ≠ 0 := norm_pos_iff.mp (hxpos.trans_le hxy)
    have hdir : dist (radialDirection x) (radialDirection y) ≤ (2 / ‖x‖) * dist x y := by
      change dist (radialDirection x : ℂ) (radialDirection y : ℂ) ≤ _
      rw [radialDirection_coe hx, radialDirection_coe hy]
      exact DifferentialGeometry.Analysis.normalize_dist_le hxpos le_rfl hxy
    have hangular := (hF.dist_le_mul (radialDirection x) (radialDirection y)).trans
      (mul_le_mul_of_nonneg_left hdir L.coe_nonneg)
    have hnormdiff := abs_norm_sub_norm_le x y
    have heq : radialExtension F x - radialExtension F y =
        ‖x‖ • ((F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ)) +
          (‖x‖ - ‖y‖) • (F (radialDirection y) : ℂ) := by
      simp only [radialExtension, smul_sub, sub_smul]
      abel
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖‖x‖ • ((F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ))‖ +
          ‖(‖x‖ - ‖y‖) • (F (radialDirection y) : ℂ)‖ := norm_add_le _ _
      _ = ‖x‖ * dist (F (radialDirection x)) (F (radialDirection y)) + |‖x‖ - ‖y‖| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hxpos, Circle.norm_coe, mul_one]
        rw [Real.norm_eq_abs]
        have hd : dist (F (radialDirection x)) (F (radialDirection y)) =
            ‖(F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ)‖ :=
          Complex.dist_eq _ _
        rw [hd]
      _ ≤ ‖x‖ * ((L : ℝ) * ((2 / ‖x‖) * dist x y)) + dist x y := by
        apply add_le_add (mul_le_mul_of_nonneg_left hangular hxpos.le)
        simpa only [← dist_eq_norm] using hnormdiff
      _ = _ := by field_simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h : dist (radialExtension F x) (radialExtension F y) ≤ (2 * (L : ℝ) + 1) * dist x y := by
    by_cases hxy : ‖x‖ ≤ ‖y‖
    · exact hordered x y hxy
    · simpa only [dist_comm] using hordered y x (le_of_not_ge hxy)
  exact h

open MeasureTheory in
theorem measurable_coe_radialDirection :
    Measurable (fun z : ℂ => (radialDirection z : ℂ)) := by
  classical
  have heq : (fun z : ℂ => (radialDirection z : ℂ)) =
      fun z => if z = 0 then 1 else ‖z‖⁻¹ • z := by
    funext z
    by_cases hz : z = 0 <;> simp [radialDirection, hz, NormedSpace.normalize]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (0 : ℂ)) measurable_const
    (measurable_norm.inv.smul measurable_id)

end DifferentialGeometry.Topology
