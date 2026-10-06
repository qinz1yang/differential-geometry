import DifferentialGeometry.Analysis.Complex.CauchyTransform.Disk
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.CompactConvergence

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.CauchyTransform

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- A genuinely constructed continuous matrix solution of the integral equation. -/
theorem exists_integral_fixedPoint (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : C(closedBall a R, V →L[ℂ] V)) (hk : 4 * R * ‖A‖ < 1) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + diskCauchyTransform a R hR (A * P) ∧
      ‖P - 1‖ ≤ (4 * R * ‖A‖) / (1 - 4 * R * ‖A‖) ∧
      ∀ z : closedBall a R, P z = 1 + (Real.pi : ℂ)⁻¹ •
        ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • (A w * P w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
  let T := diskCauchyTransform (F := V →L[ℂ] V) a R hR
  let k : ℝ := 4 * R * ‖A‖
  have hk0 : 0 ≤ k := by positivity
  have hb (P : C(closedBall a R, V →L[ℂ] V)) : ‖T (A * P)‖ ≤ k * ‖P‖ := by
    calc
      _ ≤ ‖T‖ * ‖A * P‖ := T.le_opNorm _
      _ ≤ (4 * R) * (‖A‖ * ‖P‖) := mul_le_mul
        (norm_diskCauchyTransform_le a R hR) (norm_mul_le A P)
        (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [k]; ring
  let Φ (P : C(closedBall a R, V →L[ℂ] V)) := 1 + T (A * P)
  have hcon : ContractingWith ⟨k, hk0⟩ Φ := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun P Q => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have he : Φ P - Φ Q = T (A * (P - Q)) := by
      simp only [Φ, add_sub_add_left_eq_sub, mul_sub, map_sub]
    rw [he]
    exact hb (P - Q)
  obtain ⟨P, hP, _, _⟩ := hcon.exists_fixedPoint 0 (edist_ne_top _ _)
  have he : P = 1 + T (A * P) := hP.symm
  have hnorm : ‖P - 1‖ ≤ k * ‖P‖ := by
    have hh : P - 1 = T (A * P) := by
      simpa only [add_sub_cancel_left] using
        congrArg (fun Q : C(closedBall a R, V →L[ℂ] V) => Q - 1) he
    rw [hh]
    exact hb P
  have hI : ‖(1 : C(closedBall a R, V →L[ℂ] V))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro z
    exact ContinuousLinearMap.norm_id_le
  have htriangle : ‖P‖ ≤ ‖P - 1‖ + 1 := by
    calc
      _ = ‖(P - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖P - 1‖ + ‖(1 : C(closedBall a R, V →L[ℂ] V))‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hI
  have hnear : ‖P - 1‖ ≤ k / (1 - k) := by
    apply (le_div_iff₀ (by dsimp [k]; linarith : 0 < 1 - k)).mpr
    have hh := mul_le_mul_of_nonneg_left htriangle hk0
    nlinarith
  refine ⟨P, he, hnear, ?_⟩
  intro z
  have hz := congrArg (fun Q : C(closedBall a R, V →L[ℂ] V) => Q z) he
  simpa only [T, ContinuousMap.add_apply, ContinuousMap.one_apply,
    diskCauchyTransform_apply, ContinuousMap.mul_apply] using hz

/-- Smallness yields actual pointwise units, rather than an assumed invertible matrix field. -/
theorem exists_unit_integral_fixedPoint (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : C(closedBall a R, V →L[ℂ] V)) (hk : 4 * R * ‖A‖ < 1 / 2) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + diskCauchyTransform a R hR (A * P) ∧
      ‖P - 1‖ ≤ (4 * R * ‖A‖) / (1 - 4 * R * ‖A‖) ∧
      (∀ z : closedBall a R, IsUnit (P z)) ∧
      ∀ z : closedBall a R, P z = 1 + (Real.pi : ℂ)⁻¹ •
        ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • (A w * P w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
  obtain ⟨P, hP, hn, hi⟩ := exists_integral_fixedPoint a R hR A (by linarith)
  refine ⟨P, hP, hn, ?_, hi⟩
  intro z
  have hb : (4 * R * ‖A‖) / (1 - 4 * R * ‖A‖) < 1 := by
    apply (div_lt_one (by linarith : 0 < 1 - 4 * R * ‖A‖)).mpr
    linarith
  have hz : ‖1 - P z‖ < 1 := by
    rw [norm_sub_rev]
    exact ((P - 1).norm_coe_le_norm z).trans_lt (hn.trans_lt hb)
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hz

end DifferentialGeometry.Analysis.CauchyTransform
