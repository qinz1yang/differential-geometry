import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedData
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.CompactConvergence

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.CauchyTransform

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
private theorem ae_norm_coefficient_mul_le {a : ℂ} {R B : ℝ}
    (A : closedBall a R → V →L[ℂ] V) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (P : C(closedBall a R, V →L[ℂ] V)) :
    ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w * P w‖ ≤ B * ‖P‖ := by
  filter_upwards [hbound] with w hw
  exact (norm_mul_le _ _).trans
    (mul_le_mul hw (P.norm_coe_le_norm w) (norm_nonneg _) hB)

/-- Apply the literal disk Cauchy integral to a fixed bounded measurable coefficient
times a continuous matrix field. The coefficient is unchanged. -/
def boundedCoefficientCauchyTransform {a : ℂ} {R B : ℝ} (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (P : C(closedBall a R, V →L[ℂ] V)) : C(closedBall a R, V →L[ℂ] V) :=
  boundedDiskCauchyTransform hR (fun w => A w * P w)
    (hA.mul P.continuous.stronglyMeasurable.aestronglyMeasurable)
    (mul_nonneg hB (norm_nonneg P)) (ae_norm_coefficient_mul_le A hB hbound P)

omit [CompleteSpace V] in
/-- The coefficient transform uses the same coefficient and the explicit disk integral. -/
theorem boundedCoefficientCauchyTransform_apply {a : ℂ} {R B : ℝ} (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (P : C(closedBall a R, V →L[ℂ] V)) (z : closedBall a R) :
    boundedCoefficientCauchyTransform hR A hA hB hbound P z =
      (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R,
        ((z : ℂ) - (w : ℂ))⁻¹ • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) := rfl

/-- Banach contraction constructs a continuous integral solution for the same bounded
measurable complex-linear coefficient, without a differentiability hypothesis. -/
theorem exists_bounded_integral_fixedPoint (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (hk : 4 * R * B < 1) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + boundedCoefficientCauchyTransform hR A hA hB hbound P ∧
      ‖P - 1‖ ≤ (4 * R * B) / (1 - 4 * R * B) ∧
      ∀ z : closedBall a R, P z = 1 + (Real.pi : ℂ)⁻¹ •
        ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • (A w * P w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
  let T := boundedCoefficientCauchyTransform hR A hA hB hbound
  let k : ℝ := 4 * R * B
  have hk0 : 0 ≤ k := by positivity
  have hb (P : C(closedBall a R, V →L[ℂ] V)) : ‖T P‖ ≤ k * ‖P‖ := by
    have hh := norm_boundedDiskCauchyTransform_le hR (fun w => A w * P w)
      (hA.mul P.continuous.stronglyMeasurable.aestronglyMeasurable)
      (mul_nonneg hB (norm_nonneg P)) (ae_norm_coefficient_mul_le A hB hbound P)
    simpa only [T, boundedCoefficientCauchyTransform, k, mul_assoc] using hh
  have hsub (P Q : C(closedBall a R, V →L[ℂ] V)) :
      T P - T Q = T (P - Q) := by
    apply ContinuousMap.ext
    intro z
    change diskCauchyIntegral (fun w => A w * P w) z -
      diskCauchyIntegral (fun w => A w * Q w) z =
      diskCauchyIntegral (fun w => A w * (P - Q) w) z
    simp only [diskCauchyIntegral, ContinuousMap.sub_apply, mul_sub, smul_sub]
    rw [integral_sub
      (integrable_diskCauchyIntegral_kernel hR (fun w => A w * P w)
        (hA.mul P.continuous.stronglyMeasurable.aestronglyMeasurable)
        (ae_norm_coefficient_mul_le A hB hbound P) z)
      (integrable_diskCauchyIntegral_kernel hR (fun w => A w * Q w)
        (hA.mul Q.continuous.stronglyMeasurable.aestronglyMeasurable)
        (ae_norm_coefficient_mul_le A hB hbound Q) z), smul_sub]
  let Φ (P : C(closedBall a R, V →L[ℂ] V)) := 1 + T P
  have hcon : ContractingWith ⟨k, hk0⟩ Φ := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun P Q => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have he : Φ P - Φ Q = T (P - Q) := by
      simpa only [Φ, add_sub_add_left_eq_sub] using hsub P Q
    rw [he]
    exact hb (P - Q)
  obtain ⟨P, hP, _, _⟩ := hcon.exists_fixedPoint 0 (edist_ne_top _ _)
  have he : P = 1 + T P := hP.symm
  have hnorm : ‖P - 1‖ ≤ k * ‖P‖ := by
    have hh : P - 1 = T P := by
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
    boundedCoefficientCauchyTransform_apply] using hz

/-- Smallness constructs pointwise units of the continuous gauge, including at all
disk points where the coefficient's almost-everywhere bound need not hold. -/
theorem exists_unit_bounded_integral_fixedPoint (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (hk : 4 * R * B < 1 / 2) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + boundedCoefficientCauchyTransform hR A hA hB hbound P ∧
      ‖P - 1‖ ≤ (4 * R * B) / (1 - 4 * R * B) ∧
      (∀ z : closedBall a R, IsUnit (P z)) ∧
      ∀ z : closedBall a R, P z = 1 + (Real.pi : ℂ)⁻¹ •
        ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • (A w * P w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
  obtain ⟨P, hP, hn, hi⟩ :=
    exists_bounded_integral_fixedPoint a R hR A hA B hB hbound (by linarith)
  refine ⟨P, hP, hn, ?_, hi⟩
  intro z
  have hb : (4 * R * B) / (1 - 4 * R * B) < 1 := by
    apply (div_lt_one (by linarith : 0 < 1 - 4 * R * B)).mpr
    linarith
  have hz : ‖1 - P z‖ < 1 := by
    rw [norm_sub_rev]
    exact ((P - 1).norm_coe_le_norm z).trans_lt (hn.trans_lt hb)
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hz

end DifferentialGeometry.Analysis.CauchyTransform
