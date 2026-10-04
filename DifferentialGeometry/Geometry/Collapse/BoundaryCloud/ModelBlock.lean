import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile

/-!
# The boundary model block (blueprint 207B, BCG03 (BCG03.a)–(BCG03.b), B:8960–9010; BCG05 B:9270–9280)

For a reference with raw coordinate `z ∈ E`, radius `R = R_a`, unit row `A = A_b` and centering values
`s₀ = η_b(p_a)`, `z₀ = η_a(p_a)`, the model height is `h_b(z) = s₀ + R A(z - z₀)` and the model block is
`Φ_{a,b}(z) = R⁻¹ 𝓑(h_b(z))`. The prefactor `R⁻¹` cancels once in `DΦ` and leaves a factor `R` in
`D²Φ`, so `‖DΦ‖ ≤ P` and `‖D²Φ‖ ≤ R P` (BCG03.b); the large value `1/R` never enters.
On the open plateau the model marker is locally the constant `R⁻¹` (BCG05).
-/

set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine model height `h_b(z) = η_b(p_a) + R_a A_b (z - η_a(p_a))` of (BCG03.a). -/
noncomputable def modelHeight (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) : ℝ := s₀ + R * A (z - z₀)

/-- The boundary model block `Φ_{a,b}(z) = R_a⁻¹ 𝓑(h_b(z))` of (BCG03.a). -/
noncomputable def modelBlock (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) : ℝ × ℝ :=
  R⁻¹ • boundaryBlock (modelHeight s₀ R A z₀ z)

theorem hasFDerivAt_modelHeight (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) :
    HasFDerivAt (modelHeight s₀ R A z₀) (R • A) z := by
  have h1 : HasFDerivAt (fun y => A (y - z₀)) A z := by
    have h := A.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const z₀)
    rwa [ContinuousLinearMap.comp_id] at h
  exact (h1.const_mul R).const_add s₀

theorem continuous_modelHeight (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ : E) :
    Continuous (modelHeight s₀ R A z₀) :=
  continuous_const.add (continuous_const.mul (A.continuous.comp (continuous_id.sub continuous_const)))

theorem contDiff_modelBlock (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ : E) :
    ContDiff ℝ ∞ (modelBlock s₀ R A z₀) := by
  have hh : ContDiff ℝ ∞ (modelHeight s₀ R A z₀) :=
    contDiff_const.add (contDiff_const.mul (A.contDiff.comp (contDiff_id.sub contDiff_const)))
  exact (contDiff_boundaryBlock.comp hh).const_smul R⁻¹

private theorem hasDerivAt_boundaryBlock (t : ℝ) :
    HasDerivAt boundaryBlock (deriv boundaryBlock t) t :=
  ((contDiff_boundaryBlock.differentiable (by simp)) t).hasDerivAt

private theorem hasDerivAt_deriv_boundaryBlock (t : ℝ) :
    HasDerivAt (deriv boundaryBlock) (deriv (deriv boundaryBlock) t) t := by
  have h2 : ContDiff ℝ (1 + 1) boundaryBlock := contDiff_boundaryBlock.of_le (by norm_cast)
  exact ((h2.deriv'.differentiable (by simp)) t).hasDerivAt

/-- `DΦ_{a,b}(z) = A_b ⊗ 𝓑'(h_b(z))`: the prefactor `R⁻¹` cancels (BCG03.b). -/
theorem hasFDerivAt_modelBlock (s₀ : ℝ) {R : ℝ} (hR : R ≠ 0) (A : E →L[ℝ] ℝ) (z₀ z : E) :
    HasFDerivAt (modelBlock s₀ R A z₀)
      (A.smulRight (deriv boundaryBlock (modelHeight s₀ R A z₀ z))) z := by
  have hc := ((hasDerivAt_boundaryBlock (modelHeight s₀ R A z₀ z)).hasFDerivAt.comp z
    (hasFDerivAt_modelHeight s₀ R A z₀ z)).const_smul R⁻¹
  have hfun : modelBlock s₀ R A z₀ = fun y => R⁻¹ • (boundaryBlock ∘ modelHeight s₀ R A z₀) y :=
    rfl
  rw [hfun]
  convert hc using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [smul_smul, inv_mul_cancel₀ hR]

theorem fderiv_modelBlock (s₀ : ℝ) {R : ℝ} (hR : R ≠ 0) (A : E →L[ℝ] ℝ) (z₀ : E) :
    fderiv ℝ (modelBlock s₀ R A z₀) =
      fun z => A.smulRight (deriv boundaryBlock (modelHeight s₀ R A z₀ z)) :=
  funext fun z => (hasFDerivAt_modelBlock s₀ hR A z₀ z).fderiv

/-- First half of (BCG03.b): `‖DΦ_{a,b}‖ ≤ P` for a row of norm at most one. -/
theorem norm_fderiv_modelBlock_le (s₀ : ℝ) {R P : ℝ} (hR : R ≠ 0) {A : E →L[ℝ] ℝ}
    (hA : ‖A‖ ≤ 1) (hP : ∀ t, ‖deriv boundaryBlock t‖ ≤ P) (z₀ z : E) :
    ‖fderiv ℝ (modelBlock s₀ R A z₀) z‖ ≤ P := by
  rw [fderiv_modelBlock s₀ hR A z₀, ContinuousLinearMap.norm_smulRight_apply]
  calc ‖A‖ * ‖deriv boundaryBlock (modelHeight s₀ R A z₀ z)‖ ≤ 1 * P :=
        mul_le_mul hA (hP _) (norm_nonneg _) zero_le_one
    _ = P := one_mul P

/-- Second half of (BCG03.b): `‖D²Φ_{a,b}‖ ≤ R P`; the factor `R` survives the second derivative. -/
theorem norm_fderiv_fderiv_modelBlock_le (s₀ : ℝ) {R P : ℝ} (hR : 0 < R) {A : E →L[ℝ] ℝ}
    (hA : ‖A‖ ≤ 1) (hP : ∀ t, ‖deriv (deriv boundaryBlock) t‖ ≤ P) (z₀ z : E) :
    ‖fderiv ℝ (fderiv ℝ (modelBlock s₀ R A z₀)) z‖ ≤ R * P := by
  rw [fderiv_modelBlock s₀ hR.ne' A z₀]
  let T := ContinuousLinearMap.smulRightL ℝ E (ℝ × ℝ) A
  have hT : ∀ u, T u = A.smulRight u := fun _ => rfl
  have hd : HasFDerivAt (fun z => T (deriv boundaryBlock (modelHeight s₀ R A z₀ z)))
      (T.comp (((1 : ℝ →L[ℝ] ℝ).smulRight
        (deriv (deriv boundaryBlock) (modelHeight s₀ R A z₀ z))).comp (R • A))) z :=
    T.hasFDerivAt.comp z ((hasDerivAt_deriv_boundaryBlock _).hasFDerivAt.comp z
      (hasFDerivAt_modelHeight s₀ R A z₀ z))
  have hfun : (fun z => A.smulRight (deriv boundaryBlock (modelHeight s₀ R A z₀ z))) =
      fun z => T (deriv boundaryBlock (modelHeight s₀ R A z₀ z)) := funext fun z => (hT _).symm
  rw [hfun, hd.fderiv]
  have hTn : ‖T‖ ≤ ‖A‖ := by
    rw [ContinuousLinearMap.norm_smulRightL]
  have hB := hP (modelHeight s₀ R A z₀ z)
  have hRA : ‖R • A‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_of_le_one_right hR.le hA
  have hS : ‖(1 : ℝ →L[ℝ] ℝ).smulRight (deriv (deriv boundaryBlock) (modelHeight s₀ R A z₀ z))‖ ≤ P := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    exact hB
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hB
  calc ‖T.comp (((1 : ℝ →L[ℝ] ℝ).smulRight
          (deriv (deriv boundaryBlock) (modelHeight s₀ R A z₀ z))).comp (R • A))‖
      ≤ ‖T‖ * (‖(1 : ℝ →L[ℝ] ℝ).smulRight
          (deriv (deriv boundaryBlock) (modelHeight s₀ R A z₀ z))‖ * ‖R • A‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (P * R) := by
        apply mul_le_mul (hTn.trans hA) (mul_le_mul hS hRA (norm_nonneg _) hP0)
          (by positivity) zero_le_one
    _ = R * P := by ring

/-- Normalized value comparison of BCG03: `‖R⁻¹𝓑(s) - R⁻¹𝓑(s')‖ ≤ R⁻¹ P |s - s'|`, hence an actual/model
height error below `R θ` costs at most `P θ`. -/
theorem norm_inv_smul_boundaryBlock_sub_lt {R P θ : ℝ} (hR : 0 < R) (hP0 : 0 < P)
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) {s s' : ℝ} (hss : |s - s'| < R * θ) :
    ‖R⁻¹ • boundaryBlock s - R⁻¹ • boundaryBlock s'‖ < P * θ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have h := norm_boundaryBlock_sub_le hP s s'
  have h2 : P * |s - s'| < P * (R * θ) := mul_lt_mul_of_pos_left hss hP0
  calc R⁻¹ * ‖boundaryBlock s - boundaryBlock s'‖ ≤ R⁻¹ * (P * |s - s'|) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR.le)
    _ < R⁻¹ * (P * (R * θ)) := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hR)
    _ = P * θ := by field_simp

/-- BCG05's model marker: when the model height lies strictly between `30` and `80`, the marker
component of the model block is locally the constant `R⁻¹`. -/
theorem modelBlock_snd_eventuallyEq (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E)
    (hz : modelHeight s₀ R A z₀ z ∈ Ioo (30 : ℝ) 80) :
    (fun y => (modelBlock s₀ R A z₀ y).2) =ᶠ[𝓝 z] fun _ => R⁻¹ := by
  have hev := (continuous_modelHeight s₀ R A z₀).continuousAt.preimage_mem_nhds
    (Ioo_mem_nhds hz.1 hz.2)
  filter_upwards [hev] with y hy
  simp only [modelBlock, Prod.smul_snd, boundaryBlock_snd, smul_eq_mul,
    boundaryProfile_eq_one (Ioo_subset_Icc_self hy), mul_one]

/-- BCG05: the physical model plane lies in the scalar marker kernel (marker derivative zero). -/
theorem hasFDerivAt_modelBlock_snd_zero (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E)
    (hz : modelHeight s₀ R A z₀ z ∈ Ioo (30 : ℝ) 80) :
    HasFDerivAt (fun y => (modelBlock s₀ R A z₀ y).2) (0 : E →L[ℝ] ℝ) z :=
  (hasFDerivAt_const R⁻¹ z).congr_of_eventuallyEq (modelBlock_snd_eventuallyEq s₀ R A z₀ z hz)

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
