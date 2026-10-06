import DifferentialGeometry.Analysis.Complex.CauchyTransform.OffSupport
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.CutoffGradient
import DifferentialGeometry.Analysis.Schauder.Holder.Cutoff

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private def rawDensity {a : ℂ} {R : ℝ} (f : C(closedBall a R, F)) (z : ℂ) : F := by
  classical
  exact if hz : z ∈ closedBall a R then f ⟨z, hz⟩ else 0

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem rawDensity_coe {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (w : closedBall a R) : rawDensity f w = f w := by
  simp only [rawDensity, dite_eq_left w.property]

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem rawDensity_zero {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {w : ℂ} (hw : w ∉ closedBall a R) : rawDensity f w = 0 := by
  simp only [rawDensity, dite_eq_right hw]

private theorem locallyIntegrable_inverse_kernel (z : ℂ) :
    LocallyIntegrable (fun w : ℂ => (z - w)⁻¹) := by
  have he : (fun w : ℂ => (z - w)⁻¹) =
      (-(Real.pi : ℂ)) • (fun w : ℂ => ((Real.pi : ℂ) * (w - z))⁻¹) := by
    funext w
    rw [show z - w = -(w - z) by ring, inv_neg]
    change -(w - z)⁻¹ = -(Real.pi : ℂ) * ((Real.pi : ℂ) * (w - z))⁻¹
    rw [mul_inv_rev]
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    calc
      _ = -((w - z)⁻¹ * ((Real.pi : ℂ) * (Real.pi : ℂ)⁻¹)) := by
        rw [mul_inv_cancel₀ hp, mul_one]
      _ = _ := by ring
  rw [he]
  exact (locallyIntegrable_cauchyKernel z).smul (-(Real.pi : ℂ))

omit [CompleteSpace F] in
private theorem integrable_subtype_kernel {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (z : ℂ) :
    Integrable (fun w : closedBall a R => (z - (w : ℂ))⁻¹ • f w)
      (volume.comap ((↑) : closedBall a R → ℂ)) := by
  have hk := (locallyIntegrable_inverse_kernel z).integrableOn_isCompact
    (isCompact_closedBall a R)
  have hk' : Integrable (fun w : closedBall a R => (z - (w : ℂ))⁻¹)
      (volume.comap ((↑) : closedBall a R → ℂ)) := by
    simpa only [Function.comp_def] using
      (integrableOn_iff_comap_subtypeVal measurableSet_closedBall).mp hk
  exact hk'.smul_bdd ‖f‖ f.continuous.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall f.norm_coe_le_norm)

omit [CompleteSpace F] in
private theorem ambientCauchyIntegral_add {a : ℂ} {R : ℝ}
    (f g : C(closedBall a R, F)) (z : ℂ) :
    ambientCauchyIntegral (f + g) z =
      ambientCauchyIntegral f z + ambientCauchyIntegral g z := by
  change (Real.pi : ℂ)⁻¹ • (∫ w : closedBall a R,
    (z - (w : ℂ))⁻¹ • (f w + g w) ∂(volume.comap Subtype.val)) = _
  simp only [smul_add]
  rw [integral_add (integrable_subtype_kernel f z) (integrable_subtype_kernel g z), smul_add]
  rfl

omit [CompleteSpace F] in
private theorem ambientCauchyIntegral_eq_integral {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {u : ℂ → F}
    (he : ∀ w : closedBall a R, u w = f w)
    (hz : ∀ w ∉ closedBall a R, u w = 0) (z : ℂ) :
    ambientCauchyIntegral f z = (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, (z - w)⁻¹ • u w := by
  have hout : ∀ w ∉ closedBall a R, (z - w)⁻¹ • u w = 0 := by
    intro w hw
    rw [hz w hw, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← integral_subtype_comap measurableSet_closedBall]
  unfold ambientCauchyIntegral
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change (z - (w : ℂ))⁻¹ • f w = (z - (w : ℂ))⁻¹ • u w
    rw [he w]

omit [CompleteSpace F] in
private theorem ofReal_smul (r : ℝ) (x : F) : (r : ℂ) • x = r • x :=
  algebraMap_smul ℂ r x

omit [CompleteSpace F] in
/-- A genuine constant germ, not a single cutoff value, removes the cutoff
 differential in the actual logarithmic gradient. The totalized pole is retained. -/
private theorem inverse_smul_eq_logGradient {χ : ℂ → ℝ} {d : ℂ}
    (hχ : χ =ᶠ[𝓝 d] fun _ => (1 : ℝ)) (x : F) :
    ((Real.pi : ℂ)⁻¹ * d⁻¹) • x = (-2 : ℝ) •
      (truncatedLogGradient χ d 1 • x - Complex.I • (truncatedLogGradient χ d Complex.I • x)) := by
  have hD : fderiv ℝ χ d = 0 := by
    have h := hχ.fderiv (𝕜 := ℝ)
    simpa only [fderiv_const_apply] using h.self_of_nhds
  have hΓ : truncatedLogGradient χ d =
      (-(2 * Real.pi)⁻¹) • ((‖d‖ ^ 2)⁻¹ • innerSL ℝ d) := by
    change (-(2 * Real.pi)⁻¹) •
      (Real.log ‖d‖ • fderiv ℝ χ d + χ d • ((‖d‖ ^ 2)⁻¹ • innerSL ℝ d)) = _
    rw [hD, hχ.self_of_nhds, smul_zero, zero_add, one_smul]
  have hscalar : (Real.pi : ℂ)⁻¹ * d⁻¹ = ((-2 : ℝ) : ℂ) *
      ((truncatedLogGradient χ d 1 : ℂ) -
        Complex.I * (truncatedLogGradient χ d Complex.I : ℂ)) := by
    rw [hΓ, ← Complex.ofReal_inv, RCLike.inv_def d]
    simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
    generalize (‖d‖ ^ 2)⁻¹ = t
    apply Complex.ext <;> simp [real_inner_eq_re_inner] <;>
      field_simp [Real.pi_ne_zero]
  rw [hscalar, mul_smul, sub_smul, mul_smul, ofReal_smul, ofReal_smul, ofReal_smul]

/-- The near term is identified with first derivatives of the SAME actual
potential on a neighborhood. Its C2 regularity is produced internally. -/
private theorem contDiffAt_ambientCauchyIntegral_of_localized_extension
    {a q : ℂ} {R ε : ℝ} (hε : 0 < ε) (f : C(closedBall a R, F))
    {u : ℂ → F} (huc : HasCompactSupport u)
    (hus : tsupport u ⊆ closedBall q (ε / 2))
    (he : ∀ w : closedBall a R, u w = f w)
    (hz : ∀ w ∉ closedBall a R, u w = 0)
    {α H : ℝ≥0} (hu : HolderWith H α u) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffAt ℝ 1 (ambientCauchyIntegral f) q := by
  let χ : ContDiffBump (0 : ℂ) := ⟨ε, 2 * ε, hε, by linarith⟩
  let P : ℂ → F := cutoffLogPotential χ u
  have hu0 : Continuous u := hu.continuous hα
  have hχone : (χ : ℂ → ℝ) =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℝ) := χ.eventuallyEq_one
  have hp : ContDiff ℝ 2 P :=
    contDiff_two_cutoffLogPotential χ.contDiff χ.hasCompactSupport hχone huc hu hα hα1
  let V (z : ℂ) : F := (-2 : ℝ) •
    (fderiv ℝ P z 1 - Complex.I • fderiv ℝ P z Complex.I)
  have hV : ContDiff ℝ 1 V := by
    have hd := hp.fderiv_right (m := 1) (by norm_num)
    exact contDiff_const.smul ((hd.clm_apply contDiff_const).sub
      (contDiff_const.smul (hd.clm_apply contDiff_const)))
  have hEq : ambientCauchyIntegral f =ᶠ[𝓝 q] V := by
    filter_upwards [Metric.ball_mem_nhds q (show 0 < ε / 8 by positivity)] with z hzq
    have hi (v : ℂ) : Integrable
        (fun w : ℂ => truncatedLogGradient χ (z - w) v • u w) := by
      have hg := (integrable_truncatedLogGradient
        χ.contDiff χ.hasCompactSupport).apply_continuousLinearMap v
      exact (huc.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hg.locallyIntegrable hu0 z).integrable_swap
    rw [ambientCauchyIntegral_eq_integral f he hz]
    calc
      _ = ∫ w : ℂ, ((Real.pi : ℂ)⁻¹ * (z - w)⁻¹) • u w := by
        rw [← integral_smul]
        apply integral_congr_ae
        exact Eventually.of_forall fun w => (mul_smul _ _ _).symm
      _ = ∫ w : ℂ, (-2 : ℝ) •
          (truncatedLogGradient χ (z - w) 1 • u w -
            Complex.I • (truncatedLogGradient χ (z - w) Complex.I • u w)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          by_cases hw : u w = 0
          · simp only [hw, smul_zero, sub_zero]
          have hws : w ∈ closedBall q (ε / 2) := hus (subset_tsupport u hw)
          have hd : z - w ∈ ball (0 : ℂ) ε := by
            have ht := dist_triangle z q w
            have hzw : dist w q ≤ ε / 2 := hws
            have hz' : dist z q < ε / 8 := hzq
            rw [dist_comm q w] at ht
            change dist (z - w) 0 < ε
            rw [dist_zero_right, ← dist_eq_norm]
            linarith
          exact inverse_smul_eq_logGradient
            (χ.eventuallyEq_one_of_mem_ball (by simpa only [χ] using hd)) (u w)
      _ = (-2 : ℝ) • ((∫ w : ℂ, truncatedLogGradient χ (z - w) 1 • u w) -
          Complex.I • ∫ w : ℂ, truncatedLogGradient χ (z - w) Complex.I • u w) := by
        have hiI : Integrable (fun w : ℂ =>
            Complex.I • (truncatedLogGradient χ (z - w) Complex.I • u w)) :=
          (hi Complex.I).smul Complex.I
        rw [integral_smul, integral_sub (hi 1) hiI, integral_smul]
      _ = V z := by
        dsimp only [V, P]
        rw [fderiv_cutoffLogPotential_apply χ.contDiff χ.hasCompactSupport hχone huc hu hα hα1,
          fderiv_cutoffLogPotential_apply χ.contDiff χ.hasCompactSupport hχone huc hu hα hα1]
  exact hV.contDiffAt.congr_of_eventuallyEq hEq

/-- Local Hölder data on the original disk gives real C1 regularity of the
SAME ambient Cauchy integral. The near cutoff's global Hölder regularity,
its potential representation, the far support gap and the integral split
are all derived. No regularity across the original circle is assumed. -/
theorem contDiffAt_ambientCauchyIntegral_of_holderOn
    {a q : ℂ} {R ε : ℝ} (f : C(closedBall a R, F)) (hε : 0 < ε)
    (hinside : closedBall q ε ⊆ ball a R) {α H : ℝ≥0}
    (hf : HolderOnWith H α f {w : closedBall a R | (w : ℂ) ∈ closedBall q ε})
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffAt ℝ 1 (ambientCauchyIntegral f) q := by
  let η : ContDiffBump q := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let u (z : ℂ) : F := η z • rawDensity f z
  let near : C(closedBall a R, F) :=
    ⟨fun w => η (w : ℂ) • f w, (η.continuous.comp continuous_subtype_val).smul f.continuous⟩
  let far : C(closedBall a R, F) :=
    ⟨fun w => (1 - η (w : ℂ)) • f w,
      (continuous_const.sub (η.continuous.comp continuous_subtype_val)).smul f.continuous⟩
  have hlocal : HolderOnWith H α (rawDensity f) (closedBall q ε) := by
    intro x hx y hy
    have hxK : x ∈ closedBall a R := ball_subset_closedBall (hinside hx)
    have hyK : y ∈ closedBall a R := ball_subset_closedBall (hinside hy)
    simpa only [rawDensity, dite_eq_left hxK, dite_eq_left hyK, Subtype.edist_eq] using
      hf ⟨x, hxK⟩ hx ⟨y, hyK⟩ hy
  have hηs : tsupport (η : ℂ → ℝ) ⊆ closedBall q ε := by
    rw [η.tsupport_eq]
    exact closedBall_subset_closedBall (by dsimp only [η]; linarith)
  obtain ⟨B, C, _, hu⟩ := Schauder.exists_holderWith_smul_cutoff_of_holderOnWith
    (isCompact_closedBall q ε) hα hα1 hlocal
    η.contDiff η.hasCompactSupport hηs
  have huc : HasCompactSupport u := η.hasCompactSupport.smul_right
  have hus : tsupport u ⊆ closedBall q (ε / 2) := by
    exact (tsupport_smul_subset_left η (rawDensity f)).trans (by rw [η.tsupport_eq])
  have he : ∀ w : closedBall a R, u w = near w := by
    intro w
    change η (w : ℂ) • rawDensity f w = η (w : ℂ) • f w
    rw [rawDensity_coe]
  have hz : ∀ w ∉ closedBall a R, u w = 0 := by
    intro w hw
    change η w • rawDensity f w = 0
    rw [rawDensity_zero f hw, smul_zero]
  have hnear : ContDiffAt ℝ 1 (ambientCauchyIntegral near) q :=
    contDiffAt_ambientCauchyIntegral_of_localized_extension hε near huc hus he hz hu hα hα1
  have hqK : q ∈ closedBall a R := ball_subset_closedBall
    (hinside (mem_closedBall_self hε.le))
  let qK : closedBall a R := ⟨q, hqK⟩
  have hfarq : qK ∉ tsupport far := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [η.eventuallyEq_one.comp_tendsto
      (continuous_subtype_val.continuousAt : Tendsto
        ((↑) : closedBall a R → ℂ) (𝓝 qK) (𝓝 q))] with w hw
    change (1 - η (w : ℂ)) • f w = 0
    change η (w : ℂ) = 1 at hw
    rw [hw, sub_self, zero_smul]
  have hfarGap : q ∉ ((↑) : closedBall a R → ℂ) '' tsupport far := by
    rintro ⟨w, hw, hwq⟩
    have heq : w = qK := Subtype.ext hwq
    exact hfarq (heq ▸ hw)
  have hfar : ContDiffAt ℝ 1 (ambientCauchyIntegral far) q :=
    (contDiffAt_ambientCauchyIntegral_off_support far hfarGap).of_le (by simp)
  have hsplit : f = near + far := by
    ext w
    change f w = η (w : ℂ) • f w + (1 - η (w : ℂ)) • f w
    rw [← add_smul]
    rw [show η (w : ℂ) + (1 - η (w : ℂ)) = (1 : ℝ) by ring, one_smul]
  have hsplitT : ambientCauchyIntegral f =
      fun z => ambientCauchyIntegral near z + ambientCauchyIntegral far z := by
    funext z
    rw [hsplit, ambientCauchyIntegral_add]
  rw [hsplitT]
  exact hnear.add hfar

end DifferentialGeometry.Analysis
