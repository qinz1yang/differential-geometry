import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Transitivity
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open scoped ComplexConjugate ContDiff NNReal

namespace Complex

private theorem parabolic_negative_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    let t : ℝ := -ζ.im / (2 * (1 - ζ.re))
    ((1 + I * (t : ℂ)) * (-1) - I * (t : ℂ)) /
      (I * (t : ℂ) * (-1) + 1 - I * (t : ℂ)) = ζ := by
  let t : ℝ := -ζ.im / (2 * (1 - ζ.re))
  have hsq : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have hs := normSq_eq_norm_sq ζ
    rw [hζ] at hs
    simpa only [normSq_apply, pow_two, one_mul] using hs
  have hr : 1 - ζ.re ≠ 0 := by
    intro heq
    have hre : ζ.re = 1 := by linarith
    have him : ζ.im = 0 := by rw [hre] at hsq; nlinarith [sq_nonneg ζ.im]
    apply hζ1
    apply Complex.ext <;> simp [hre, him]
  have hd : I * (t : ℂ) * (-1) + 1 - I * (t : ℂ) ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [mul_re, mul_im] at hre
  apply (div_eq_iff hd).mpr
  apply Complex.ext
  · simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im,
      neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero,
      zero_add, add_zero, one_mul, mul_one, sub_zero, neg_zero]
    dsimp only [t]
    field_simp [hr]
    nlinarith [hsq]
  · simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im,
      neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero,
      zero_add, add_zero, one_mul, mul_one, sub_zero, neg_zero]
    dsimp only [t]
    field_simp [hr]
    ring

/-- A smooth bi-Lipschitz circle reparametrization with prescribed images of `1` and `-1`.
The total functions are rational ambient extensions; their smoothness is asserted at circle
points, where their denominators do not vanish. -/
theorem exists_circle_straightening {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    let t : ℝ := -ζ.im / (2 * (1 - ζ.re))
    ∃ (h hInv : ℂ → ℂ) (K : ℝ≥0),
      (∀ z : ℂ, h z = ((1 + Complex.I * (t : ℂ)) * z - Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) * z + 1 - Complex.I * (t : ℂ))) ∧
      h 1 = 1 ∧ h (-1) = ζ ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1 ∧ ‖hInv z‖ = 1 ∧
        hInv (h z) = z ∧ h (hInv z) = z ∧
        ContDiffAt ℝ ∞ h z ∧ ContDiffAt ℝ ∞ hInv z ∧
        (∃ d : ℂ, d ≠ 0 ∧ HasDerivAt h d z) ∧
        (∃ d : ℂ, d ≠ 0 ∧ HasDerivAt hInv d z)) ∧
      LipschitzOnWith K h (Metric.sphere (0 : ℂ) 1) ∧
      LipschitzOnWith K hInv (Metric.sphere (0 : ℂ) 1) := by
  let t : ℝ := -ζ.im / (2 * (1 - ζ.re))
  let α : ℂ := 2 - I * ((2 * t : ℝ) : ℂ)
  let β : ℂ := I * ((2 * t : ℝ) : ℂ)
  let a : ℂ := -conj β / conj α
  let η : ℂ := conj α / α
  have hparams : ‖a‖ < 1 ∧ ‖η‖ = 1 ∧
      (∀ z : ℂ, η * diskMoebius a z = (conj α * z + conj β) / (α + β * z)) ∧
      η * diskMoebius a 1 = 1 := by
    simpa only [a, η, α, β, one_add_one_eq_two, sub_self, ofReal_ofNat, ofReal_zero,
      zero_add, one_mul, mul_one, neg_one_mul] using
      diskMoebius_cayley_affine_parameters (1 : ℂ) 1 1 (2 * t)
        (by simp) (by simp) (by norm_num)
  obtain ⟨ha, hη, hformula, h1⟩ := hparams
  let h : ℂ → ℂ := fun z => η * diskMoebius a z
  let hInv : ℂ → ℂ := fun z => diskMoebius (-a) (conj η * z)
  let K : ℝ≥0 := ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩
  have hη0 : η ≠ 0 := norm_ne_zero_iff.mp (by rw [hη]; exact one_ne_zero)
  have hηc0 : conj η ≠ 0 := by simpa using hη0
  have haNeg : ‖-a‖ < 1 := by simpa using ha
  have hn : (1 - (normSq a : ℂ)) ≠ 0 := by
    have hp : 0 < 1 - normSq a := by
      rw [normSq_eq_norm_sq]
      nlinarith [norm_nonneg a]
    exact_mod_cast hp.ne'
  have hnNeg : (1 - (normSq (-a) : ℂ)) ≠ 0 := by simpa using hn
  have hrational (z : ℂ) :
      h z = ((1 + I * (t : ℂ)) * z - I * (t : ℂ)) /
        (I * (t : ℂ) * z + 1 - I * (t : ℂ)) := by
    rw [show h z = (conj α * z + conj β) / (α + β * z) from hformula z]
    have hnum : conj α * z + conj β =
        (2 : ℂ) * ((1 + I * (t : ℂ)) * z - I * (t : ℂ)) := by
      dsimp only [α, β]
      simp only [map_sub, map_mul, conj_ofReal, conj_I, map_ofNat, ofReal_mul,
        ofReal_ofNat]
      ring
    have hden : α + β * z =
        (2 : ℂ) * (I * (t : ℂ) * z + 1 - I * (t : ℂ)) := by
      dsimp only [α, β]
      push_cast
      ring
    rw [hnum, hden, mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  refine ⟨h, hInv, K, hrational, h1, ?_, ?_, ?_, ?_⟩
  · rw [hrational]
    exact parabolic_negative_one hζ hζ1
  · intro z hz
    let zc : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    let e := diskAutomorphismCircle a η ha hη
    have hnorm : ‖h z‖ = 1 := by
      change ‖(e zc : ℂ)‖ = 1
      exact Circle.norm_coe (e zc)
    have hinvnorm : ‖hInv z‖ = 1 := by
      change ‖(e.symm zc : ℂ)‖ = 1
      exact Circle.norm_coe (e.symm zc)
    have hleft : hInv (h z) = z := by
      exact congrArg (fun v : Circle => (v : ℂ)) (e.symm_apply_apply zc)
    have hright : h (hInv z) = z := by
      exact congrArg (fun v : Circle => (v : ℂ)) (e.apply_symm_apply zc)
    have hdz := diskMoebius_denominator_ne_zero ha hz.le
    have hnormc : ‖conj η * z‖ = 1 := by rw [norm_mul, norm_conj, hη, hz, one_mul]
    have hdi := diskMoebius_denominator_ne_zero haNeg hnormc.le
    have hsmooth : ContDiffAt ℂ ∞ h z := by
      exact contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).div
        (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) hdz)
    have hismooth : ContDiffAt ℂ ∞ hInv z := by
      exact ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const).div
        (contDiffAt_const.sub
          (contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id))) hdi
    refine ⟨hnorm, hinvnorm, hleft, hright, hsmooth.restrict_scalars ℝ,
      hismooth.restrict_scalars ℝ, ?_, ?_⟩
    · refine ⟨η * ((1 - normSq a) / (1 - conj a * z) ^ 2),
        mul_ne_zero hη0 (div_ne_zero hn (pow_ne_zero 2 hdz)), ?_⟩
      exact hasDerivAt_const_mul_diskMoebius η hdz
    · refine ⟨((1 - normSq (-a)) / (1 - conj (-a) * (conj η * z)) ^ 2) * conj η,
        mul_ne_zero (div_ne_zero hnNeg (pow_ne_zero 2 hdi)) hηc0, ?_⟩
      simpa only [Function.comp_def, hInv, mul_one] using!
        (hasDerivAt_diskMoebius hdi).comp z ((hasDerivAt_id z).const_mul (conj η))
  · apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hz' := mem_sphere_zero_iff_norm.mp hz
    have hw' := mem_sphere_zero_iff_norm.mp hw
    change dist (η * diskMoebius a z) (η * diskMoebius a w) ≤
      (1 + ‖a‖) / (1 - ‖a‖) * dist z w
    rw [dist_eq_norm, ← mul_sub, norm_mul, hη, one_mul, ← dist_eq_norm]
    exact dist_diskMoebius_le ha hz'.le hw'.le
  · apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hz' := mem_sphere_zero_iff_norm.mp hz
    have hw' := mem_sphere_zero_iff_norm.mp hw
    have hnormc (v : ℂ) (hv : ‖v‖ = 1) : ‖conj η * v‖ ≤ 1 := by
      rw [norm_mul, norm_conj, hη, hv, one_mul]
    have hi := dist_diskMoebius_le haNeg (hnormc z hz') (hnormc w hw')
    change dist (diskMoebius (-a) (conj η * z)) (diskMoebius (-a) (conj η * w)) ≤
      (1 + ‖a‖) / (1 - ‖a‖) * dist z w
    simpa only [norm_neg, dist_eq_norm, ← mul_sub, norm_mul, norm_conj, hη,
      one_mul] using hi

end Complex

end
