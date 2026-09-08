import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

open scoped ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv_add_prod_mul_ne_zero {q η : E → ℝ} {φ ψ : G → ℝ} {x : E} {y : G}
    (hq : DifferentiableAt ℝ q x) (hη : DifferentiableAt ℝ η x)
    (hφ : DifferentiableAt ℝ φ y) (hψ : DifferentiableAt ℝ ψ y)
    (hsmall : |ψ y| * ‖fderiv ℝ η x‖ < ‖fderiv ℝ q x‖) :
    fderiv ℝ (fun p : E × G => q p.1 + φ p.2 + η p.1 * ψ p.2) (x, y) ≠ 0 := by
  have hF : DifferentiableAt ℝ
      (fun p : E × G => q p.1 + φ p.2 + η p.1 * ψ p.2) (x, y) :=
    ((hq.comp (x, y) differentiableAt_fst).add
      (hφ.comp (x, y) differentiableAt_snd)).add
        ((hη.comp (x, y) differentiableAt_fst).mul
          (hψ.comp (x, y) differentiableAt_snd))
  intro hz
  have hrestricted := hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
  have hexplicit := (hq.hasFDerivAt.add_const (φ y)).add (hη.hasFDerivAt.mul_const (ψ y))
  have heq : fderiv ℝ q x + ψ y • fderiv ℝ η x = 0 := by
    simpa only [hz, ContinuousLinearMap.zero_comp] using hexplicit.unique hrestricted
  have hnorm := congrArg norm (eq_neg_of_add_eq_zero_left heq)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs] at hnorm
  exact (ne_of_lt hsmall) hnorm.symm

private theorem abs_translated_smoothAbs_sub_le {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    |a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u| ≤ 2 * a := by
  have hs := Real.smoothAbs.sub_abs_mem_Icc (by linarith : 0 < a / 2) (u - a / 2)
  have hnorm : |u - a / 2| ≤ u + a / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply abs_le.mpr
  constructor <;> linarith [hs.1, hs.2, le_abs_self (u - a / 2)]

theorem exists_pos_forall_fderiv_add_smoothAbs_ne_zero {q η : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hq : ∀ x ∈ K, ContDiffAt ℝ 1 q x)
    (hη : ∀ x ∈ K, ContDiffAt ℝ 1 η x)
    (hregular : ∀ x ∈ K, fderiv ℝ q x ≠ 0) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ p ∈ K ×ˢ Set.Ici 0,
      fderiv ℝ (fun z : E × ℝ => q z.1 + z.2 + η z.1 *
        (a / 2 + Real.smoothAbs (a / 2) (z.2 - a / 2) - z.2)) p ≠ 0 := by
  have hcq : ContinuousOn (fun x => ‖fderiv ℝ q x‖) K :=
    fun x hx => ((hq x hx).continuousAt_fderiv one_ne_zero).norm.continuousWithinAt
  have hcη : ContinuousOn (fderiv ℝ η) K :=
    fun x hx => ((hη x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt
  obtain ⟨μ, hμ, hμq⟩ := hK.exists_forall_le' hcq (fun x hx => norm_pos_iff.mpr (hregular x hx))
  obtain ⟨B, hB, hBη⟩ := (hK.image_of_continuousOn hcη).isBounded.exists_pos_norm_le
  refine ⟨μ / (4 * B), by positivity, ?_⟩
  intro a ha p hp
  have hηB : ‖fderiv ℝ η p.1‖ ≤ B := hBη _ (Set.mem_image_of_mem _ hp.1)
  have ham : 2 * a * B ≤ μ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp ha.2
    nlinarith
  have hsmall : |a / 2 + Real.smoothAbs (a / 2) (p.2 - a / 2) - p.2| *
      ‖fderiv ℝ η p.1‖ < ‖fderiv ℝ q p.1‖ := by
    calc
      _ ≤ (2 * a) * ‖fderiv ℝ η p.1‖ :=
        mul_le_mul_of_nonneg_right (abs_translated_smoothAbs_sub_le ha.1 hp.2) (norm_nonneg _)
      _ ≤ (2 * a) * B :=
        mul_le_mul_of_nonneg_left hηB (mul_nonneg (by norm_num) ha.1.le)
      _ ≤ μ / 2 := ham
      _ < μ := by linarith
      _ ≤ ‖fderiv ℝ q p.1‖ := hμq _ hp.1
  have hψ : DifferentiableAt ℝ
      (fun u => a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u) p.2 :=
    ((differentiableAt_const (a / 2)).add
      (((Real.smoothAbs.contDiff (a / 2)).differentiable (by simp) _).comp p.2
        (differentiableAt_id.sub_const (a / 2)))).sub differentiableAt_id
  exact fderiv_add_prod_mul_ne_zero ((hq _ hp.1).differentiableAt one_ne_zero)
    ((hη _ hp.1).differentiableAt one_ne_zero) differentiableAt_id hψ hsmall

