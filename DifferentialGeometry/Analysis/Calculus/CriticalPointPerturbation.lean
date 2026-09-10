import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
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

theorem exists_pos_forall_fderiv_add_const_smul_ne_zero {q η : E → F} {K : Set E}
    (hK : IsCompact K) (hq : ∀ x ∈ K, ContDiffAt ℝ 1 q x)
    (hη : ∀ x ∈ K, ContDiffAt ℝ 1 η x)
    (hregular : ∀ x ∈ K, fderiv ℝ q x ≠ 0) :
    ∃ ε > 0, ∀ x ∈ K, ∀ s : ℝ, |s| ≤ ε →
      fderiv ℝ (fun z => q z + s • η z) x ≠ 0 := by
  have hcq : ContinuousOn (fun x => ‖fderiv ℝ q x‖) K :=
    fun x hx => ((hq x hx).continuousAt_fderiv one_ne_zero).norm.continuousWithinAt
  have hcη : ContinuousOn (fderiv ℝ η) K :=
    fun x hx => ((hη x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt
  obtain ⟨μ, hμ, hμq⟩ := hK.exists_forall_le' hcq (fun x hx => norm_pos_iff.mpr (hregular x hx))
  obtain ⟨B, hB, hBη⟩ := (hK.image_of_continuousOn hcη).isBounded.exists_pos_norm_le
  refine ⟨μ / (2 * B), by positivity, ?_⟩
  intro x hx s hs hz
  have hηB : ‖fderiv ℝ η x‖ ≤ B := hBη _ (Set.mem_image_of_mem _ hx)
  have hsmall : |s| * ‖fderiv ℝ η x‖ < ‖fderiv ℝ q x‖ := by
    calc
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left hηB (abs_nonneg _)
      _ ≤ μ / 2 := by
        have h := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hs
        nlinarith
      _ < μ := by linarith
      _ ≤ ‖fderiv ℝ q x‖ := hμq x hx
  have hderiv := ((hq x hx).differentiableAt one_ne_zero).hasFDerivAt.add
    (((hη x hx).differentiableAt one_ne_zero).hasFDerivAt.const_smul s)
  have heq : fderiv ℝ q x + s • fderiv ℝ η x = 0 := by
    rw [← hderiv.fderiv]
    exact hz
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
  obtain ⟨ε, hε, hεreg⟩ := exists_pos_forall_fderiv_add_const_smul_ne_zero hK hq hη hregular
  refine ⟨ε / 2, by positivity, ?_⟩
  intro a ha p hp
  let ψ := fun u => a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u
  have hsmall : |ψ p.2| ≤ ε :=
    (abs_translated_smoothAbs_sub_le ha.1 hp.2).trans (by linarith [ha.2])
  have hscalar := hεreg p.1 hp.1 (ψ p.2) hsmall
  have hψ : DifferentiableAt ℝ ψ p.2 :=
    ((differentiableAt_const (a / 2)).add
      (((Real.smoothAbs.contDiff (a / 2)).differentiable (by simp) _).comp p.2
        (differentiableAt_id.sub_const (a / 2)))).sub differentiableAt_id
  have hq' := (hq p.1 hp.1).differentiableAt one_ne_zero
  have hη' := (hη p.1 hp.1).differentiableAt one_ne_zero
  have hF : DifferentiableAt ℝ
      (fun z : E × ℝ => q z.1 + z.2 + η z.1 * ψ z.2) p :=
    ((hq'.comp p differentiableAt_fst).add differentiableAt_snd).add
      ((hη'.comp p differentiableAt_fst).mul (hψ.comp p differentiableAt_snd))
  intro hz
  have hrestricted := hF.hasFDerivAt.comp p.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  rw [hz, ContinuousLinearMap.zero_comp] at hrestricted
  change HasFDerivAt (fun z => q z + p.2 + η z * ψ p.2) 0 p.1 at hrestricted
  have heq : (fun z => q z + p.2 + η z * ψ p.2) =
      (fun z => (q z + ψ p.2 • η z) + p.2) := by
    funext z
    simp only [smul_eq_mul]
    ring
  rw [heq] at hrestricted
  exact hscalar (((hq'.add (hη'.const_smul (ψ p.2))).hasFDerivAt.add_const p.2).unique
    hrestricted)
