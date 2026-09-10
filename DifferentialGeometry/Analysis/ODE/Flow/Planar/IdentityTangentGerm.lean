import DifferentialGeometry.Analysis.Calculus.Cutoff.SmallGermCutoff
import DifferentialGeometry.Analysis.Calculus.Interpolation.SmallPerturbation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold NNReal

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_compact_isotopy_realizing_identity_tangent_germ
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hdf0 : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (D 1 : E → E) =ᶠ[𝓝 0] f ∧ (∀ p, D p 0 = 0) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧
        ∀ p x, x ∉ K → D p x = x ∧ (D p).symm x = x := by
  let h : E → E := fun x ↦ f x - x
  have hh : ContDiffOn ℝ ∞ h U := hf.sub contDiffOn_id
  have hh0 : h 0 = 0 := by simp only [h, hf0, sub_self]
  have hd : fderiv ℝ h 0 = 0 := by
    have hhderiv : HasFDerivAt h
        (ContinuousLinearMap.id ℝ E - ContinuousLinearMap.id ℝ E) 0 :=
      hdf0.sub (hasFDerivAt_id 0)
    rw [hhderiv.fderiv, sub_self]
  obtain ⟨g, hg, hgcompact, hgU, hgerm, hglip⟩ :=
    exists_small_compact_extension_of_zero_derivative hU h0U hh hh0 hd (1 / 2) (by norm_num)
  have hg0 : g 0 = 0 := hgerm.eq_of_nhds.trans hh0
  let u : ℝ × E → E := fun q ↦ Real.smoothTransition q.1 • g q.2
  have hu : ContDiff ℝ ∞ u :=
    (Real.smoothTransition.contDiff.comp contDiff_fst).smul (hg.comp contDiff_snd)
  have husmall (p : ℝ) : ∃ c : ℝ≥0, c < 1 ∧ LipschitzWith c (fun x ↦ u (p, x)) := by
    refine ⟨1 / 2, by norm_num, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
    change dist (Real.smoothTransition p • g x) (Real.smoothTransition p • g y) ≤ _
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg p)]
    calc
      Real.smoothTransition p * ‖g x - g y‖ ≤ 1 * ((1 / 2 : ℝ≥0) * ‖x - y‖) :=
        mul_le_mul (Real.smoothTransition.le_one p) (hglip.norm_sub_le x y)
          (norm_nonneg _) (by norm_num)
      _ = _ := by rw [one_mul, dist_eq_norm]
  obtain ⟨D, hD, hDi, hDe⟩ := exists_diffeomorphs_of_small_lipschitz_displacement hu husmall
  have hfix (p : ℝ) (x : E) (hx : x ∉ tsupport g) : D p x = x := by
    rw [hDe]
    change x + Real.smoothTransition p • g x = x
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, add_zero]
  refine ⟨D, hD, hDi, ?_, ?_, ?_, tsupport g, hgcompact.isCompact, hgU, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [hDe]
    change x + Real.smoothTransition 0 • g x = x
    rw [Real.smoothTransition.zero, zero_smul, add_zero]
  · filter_upwards [hgerm] with x hx
    rw [hDe]
    change x + Real.smoothTransition 1 • g x = f x
    rw [Real.smoothTransition.one, one_smul, hx]
    change x + (f x - x) = f x
    abel
  · intro p
    rw [hDe]
    change (0 : E) + Real.smoothTransition p • g 0 = 0
    rw [hg0, smul_zero, add_zero]
  · intro p x hx
    refine ⟨hfix p x hx, ?_⟩
    apply (D p).injective
    exact ((D p).apply_symm_apply x).trans (hfix p x hx).symm

end Poincare.Analysis
