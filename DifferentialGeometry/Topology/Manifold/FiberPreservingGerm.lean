/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.Calculus.Cutoff.SmallGermCutoff
import DifferentialGeometry.Analysis.Calculus.Interpolation.SmallPerturbation
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Compact isotopies preserving the fibers of a planar coordinate. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold NNReal

namespace DifferentialGeometry.Topology.Manifold

theorem exists_compact_isotopy_realizing_fiber_germ
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h0U : (0 : ℂ) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hdf0 : HasFDerivAt f (ContinuousLinearMap.id ℝ ℂ) 0)
    (hfiber : ∀ z ∈ U, (f z).im = z.im) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ => D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ => (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] f ∧ (∀ p, D p 0 = 0) ∧
      (∀ p z, (D p z).im = z.im) ∧
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧
        ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z := by
  let h : ℂ → ℝ := fun z => (f z - z).re
  have hh : ContDiffOn ℝ ∞ h U := Complex.reCLM.contDiff.comp_contDiffOn (hf.sub contDiffOn_id)
  have hh0 : h 0 = 0 := by simp only [h, hf0, sub_self, Complex.zero_re]
  have hd : fderiv ℝ h 0 = 0 := by
    have hder := Complex.reCLM.hasFDerivAt.comp 0 (hdf0.sub (hasFDerivAt_id 0))
    simpa only [h, Function.comp_def, Pi.sub_apply, id_eq, Complex.reCLM_apply, sub_self,
      ContinuousLinearMap.comp_zero] using hder.fderiv
  obtain ⟨g, hg, hgc, hgU, hge, hglip⟩ :=
    DifferentialGeometry.Analysis.exists_small_compact_extension_of_zero_derivative
      hU h0U hh hh0 hd (1 / 2) (by norm_num)
  have hg0 : g 0 = 0 := hge.eq_of_nhds.trans hh0
  let u : ℝ × ℂ → ℂ := fun q => (Real.smoothTransition q.1 * g q.2 : ℝ)
  have hu : ContDiff ℝ ∞ u :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hg.comp contDiff_snd))
  have husmall (p : ℝ) : ∃ c : ℝ≥0, c < 1 ∧ LipschitzWith c (fun z => u (p, z)) := by
    refine ⟨1 / 2, by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist ((Real.smoothTransition p * g x : ℝ) : ℂ)
      ((Real.smoothTransition p * g y : ℝ) : ℂ) ≤ _
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, ← mul_sub, norm_mul,
      Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg p)]
    calc
      Real.smoothTransition p * ‖g x - g y‖ ≤ 1 * ((1 / 2 : ℝ≥0) * ‖x - y‖) :=
        mul_le_mul (Real.smoothTransition.le_one p) (hglip.norm_sub_le x y)
          (norm_nonneg _) (by norm_num)
      _ = _ := by rw [one_mul, dist_eq_norm]
  obtain ⟨D, hD, hDi, hDe⟩ :=
    DifferentialGeometry.Analysis.exists_diffeomorphs_of_small_lipschitz_displacement hu husmall
  have hfix (p : ℝ) (z : ℂ) (hz : z ∉ tsupport g) : D p z = z := by
    rw [hDe]
    change z + (Real.smoothTransition p * g z : ℝ) = z
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, Complex.ofReal_zero, add_zero]
  refine ⟨D, hD, hDi, ?_, ?_, ?_, ?_, tsupport g, hgc.isCompact, hgU, ?_⟩
  · apply Diffeomorph.ext
    intro z
    rw [hDe]
    change z + (Real.smoothTransition 0 * g z : ℝ) = z
    rw [Real.smoothTransition.zero, zero_mul, Complex.ofReal_zero, add_zero]
  · filter_upwards [hge, hU.mem_nhds h0U] with z hz hzU
    rw [hDe]
    change z + (Real.smoothTransition 1 * g z : ℝ) = f z
    rw [Real.smoothTransition.one, one_mul, hz]
    apply Complex.ext
    · change z.re + (f z - z).re = (f z).re
      rw [Complex.sub_re]
      ring
    · change z.im + 0 = (f z).im
      rw [add_zero, hfiber z hzU]
  · intro p
    rw [hDe]
    change (0 : ℂ) + (Real.smoothTransition p * g 0 : ℝ) = 0
    rw [hg0, mul_zero, Complex.ofReal_zero, add_zero]
  · intro p z
    rw [hDe]
    exact add_zero z.im
  · intro p z hz
    refine ⟨hfix p z hz, ?_⟩
    apply (D p).injective
    exact ((D p).apply_symm_apply z).trans (hfix p z hz).symm


theorem exists_compact_isotopy_straightening_fiber_germ
    {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (A : ℂ ≃L[ℝ] ℂ)
    (hA : HasFDerivAt f (A : ℂ →L[ℝ] ℂ) z₀)
    (hfiber : ∀ z ∈ U, (f z).im = z.im + (f z₀).im - z₀.im)
    {V : Set ℂ} (hV : IsOpen V) (hV₀ : f z₀ ∈ V) :
    (∀ z, (A z).im = z.im) ∧
      ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        ContDiff ℝ ∞ (fun q : ℝ × ℂ => D q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × ℂ => (D q.1).symm q.2) ∧
        D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
        (∀ᶠ z in 𝓝 z₀, D 1 (A (z - z₀) + f z₀) = f z) ∧
        (∀ p, D p (f z₀) = f z₀) ∧ (∀ p z, (D p z).im = z.im) ∧
        ∃ K : Set ℂ, IsCompact K ∧ K ⊆ V ∧
          ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z := by
  have hAi (z : ℂ) : (A z).im = z.im := by
    have h₁ := Complex.imCLM.hasFDerivAt.comp z₀ hA
    have h₂ : HasFDerivAt (fun z : ℂ => z.im + (f z₀).im - z₀.im)
        Complex.imCLM z₀ :=
      (Complex.imCLM.hasFDerivAt.add_const (f z₀).im).sub_const z₀.im
    have he : (fun z => (f z).im) =ᶠ[𝓝 z₀]
        (fun z => z.im + (f z₀).im - z₀.im) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz₀) hfiber
    have hmap : Complex.imCLM.comp (A : ℂ →L[ℝ] ℂ) = Complex.imCLM :=
      h₁.unique (h₂.congr_of_eventuallyEq he)
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L z) hmap
  let W := (fun z => A.symm z + z₀) ⁻¹' U ∩ (fun z => z + f z₀) ⁻¹' V
  have hW : IsOpen W :=
    (hU.preimage (A.symm.continuous.add continuous_const)).inter
      (hV.preimage (continuous_id.add continuous_const))
  have h0W : (0 : ℂ) ∈ W := by
    simp only [W, mem_inter_iff, mem_preimage, map_zero, zero_add]
    exact ⟨hz₀, hV₀⟩
  let g : ℂ → ℂ := fun z => f (A.symm z + z₀) - f z₀
  have hg : ContDiffOn ℝ ∞ g W :=
    (hf.comp (A.symm.contDiff.add contDiff_const).contDiffOn (fun _ hz => hz.1)).sub
      contDiffOn_const
  have hg0 : g 0 = 0 := by simp only [g, map_zero, zero_add, sub_self]
  have hgd : HasFDerivAt g (ContinuousLinearMap.id ℝ ℂ) 0 := by
    have hA' : HasFDerivAt f (A : ℂ →L[ℝ] ℂ) (A.symm 0 + z₀) := by
      simpa only [map_zero, zero_add] using hA
    have hd := (hA'.comp 0 (A.symm.hasFDerivAt.add_const z₀)).sub_const (f z₀)
    simpa only [ContinuousLinearEquiv.coe_comp_coe_symm, Function.comp_def] using hd
  have hgfiber (z : ℂ) (hz : z ∈ W) : (g z).im = z.im := by
    have hi : (A.symm z).im = z.im := by
      simpa only [A.apply_symm_apply] using (hAi (A.symm z)).symm
    change (f (A.symm z + z₀) - f z₀).im = z.im
    rw [Complex.sub_im, hfiber _ hz.1, Complex.add_im, hi]
    ring
  obtain ⟨J, hJ, hJi, hJ0, hJe, hJfix0, hJfiber, K, hK, hKW, hJfix⟩ :=
    exists_compact_isotopy_realizing_fiber_germ hW h0W hg hg0 hgd hgfiber
  let T := DifferentialGeometry.Topology.translateDiffeomorph (f z₀)
  let D (p : ℝ) := (T.symm.trans (J p)).trans T
  have hDe (p : ℝ) (z : ℂ) : D p z = J p (z - f z₀) + f z₀ := by
    change J p (z + -(f z₀)) + f z₀ = _
    rw [← sub_eq_add_neg]
  have hDie (p : ℝ) (z : ℂ) : (D p).symm z = (J p).symm (z - f z₀) + f z₀ := by
    change (J p).symm (z + -(f z₀)) + f z₀ = _
    rw [← sub_eq_add_neg]
  have hfix (p : ℝ) (z : ℂ) (hz : z ∉ (fun z => z + f z₀) '' K) : D p z = z := by
    have hzK : z - f z₀ ∉ K := fun hk => hz ⟨z - f z₀, hk, sub_add_cancel _ _⟩
    rw [hDe, (hJfix p _ hzK).1, sub_add_cancel]
  refine ⟨hAi, D, ?_, ?_, ?_, ?_, ?_, ?_, (fun z => z + f z₀) '' K,
    hK.image (continuous_id.add continuous_const), ?_, ?_⟩
  · simp_rw [hDe]
    exact (hJ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).add contDiff_const
  · simp_rw [hDie]
    exact (hJi.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).add contDiff_const
  · apply Diffeomorph.ext
    intro z
    rw [hDe, hJ0]
    exact sub_add_cancel z (f z₀)
  · have ht : Tendsto (fun z => A (z - z₀)) (𝓝 z₀) (𝓝 0) := by
      simpa only [Function.comp_def, Pi.sub_apply, id_eq, sub_self, map_zero] using
        (A.continuous.comp (continuous_id.sub (continuous_const (y := z₀)))).tendsto z₀
    filter_upwards [hJe.comp_tendsto ht] with z hz
    change J 1 (A (z - z₀)) = g (A (z - z₀)) at hz
    rw [hDe, add_sub_cancel_right, hz]
    simp only [g, A.symm_apply_apply, sub_add_cancel]
  · intro p
    rw [hDe, sub_self, hJfix0, zero_add]
  · intro p z
    rw [hDe, Complex.add_im, hJfiber, Complex.sub_im, sub_add_cancel]
  · rintro z ⟨y, hy, rfl⟩
    exact (hKW hy).2
  · intro p z hz
    refine ⟨hfix p z hz, ?_⟩
    apply (D p).injective
    exact ((D p).apply_symm_apply z).trans (hfix p z hz).symm

end DifferentialGeometry.Topology.Manifold
