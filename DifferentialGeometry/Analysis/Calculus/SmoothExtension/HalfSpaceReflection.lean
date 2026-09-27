import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_extension_across_negative_halfSpace_boundary
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} {U : Set (E × ℝ)} {p : E}
    (hU : IsOpen U) (hp : (p, (0 : ℝ)) ∈ U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ (univ ×ˢ Iic (0 : ℝ)))) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      ∃ g : E × ℝ → F, ContDiffOn ℝ ∞ g V ∧
        EqOn g f (V ∩ (univ ×ˢ Iic (0 : ℝ))) := by
  let r : E × ℝ → E × ℝ := fun q => (q.1, -q.2)
  have hr : ContDiff ℝ ∞ r := contDiff_fst.prodMk contDiff_snd.neg
  let U' := r ⁻¹' U
  have hU' : IsOpen U' := hU.preimage hr.continuous
  have hp' : (p, (0 : ℝ)) ∈ U' := by simpa only [U', r, mem_preimage, neg_zero] using hp
  have hf' : ContDiffOn ℝ ∞ (fun q => f (r q)) (U' ∩ (univ ×ˢ Ici (0 : ℝ))) := by
    apply hf.comp hr.contDiffOn
    intro q hq
    exact ⟨hq.1, mem_univ _, (show -q.2 ≤ 0 from neg_nonpos.mpr hq.2.2)⟩
  obtain ⟨V, hV, hpV, hVU, G, hG, hEq⟩ :=
    exists_contDiffOn_extension_across_halfSpace_boundary hU' hp' hf'
  refine ⟨r ⁻¹' V, hV.preimage hr.continuous,
    (by simpa only [r, mem_preimage, neg_zero] using hpV), ?_, fun q => G (r q), ?_, ?_⟩
  · intro q hq
    have hh := hVU hq
    simpa only [U', r, mem_preimage, neg_neg] using hh
  · exact hG.comp hr.contDiffOn (fun q hq => hq)
  · intro q hq
    have hh := hEq ⟨hq.1, mem_univ _, (show 0 ≤ -q.2 from neg_nonneg.mpr hq.2.2)⟩
    simpa only [r, neg_neg] using hh

end DifferentialGeometry.Analysis
