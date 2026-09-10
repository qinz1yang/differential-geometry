import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace Poincare.Morse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem fderiv_fderiv_comp_at_critical {f : F → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (c x)) (hc : ContDiffAt ℝ 2 c x)
    (hcrit : fderiv ℝ f (c x) = 0) :
    fderiv ℝ (fderiv ℝ (f ∘ c)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ c x)).comp
        ((fderiv ℝ (fderiv ℝ f) (c x)).comp (fderiv ℝ c x)) := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdc := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd := (hdf.hasFDerivAt.comp x (hc.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hdc.hasFDerivAt
  have heq : fderiv ℝ (f ∘ c) =ᶠ[𝓝 x] fun y => (fderiv ℝ f (c y)).comp (fderiv ℝ c y) := by
    filter_upwards [hc.eventually (by norm_num), hc.continuousAt.preimage_mem_nhds
      (hf.eventually (by norm_num))] with y hcy hfy
    have hfy' : ContDiffAt ℝ 2 f (c y) := hfy
    exact fderiv_comp y (hfy'.differentiableAt (by norm_num)) (hcy.differentiableAt (by norm_num))
  rw [heq.fderiv_eq]
  simpa only [comp_apply,hcrit,map_zero,ContinuousLinearMap.zero_comp,zero_add] using hd.fderiv


theorem bijective_dual_precomp (e : E ≃L[ℝ] F) :
    Bijective ((ContinuousLinearMap.compL ℝ E F ℝ).flip e.toContinuousLinearMap) := by
  constructor
  · intro L T h
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    exact congrArg (fun K : E →L[ℝ] ℝ => K v) h
  · intro L
    refine ⟨L.comp e.symm.toContinuousLinearMap,?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg L (e.symm_apply_apply v)


theorem bijective_fderiv_fderiv_comp_at_critical_iff {f : F → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (c x)) (hc : ContDiffAt ℝ 2 c x)
    (hcrit : fderiv ℝ f (c x) = 0) (hcinv : (fderiv ℝ c x).IsInvertible) :
    Bijective (fderiv ℝ (fderiv ℝ (f ∘ c)) x) ↔
      Bijective (fderiv ℝ (fderiv ℝ f) (c x)) := by
  obtain ⟨e,he⟩ := hcinv
  have hce : e.toContinuousLinearMap = fderiv ℝ c x := he
  rw [fderiv_fderiv_comp_at_critical hf hc hcrit,← hce]
  change Bijective (((ContinuousLinearMap.compL ℝ E F ℝ).flip e.toContinuousLinearMap) ∘
    ((fderiv ℝ (fderiv ℝ f) (c x)) ∘ e)) ↔ _
  rw [(bijective_dual_precomp e).of_comp_iff',Bijective.of_comp_iff _ e.bijective]

end Poincare.Morse
