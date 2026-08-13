import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import DifferentialGeometry.Tensor.Alternating.Wedge

noncomputable section

open ContinuousAlternatingMap

namespace DifferentialGeometry
namespace DifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m k l : ℕ}

theorem contDiffOn_extDeriv {s : Set E} (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (hω : ContDiffOn ℝ ⊤ ω s) (hs : IsOpen s) :
    ContDiffOn ℝ ⊤ (fun x => extDeriv ω x) s := by
  have hf : ContDiffOn ℝ ⊤ (fderiv ℝ ω) s := hω.fderiv_of_isOpen hs le_top
  have hc : ContDiff ℝ ⊤ (fun L : E →L[ℝ] E [⋀^Fin n]→L[ℝ] F =>
      alternatizeUncurryFinCLM ℝ E F L) :=
    (alternatizeUncurryFinCLM ℝ E F).contDiff
  exact hc.comp_contDiffOn hf

theorem contDiffOn_wedge_product {s : Set E} (a : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (b : E → E [⋀^Fin l]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ⊤ a s) (hb : ContDiffOn ℝ ⊤ b s) :
    ContDiffOn ℝ ⊤ (fun x => a x ∧[ℝ] b x) s := by
  let B : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
    wedge_productL (ContinuousLinearMap.mul ℝ ℝ)
  have h₁ : ContDiffOn ℝ ⊤ (fun x => B (a x)) s := by
    exact (contDiffOn_const (c := B)).clm_apply ha
  exact h₁.clm_apply hb

theorem contDiffOn_pullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {s : Set E} {t : Set E'} (f : E → E')
    (ω : E' → E' [⋀^Fin n]→L[ℝ] F) (hf : ContDiffOn ℝ ⊤ f s) (hω : ContDiffOn ℝ ⊤ ω t)
    (hst : Set.MapsTo f s t) (hs : IsOpen s) :
    ContDiffOn ℝ ⊤ (fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) s := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs le_top
  have h₁ : ContDiffOn ℝ ⊤ (fun x =>
      (compContinuousLinearMapCLM (fderiv ℝ f x) : (E' [⋀^Fin n]→L[ℝ] F) →L[ℝ]
        (E [⋀^Fin n]→L[ℝ] F))) s :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
      (F₁ := E) (F₁' := E') (F₂ := F) (ι := Fin n)).comp_contDiffOn hfd
  have h₂ : ContDiffOn ℝ ⊤ (fun x => ω (f x)) s := hω.comp hf hst
  change ContDiffOn ℝ ⊤ (fun x => (compContinuousLinearMapCLM (fderiv ℝ f x)) (ω (f x))) s
  exact h₁.clm_apply h₂

theorem wedge_product_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (g : E [⋀^Fin k]→L[ℝ] ℝ) (h : E [⋀^Fin l]→L[ℝ] ℝ)
    (A : E' →L[ℝ] E) :
    (g ∧[ℝ] h).compContinuousLinearMap A =
      (g.compContinuousLinearMap A) ∧[ℝ] (h.compContinuousLinearMap A) := by
  ext v
  simp only [compContinuousLinearMap_apply, wedge_product_def]
  change uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
    (ContinuousLinearMap.mul ℝ ℝ) g h) (A ∘ v) =
      uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
        (ContinuousLinearMap.mul ℝ ℝ) (g.compContinuousLinearMap A)
        (h.compContinuousLinearMap A)) v
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  refine Quotient.inductionOn' σ ?_
  intro σ'
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    compContinuousLinearMap_apply, Function.comp_apply]
  rfl

theorem domDomCongr_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (σ : Fin m ≃ Fin n) (L : E [⋀^Fin m]→L[ℝ] F) (A : E' →L[ℝ] E) :
    (domDomCongr σ L).compContinuousLinearMap A =
      domDomCongr σ (L.compContinuousLinearMap A) := by
  ext v
  rfl

theorem constOfIsEmpty_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (y : F) (A : E' →L[ℝ] E) :
    (constOfIsEmpty ℝ E (Fin 0) y).compContinuousLinearMap A =
      constOfIsEmpty ℝ E' (Fin 0) y := by
  ext v
  rfl

private theorem ofSubsingleton_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (g : E →L[ℝ] F) (A : E' →L[ℝ] E) :
    (ofSubsingleton ℝ E F (0 : Fin 1) g).compContinuousLinearMap A =
      ofSubsingleton ℝ E' F (0 : Fin 1) (g.comp A) := by
  ext v
  rfl

end DifferentialForm
end DifferentialGeometry

end
