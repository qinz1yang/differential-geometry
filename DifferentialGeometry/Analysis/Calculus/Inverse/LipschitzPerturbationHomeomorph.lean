import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Abel

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis

theorem approximatesLinearOn_id_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : E → E} (hη : Differentiable ℝ η) {c : ℝ≥0} (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) :
    ApproximatesLinearOn (fun x => x + η x)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) univ c := by
  intro x _ y _
  have key : ‖η x - η y‖ ≤ (c : ℝ) * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hη z) (fun z _ => hbound z)
      convex_univ (mem_univ y) (mem_univ x)
  have e : x + η x - (y + η y) -
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (x - y) = η x - η y := by
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
    abel
  have key' : ‖x + η x - (y + η y) -
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (x - y)‖ ≤
        (c : ℝ) * ‖x - y‖ := by
    rw [e]
    exact key
  exact key'

private theorem subsingleton_or_lt_inv_nnnorm_refl_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℝ≥0} (hc : c < 1) :
    Subsingleton E ∨
      c < ‖(((ContinuousLinearEquiv.refl ℝ E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial E with _i | _i
  · exact Or.inl inferInstance
  · refine Or.inr ?_
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one]
    exact hc

def lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ} (hc : c < 1)
    (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) : E ≃ₜ E :=
  ApproximatesLinearOn.toHomeomorph (fun x => x + η x)
    (approximatesLinearOn_id_add hη (c := c.toNNReal)
      (fun x => (hbound x).trans (Real.le_coe_toNNReal c)))
    (subsingleton_or_lt_inv_nnnorm_refl_symm (Real.toNNReal_lt_one.mpr hc))

theorem coe_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) :
    ⇑(lipschitzPerturbationHomeomorph η hη hc hbound) = fun x => x + η x :=
  rfl

theorem lipschitzPerturbationHomeomorph_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) (x : E) :
    lipschitzPerturbationHomeomorph η hη hc hbound x = x + η x :=
  rfl

theorem contDiff_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) {n : ℕ∞ω} (hηn : ContDiff ℝ n η) :
    ContDiff ℝ n ⇑(lipschitzPerturbationHomeomorph η hη hc hbound) := by
  rw [coe_lipschitzPerturbationHomeomorph]
  exact contDiff_fun_id.add hηn

def idAddEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : ‖T‖ < 1) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.unitsEquiv ℝ E (Units.oneSub (-T) ((norm_neg T).trans_lt hT))

theorem coe_idAddEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : ‖T‖ < 1) :
    ((idAddEquiv T hT : E ≃L[ℝ] E) : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + T := by
  ext v
  change v - -T v = v + T v
  exact sub_neg_eq_add v (T v)

theorem hasFDerivAt_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) (x : E) :
    HasFDerivAt ⇑(lipschitzPerturbationHomeomorph η hη hc hbound)
      ((idAddEquiv (fderiv ℝ η x) ((hbound x).trans_lt hc) : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
  rw [coe_idAddEquiv, coe_lipschitzPerturbationHomeomorph]
  exact (hasFDerivAt_id (𝕜 := ℝ) x).fun_add (hη x).hasFDerivAt

theorem fderiv_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) (x : E) :
    fderiv ℝ ⇑(lipschitzPerturbationHomeomorph η hη hc hbound) x =
      ((idAddEquiv (fderiv ℝ η x) ((hbound x).trans_lt hc) : E ≃L[ℝ] E) : E →L[ℝ] E) :=
  (hasFDerivAt_lipschitzPerturbationHomeomorph η hη hc hbound x).fderiv

theorem hasStrictFDerivAt_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) {n : ℕ∞ω} (hn : n ≠ 0)
    (hηn : ContDiff ℝ n η) (x : E) :
    HasStrictFDerivAt ⇑(lipschitzPerturbationHomeomorph η hη hc hbound)
      ((idAddEquiv (fderiv ℝ η x) ((hbound x).trans_lt hc) : E ≃L[ℝ] E) : E →L[ℝ] E) x :=
  (contDiff_lipschitzPerturbationHomeomorph η hη hc hbound hηn).contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_lipschitzPerturbationHomeomorph η hη hc hbound x) hn

theorem contDiff_symm_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) {n : ℕ∞ω} (hηn : ContDiff ℝ n η) :
    ContDiff ℝ n ⇑((lipschitzPerturbationHomeomorph η hη hc hbound).symm) :=
  Homeomorph.contDiff_symm (lipschitzPerturbationHomeomorph η hη hc hbound)
    (f₀' := fun x => idAddEquiv (fderiv ℝ η x) ((hbound x).trans_lt hc))
    (fun x => hasFDerivAt_lipschitzPerturbationHomeomorph η hη hc hbound x)
    (contDiff_lipschitzPerturbationHomeomorph η hη hc hbound hηn)

theorem homeomorph_image_eq_self_of_apply_eq {X : Type*} [TopologicalSpace X] (g : X ≃ₜ X)
    {W : Set X} (hg : ∀ x, x ∉ W → g x = x) : g '' W = W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hgy : g y ∈ W
    · exact hgy
    · have h2 : g y = y := g.injective (hg (g y) hgy)
      rw [h2]
      exact hy
  · intro hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    by_cases hy : g.symm x ∈ W
    · exact hy
    · have h1 : g.symm x = x := (hg (g.symm x) hy).symm.trans (g.apply_symm_apply x)
      rw [h1]
      exact hx

theorem homeomorph_symm_apply_eq_self_of_apply_eq {X : Type*} [TopologicalSpace X]
    (g : X ≃ₜ X) {W : Set X} (hg : ∀ x, x ∉ W → g x = x) {x : X} (hx : x ∉ W) :
    g.symm x = x := by
  have h := g.symm_apply_apply x
  rw [hg x hx] at h
  exact h

theorem lipschitzPerturbationHomeomorph_apply_of_notMem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) {W : Set E}
    (hW : ∀ x, x ∉ W → η x = 0) {x : E} (hx : x ∉ W) :
    lipschitzPerturbationHomeomorph η hη hc hbound x = x := by
  rw [lipschitzPerturbationHomeomorph_apply, hW x hx, add_zero]

theorem image_lipschitzPerturbationHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) {W : Set E}
    (hW : ∀ x, x ∉ W → η x = 0) :
    lipschitzPerturbationHomeomorph η hη hc hbound '' W = W :=
  homeomorph_image_eq_self_of_apply_eq _ fun _ hx =>
    lipschitzPerturbationHomeomorph_apply_of_notMem η hη hc hbound hW hx

theorem symm_apply_lipschitzPerturbationHomeomorph_of_notMem {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (η : E → E)
    (hη : Differentiable ℝ η) {c : ℝ} (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c)
    {W : Set E} (hW : ∀ x, x ∉ W → η x = 0) {x : E} (hx : x ∉ W) :
    (lipschitzPerturbationHomeomorph η hη hc hbound).symm x = x :=
  homeomorph_symm_apply_eq_self_of_apply_eq _
    (fun _ hy => lipschitzPerturbationHomeomorph_apply_of_notMem η hη hc hbound hW hy) hx

theorem exists_homeomorph_add_of_norm_fderiv_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {η : E → E} {r : ℕ} (hr : 1 ≤ r)
    (hη : ContDiff ℝ r η) {c : ℝ} (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) :
    ∃ g : E ≃ₜ E, (∀ x, g x = x + η x) ∧ ContDiff ℝ r g ∧ ContDiff ℝ r g.symm ∧
      (∀ x, ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + fderiv ℝ η x ∧
        HasStrictFDerivAt g (L : E →L[ℝ] E) x) ∧
      ∀ W : Set E, (∀ x, x ∉ W → η x = 0) → g '' W = W ∧ ∀ x, x ∉ W → g.symm x = x := by
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd : Differentiable ℝ η := hη.differentiable hr0
  refine ⟨lipschitzPerturbationHomeomorph η hd hc hbound,
    lipschitzPerturbationHomeomorph_apply η hd hc hbound,
    contDiff_lipschitzPerturbationHomeomorph η hd hc hbound hη,
    contDiff_symm_lipschitzPerturbationHomeomorph η hd hc hbound hη, fun x => ?_,
    fun W hW => ?_⟩
  · exact ⟨idAddEquiv (fderiv ℝ η x) ((hbound x).trans_lt hc), coe_idAddEquiv _ _,
      hasStrictFDerivAt_lipschitzPerturbationHomeomorph η hd hc hbound hr0 hη x⟩
  · exact ⟨image_lipschitzPerturbationHomeomorph η hd hc hbound hW,
      fun _ hx => symm_apply_lipschitzPerturbationHomeomorph_of_notMem η hd hc hbound hW hx⟩

end DifferentialGeometry.Analysis
