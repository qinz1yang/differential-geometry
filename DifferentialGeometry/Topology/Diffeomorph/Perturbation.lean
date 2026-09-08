import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Abel

open scoped ContDiff Manifold NNReal

namespace Diffeomorph

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {n : ℕ∞ω} {f : E → E} {C : ℝ≥0}

noncomputable def addLipschitz (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n := by
  have ha : ApproximatesLinearOn (fun x => x + f x)
      (ContinuousLinearEquiv.refl 𝕜 E : E →L[𝕜] E) Set.univ C := by
    intro x hx y hy
    convert hlip.norm_sub_le x y using 1
    congr 1
    simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
    abel
  have hc : Subsingleton E ∨
      C < ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · exact Or.inr (by simpa using hC)
  let h : E ≃ₜ E := ApproximatesLinearOn.toHomeomorph
    (f' := ContinuousLinearEquiv.refl 𝕜 E) (fun x => x + f x) ha hc
  have hh : ContDiff 𝕜 n h := contDiff_id.add hf
  refine
    { toEquiv := h.toEquiv
      contMDiff_toFun := hh.contMDiff
      contMDiff_invFun := ?_ }
  by_cases hn : n = 0
  · subst n
    exact (contDiff_zero.mpr h.symm.continuous).contMDiff
  · have hi : ∀ x, IsUnit (1 + fderiv 𝕜 f x) := by
      intro x
      have hb : ‖-fderiv 𝕜 f x‖ < 1 := by
        rw [norm_neg]
        exact (norm_fderiv_le_of_lipschitz 𝕜 hlip).trans_lt (by exact_mod_cast hC)
      simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hb
    let e : E → E ≃L[𝕜] E := fun x => ContinuousLinearEquiv.ofUnit (hi x).unit
    have he : ∀ x, (e x : E →L[𝕜] E) = 1 + fderiv 𝕜 f x := by
      intro x
      exact (hi x).unit_spec
    apply (h.contDiff_symm (f₀' := e) ?_ hh).contMDiff
    intro x
    rw [he]
    exact (hasFDerivAt_id x).add ((hf.differentiable hn) x).hasFDerivAt

@[simp] theorem addLipschitz_apply (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    addLipschitz hf hlip hC x = x + f x := rfl

theorem addLipschitz_apply_eq_self_iff (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    addLipschitz hf hlip hC x = x ↔ f x = 0 := by
  rw [addLipschitz_apply, add_eq_left]

theorem addLipschitz_symm_apply_eq_self_iff (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    (addLipschitz hf hlip hC).symm x = x ↔ f x = 0 := by
  rw [← addLipschitz_apply_eq_self_iff hf hlip hC x]
  constructor
  · intro hx
    have h := congrArg (addLipschitz hf hlip hC) hx
    rw [apply_symm_apply] at h
    exact h.symm
  · intro hx
    have h := congrArg (addLipschitz hf hlip hC).symm hx
    rw [symm_apply_apply] at h
    exact h.symm

@[simp] theorem addLipschitz_zero (hC : C < 1) :
    addLipschitz (𝕜 := 𝕜) (E := E) (n := n) contDiff_zero_fun
      ((LipschitzWith.const (0 : E)).weaken (show 0 ≤ C from zero_le)) hC = Diffeomorph.refl 𝓘(𝕜, E) E n := by
  apply Diffeomorph.ext
  intro x
  simp

theorem support_addLipschitz_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Function.support (fun x => addLipschitz hf hlip hC x - x) = Function.support f := by
  ext x
  simp only [Function.mem_support, sub_ne_zero]
  exact not_congr (addLipschitz_apply_eq_self_iff hf hlip hC x)

theorem support_addLipschitz_symm_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Function.support (fun x => (addLipschitz hf hlip hC).symm x - x) =
      Function.support f := by
  ext x
  simp only [Function.mem_support, sub_ne_zero]
  exact not_congr (addLipschitz_symm_apply_eq_self_iff hf hlip hC x)

theorem hasCompactSupport_addLipschitz_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (hs : HasCompactSupport f) :
    HasCompactSupport (fun x => addLipschitz hf hlip hC x - x) := by
  simpa only [HasCompactSupport, tsupport, support_addLipschitz_sub_id] using hs

theorem hasCompactSupport_addLipschitz_symm_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (hs : HasCompactSupport f) :
    HasCompactSupport (fun x => (addLipschitz hf hlip hC).symm x - x) := by
  simpa only [HasCompactSupport, tsupport, support_addLipschitz_symm_sub_id] using hs

end Diffeomorph
