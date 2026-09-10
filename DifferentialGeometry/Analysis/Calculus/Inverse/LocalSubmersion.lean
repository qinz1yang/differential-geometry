import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Normed.Module.ContinuousInverse

set_option autoImplicit false
noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_localProjection_of_hasRightInverse
    {f : E → F} {U : Set E} {x₀ : E} {f' : E →L[ℝ] F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hdf : HasFDerivAt f f' x₀) (hsplit : f'.HasRightInverse) :
    ∃ e : OpenPartialHomeomorph E (F × f'.ker),
      x₀ ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x, (e x).1 = f x) ∧ (∀ y ∈ e.target, f (e.symm y) = y.1) := by
  let R := hsplit.rightInverse
  have hR : Function.RightInverse R f' := hsplit.rightInverse_rightInverse
  let P := f'.projKerOfRightInverse R hR
  let A := ContinuousLinearEquiv.equivOfRightInverse f' R hR
  let g : E → F × f'.ker := fun x ↦ (f x, P x)
  have hg : ContDiffOn ℝ ∞ g U := hf.prodMk P.contDiff.contDiffOn
  have hd : HasFDerivAt g (A : E →L[ℝ] F × f'.ker) x₀ :=
    hdf.prodMk P.hasFDerivAt
  obtain ⟨e, hxe, heU, he, heinv, heq⟩ :=
    exists_localInverse_of_hasFDerivAt_equiv hg hU hx₀ hd
  refine ⟨e, hxe, heU, he, heinv, ?_, ?_⟩
  · intro x
    exact congrArg Prod.fst (heq x)
  · intro y hy
    calc
      f (e.symm y) = (e (e.symm y)).1 := (congrArg Prod.fst (heq (e.symm y))).symm
      _ = y.1 := congrArg Prod.fst (e.right_inv hy)

end DifferentialGeometry.Analysis
