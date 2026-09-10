import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem derivWithin_pos_of_left_inverse_Icc
    {f g : ℝ → ℝ} {a b : ℝ} {T : Set ℝ} (hab : a < b)
    (hf : DifferentiableOn ℝ f (Icc a b)) (hg : DifferentiableOn ℝ g T)
    (hmap : MapsTo f (Icc a b) T) (hinv : LeftInvOn g f (Icc a b))
    (hfab : f a ≤ f b) {x : ℝ} (hx : x ∈ Icc a b) :
    0 < derivWithin f (Icc a b) x := by
  have hmono : StrictMonoOn f (Icc a b) :=
    hf.continuousOn.strictMonoOn_of_injOn_Icc hab.le hfab hinv.injOn
  have hnonneg : 0 ≤ derivWithin f (Icc a b) x := hmono.monotoneOn.derivWithin_nonneg
  have hcomp := (hg _ (hmap hx)).hasDerivWithinAt.comp x (hf x hx).hasDerivWithinAt hmap
  have hid : HasDerivWithinAt (fun y : ℝ ↦ y)
      (derivWithin g T (f x) * derivWithin f (Icc a b) x) (Icc a b) x :=
    hcomp.congr (fun y hy ↦ (hinv hy).symm) (hinv hx).symm
  have he : derivWithin g T (f x) * derivWithin f (Icc a b) x = 1 :=
    (hid.derivWithin (uniqueDiffOn_Icc hab x hx)).symm.trans
      ((hasDerivWithinAt_id x (Icc a b)).derivWithin (uniqueDiffOn_Icc hab x hx))
  have hne : derivWithin f (Icc a b) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  exact lt_of_le_of_ne hnonneg hne.symm

theorem deriv_pos_of_monotone_left_inverse
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hinv : Function.LeftInverse g f) (hmono : Monotone f) (x : ℝ) :
    0 < deriv f x := by
  have hcomp := (hg (f x)).hasDerivAt.comp x (hf x).hasDerivAt
  have hid : HasDerivAt (fun y : ℝ ↦ y) (deriv g (f x) * deriv f x) x :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ (hinv y).symm)
  have he : deriv g (f x) * deriv f x = 1 := hid.unique (hasDerivAt_id x)
  have hne : deriv f x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  exact lt_of_le_of_ne hmono.deriv_nonneg hne.symm

end DifferentialGeometry.Analysis
