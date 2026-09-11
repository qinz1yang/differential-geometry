import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_of_touching_differentiable_bounds
    {f lower upper : E → ℝ} {x : E} {lower' upper' : E →L[ℝ] ℝ}
    (hlower : HasFDerivAt lower lower' x) (hupper : HasFDerivAt upper upper' x)
    (hlower_eq : lower x = f x) (hupper_eq : upper x = f x)
    (hlower_le : ∀ᶠ y in 𝓝 x, lower y ≤ f y)
    (hupper_le : ∀ᶠ y in 𝓝 x, f y ≤ upper y) :
    lower' = upper' ∧ HasFDerivAt f lower' x := by
  have hmin : IsLocalMin (fun y => upper y - lower y) x := by
    change ∀ᶠ y in 𝓝 x, upper x - lower x ≤ upper y - lower y
    filter_upwards [hlower_le, hupper_le] with y hly huy
    rw [hupper_eq, hlower_eq, sub_self]
    exact sub_nonneg.mpr (hly.trans huy)
  have hdifference : upper' - lower' = 0 :=
    hmin.hasFDerivAt_eq_zero (hupper.sub hlower)
  have heq : upper' = lower' := sub_eq_zero.mp hdifference
  have hupper_same : HasFDerivAt upper lower' x := heq ▸ hupper
  refine ⟨heq.symm, HasFDerivAt.of_isLittleO ?_⟩
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  filter_upwards [hlower.isLittleO.bound hε, hupper_same.isLittleO.bound hε,
    hlower_le, hupper_le] with y hlow_rem hupp_rem hly huy
  rw [Real.norm_eq_abs, hlower_eq] at hlow_rem
  rw [Real.norm_eq_abs, hupper_eq] at hupp_rem
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hl := (abs_le.mp hlow_rem).1
  have hu := (abs_le.mp hupp_rem).2
  constructor <;> linarith only [hl, hu, hly, huy]

theorem differentiableAt_of_opposite_upper_supports
    {f phi psi : E → ℝ} {x : E}
    (hphi : DifferentiableAt ℝ phi x) (hpsi : DifferentiableAt ℝ psi x)
    (hphi_eq : phi x = f x) (hpsi_eq : psi x = -f x)
    (hphi_le : ∀ᶠ y in 𝓝 x, f y ≤ phi y)
    (hpsi_le : ∀ᶠ y in 𝓝 x, -f y ≤ psi y) :
    DifferentiableAt ℝ f x := by
  have hlower_eq : -psi x = f x := by rw [hpsi_eq, neg_neg]
  have hlower_le : ∀ᶠ y in 𝓝 x, -psi y ≤ f y := by
    filter_upwards [hpsi_le] with y hy
    linarith only [hy]
  have h := hasFDerivAt_of_touching_differentiable_bounds
    hpsi.hasFDerivAt.neg hphi.hasFDerivAt hlower_eq hphi_eq hlower_le hphi_le
  exact h.2.differentiableAt

end DifferentialGeometry.Analysis
