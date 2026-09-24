import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.EReal.Lemmas
import DifferentialGeometry.Analysis.Calculus.SecondDifference
import Mathlib.Tactic.Linarith

section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem limsup_right_slope_le_of_upper_contact
    {f F : ℝ → ℝ} {x d : ℝ} (hF : HasDerivAt F d x)
    (hle : ∀ᶠ t in 𝓝[>] x, f t ≤ F t) (heq : f x = F x) :
    limsup (fun t => (slope f x t : EReal)) (𝓝[>] x) ≤ (d : EReal) := by
  have hsl : (fun t => (slope f x t : EReal)) ≤ᶠ[𝓝[>] x]
      (fun t => (slope F x t : EReal)) := by
    filter_upwards [hle, self_mem_nhdsWithin] with t ht hxt
    apply EReal.coe_le_coe_iff.mpr
    rw [slope_def_field, slope_def_field, heq]
    exact div_le_div_of_nonneg_right (sub_le_sub_right ht _) (sub_nonneg.mpr (le_of_lt hxt))
  have ht : Tendsto (slope F x) (𝓝[>] x) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x from lt_irrefl x)).mp
      hF.hasDerivWithinAt
  exact (limsup_le_limsup hsl).trans_eq
    ((continuous_coe_real_ereal.tendsto d).comp ht).limsup_eq

end DifferentialGeometry.Analysis

end

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis

theorem directional_second_difference_limit_le_of_scalar_upper_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → Real} {psi : Real → Real} {x : E} {q : Real} (v : E)
    (hpsi : ContDiffAt Real 2 psi 0)
    (hle : ∀ᶠ t in 𝓝 0, f (x + t • v) ≤ psi t) (heq : f x = psi 0)
    {α : Type*} {l : Filter α} [NeBot l] (h : α → Real)
    (hh : Tendsto h l (𝓝 0)) (hne : ∀ᶠ i in l, h i ≠ 0)
    (hlim : Tendsto
      (fun i ↦ (f (x + h i • v) - 2 * f x + f (x - h i • v)) / (h i) ^ 2)
      l (𝓝 q)) :
    q ≤ deriv (deriv psi) 0 := by
  have hm : Tendsto (fun i ↦ -h i) l (𝓝 0) := by
    simpa only [neg_zero] using hh.neg
  have hhne : Tendsto h l (𝓝[≠] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, hne⟩
  have hpsilim : Tendsto
      (fun i ↦ (psi (h i) - 2 * psi 0 + psi (-h i)) / (h i) ^ 2)
      l (𝓝 (deriv (deriv psi) 0)) := by
    simpa only [Function.comp_def, zero_add, zero_sub] using
      hpsi.tendsto_centered_second_difference.comp hhne
  apply le_of_tendsto_of_tendsto hlim hpsilim
  filter_upwards [hh.eventually hle, hm.eventually hle] with i hip him
  have him' : f (x - h i • v) ≤ psi (-h i) := by
    simpa only [neg_smul, ← sub_eq_add_neg] using him
  apply div_le_div_of_nonneg_right _ (sq_nonneg (h i))
  rw [heq]
  linarith

theorem sum_mul_directional_second_difference_limit_le_of_scalar_upper_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → Real} {x : E} {κ : Type*} (s : Finset κ)
    (a q : κ → Real) (v : κ → E) (psi : κ → Real → Real)
    (ha : ∀ k ∈ s, 0 ≤ a k) (hpsi : ∀ k ∈ s, ContDiffAt Real 2 (psi k) 0)
    (hle : ∀ k ∈ s, ∀ᶠ t in 𝓝 0, f (x + t • v k) ≤ psi k t)
    (heq : ∀ k ∈ s, f x = psi k 0)
    {α : Type*} {l : Filter α} [NeBot l] (h : α → Real)
    (hh : Tendsto h l (𝓝 0)) (hne : ∀ᶠ i in l, h i ≠ 0)
    (hlim : ∀ k ∈ s, Tendsto
      (fun i ↦ (f (x + h i • v k) - 2 * f x + f (x - h i • v k)) / (h i) ^ 2)
      l (𝓝 (q k))) :
    (∑ k ∈ s, a k * q k) ≤ ∑ k ∈ s, a k * deriv (deriv (psi k)) 0 := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (directional_second_difference_limit_le_of_scalar_upper_contact
      (v k) (hpsi k hk) (hle k hk) (heq k hk) h hh hne (hlim k hk)) (ha k hk)

theorem directional_second_difference_limit_le_of_upper_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f psi : E → Real} {x : E} {q : Real} (hpsi : ContDiffAt Real 2 psi x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ psi y) (heq : f x = psi x) (v : E)
    {α : Type*} {l : Filter α} [NeBot l] (h : α → Real)
    (hh : Tendsto h l (𝓝 0)) (hne : ∀ᶠ i in l, h i ≠ 0)
    (hlim : Tendsto
      (fun i ↦ (f (x + h i • v) - 2 * f x + f (x - h i • v)) / (h i) ^ 2)
      l (𝓝 q)) :
    q ≤ fderiv Real (fun y ↦ fderiv Real psi y v) x v := by
  have hline : ContDiff Real 2 (fun t : Real ↦ x + t • v) :=
    contDiff_const.add (contDiff_id.smul_const v)
  have hline_lim : Tendsto (fun t : Real ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hline.continuous.tendsto (0 : Real)
  have hpsi_line : ContDiffAt Real 2 psi (x + (0 : Real) • v) := by
    simpa only [zero_smul, add_zero] using hpsi
  have hcomp : ContDiffAt Real 2 (fun t : Real ↦ psi (x + t • v)) 0 := by
    simpa only [Function.comp_def] using hpsi_line.comp 0 hline.contDiffAt
  have hcontact : f x = psi (x + (0 : Real) • v) := by
    simpa only [zero_smul, add_zero] using heq
  have hbound := directional_second_difference_limit_le_of_scalar_upper_contact
    v hcomp (hline_lim.eventually hle) hcontact h hh hne hlim
  rwa [hpsi.deriv_deriv_comp_affine v] at hbound

theorem sum_mul_directional_second_difference_limit_le_of_upper_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f psi : E → Real} {x : E} (hpsi : ContDiffAt Real 2 psi x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ psi y) (heq : f x = psi x)
    {κ : Type*} (s : Finset κ) (a q : κ → Real) (v : κ → E)
    (ha : ∀ k ∈ s, 0 ≤ a k)
    {α : Type*} {l : Filter α} [NeBot l] (h : α → Real)
    (hh : Tendsto h l (𝓝 0)) (hne : ∀ᶠ i in l, h i ≠ 0)
    (hlim : ∀ k ∈ s, Tendsto
      (fun i ↦ (f (x + h i • v k) - 2 * f x + f (x - h i • v k)) / (h i) ^ 2)
      l (𝓝 (q k))) :
    (∑ k ∈ s, a k * q k) ≤
      ∑ k ∈ s, a k * fderiv Real (fun y ↦ fderiv Real psi y (v k)) x (v k) := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (directional_second_difference_limit_le_of_upper_contact
      hpsi hle heq (v k) h hh hne (hlim k hk)) (ha k hk)

end DifferentialGeometry.Analysis
