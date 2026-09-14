import DifferentialGeometry.Analysis.Calculus.Displacement
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Set MeasureTheory
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mul_sub_le_inner_sub_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ C ε : ℝ} (hx₀ : x₀ ∈ Icc a b) (hC : 0 ≤ C) (hε : ε ≤ 1)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ s ∈ Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ Ioo a b, C ≤ v s)
    (hT : ContinuousOn T (Icc a b)) (hdT : DifferentiableOn ℝ T (Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    C * (1 - ε) * (y - x) ≤ ⟪γ y - γ x, T x₀⟫_ℝ := by
  let p := fun s => ⟪γ s, T x₀⟫_ℝ
  have hp : ContinuousOn p (Icc a b) := hγ.inner continuousOn_const
  have hdir (s : ℝ) (hs : s ∈ Icc a b) : 1 - ε ≤ ⟪T s, T x₀⟫_ℝ := by
    have hn := (norm_sub_le_integral_norm_deriv_of_mem_Icc hT hdT hi hs hx₀).trans hvar
    have hc := real_inner_le_norm (T x₀ - T s) (T x₀)
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hunit, norm_sub_rev] at hc
    nlinarith only [hn, hc]
  have hder (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt p (v s * ⟪T s, T x₀⟫_ℝ) s := by
    simpa only [real_inner_smul_left, inner_zero_right, zero_add] using
      (hdγ s hs).inner ℝ (hasDerivAt_const s (T x₀))
  have hlow (s : ℝ) (hs : s ∈ interior (Icc a b)) : C * (1 - ε) ≤ deriv p s := by
    rw [interior_Icc] at hs
    rw [(hder s hs).deriv]
    exact mul_le_mul (hv s hs) (hdir s (Ioo_subset_Icc_self hs)) (sub_nonneg.mpr hε)
      (hC.trans (hv s hs))
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hp
    (fun s hs => (hder s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    hlow x hx y hy hxy
  simpa only [p, inner_sub_left] using h

theorem strictMonoOn_inner_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ C ε : ℝ} (hx₀ : x₀ ∈ Icc a b) (hC : 0 < C) (hε : ε < 1)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ s ∈ Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ Ioo a b, C ≤ v s)
    (hT : ContinuousOn T (Icc a b)) (hdT : DifferentiableOn ℝ T (Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1) :
    StrictMonoOn (fun s => ⟪γ s, T x₀⟫_ℝ) (Icc a b) := by
  intro x hx y hy hxy
  have h := mul_sub_le_inner_sub_of_tangent_variation hx₀ hC.le hε.le hγ hdγ hv hT hdT hi
    hvar hunit hx hy hxy.le
  rw [inner_sub_left] at h
  have hp : 0 < C * (1 - ε) * (y - x) :=
    mul_pos (mul_pos hC (sub_pos.mpr hε)) (sub_pos.mpr hxy)
  linarith only [h, hp]

theorem exists_unique_inner_projection_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ C ε : ℝ} (hx₀ : x₀ ∈ Icc a b) (hC : 0 < C) (hε : ε < 1)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ s ∈ Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ Ioo a b, C ≤ v s)
    (hT : ContinuousOn T (Icc a b)) (hdT : DifferentiableOn ℝ T (Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {z : ℝ} (hz : z ∈ Ioo (-C * (1 - ε) * (x₀ - a)) (C * (1 - ε) * (b - x₀))) :
    ∃! s, s ∈ Ioo a b ∧ ⟪γ s - γ x₀, T x₀⟫_ℝ = z := by
  let p := fun s => ⟪γ s - γ x₀, T x₀⟫_ℝ
  have hab := hx₀.1.trans hx₀.2
  have hleft := mul_sub_le_inner_sub_of_tangent_variation hx₀ hC.le hε.le hγ hdγ hv hT hdT hi
    hvar hunit ⟨le_rfl, hab⟩ hx₀ hx₀.1
  have hright := mul_sub_le_inner_sub_of_tangent_variation hx₀ hC.le hε.le hγ hdγ hv hT hdT hi
    hvar hunit hx₀ ⟨hab, le_rfl⟩ hx₀.2
  have hp : ContinuousOn p (Icc a b) := (hγ.sub continuousOn_const).inner continuousOn_const
  have hmem : z ∈ Ioo (p a) (p b) := by
    dsimp only [p]
    simp only [mem_Ioo, inner_sub_left] at hleft hright ⊢
    constructor <;> linarith only [hleft, hright, hz.1, hz.2]
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Ioo hab hp hmem
  have hmono := strictMonoOn_inner_of_tangent_variation hx₀ hC hε hγ hdγ hv hT hdT hi hvar hunit
  refine ⟨s, ⟨hs, hsz⟩, ?_⟩
  intro w hw
  apply hmono.injOn (Ioo_subset_Icc_self hw.1) (Ioo_subset_Icc_self hs)
  have heq := hw.2.trans hsz.symm
  simp only [p, inner_sub_left] at heq
  linarith only [heq]

end DifferentialGeometry.Analysis
