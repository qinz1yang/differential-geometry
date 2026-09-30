import DifferentialGeometry.Tensor.LinearAlgebra.Eigenspace.FixedSubspace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Metric
open scoped Real

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem circleIntegral_apply {f : ℂ → H →L[ℂ] H} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (v : H) :
    (∮ z in C(c, r), f z) v = ∮ z in C(c, r), f z v := by
  simpa only [circleIntegral, smul_apply] using intervalIntegral_apply hf.out v

private theorem resolvent_apply_of_mem_eigenspace (A : H →L[ℂ] H) {μ z : ℂ} {v : H}
    (hv : v ∈ Module.End.eigenspace A.toLinearMap μ) (hz : z ∈ resolventSet ℂ A) :
    resolvent A z v = (z - μ)⁻¹ • v := by
  have hAv : A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hi := congrArg (fun T : H →L[ℂ] H => T v)
    (Ring.inverse_mul_cancel (algebraMap ℂ (H →L[ℂ] H) z - A) hz)
  change resolvent A z (z • v - A v) = v at hi
  rw [hAv, ← sub_smul, map_smul] at hi
  by_cases h : z - μ = 0
  · have hv0 : v = 0 := by simpa only [h, zero_smul] using hi.symm
    simp [hv0]
  · calc
      resolvent A z v = (z - μ)⁻¹ • ((z - μ) • resolvent A z v) := by
        rw [smul_smul, inv_mul_cancel₀ h, one_smul]
      _ = (z - μ)⁻¹ • v := congrArg ((z - μ)⁻¹ • ·) hi

private theorem integral_sub_inv_eq_zero_of_not_mem_closedBall {c μ : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hμ : μ ∉ closedBall c r) :
    (∮ z in C(c, r), (z - μ)⁻¹) = 0 := by
  have hn (z : ℂ) (hz : z ∈ closedBall c r) : z - μ ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hμ)
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ hn
  · intro z hz
    exact (differentiableAt_id.sub_const μ).inv (hn z (ball_subset_closedBall hz.1))

variable [FiniteDimensional ℂ H]

open Classical in
private theorem starProjection_eigenspace_iSup_apply (A : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (s : Set ℂ) {μ : ℂ} {v : H}
    (hv : v ∈ Module.End.eigenspace A.toLinearMap μ) :
    (⨆ a ∈ s, Module.End.eigenspace A.toLinearMap a).starProjection v =
      if μ ∈ s then v else 0 := by
  classical
  split_ifs with hμ
  · exact Submodule.starProjection_eq_self_iff.mpr ((le_iSup₂_of_le μ hμ le_rfl : Module.End.eigenspace A.toLinearMap μ ≤ _) hv)
  · apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    rw [← Submodule.iInf_orthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro a
    by_cases ha : a ∈ s
    · simpa only [iSup_pos ha] using
        hA.orthogonalFamily_eigenspaces.pairwise (Ne.symm (ne_of_mem_of_not_mem ha hμ)) hv
    · simp [ha]

theorem circleIntegral_resolvent_eq_starProjection (A : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet ℂ A) :
    (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent A z) =
      (⨆ μ ∈ ball c r, Module.End.eigenspace A.toLinearMap μ).starProjection := by
  classical
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hcont : ContinuousOn (resolvent A) (sphere c r) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left (hc hz)).continuousAt.continuousWithinAt
  have hint := hcont.circleIntegrable hr
  apply ContinuousLinearMap.coe_injective
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  let v := hA.eigenvectorBasis rfl i
  let μ : ℂ := hA.eigenvalues rfl i
  have hv : Module.End.HasEigenvector A.toLinearMap μ v := hA.hasEigenvector_eigenvectorBasis rfl i
  have hspec : μ ∈ spectrum ℂ A := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp (Module.End.hasEigenvalue_of_hasEigenvector hv)
  have hnot : μ ∉ sphere c r := fun hm => hspec (hc hm)
  have hcalc : (∮ z in C(c, r), resolvent A z) v =
      (∮ z in C(c, r), (z - μ)⁻¹) • v := by
    rw [circleIntegral_apply hint v]
    calc
      (∮ z in C(c, r), resolvent A z v) = ∮ z in C(c, r), (z - μ)⁻¹ • v := by
        apply circleIntegral.integral_congr hr
        intro z hz
        exact resolvent_apply_of_mem_eigenspace A hv.1 (hc hz)
      _ = _ := circleIntegral.integral_smul_const _ _ _ _
  change ((2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent A z)) v =
    (⨆ μ ∈ ball c r, Module.End.eigenspace A.toLinearMap μ).starProjection v
  rw [smul_apply, hcalc, starProjection_eigenspace_iSup_apply A hA _ hv.1]
  by_cases hμ : μ ∈ ball c r
  · rw [ite_eq_left hμ, circleIntegral.integral_sub_inv_of_mem_ball hμ, smul_smul,
      inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]
  · have hout : μ ∉ closedBall c r := by
      intro hh
      have heq : dist μ c = r := le_antisymm hh (le_of_not_gt hμ)
      exact hnot heq
    rw [ite_eq_right hμ, integral_sub_inv_eq_zero_of_not_mem_closedBall hr hout,
      zero_smul, smul_zero]

end ContinuousLinearMap

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem iSup_eigenspace_starProjection_eq (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    (s : Set 𝕜) (h1 : 1 ∈ s) (h0 : 0 ∉ s) :
    (⨆ μ ∈ s, Module.End.eigenspace P.starProjection.toLinearMap μ) = P := by
  apply le_antisymm
  · refine iSup_le (fun μ => iSup_le (fun hμ => ?_))
    intro v hv
    have heq : P.starProjection v = μ • v := Module.End.mem_eigenspace_iff.mp hv
    have hn : μ ≠ 0 := ne_of_mem_of_not_mem hμ h0
    have hm := P.smul_mem μ⁻¹ (P.starProjection_apply_mem v)
    simpa only [heq, smul_smul, inv_mul_cancel₀ hn, one_smul] using hm
  · exact le_iSup_eigenspace_of_fixed P P.starProjection.toLinearMap s h1
      (fun _ hv => starProjection_eq_self_iff.mpr hv)

end Submodule
