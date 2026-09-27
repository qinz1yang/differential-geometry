import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalCutoffEstimate
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem exists_uniform_cutoff_of_buffered_function
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set M), IsOpen U → ∀ (u : M → ℝ),
      ContMDiffOn I 𝓘(ℝ) ∞ u U → ∀ (a b η : ℝ), 0 < η →
      closure (U ∩ u ⁻¹' Icc a b) ⊆ U →
      ∃ β : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ β ∧
        (∀ x, 0 ≤ β x ∧ β x ≤ 1) ∧
        tsupport β ⊆ closure (U ∩ u ⁻¹' Icc a b) ∧
        (∀ x ∈ U, u x ∈ Icc (a + η) (b - η) → β x = 1) ∧
        ∀ x ∈ U, ∀ v : TangentSpace I x,
          |mvfderiv I β x v| ≤ (C / η) * |mvfderiv I u x v| := by
  classical
  obtain ⟨C, hC, hcutoff⟩ := DifferentialGeometry.Analysis.exists_uniform_smooth_interval_cutoff
  refine ⟨C, hC, ?_⟩
  intro U hU u hu a b η hη hbuffer
  obtain ⟨χ, hχ, hχbound, hχsupport, hχone, hχderiv⟩ := hcutoff a b η hη
  let β : M → ℝ := U.piecewise (fun x ↦ χ (u x)) (fun _ ↦ 0)
  have hagree (x : M) (hx : x ∈ U) : β =ᶠ[𝓝 x] fun y ↦ χ (u y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact piecewise_eq_of_mem U _ _ hy
  have hsupp : Function.support β ⊆ U ∩ u ⁻¹' Icc a b := by
    intro x hx
    by_cases hxu : x ∈ U
    · refine ⟨hxu, hχsupport (subset_tsupport χ ?_)⟩
      change χ (u x) ≠ 0
      have he : β x = χ (u x) := piecewise_eq_of_mem U _ _ hxu
      exact he ▸ hx
    · have he : β x = 0 := piecewise_eq_of_notMem U _ _ hxu
      exact False.elim (hx he)
  have htsupp : tsupport β ⊆ closure (U ∩ u ⁻¹' Icc a b) := closure_mono hsupp
  have hβ : ContMDiff I 𝓘(ℝ) ∞ β := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxu := hbuffer (htsupp hx)
    exact (hχ.contMDiff.contMDiffAt.comp x ((hu x hxu).contMDiffAt (hU.mem_nhds hxu))).congr_of_eventuallyEq
      (hagree x hxu)
  refine ⟨β, hβ, ?_, htsupp, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · rw [show β x = χ (u x) from piecewise_eq_of_mem U _ _ hx]
      exact hχbound (u x)
    · rw [show β x = 0 from piecewise_eq_of_notMem U _ _ hx]
      exact ⟨le_rfl, zero_le_one⟩
  · intro x hx hcore
    rw [show β x = χ (u x) from piecewise_eq_of_mem U _ _ hx]
    exact hχone (u x) hcore
  · intro x hx v
    have hdu := ((hu x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hdχ := (hχ.differentiable (by simp) (u x)).hasDerivAt
    have heq : mvfderiv I β x v = deriv χ (u x) * mvfderiv I u x v := by
      change (show ℝ from mfderiv I 𝓘(ℝ) β x v) = _
      rw [(hagree x hx).mfderiv_eq]
      change (show ℝ from mfderiv I 𝓘(ℝ) (χ ∘ u) x v) = _
      rw [mfderiv_comp x hdχ.differentiableAt.mdifferentiableAt hdu]
      change (show ℝ from mfderiv 𝓘(ℝ) 𝓘(ℝ) χ (u x) (mfderiv I 𝓘(ℝ) u x v)) = _
      rw [mfderiv_eq_fderiv, hdχ.hasFDerivAt.fderiv]
      change mvfderiv I u x v * deriv χ (u x) = deriv χ (u x) * mvfderiv I u x v
      ring
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_right (hχderiv (u x)) (abs_nonneg _)

end DifferentialGeometry.Topology.Manifold
