import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_localInverse_of_hasFDerivAt_equiv
    {f : E → F} {U : Set E} {x₀ : E} {A : E ≃L[ℝ] F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hdf : HasFDerivAt f (A : E →L[ℝ] F) x₀) :
    ∃ e : OpenPartialHomeomorph E F,
      x₀ ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x, e x = f x) := by
  have hf₀ := hf.contDiffAt (hU.mem_nhds hx₀)
  have hinv : {x | ∃ D : E ≃L[ℝ] F,
      (D : E →L[ℝ] F) = fderiv ℝ f x} ∈ 𝓝 x₀ := by
    have hset : Set.range (fun D : E ≃L[ℝ] F ↦ (D : E →L[ℝ] F)) ∈
        𝓝 (fderiv ℝ f x₀) := by
      rw [hdf.fderiv]
      exact A.nhds
    exact (hf₀.continuousAt_fderiv (by simp)).preimage_mem_nhds hset
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem hinv (hU.mem_nhds hx₀))
  let e₀ := hf₀.toOpenPartialHomeomorph f hdf (by simp)
  let e := e₀.restrOpen V hVo
  have hsourceU : e.source ⊆ U := fun x hx ↦ (hV hx.2).2
  refine ⟨e, ⟨hf₀.mem_toOpenPartialHomeomorph_source hdf (by simp), hxV⟩,
    hsourceU, hf.mono hsourceU, ?_, fun _ ↦ rfl⟩
  intro y hy
  have hx := e.map_target hy
  obtain ⟨D, hD⟩ := (hV hx.2).1
  have hfe : ContDiffAt ℝ ∞ e (e.symm y) :=
    hf.contDiffAt (hU.mem_nhds (hsourceU hx))
  have hde : HasFDerivAt e (D : E →L[ℝ] F) (e.symm y) := by
    rw [hD]
    exact hfe.differentiableAt (by simp) |>.hasFDerivAt
  exact (e.contDiffAt_symm hy hde hfe).contDiffWithinAt

end DifferentialGeometry.Analysis
