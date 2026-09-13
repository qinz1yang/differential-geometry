import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Complemented

noncomputable section
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero
    {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {U : Set E} {x₀ : E} {A : E ≃L[𝕜] F} {n : ℕ∞ω}
    (hn : n ≠ 0) (hf : ContDiffOn 𝕜 n f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hdf : HasFDerivAt f (A : E →L[𝕜] F) x₀) :
    ∃ e : OpenPartialHomeomorph E F,
      x₀ ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn 𝕜 n e e.source ∧ ContDiffOn 𝕜 n e.symm e.target ∧
      (∀ x, e x = f x) := by
  have hf₀ := hf.contDiffAt (hU.mem_nhds hx₀)
  have hinv : {x | ∃ D : E ≃L[𝕜] F, (D : E →L[𝕜] F) = fderiv 𝕜 f x} ∈ 𝓝 x₀ := by
    have hset : Set.range (fun D : E ≃L[𝕜] F ↦ (D : E →L[𝕜] F)) ∈
        𝓝 (fderiv 𝕜 f x₀) := by
      rw [hdf.fderiv]
      exact A.nhds
    exact (hf₀.continuousAt_fderiv hn).preimage_mem_nhds hset
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem hinv (hU.mem_nhds hx₀))
  let e₀ := hf₀.toOpenPartialHomeomorph f hdf hn
  let e := e₀.restrOpen V hVo
  have hsourceU : e.source ⊆ U := fun x hx ↦ (hV hx.2).2
  refine ⟨e, ⟨hf₀.mem_toOpenPartialHomeomorph_source hdf hn, hxV⟩,
    hsourceU, hf.mono hsourceU, ?_, fun _ ↦ rfl⟩
  intro y hy
  have hx := e.map_target hy
  obtain ⟨D, hD⟩ := (hV hx.2).1
  have hfe : ContDiffAt 𝕜 n e (e.symm y) :=
    hf.contDiffAt (hU.mem_nhds (hsourceU hx))
  have hde : HasFDerivAt e (D : E →L[𝕜] F) (e.symm y) := by
    rw [hD]
    exact (hfe.differentiableAt hn).hasFDerivAt
  exact (e.contDiffAt_symm hy hde hfe).contDiffWithinAt


theorem exists_localInverse_of_hasFDerivAt_equiv
    {f : E → F} {U : Set E} {x₀ : E} {A : E ≃L[ℝ] F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hdf : HasFDerivAt f (A : E →L[ℝ] F) x₀) :
    ∃ e : OpenPartialHomeomorph E F,
      x₀ ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x, e x = f x) :=
  exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero (𝕜 := ℝ) (n := ∞) (by simp) hf hU hx₀ hdf

theorem exists_contDiff_submersion_chart_of_hasFDerivAt
    {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} {U : Set E} {a : E} {L : E →L[𝕜] F} {r : ℕ∞ω}
    (hr : r ≠ 0) (hf : ContDiffOn 𝕜 r f U) (hU : IsOpen U) (ha : a ∈ U)
    (hdf : HasFDerivAt f L a) (hL : Function.Surjective L)
    (hker : L.ker.ClosedComplemented) :
    ∃ e : OpenPartialHomeomorph E (F × L.ker),
      a ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn 𝕜 r e e.source ∧ ContDiffOn 𝕜 r e.symm e.target ∧
      ∀ x, (e x).1 = f x := by
  let : CompleteSpace L.ker := L.isClosed_ker.completeSpace_coe
  obtain ⟨P, hP⟩ := hker
  let A := L.equivProdOfSurjectiveOfIsCompl P (LinearMap.range_eq_top.mpr hL)
    (LinearMap.range_eq_of_proj hP) (LinearMap.isCompl_of_proj hP)
  have hH : ContDiffOn 𝕜 r (fun x => (f x, P x)) U := hf.prodMk P.contDiff.contDiffOn
  have hdH : HasFDerivAt (fun x => (f x, P x)) (A : E →L[𝕜] F × L.ker) a :=
    hdf.prodMk P.hasFDerivAt
  obtain ⟨e, hea, heU, he, hei, heq⟩ :=
    exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero hr hH hU ha hdH
  exact ⟨e, hea, heU, he, hei, fun x => congrArg Prod.fst (heq x)⟩

end DifferentialGeometry.Analysis
