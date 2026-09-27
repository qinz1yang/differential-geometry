import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped ContDiff Manifold Topology

theorem contDiffOn_cutoff_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {S U : Set E} (hU : IsOpen U) {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n f (S ∩ U)) : ContDiffOn ℝ n (fun x => χ x • f x) S := by
  intro x hx
  by_cases hxχ : x ∈ tsupport χ
  · have hxU : x ∈ U := hχU hxχ
    exact hχ.contDiffWithinAt.smul ((hf x ⟨hx, hxU⟩).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin S (hU.mem_nhds hxU)))
  · have heq : (fun y => χ y • f y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

theorem contDiff_cutoff_smul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U)
    {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  apply contDiffOn_univ.mp
  exact contDiffOn_cutoff_smul (S := univ) hU hχ hχU
    (by simpa only [univ_inter] using hf)

theorem exists_bump_one_on
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
      Set.EqOn χ 1 K ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  have : NormalSpace E := inferInstance
  have : LocallyCompactSpace E := inferInstance
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χM, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, E)) (M := E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  let χ : E → ℝ := χM
  refine ⟨χ, ?_, ?_, ?_, Set.range_subset_iff.mpr hχrange⟩
  · exact contMDiff_iff_contDiff.mp
      (χM.contMDiff.of_le (by exact_mod_cast le_top))
  · intro x hx
    exact hχone.self_of_nhdsSet x hx
  · change closure (Function.support χ) ⊆ U
    exact (closure_minimal
      (fun x hx => by
        by_contra hxL
        exact hx (hχzero x hxL))
      hL.isClosed).trans hLU

end DifferentialGeometry.Analysis
