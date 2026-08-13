import DifferentialGeometry.Analysis.Calculus.Cutoff
import Mathlib.Geometry.Manifold.Metrizable

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped ContDiff Manifold Topology

theorem exists_bump_compact
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ K] 1 ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  haveI : NormalSpace E := inferInstance
  haveI : LocallyCompactSpace E := inferInstance
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χM, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, E)) (M := E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  let χ : E → ℝ := χM
  refine ⟨χ, ?_, ?_, ?_, ?_, Set.range_subset_iff.mpr hχrange⟩
  · exact contMDiff_iff_contDiff.mp
      (χM.contMDiff.of_le (by exact_mod_cast le_top))
  · refine HasCompactSupport.intro hL ?_
    intro x hx
    exact hχzero x hx
  · exact hχone
  · change closure (Function.support χ) ⊆ U
    exact (closure_minimal
      (fun x hx => by
        by_contra hxL
        exact hx (hχzero x hxL))
      hL.isClosed).trans hLU

theorem exists_mfd_bump
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {K U : Set M}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧
      HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ K] 1 ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  haveI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  haveI : NormalSpace M := inferInstance
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χM, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (M := M) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  let χ : M → ℝ := χM
  refine ⟨χ, χM.contMDiff, ?_, hχone, ?_, Set.range_subset_iff.mpr hχrange⟩
  · refine HasCompactSupport.intro hL ?_
    intro x hx
    exact hχzero x hx
  · change closure (Function.support χ) ⊆ U
    exact (closure_minimal
      (fun x hx => by
        by_contra hxL
        exact hx (hχzero x hxL))
      hL.isClosed).trans hLU

end DifferentialGeometry.Analysis
