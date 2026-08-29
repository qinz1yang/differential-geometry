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
  have : NormalSpace E := inferInstance
  have : LocallyCompactSpace E := inferInstance
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

theorem exists_bump_nhds
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    {K : Set M}
    (hK : IsCompact K) :
    ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧
      HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ K] 1 := by
  classical
  let b : (x : M) → SmoothBumpFunction I x := fun _ => Classical.choice inferInstance
  let U : M → Set M := fun x => interior {y | b x y = 1}
  have hUopen : ∀ x, IsOpen (U x) := fun _ => isOpen_interior
  have hxU : ∀ x, x ∈ U x := by
    intro x
    apply mem_interior_iff_mem_nhds.mpr
    exact (b x).eventuallyEq_one
  have hcover : K ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUopen hcover
  let χ : M → ℝ := fun y => 1 - ∏ x ∈ s, (1 - b x y)
  refine ⟨χ, ?_, ?_, ?_⟩
  · apply contMDiff_const.sub
    exact contMDiff_finsetProd fun x _ =>
      contMDiff_const.sub (b x).contMDiff
  · let L : Set M := ⋃ x ∈ s, tsupport (b x : M → ℝ)
    have hL : IsCompact L :=
      s.isCompact_biUnion fun x _ => (b x).hasCompactSupport
    refine HasCompactSupport.intro hL ?_
    intro y hy
    have hbzero : ∀ x ∈ s, b x y = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hyx
      exact hy (mem_iUnion₂.mpr ⟨x, hx, hyx⟩)
    have hprod : ∏ x ∈ s, (1 - b x y) = 1 := by
      apply Finset.prod_eq_one
      intro x hx
      rw [hbzero x hx]
      exact sub_zero 1
    simp only [χ, hprod, sub_self]
  · have hopen : IsOpen (⋃ x ∈ s, U x) :=
      isOpen_biUnion fun x _ => hUopen x
    filter_upwards [hopen.mem_nhdsSet.mpr hs] with y hy
    obtain ⟨x, hxs, hyU⟩ := mem_iUnion₂.mp hy
    have hbx : b x y = 1 := by
      change y ∈ interior {z | b x z = 1} at hyU
      exact (show interior {z : M | b x z = 1} ⊆
        {z : M | b x z = 1} from interior_subset) hyU
    have hprod : ∏ z ∈ s, (1 - b z y) = 0 := by
      exact Finset.prod_eq_zero hxs (by simp only [hbx, sub_self])
    change χ y = (1 : M → ℝ) y
    simp only [χ, hprod, sub_zero, Pi.one_apply]

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
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have : NormalSpace M := inferInstance
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
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
