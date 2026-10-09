import DifferentialGeometry.Topology.Manifold.PartitionOfUnity.CompactSmoothChart
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology Manifold ContDiff

universe u

namespace DifferentialGeometry.Analysis

def chartUnionOpens {E : Type*} [TopologicalSpace E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) : TopologicalSpace.Opens E :=
  ⟨⋃ a, (χ a).source, isOpen_iUnion fun a => (χ a).open_source⟩

theorem mem_chartUnionOpens {E : Type*} [TopologicalSpace E] {ι : Type*}
    {χ : ι → OpenPartialHomeomorph E E} {x : E} :
    x ∈ chartUnionOpens χ ↔ ∃ a, x ∈ (χ a).source := by
  change x ∈ ⋃ a, (χ a).source ↔ ∃ a, x ∈ (χ a).source
  exact Set.mem_iUnion

private theorem chartUnion_mem_source {E : Type*} [TopologicalSpace E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (z : chartUnionOpens χ) : ∃ a, z ∈ ((χ a).subtypeRestr hne).source := by
  obtain ⟨a, ha⟩ := mem_chartUnionOpens.mp z.2
  refine ⟨a, ?_⟩
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  exact ha

private theorem chartUnion_target {E : Type*} [TopologicalSpace E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ)) (b : ι) :
    ((χ b).subtypeRestr hne).target = (χ b).target := by
  refine Subset.antisymm ((χ b).subtypeRestr_target_subset hne) fun y hy => ?_
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact ⟨hy, mem_chartUnionOpens.mpr ⟨b, (χ b).map_target hy⟩⟩

theorem chartUnion_symm_apply {E : Type*} [TopologicalSpace E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ)) {b : ι} {y : E}
    (hy : y ∈ (χ b).target) :
    (((χ b).subtypeRestr hne).symm y : E) = (χ b).symm y := by
  have hy' : y ∈ ((χ b).subtypeRestr hne).target := by
    rw [chartUnion_target χ hne b]
    exact hy
  exact (χ b).subtypeRestr_symm_apply hne hy'

@[instance_reducible]
def chartUnionChartedSpace {E : Type*} [NormedAddCommGroup E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ)) :
    ChartedSpace E (chartUnionOpens χ) :=
  DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
    (fun a => (χ a).subtypeRestr hne) (chartUnion_mem_source χ hne)

theorem chartUnion_transition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    (a b : ι) :
    ContDiffOn ℝ ∞ (((χ a).subtypeRestr hne).symm.trans ((χ b).subtypeRestr hne))
      (((χ a).subtypeRestr hne).symm.trans ((χ b).subtypeRestr hne)).source := by
  have h := OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr hne (χ a) (χ b)
  have hsub : (((χ a).subtypeRestr hne).symm.trans ((χ b).subtypeRestr hne)).source ⊆
      ((χ a).symm.trans (χ b)).source := by
    rw [h.source_eq, OpenPartialHomeomorph.restr_source]
    exact inter_subset_left
  exact ((htrans a b).mono hsub).congr fun y hy => h.eqOn hy

theorem isManifold_chartUnion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source) :
    letI := chartUnionChartedSpace χ hne
    IsManifold 𝓘(ℝ, E) ∞ (chartUnionOpens χ) :=
  DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
    (fun a => (χ a).subtypeRestr hne) (chartUnion_mem_source χ hne)
    (chartUnion_transition χ hne htrans)

private theorem chartUnion_mem_maximalAtlas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    (a : ι) :
    letI := chartUnionChartedSpace χ hne
    (χ a).subtypeRestr hne ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ (chartUnionOpens χ) := by
  let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
  have : IsManifold 𝓘(ℝ, E) ∞ (chartUnionOpens χ) := isManifold_chartUnion χ hne htrans
  have hat : (χ a).subtypeRestr hne ∈ atlas E (chartUnionOpens χ) := by
    change (χ a).subtypeRestr hne ∈ range (fun b => (χ b).subtypeRestr hne)
    exact mem_range_self a
  exact IsManifold.subset_maximalAtlas hat

theorem contDiffOn_comp_chartUnion_symm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    (f : chartUnionOpens χ → F)
    (hf : letI := chartUnionChartedSpace χ hne; ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (b : ι) :
    ContDiffOn ℝ ∞ (f ∘ ((χ b).subtypeRestr hne).symm) (χ b).target := by
  let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
  have hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := hf
  have hmem : (χ b).subtypeRestr hne ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ (chartUnionOpens χ) :=
    chartUnion_mem_maximalAtlas χ hne htrans b
  have h1 := contMDiffOn_symm_of_mem_maximalAtlas hmem
  have h2 := (hf'.comp_contMDiffOn h1).contDiffOn
  rw [chartUnion_target χ hne b] at h2
  exact h2

theorem contMDiffAt_comp_chartUnion {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (χ : ι → OpenPartialHomeomorph E E) (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    (g : E → F) (hg : ContDiff ℝ ∞ g) (a : ι) (z : chartUnionOpens χ)
    (hz : (z : E) ∈ (χ a).source) :
    letI := chartUnionChartedSpace χ hne
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun w : chartUnionOpens χ => g (χ a w)) z := by
  let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
  have hmem : (χ a).subtypeRestr hne ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ (chartUnionOpens χ) :=
    chartUnion_mem_maximalAtlas χ hne htrans a
  have hz' : z ∈ ((χ a).subtypeRestr hne).source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hz
  exact hg.contMDiff.contMDiffAt.comp z (contMDiffAt_of_mem_maximalAtlas hmem hz')

theorem exists_chartUnion_partition {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} (χ : ι → OpenPartialHomeomorph E E)
    (hne : Nonempty (chartUnionOpens χ))
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source) :
    letI := chartUnionChartedSpace χ hne
    ∃ (κ : Type u), Nonempty (Encodable κ) ∧
      ∃ (a : κ → ι) (U : κ → Set (chartUnionOpens χ))
        (ρ : SmoothPartitionOfUnity κ 𝓘(ℝ, E) (chartUnionOpens χ) univ),
        (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧ (∀ i, tsupport (ρ i) ⊆ U i) ∧
        (∀ i, HasCompactSupport (ρ i)) ∧ (∀ i, U i ⊆ Subtype.val ⁻¹' (χ (a i)).source) := by
  let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
  have : IsManifold 𝓘(ℝ, E) ∞ (chartUnionOpens χ) := isManifold_chartUnion χ hne htrans
  have : LocallyCompactSpace (chartUnionOpens χ) :=
    (chartUnionOpens χ).isOpen.locallyCompactSpace
  obtain ⟨κ, hκ, c, U, ρ, hUo, hUlf, _, hUsub, hρ, hρc⟩ :=
    exists_countable_compact_smooth_chart_partition 𝓘(ℝ, E) (M := chartUnionOpens χ)
      (fun _ => univ) (fun _ => univ_mem)
  refine ⟨κ, hκ, fun i => (chartUnion_mem_source χ hne (c i)).choose, U, ρ, hUo, hUlf, hρ,
    hρc, fun i z hz => ?_⟩
  have h1 : z ∈ ((χ (chartUnion_mem_source χ hne (c i)).choose).subtypeRestr hne).source :=
    (hUsub i (subset_closure hz)).2
  rw [OpenPartialHomeomorph.subtypeRestr_source] at h1
  exact h1

end DifferentialGeometry.Analysis
