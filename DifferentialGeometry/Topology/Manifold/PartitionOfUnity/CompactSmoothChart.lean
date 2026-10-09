import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology Manifold ContDiff

universe uM

namespace DifferentialGeometry.Analysis

theorem exists_countable_compact_smooth_chart_partition
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (V : M → Set M) (hV : ∀ x, V x ∈ 𝓝 x) :
    ∃ (ι : Type uM), Nonempty (Encodable ι) ∧
      ∃ (c : ι → M) (U : ι → Set M) (ρ : SmoothPartitionOfUnity ι I M univ),
        (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧
        (∀ i, IsCompact (closure (U i))) ∧
        (∀ i, closure (U i) ⊆ V (c i) ∩ (chartAt H (c i)).source) ∧
        ρ.IsSubordinate U ∧ (∀ i, HasCompactSupport (ρ i)) := by
  obtain ⟨ι, b, hb⟩ :=
    SmoothBumpCovering.exists_isSubordinate I isClosed_univ (fun x _ => hV x)
  let U : ι → Set M := fun i => support (b i)
  have hUopen (i : ι) : IsOpen (U i) := (b i).isOpen_support
  have hUcover : (univ : Set M) ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion_of_mem (b.ind x hx) (b.mem_support_ind x hx)
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUopen hUcover
  refine ⟨ι, ⟨b.locallyFinite.encodable (fun i => (b i).nonempty_support)⟩,
    b.c, U, ρ, hUopen, b.locallyFinite,
    fun i => (b i).hasCompactSupport.isCompact, ?_, hρ, ?_⟩
  · intro i x hx
    exact ⟨hb i hx, (b i).tsupport_subset_chartAt_source hx⟩
  · intro i
    exact (b i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _)
      ((hρ i).trans subset_closure)

end DifferentialGeometry.Analysis
