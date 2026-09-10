import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_smoothPartitionOfUnity_eq_one_near_closed
    {U C : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hC : ∀ i, IsClosed (C i)) (hCfinite : LocallyFinite C)
    (hdisj : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hCU : ∀ i, C i ⊆ U i) :
    ∃ ρ : SmoothPartitionOfUnity ι I M,
      ρ.IsSubordinate U ∧ ∀ i, ∀ᶠ x in 𝓝ˢ (C i),
        ρ i x = 1 ∧ ∀ j, j ≠ i → ρ j x = 0 := by
  classical
  let D : ι → Set M := fun i ↦ ⋃ j : {j : ι // j ≠ i}, C j.1
  have hD (i : ι) : IsClosed (D i) :=
    (hCfinite.comp_injective Subtype.val_injective).isClosed_iUnion (fun j ↦ hC j.1)
  let V : ι → Set M := fun i ↦ U i \ D i
  have hV (i : ι) : IsOpen (V i) := (hU i).sdiff (hD i)
  have hVcover : univ ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : ∃ i, x ∈ C i
    · obtain ⟨i, hi⟩ := hx
      refine mem_iUnion.mpr ⟨i, hCU i hi, ?_⟩
      intro hxD
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
      exact Set.disjoint_left.mp (hdisj j.2) hj hi
    · obtain ⟨i, hi⟩ := hcover x
      refine mem_iUnion.mpr ⟨i, hi, ?_⟩
      intro hxD
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
      exact hx ⟨j.1, hj⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hV hVcover
  refine ⟨ρ, (fun i x hx ↦ (hρ i hx).1), ?_⟩
  intro i
  let B := ⋃ j : {j : ι // j ≠ i}, tsupport (ρ j.1)
  have hB : IsClosed B :=
    (ρ.locallyFinite.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun _ ↦ isClosed_tsupport _)
  have hCB : C i ⊆ Bᶜ := by
    intro x hx hxB
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    exact (hρ j.1 hj).2 (mem_iUnion.mpr ⟨⟨i, j.2.symm⟩, hx⟩)
  filter_upwards [hB.isOpen_compl.mem_nhdsSet.mpr hCB] with x hx
  have hzero : ∀ j, j ≠ i → ρ j x = 0 := by
    intro j hj
    apply image_eq_zero_of_notMem_tsupport
    intro hxj
    exact hx (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)
  refine ⟨?_, hzero⟩
  have hs := ρ.sum_eq_one (mem_univ x)
  rwa [finsum_eq_single _ i hzero] at hs

theorem exists_smooth_patch_eq_near_closed
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}
    {U C : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hC : ∀ i, IsClosed (C i)) (hCfinite : LocallyFinite C)
    (hdisj : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hCU : ∀ i, C i ⊆ U i) (g : ι → M → F)
    (hg : ∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) :
    ∃ ρ : SmoothPartitionOfUnity ι I M,
      ρ.IsSubordinate U ∧
      ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∑ᶠ j, ρ j x • g j x) ∧
      ∀ i, ∀ᶠ x in 𝓝ˢ (C i), (∑ᶠ j, ρ j x • g j x) = g i x := by
  obtain ⟨ρ, hρ, hflat⟩ := exists_smoothPartitionOfUnity_eq_one_near_closed (I := I)
    hU hcover hC hCfinite hdisj hCU
  refine ⟨ρ, hρ, hρ.contMDiff_finsum_smul hU hg, ?_⟩
  intro i
  filter_upwards [hflat i] with x hx
  rw [finsum_eq_single _ i (fun j hj ↦ by rw [hx.2 j hj, zero_smul]), hx.1, one_smul]

end Poincare.Topology.Manifold
