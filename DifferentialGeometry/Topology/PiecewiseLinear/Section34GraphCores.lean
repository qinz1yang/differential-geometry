import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem isClosed_preimage_graphSkeletonSpace (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    IsClosed {x : 𝒦.complex.space | 𝒦.map x ∈ graphSkeletonSpace 𝒦} := by
  let F : 𝒦.complex.faces → Set 𝒦.complex.space := fun s =>
    {x | s.1.card ≤ 2 ∧ (x : Ea) ∈ convexHull ℝ (s.1 : Set Ea)}
  have hFloc : LocallyFinite F := 𝒦.locallyFinite.subset fun s x hx => hx.2
  have hFclosed : ∀ s, IsClosed (F s) := by
    intro s
    by_cases hs : s.1.card ≤ 2
    · have heq : F s = (Subtype.val : 𝒦.complex.space → Ea) ⁻¹'
          convexHull ℝ (s.1 : Set Ea) := by
        ext x
        exact ⟨fun hx => hx.2, fun hx => ⟨hs, hx⟩⟩
      rw [heq]
      exact (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
        continuous_subtype_val
    · have heq : F s = ∅ := eq_empty_of_forall_notMem fun x hx => hs hx.1
      rw [heq]
      exact isClosed_empty
  have heq : {x : 𝒦.complex.space | 𝒦.map x ∈ graphSkeletonSpace 𝒦} = ⋃ s, F s := by
    ext x
    constructor
    · intro hx
      change 𝒦.map x ∈ ⋃ t ∈
        {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2}, simplexBody 𝒦 t at hx
      obtain ⟨t, ⟨ht, hcard⟩, y, hy, hxy⟩ := mem_iUnion₂.mp hx
      have hyx : y = x :=
        𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space ht hy) x.2 hxy
      exact mem_iUnion.mpr ⟨⟨t, ht⟩, hcard, hyx ▸ hy⟩
    · intro hx
      obtain ⟨s, hcard, hx⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨s.1, ⟨s.2, hcard⟩, x, hx, rfl⟩
  rw [heq]
  exact hFloc.isClosed_iUnion hFclosed

theorem isClosed_graphSkeletonSpace_in_domain (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    IsClosed {x : U | (x : M₁) ∈ graphSkeletonSpace 𝒦} := by
  obtain ⟨C, hC, hpre⟩ := 𝒦.isEmbedding.isInducing.isClosed_iff.mp
    (isClosed_preimage_graphSkeletonSpace 𝒦)
  have heq : (Subtype.val : U → M₁) ⁻¹' C = {x : U | (x : M₁) ∈ graphSkeletonSpace 𝒦} := by
    ext x
    obtain ⟨y, hy, hmap⟩ := 𝒦.bijOn.surjOn x.2
    have he := Set.ext_iff.mp hpre ⟨y, hy⟩
    change (𝒦.map y ∈ C ↔ 𝒦.map y ∈ graphSkeletonSpace 𝒦) at he
    rwa [hmap] at he
  exact heq ▸ hC.preimage continuous_subtype_val

theorem exists_section34_graph_cores
    {Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁}
    (hcompact : ∀ w, IsCompact (Cp w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hvertex : ∀ w, simplexBody 𝒦' w.1 ⊆ interior (Cp w))
    (hcover : graphSkeletonSpace 𝒦 ⊆ ⋃ w, interior (Cp w)) :
    ∃ Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁,
      (∀ w, IsCompact (Kcore w) ∧ simplexBody 𝒦' w.1 ⊆ Kcore w ∧
        Kcore w ⊆ interior (Cp w)) ∧ graphSkeletonSpace 𝒦 ⊆ ⋃ w, Kcore w := by
  let f : 𝒦.complex.space → M₁ := fun x => 𝒦.map x
  let A : Section34VertexIndex 𝒦 𝒦' → Set 𝒦.complex.space := fun w =>
    f ⁻¹' interior (Cp w)
  let S : Set 𝒦.complex.space := f ⁻¹' graphSkeletonSpace 𝒦
  have hSclosed : IsClosed S := isClosed_preimage_graphSkeletonSpace 𝒦
  have hAopen : ∀ w, IsOpen (A w) := fun w =>
    isOpen_interior.preimage 𝒦.isEmbedding.continuous
  have hSA : S ⊆ ⋃ w, A w := by
    intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨w, hw⟩
  obtain ⟨V, hVopen, hSV, hVloc, hVA⟩ :=
    precise_refinement_set hSclosed A hAopen hSA
  obtain ⟨O, hSO, -, hOV⟩ := exists_subset_iUnion_closure_subset hSclosed hVopen
    (fun x _ => hVloc.point_finite x) hSV
  have hOr : ∀ w, closure (O w) ⊆ f ⁻¹' Cp w := fun w x hx =>
    (interior_subset : interior (Cp w) ⊆ Cp w) (hVA w (hOV w hx))
  have hrange : U ⊆ range f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := 𝒦.bijOn.surjOn hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hOcompact : ∀ w, IsCompact (closure (O w)) := fun w =>
    (𝒦.isEmbedding.isInducing.isCompact_preimage' (hcompact w)
      ((hCpU w).trans hrange)).of_isClosed_subset isClosed_closure (hOr w)
  let Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁ := fun w =>
    f '' closure (O w) ∪ simplexBody 𝒦' w.1
  refine ⟨Kcore, fun w => ⟨?_, subset_union_right, ?_⟩, ?_⟩
  · refine ((hOcompact w).image 𝒦.isEmbedding.continuous).union ?_
    exact (w.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (𝒦'.continuousOn.mono (𝒦'.complex.convexHull_subset_space w.2.1))
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hy
      exact hVA w (hOV w hx)
    · exact hvertex w hy
  · intro y hy
    have hyU : y ∈ U := by
      obtain ⟨w, hw⟩ := mem_iUnion.mp (hcover hy)
      exact hCpU w (interior_subset hw)
    obtain ⟨x, hx, rfl⟩ := 𝒦.bijOn.surjOn hyU
    obtain ⟨w, hw⟩ := mem_iUnion.mp (hSO (show (⟨x, hx⟩ : 𝒦.complex.space) ∈ S from hy))
    exact mem_iUnion.mpr ⟨w, Or.inl ⟨⟨x, hx⟩, subset_closure hw, rfl⟩⟩

theorem exists_section34_graph_cores_of_isPLCellOn
    {Cp CpBd : Section34VertexIndex 𝒦 𝒦' → Set M₁}
    (hcell : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hvertex : ∀ w, simplexBody 𝒦' w.1 ⊆ interior (Cp w))
    (hcover : graphSkeletonSpace 𝒦 ⊆ ⋃ w, interior (Cp w)) :
    ∃ Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁,
      (∀ w, IsCompact (Kcore w) ∧ simplexBody 𝒦' w.1 ⊆ Kcore w ∧
        Kcore w ⊆ Cp w \ CpBd w) ∧ graphSkeletonSpace 𝒦 ⊆ ⋃ w, Kcore w := by
  obtain ⟨Kcore, hKcore, hcover⟩ := exists_section34_graph_cores
    (fun w => (hcell w).isCompact) hCpU hvertex hcover
  refine ⟨Kcore, fun w => ⟨(hKcore w).1, (hKcore w).2.1, ?_⟩, hcover⟩
  rw [(hcell w).sdiff_boundary_eq_interior]
  exact (hKcore w).2.2

end DifferentialGeometry.Topology.PiecewiseLinear
