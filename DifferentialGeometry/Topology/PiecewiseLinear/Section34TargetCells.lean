/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk
import DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionTools
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}

theorem IsPLCellOn.image_chart_symm {d : ℕ} {S B : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLCellOn d S B) (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.target) :
    IsPLCellOn d (c.symm '' S) (c.symm '' B) :=
  hS.image (isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hS.isPolyhedron hSc)

theorem IsPolyhedralSphere.isPLSphere_image_of_mem_maximalAtlas {m : ℕ} {C : Set M}
    (hC : IsPolyhedralSphere (n := 3) m C) (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPolyhedron P) (hPc : P ⊆ c.target)
    (hCP : C ⊆ c.symm '' P) : IsPLSphere m (c '' C) := by
  have hu := isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hP hPc
  have h := hu.isPLSphere_invFunOn_image hC hCP
  convert h using 1
  refine image_congr fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hCP hx
  rw [c.right_inv (hPc hy)]
  exact (hu.injOn.leftInvOn_invFunOn hy).symm

end Chart

theorem OpenPartialHomeomorph.mem_interior_of_mem_interior_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {S : Set X}
    (hS : S ⊆ e.source) {x : X} (hx : x ∈ e.source) (h : e x ∈ interior (e '' S)) :
    x ∈ interior S := by
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    ((e.isOpen_inter_preimage isOpen_interior).mem_nhds ⟨hx, h⟩) ?_)
  rintro z ⟨hz, hzS⟩
  obtain ⟨y, hy, hyz⟩ := interior_subset hzS
  have hyz' : y = z := e.injOn (hS hy) hz hyz
  exact hyz' ▸ hy

section Frames

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem mem_section34FaceTorus_iff {V : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {s : Section34SimplexIndex 𝒦 3} {x : M₂} :
    x ∈ section34FaceTorus V s ↔
      ∃ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 ∧ x ∈ V w := by
  simp only [section34FaceTorus, mem_iUnion]
  constructor
  · rintro ⟨a, ha, hx⟩
    refine ⟨a.1.2, ?_, hx⟩
    rw [← ha]
    exact a.2
  · rintro ⟨w, hw, hx⟩
    exact ⟨⟨(s, w), hw⟩, rfl, hx⟩

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem isClosed_section34FaceTorus (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    {V : Section34VertexIndex 𝒦 𝒦' → Set M₂} (hV : ∀ w, IsClosed (V w))
    (s : Section34SimplexIndex 𝒦 3) : IsClosed (section34FaceTorus V s) := by
  have heq : section34FaceTorus V s =
      ⋃ w ∈ {w : Section34VertexIndex 𝒦 𝒦' | Section34Incident w.1 s.1}, V w := by
    ext x
    rw [mem_section34FaceTorus_iff, mem_iUnion₂]
    exact ⟨fun ⟨w, hw, hx⟩ => ⟨w, hw, hx⟩, fun ⟨w, hw, hx⟩ => ⟨w, hw, hx⟩⟩
  rw [heq]
  exact (finite_setOf_section34Incident_graphIndex hsub (graphSkeletonSpace 𝒦) 1
    s.2.1).isClosed_biUnion fun w _ => hV w

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.splitDisk_subset_cutNeighborhood
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (e : Section34EdgeIndex 𝒦 𝒦') :
    src (.splitDisk e) ⊆ section34CutNeighborhood src := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ := hcut
  obtain ⟨w, _, -, -, he⟩ := hends e
  rw [he]
  exact inter_subset_left.trans (subset_iUnion (fun v => src (.vertexBall v)) w)

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.isPLCellOn_vertexBallImage (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') :
    IsPLCellOn 3 (section34VertexBallImage src f₁ w) (section34VertexBallImage srcBd f₁ w) := by
  obtain ⟨-, -, -, hcell, -⟩ := hcut
  exact (hcell (.vertexBall w)).image (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w))
    (subset_iUnion (fun v => src (.vertexBall v)) w))

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.isPLCellOn_splitDiskImage (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    IsPLCellOn 2 (section34SplitDiskImage src f₁ e) (section34SplitDiskImage srcBd f₁ e) := by
  obtain ⟨-, -, -, hcell, -⟩ := id hcut
  exact (hcell (.splitDisk e)).image (hf₁.mono_of_isPLCellOn (hcell (.splitDisk e))
    (hcut.splitDisk_subset_cutNeighborhood e))

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem Section34CutFrame.splitDiskImage_eq_inter (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src)) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧
      section34SplitDiskImage src f₁ e =
        section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ w' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ := hcut
  obtain ⟨w, w', hww, hew, he⟩ := hends e
  refine ⟨w, w', hww, hew, ?_⟩
  change f₁ '' src (.splitDisk e) = f₁ '' src (.vertexBall w) ∩ f₁ '' src (.vertexBall w')
  rw [he]
  exact hf₁.image_inter (subset_iUnion (fun v => src (.vertexBall v)) w)
    (subset_iUnion (fun v => src (.vertexBall v)) w')

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem Section34CutFrame.subset_of_mem_splitDiskImage
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src))
    {e : Section34EdgeIndex 𝒦 𝒦'} {w : Section34VertexIndex 𝒦 𝒦'} {x : M₂}
    (hxe : x ∈ section34SplitDiskImage src f₁ e) (hxw : x ∈ section34VertexBallImage src f₁ w) :
    w.1 ⊆ e.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvertexEdge, -, -, -⟩ :=
    id hcut
  obtain ⟨y, hy, rfl⟩ := hxe
  obtain ⟨y', hy', hyy'⟩ := hxw
  have h : y' = y := hf₁ (subset_iUnion (fun v => src (.vertexBall v)) w hy')
    (hcut.splitDisk_subset_cutNeighborhood e hy) hyy'
  rw [h] at hy'
  exact hvertexEdge w e ⟨y, hy', hy⟩

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem Section34CutFrame.exists_mem_splitDiskImage_of_ne
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src))
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww : w ≠ w') {x : M₂}
    (hxw : x ∈ section34VertexBallImage src f₁ w) (hxw' : x ∈ section34VertexBallImage src f₁ w') :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', x ∈ section34SplitDiskImage src f₁ e := by
  obtain ⟨y, hy, rfl⟩ := hxw
  obtain ⟨y', hy', hyy'⟩ := hxw'
  have h : y' = y := hf₁ (subset_iUnion (fun v => src (.vertexBall v)) w' hy')
    (subset_iUnion (fun v => src (.vertexBall v)) w hy) hyy'
  rw [h] at hy'
  obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hww ⟨y, hy, hy'⟩
  refine ⟨e, y, ?_, rfl⟩
  rw [he]
  exact ⟨hy, hy'⟩

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem Section34CutFrame.disjoint_splitDiskImage (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src)) {e e' : Section34EdgeIndex 𝒦 𝒦'}
    (hee : e ≠ e') :
    Disjoint (section34SplitDiskImage src f₁ e) (section34SplitDiskImage src f₁ e') := by
  refine Set.disjoint_left.mpr fun x hx hx' => hee ?_
  have hsub : ∀ a b : Section34EdgeIndex 𝒦 𝒦', x ∈ section34SplitDiskImage src f₁ a →
      x ∈ section34SplitDiskImage src f₁ b → b.1 ⊆ a.1 := by
    intro a b ha hb
    obtain ⟨u, u', -, hbu, hb'⟩ := hcut.splitDiskImage_eq_inter hf₁ b
    rw [hb'] at hb
    rw [← Finset.coe_subset, hbu]
    exact union_subset (Finset.coe_subset.mpr (hcut.subset_of_mem_splitDiskImage hf₁ ha hb.1))
      (Finset.coe_subset.mpr (hcut.subset_of_mem_splitDiskImage hf₁ ha hb.2))
  exact Subtype.ext (Finset.Subset.antisymm (hsub e' e hx' hx) (hsub e e' hx hx'))

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.splitDiskImage_sdiff_subset_interior
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (e : Section34EdgeIndex 𝒦 𝒦') {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34VertexBallImage src f₁ w ⊆ c.source) :
    section34SplitDiskImage src f₁ e \ section34SplitDiskImage srcBd f₁ e ⊆
      interior (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34VertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ :=
    id hcut
  obtain ⟨w, w', -, hew, he⟩ := hends e
  have hN : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (.vertexBall v)) v
  have hwe : w.1 ⊆ e.1 := Finset.coe_subset.mp (hew ▸ subset_union_left)
  have hw'e : w'.1 ⊆ e.1 := Finset.coe_subset.mp (hew ▸ subset_union_right)
  have hfr : ∀ v : Section34VertexIndex 𝒦 𝒦', src (.splitDisk e) ⊆ src (.vertexBall v) →
      section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage srcBd f₁ v := by
    intro v hsub
    refine image_mono fun x hx => ?_
    rw [hbd (.vertexBall v)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hx⟩
  have hinter : section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ w' =
      section34SplitDiskImage src f₁ e := by
    change f₁ '' src (.vertexBall w) ∩ f₁ '' src (.vertexBall w') = f₁ '' src (.splitDisk e)
    rw [he]
    exact (hf₁.injOn.image_inter (hN w) (hN w')).symm
  have hsw : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    rw [he]
    exact inter_subset_left
  have hsw' : src (.splitDisk e) ⊆ src (.vertexBall w') := by
    rw [he]
    exact inter_subset_right
  obtain ⟨hBw, hFw⟩ := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_image_chart hc (hVc w hwe)
  obtain ⟨hBw', hFw'⟩ :=
    (hcut.isPLCellOn_vertexBallImage hf₁ w').isPLBall_image_chart hc (hVc w' hw'e)
  have hEc : section34SplitDiskImage src f₁ e ⊆ c.source := by
    rw [← hinter]
    exact inter_subset_left.trans (hVc w hwe)
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  obtain ⟨q, hq, hqb⟩ := hEcell.exists_isPLHomeomorphOn_image_chart hc hEc
  have hcinter : c '' section34VertexBallImage src f₁ w ∩ c '' section34VertexBallImage src f₁ w' =
      c '' section34SplitDiskImage src f₁ e := by
    rw [← hinter]
    exact (c.injOn.image_inter (hVc w hwe) (hVc w' hw'e)).symm
  have hkey := sdiff_subset_interior_union_of_inter_eq hBw hBw' hq hcinter
    (by rw [← hFw]; exact image_mono (hfr w hsw)) (by rw [← hFw']; exact image_mono (hfr w' hsw'))
  rintro y ⟨hyE, hyB⟩
  have hyc : y ∈ c.source := hEc hyE
  have hcy : c y ∈ interior (c '' (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ w')) := by
    rw [image_union]
    refine hkey ⟨mem_image_of_mem c hyE, fun h => hyB ?_⟩
    rw [← hqb] at h
    obtain ⟨z, hz, hzy⟩ := h
    have hzy' : z = y := c.injOn (hEc (hEcell.boundary_subset hz)) hyc hzy
    exact hzy' ▸ hz
  have hmem := OpenPartialHomeomorph.mem_interior_of_mem_interior_image c
    (union_subset (hVc w hwe) (hVc w' hw'e)) hyc hcy
  refine interior_mono (union_subset ?_ ?_) hmem
  · exact subset_iUnion₂ (s := fun (v : Section34VertexIndex 𝒦 𝒦') (_ : v.1 ⊆ e.1) =>
      section34VertexBallImage src f₁ v) w hwe
  · exact subset_iUnion₂ (s := fun (v : Section34VertexIndex 𝒦 𝒦') (_ : v.1 ⊆ e.1) =>
      section34VertexBallImage src f₁ v) w' hw'e

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
