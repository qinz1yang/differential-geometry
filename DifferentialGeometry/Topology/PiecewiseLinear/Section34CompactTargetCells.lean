/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSplitDiskIntersection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.splitDisk_subset_cutNeighborhood
    (hcut : Section34CompactCutFrame C K K' src srcBd) (e : Section34CompactEdgeIndex K K') :
    src (.splitDisk e) ⊆ section34CompactCutNeighborhood src := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -⟩ :=
    hcut
  obtain ⟨w, _, -, -, he⟩ := hends e
  rw [he]
  exact inter_subset_left.trans (subset_iUnion (fun v => src (.vertexBall v)) w)

theorem Section34CompactCutFrame.isPLCellOn_vertexBallImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (w : Section34CompactVertexIndex K K') :
    IsPLCellOn 3 (section34CompactVertexBallImage src f₁ w)
      (section34CompactVertexBallImage srcBd f₁ w) := by
  obtain ⟨-, -, -, -, -, -, hcell, -⟩ := hcut
  exact (hcell (.vertexBall w)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
    (hcell (.vertexBall w)).isPolyhedron (subset_iUnion (fun v => src (.vertexBall v)) w))

theorem Section34CompactCutFrame.isPLCellOn_splitDiskImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (e : Section34CompactEdgeIndex K K') :
    IsPLCellOn 2 (section34CompactSplitDiskImage src f₁ e)
      (section34CompactSplitDiskImage srcBd f₁ e) := by
  obtain ⟨-, -, -, -, -, -, hcell, -⟩ := id hcut
  exact (hcell (.splitDisk e)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
    (hcell (.splitDisk e)).isPolyhedron (hcut.splitDisk_subset_cutNeighborhood e))

theorem Section34CompactCutFrame.splitDiskImage_eq_inter
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (e : Section34CompactEdgeIndex K K') :
    ∃ w w' : Section34CompactVertexIndex K K', w ≠ w' ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (w'.1 : Set E3) ∧
      section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ w ∩ section34CompactVertexBallImage src f₁ w' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -⟩ :=
    hcut
  obtain ⟨w, w', hww, hew, he⟩ := hends e
  refine ⟨w, w', hww, hew, ?_⟩
  change f₁ '' src (.splitDisk e) = f₁ '' src (.vertexBall w) ∩ f₁ '' src (.vertexBall w')
  rw [he]
  exact hf₁.bijOn.injOn.image_inter (subset_iUnion (fun v => src (.vertexBall v)) w)
    (subset_iUnion (fun v => src (.vertexBall v)) w')

theorem Section34CompactCutFrame.subset_of_mem_splitDiskImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {e : Section34CompactEdgeIndex K K'} {w : Section34CompactVertexIndex K K'} {x : E3}
    (hxe : x ∈ section34CompactSplitDiskImage src f₁ e)
    (hxw : x ∈ section34CompactVertexBallImage src f₁ w) : w.1 ⊆ e.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, -⟩ := id hcut
  obtain ⟨y, hy, rfl⟩ := hxe
  obtain ⟨y', hy', hyy'⟩ := hxw
  have h : y' = y := hf₁.bijOn.injOn (subset_iUnion (fun v => src (.vertexBall v)) w hy')
    (hcut.splitDisk_subset_cutNeighborhood e hy) hyy'
  rw [h] at hy'
  exact hvertexEdge w e ⟨y, hy', hy⟩

theorem Section34CompactCutFrame.exists_mem_splitDiskImage_of_ne
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w w' : Section34CompactVertexIndex K K'} (hww : w ≠ w') {x : E3}
    (hxw : x ∈ section34CompactVertexBallImage src f₁ w)
    (hxw' : x ∈ section34CompactVertexBallImage src f₁ w') :
    ∃ e : Section34CompactEdgeIndex K K', x ∈ section34CompactSplitDiskImage src f₁ e := by
  obtain ⟨y, hy, rfl⟩ := hxw
  obtain ⟨y', hy', hyy'⟩ := hxw'
  have h : y' = y := hf₁.bijOn.injOn (subset_iUnion (fun v => src (.vertexBall v)) w' hy')
    (subset_iUnion (fun v => src (.vertexBall v)) w hy) hyy'
  rw [h] at hy'
  obtain ⟨e, he⟩ := hcut.exists_splitDisk_eq_inter_vertexBall hww ⟨y, hy, hy'⟩
  refine ⟨e, y, ?_, rfl⟩
  rw [he]
  exact ⟨hy, hy'⟩

theorem Section34CompactCutFrame.disjoint_splitDiskImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {e e' : Section34CompactEdgeIndex K K'} (hee : e ≠ e') :
    Disjoint (section34CompactSplitDiskImage src f₁ e)
      (section34CompactSplitDiskImage src f₁ e') := by
  refine Set.disjoint_left.mpr fun x hx hx' => hee ?_
  have hsub : ∀ a b : Section34CompactEdgeIndex K K',
      x ∈ section34CompactSplitDiskImage src f₁ a →
      x ∈ section34CompactSplitDiskImage src f₁ b → b.1 ⊆ a.1 := by
    intro a b ha hb
    obtain ⟨u, u', -, hbu, hb'⟩ := hcut.splitDiskImage_eq_inter hf₁ b
    rw [hb'] at hb
    rw [← Finset.coe_subset, hbu]
    exact union_subset (Finset.coe_subset.mpr (hcut.subset_of_mem_splitDiskImage hf₁ ha hb.1))
      (Finset.coe_subset.mpr (hcut.subset_of_mem_splitDiskImage hf₁ ha hb.2))
  exact Subtype.ext (Finset.Subset.antisymm (hsub e' e hx' hx) (hsub e e' hx hx'))

theorem Section34CompactCutFrame.splitDiskImage_sdiff_subset_interior
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (e : Section34CompactEdgeIndex K K') :
    section34CompactSplitDiskImage src f₁ e \ section34CompactSplitDiskImage srcBd f₁ e ⊆
      interior (⋃ w, section34CompactVertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, -, -, -, hcell, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hends, -⟩ := id hcut
  obtain ⟨w, w', -, -, he⟩ := hends e
  have hN : ∀ v : Section34CompactVertexIndex K K',
      src (.vertexBall v) ⊆ section34CompactCutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (.vertexBall v)) v
  have hfr : ∀ v : Section34CompactVertexIndex K K', src (.splitDisk e) ⊆ src (.vertexBall v) →
      section34CompactSplitDiskImage src f₁ e ⊆
        frontier (section34CompactVertexBallImage src f₁ v) := by
    intro v hsub
    have hG := isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hcell (.vertexBall v)).isPolyhedron (hN v)
    have hbdv : src (.splitDisk e) ⊆ srcBd (.vertexBall v) := by
      intro x hx
      rw [hbd (.vertexBall v)]
      exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hx⟩
    change f₁ '' src (.splitDisk e) ⊆ frontier (f₁ '' src (.vertexBall v))
    rw [← ((hcell (.vertexBall v)).image_boundary_interior hG).1]
    exact image_mono hbdv
  have hinter : section34CompactVertexBallImage src f₁ w ∩
      section34CompactVertexBallImage src f₁ w' = section34CompactSplitDiskImage src f₁ e := by
    change f₁ '' src (.vertexBall w) ∩ f₁ '' src (.vertexBall w') = f₁ '' src (.splitDisk e)
    rw [he]
    exact (hf₁.bijOn.injOn.image_inter (hN w) (hN w')).symm
  obtain ⟨q, hq, hqb⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hw : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    rw [he]
    exact inter_subset_left
  have hw' : src (.splitDisk e) ⊆ src (.vertexBall w') := by
    rw [he]
    exact inter_subset_right
  have h := sdiff_subset_interior_union_of_inter_eq
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
    (hcut.isPLCellOn_vertexBallImage hf₁ w').isPLBall_three hq hinter (hfr w hw) (hfr w' hw')
  rw [← hqb] at h
  exact h.trans (interior_mono (union_subset
    (subset_iUnion (section34CompactVertexBallImage src f₁) w)
    (subset_iUnion (section34CompactVertexBallImage src f₁) w')))

end DifferentialGeometry.Topology.PiecewiseLinear
