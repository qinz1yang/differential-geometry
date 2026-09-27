/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraHoles
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem mem_convexHull_inter_of_mem_segment {s : Finset E3} (hs : s ∈ K.faces) {u v x : E3}
    (huv : ({u, v} : Finset E3) ∈ K.faces) (hx : x ∈ segment ℝ u v)
    (hxs : x ∈ convexHull ℝ (s : Set E3)) :
    x ∈ convexHull ℝ ((({u, v} : Finset E3) ∩ s : Finset E3) : Set E3) := by
  classical
  have h := K.inter_subset_convexHull huv hs
    ⟨by rw [Finset.coe_pair, convexHull_pair]; exact hx, hxs⟩
  rwa [← Finset.coe_inter] at h

theorem Section34CompactFaceDiskFamily.faceDisk_inter_splitDiskImage_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K') :
    tgtD s ∩ section34CompactSplitDiskImage src f₁ e ⊆
      tgtDBd s ∩ section34CompactSplitDiskImage srcBd f₁ e := by
  obtain ⟨-, -, hD3, hD4, -⟩ := hdisk
  rintro z ⟨hzD, hzE⟩
  obtain ⟨w, w', -, -, hE⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hzE' := hzE
  rw [hE] at hzE'
  have hzV : z ∈ ⋃ u, section34CompactVertexBallImage src f₁ u := mem_iUnion.mpr ⟨w, hzE'.1⟩
  have hzDb : z ∈ tgtDBd s := by
    rw [← hD3 s]
    exact ⟨hzD, hzV⟩
  refine ⟨hzDb, ?_⟩
  by_contra hzb
  exact (hD4 s hzDb).2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hzE, hzb⟩)

theorem Section34CompactFaceDiskFamily.faceDisk_inter_splitDiskImage_eq
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (p : Section34CompactMarkIndex K K') :
    tgtD p.1.1 ∩ section34CompactSplitDiskImage src f₁ p.1.2 = tgtP p := by
  have hsub := hdisk.faceDisk_inter_splitDiskImage_subset hcut hf₁ p.1.1 p.1.2
  obtain ⟨hD1, -, -, -, -, -, -, -, -, hP10, -⟩ := hdisk
  apply Subset.antisymm
  · rw [← hP10 p]
    exact hsub
  · rw [← hP10 p]
    exact inter_subset_inter (hD1 p.1.1).boundary_subset
      (hcut.isPLCellOn_splitDiskImage hf₁ p.1.2).boundary_subset

theorem Section34CompactFaceDiskFamily.faceDisk_inter_splitDiskImage_eq_empty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {s : Section34CompactSimplexIndex K 3} {e : Section34CompactEdgeIndex K K'}
    (hse : ¬ Section34Incident e.1 s.1) :
    tgtD s ∩ section34CompactSplitDiskImage src f₁ e = ∅ := by
  have hsub := hdisk.faceDisk_inter_splitDiskImage_subset hcut hf₁ s e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hP11, -⟩ := hdisk
  exact subset_eq_empty hsub (hP11 s e hse)

theorem Section34CompactFaceDiskFamily.faceDisk_inter_vertexBallImage_eq
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (a : Section34CompactArcIndex K K') :
    tgtD a.1.1 ∩ section34CompactVertexBallImage src f₁ a.1.2 = tgtA a := by
  obtain ⟨hD1, -, hD3, -, -, -, hA7, -⟩ := hdisk
  rw [← hA7 a]
  apply Subset.antisymm
  · rintro z ⟨hzD, hzV⟩
    refine ⟨?_, hzV⟩
    rw [← hD3 a.1.1]
    exact ⟨hzD, mem_iUnion.mpr ⟨a.1.2, hzV⟩⟩
  · exact inter_subset_inter_left _ (hD1 a.1.1).boundary_subset

theorem Section34CompactFaceDiskFamily.exists_mem_faceArc_notMem_splitDiskImage
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (a : Section34CompactArcIndex K K') :
    ∃ z ∈ tgtA a, ∀ e : Section34CompactEdgeIndex K K',
      z ∉ section34CompactSplitDiskImage src f₁ e := by
  obtain ⟨-, -, -, -, -, hA6, -, -, -, -, -, hA12⟩ := hdisk
  obtain ⟨γ, hγ, hγb⟩ := (hA6 a).exists_isPLHomeomorphOn_Icc
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨γ (1 / 2), hγ.bijOn.mapsTo hhalf, fun e hze => ?_⟩
  have hb : γ (1 / 2) ∈ tgtABd a := by
    rw [hA12 a]
    exact ⟨hγ.bijOn.mapsTo hhalf, mem_iUnion.mpr ⟨e, hze⟩⟩
  rw [hγb] at hb
  rcases hb with h | h
  · have := hγ.bijOn.injOn hhalf ⟨le_rfl, zero_le_one⟩ h
    norm_num at this
  · have := hγ.bijOn.injOn hhalf ⟨zero_le_one, le_rfl⟩ (mem_singleton_iff.mp h)
    norm_num at this

theorem Section34CompactFaceDiskFamily.exists_arcs_of_inter_eq_pair
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (s : Section34CompactSimplexIndex K 3) {B₁ B₂ : Set E3} (hB₁ : IsClosed B₁)
    (hB₂ : IsClosed B₂) (hcover : tgtDBd s ⊆ B₁ ∪ B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, section34CompactVertexBallImage src f₁ w) {p q : E3} (hpq : p ≠ q)
    (hinter : tgtD s ∩ B₁ ∩ B₂ = {p, q}) (hne₁ : ((tgtD s ∩ B₁) \ {p, q}).Nonempty)
    (hne₂ : ((tgtD s ∩ B₂) \ {p, q}).Nonempty) :
    tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧
      (∃ γ₁ : ℝ → E3, IsPLHomeomorphOn γ₁ (Icc 0 1) (tgtD s ∩ B₁) ∧ γ₁ 0 = p ∧ γ₁ 1 = q) ∧
      ∃ γ₂ : ℝ → E3, IsPLHomeomorphOn γ₂ (Icc 0 1) (tgtD s ∩ B₂) ∧ γ₂ 0 = p ∧ γ₂ 1 = q := by
  obtain ⟨hD1, -, hD3, -⟩ := hdisk
  have hDc : IsClosed (tgtD s) := (hD1 s).isPolyhedron.isClosed
  have hunion : tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ = tgtDBd s := by
    rw [← inter_union_distrib_left]
    apply Subset.antisymm
    · rw [← hD3 s]
      exact inter_subset_inter_right _ hsub
    · exact subset_inter (hD1 s).boundary_subset hcover
  have hS : IsPLSphere 1 (tgtDBd s) := (hD1 s).isPLSphere_one_of_two
  have hinter' : tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} := by
    rw [← hinter]
    ext z
    simp only [mem_inter_iff]
    tauto
  have hinter'' : tgtD s ∩ B₂ ∩ (tgtD s ∩ B₁) = {p, q} := by
    rw [inter_comm]
    exact hinter'
  refine ⟨hunion.symm, ?_, ?_⟩
  · exact hS.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair (hDc.inter hB₁)
      (hDc.inter hB₂) hunion hpq hinter' hne₁ hne₂
  · rw [union_comm] at hunion
    exact hS.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair (hDc.inter hB₂)
      (hDc.inter hB₁) hunion hpq hinter'' hne₂ hne₁

end DifferentialGeometry.Topology.PiecewiseLinear
