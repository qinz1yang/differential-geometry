/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellFaceRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFacePoset
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCellComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Cells

theorem IsPLCellOn.inter_closure_sdiff_of_isPLSphere_two {S Z Zb : Set E3}
    (hS : IsPLSphere 2 S) (hZ : IsPLCellOn 2 Z Zb) (hZS : Z ⊆ S) :
    Z ∩ closure (S \ Z) = Zb := by
  obtain ⟨q, hq, rfl⟩ := hZ.exists_isPLHomeomorphOn_stdSimplex
  exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hZS

theorem IsPLCellOn.inter_closure_sdiff_of_isPLSphere_one {S Z Zb : Set E3}
    (hS : IsPLSphere 1 S) (hZ : IsPLCellOn 1 Z Zb) (hZS : Z ⊆ S) :
    Z ∩ closure (S \ Z) = Zb := by
  obtain ⟨q, hq, rfl⟩ := hZ.exists_isPLHomeomorphOn_stdSimplex
  exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary_one hq hZS

theorem IsPLCellOn.subset_closure_sdiff_boundary {d : ℕ} {Z Zb : Set E3}
    (hZ : IsPLCellOn (d + 1) Z Zb) : Z ⊆ closure (Z \ Zb) := by
  obtain ⟨q, hq, rfl⟩ := hZ.exists_isPLHomeomorphOn_stdSimplex
  intro y hy
  rwa [IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary (n := d) hq]

end Cells

section Recognition

variable {K K' : Geometry.SimplicialComplex ℝ E3} {H : Finset E3 → Set E3}
  {cV cVBd : Section34CompactVertexIndex K K' → Set E3}
  {cE cEBd : Section34CompactEdgeIndex K K' → Set E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}
  {tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set E3}
  {tgtX tgtXBd : Section34CompactPatchIndex K K' → Set E3}
  {tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set E3}
  {tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set E3}
  {tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set E3}

theorem Section34CompactFaceDiskFamily.exists_faceArc_of_mem
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {s : Section34CompactSimplexIndex K 3} {w : Section34CompactVertexIndex K K'} {y : E3}
    (hys : y ∈ tgtD s) (hyw : y ∈ cV w) :
    ∃ a : Section34CompactArcIndex K K', a.1.1 = s ∧ a.1.2 = w ∧ y ∈ tgtA a := by
  obtain ⟨-, -, hDU, -, -, -, hAeq, hDVout, -⟩ := hdisk
  have hinc : Section34Incident w.1 s.1 := by
    by_contra hn
    have h : y ∈ tgtD s ∩ cV w := ⟨hys, hyw⟩
    rw [hDVout s w hn] at h
    exact h
  have hyB : y ∈ tgtDBd s := by
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hyw⟩⟩
  refine ⟨⟨(s, w), hinc⟩, rfl, rfl, ?_⟩
  rw [← hAeq]
  exact ⟨hyB, hyw⟩

theorem Section34CompactFaceDiskFamily.exists_markedPoint_of_mem
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hEint : ∀ e, cE e \ cEBd e ⊆ interior (⋃ w, cV w)) (hEU : ∀ e, ∃ w, cE e ⊆ cV w)
    {s : Section34CompactSimplexIndex K 3} {e : Section34CompactEdgeIndex K K'} {y : E3}
    (hys : y ∈ tgtD s) (hye : y ∈ cE e) :
    ∃ p : Section34CompactMarkIndex K K', p.1.1 = s ∧ p.1.2 = e ∧ y ∈ tgtP p := by
  obtain ⟨-, -, hDU, hDBdF, -, -, -, -, -, hPeq, hDEout, -⟩ := hdisk
  obtain ⟨w, hw⟩ := hEU e
  have hyDB : y ∈ tgtDBd s := by
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hw hye⟩⟩
  have hyEB : y ∈ cEBd e := by
    by_contra hyB
    exact Set.disjoint_left.mp disjoint_interior_frontier (hEint e ⟨hye, hyB⟩) (hDBdF s hyDB)
  have hinc : Section34Incident e.1 s.1 := by
    by_contra hn
    have h : y ∈ tgtDBd s ∩ cEBd e := ⟨hyDB, hyEB⟩
    rw [hDEout s e hn] at h
    exact h
  refine ⟨⟨(s, e), hinc⟩, rfl, rfl, ?_⟩
  rw [← hPeq]
  exact ⟨hyDB, hyEB⟩

theorem Section34CompactResidualPlus.exists_patch_of_mem
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    {t : Section34CompactSimplexIndex K 4} {w : Section34CompactVertexIndex K K'} {y : E3}
    (hyt : y ∈ tgtR t) (hyw : y ∈ cV w) :
    ∃ x : Section34CompactPatchIndex K K', x.1.1 = t ∧ x.1.2 = w ∧ y ∈ tgtX x := by
  obtain ⟨-, -, -, -, -, hXeq, hRVout, -⟩ := hres
  have hinc : Section34Incident w.1 t.1 := by
    by_contra hn
    have h : y ∈ tgtR t ∩ cV w := ⟨hyt, hyw⟩
    rw [hRVout t w hn] at h
    exact h
  refine ⟨⟨(t, w), hinc⟩, rfl, rfl, ?_⟩
  rw [← hXeq]
  exact ⟨hyt, hyw⟩

theorem Section34CompactResidualPlus.exists_edgeArc_of_mem
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    {t : Section34CompactSimplexIndex K 4} {e : Section34CompactEdgeIndex K K'} {y : E3}
    (hyt : y ∈ tgtR t) (hye : y ∈ cE e) :
    ∃ i : Section34CompactEdgeArcIndex K K', i.1.1 = t ∧ i.1.2 = e ∧ y ∈ tgtI i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hIeq, hREout, -⟩ := hres
  have hinc : Section34Incident e.1 t.1 := by
    by_contra hn
    have h : y ∈ tgtR t ∩ cE e := ⟨hyt, hye⟩
    rw [hREout t e hn] at h
    exact h
  refine ⟨⟨(t, e), hinc⟩, rfl, rfl, ?_⟩
  rw [← hIeq]
  exact ⟨hyt, hye⟩

theorem Section34CompactResidualPlus.incident_of_mem_tetraBall_faceDisk
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    {t : Section34CompactSimplexIndex K 4} {s : Section34CompactSimplexIndex K 3} {y : E3}
    (hyt : y ∈ tgtR t) (hys : y ∈ tgtD s) : Section34Incident s.1 t.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hRDout, -⟩ := hres
  by_contra hn
  have h : y ∈ tgtR t ∩ tgtD s := ⟨hyt, hys⟩
  rw [hRDout t s hn] at h
  exact h

theorem Section34CompactResidualPlus.exists_patch_faceArc_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hst : ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
      Section34Incident s.1 t.1)
    (a : Section34CompactArcIndex K K') :
    ∃ x : Section34CompactPatchIndex K K', x.1.2 = a.1.2 ∧ tgtA a ⊆ tgtXBd x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXBd, -⟩ := hres
  obtain ⟨t, ht⟩ := hst a.1.1
  refine ⟨⟨(t, a.1.2), Subset.trans a.2 (convexHull_min ht (convex_convexHull ℝ _))⟩, rfl, ?_⟩
  intro y hy
  rw [hXBd]
  exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨rfl, ht⟩, hy⟩)

theorem Section34CompactResidualPlus.patch_inter_outerFace_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) {x : Section34CompactPatchIndex K K'}
    {o : Section34CompactOuterVertexIndex K K'} (hxo : x.1.2 = o.1) :
    tgtX x ∩ tgtO o ⊆ tgtXBd x ∩ tgtOBd o := by
  obtain ⟨-, hXcell, -, hOcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hOeq, -, hVtile, -⟩ :=
    hres
  have hsph : IsPLSphere 2 (cVBd o.1) := by
    rw [(hVcell o.1).boundary_eq_frontier]
    exact (hVcell o.1).isPLBall_three.isPLSphere_frontier
  have hXS : tgtX x ⊆ cVBd o.1 := fun y hy => by
    rw [hVtile o.1]
    exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨x, hxo, hy⟩))
  have hOS : tgtO o ⊆ cVBd o.1 := fun y hy => by
    rw [hVtile o.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨o, rfl, hy⟩)
  have hOcl : tgtO o ⊆ closure (cVBd o.1 \ tgtX x) := by
    rw [hOeq o]
    exact closure_mono
      (sdiff_subset_sdiff_right (subset_union_of_subset_right (subset_iUnion tgtX x) _))
  have hX : tgtX x ∩ tgtO o ⊆ tgtXBd x := fun y hy => by
    rw [← (hXcell x).inter_closure_sdiff_of_isPLSphere_two hsph hXS]
    exact ⟨hy.1, hOcl hy.2⟩
  exact subset_inter hX (inter_subset_of_inter_closure_sdiff_subset hXS
    (hXcell x).subset_closure_sdiff_boundary
    ((hOcell o).inter_closure_sdiff_of_isPLSphere_two hsph hOS).subset hX)

theorem Section34CompactResidualPlus.splitDisk_inter_outerFace_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e))
    (hEV : ∀ e w, ∀ y ∈ cE e, y ∈ cV w → w.1 ⊆ e.1)
    (o : Section34CompactOuterVertexIndex K K') (e : Section34CompactEdgeIndex K K') :
    tgtO o ∩ cE e ⊆ cEBd e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hOeq, -, hVtile, -⟩ := hres
  rintro y ⟨hyo, hye⟩
  have hOS : tgtO o ⊆ cVBd o.1 := fun z hz => by
    rw [hVtile o.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨o, rfl, hz⟩)
  have hwe := hEV e o.1 y hye ((hVcell o.1).boundary_subset (hOS hyo))
  have hES : cE e ⊆ cVBd o.1 := fun z hz => by
    rw [hVtile o.1]
    exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hz⟩))
  have hsph : IsPLSphere 2 (cVBd o.1) := by
    rw [(hVcell o.1).boundary_eq_frontier]
    exact (hVcell o.1).isPLBall_three.isPLSphere_frontier
  have hOcl : tgtO o ⊆ closure (cVBd o.1 \ cE e) := by
    rw [hOeq o]
    exact closure_mono
      (sdiff_subset_sdiff_right (subset_union_of_subset_left (subset_iUnion cE e) _))
  rw [← (hEcell e).inter_closure_sdiff_of_isPLSphere_two hsph hES]
  exact ⟨hye, hOcl hyo⟩

theorem Section34CompactResidualPlus.edgeArc_inter_outerArc_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e)) {i : Section34CompactEdgeArcIndex K K'}
    {q : Section34CompactOuterEdgeIndex K K'} (hiq : i.1.2 = q.1) :
    tgtI i ∩ tgtQ q ⊆ tgtIBd i ∩ tgtQBd q := by
  obtain ⟨-, -, hIcell, -, hQcell, -, -, -, -, -, -, -, hIsub, -, -, -, -, -, -, hQeq, -, hEtile,
    -⟩ := hres
  have hsph : IsPLSphere 1 (cEBd q.1) := (hEcell q.1).isPLSphere_one_of_two
  have hIS : tgtI i ⊆ cEBd q.1 := by
    rw [← hiq]
    exact hIsub i
  have hQS : tgtQ q ⊆ cEBd q.1 := fun y hy => by
    rw [hEtile q.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨q, rfl, hy⟩)
  have hQcl : tgtQ q ⊆ closure (cEBd q.1 \ tgtI i) := by
    rw [hQeq q]
    exact closure_mono (sdiff_subset_sdiff_right (subset_iUnion tgtI i))
  have hI : tgtI i ∩ tgtQ q ⊆ tgtIBd i := fun y hy => by
    rw [← (hIcell i).inter_closure_sdiff_of_isPLSphere_one hsph hIS]
    exact ⟨hy.1, hQcl hy.2⟩
  exact subset_inter hI (inter_subset_of_inter_closure_sdiff_subset hIS
    (hIcell i).subset_closure_sdiff_boundary
    ((hQcell q).inter_closure_sdiff_of_isPLSphere_one hsph hQS).subset hI)

theorem Section34CompactResidualPlus.boundedCell_step_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e))
    (m l : Section34CompactLabelOf K K') (h : Section34CompactCutStep m l) :
    section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ m ⊆
      section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) tgtOBd
        tgtQBd l := by
  obtain ⟨-, -, -, -, -, -, hAeq, -, -, hPeq, -, hABd⟩ := hdisk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hIsub, hRBd, hIBd, hXBd, -, -, -, -, hVtile, hEtile,
    hOBd, hQBd⟩ := hres
  have hEVB : ∀ (e : Section34CompactEdgeIndex K K') (w : Section34CompactVertexIndex K K'),
      w.1 ⊆ e.1 → cE e ⊆ cVBd w := fun e w hwe y hy => by
    rw [hVtile w]
    exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hy⟩))
  have hXVB : ∀ (x : Section34CompactPatchIndex K K') (w : Section34CompactVertexIndex K K'),
      x.1.2 = w → tgtX x ⊆ cVBd w := fun x w hxw y hy => by
    rw [hVtile w]
    exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨x, hxw, hy⟩))
  have hOVB : ∀ (o : Section34CompactOuterVertexIndex K K')
      (w : Section34CompactVertexIndex K K'), o.1 = w → tgtO o ⊆ cVBd w := fun o w how y hy => by
    rw [hVtile w]
    exact Or.inr (mem_iUnion₂.mpr ⟨o, how, hy⟩)
  have hDRB : ∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
      Section34Incident s.1 t.1 → tgtD s ⊆ tgtRBd t := fun s t hst y hy => by
    rw [hRBd t]
    exact Or.inl (mem_iUnion₂.mpr ⟨s, hst, hy⟩)
  have hXRB : ∀ (x : Section34CompactPatchIndex K K') (t : Section34CompactSimplexIndex K 4),
      x.1.1 = t → tgtX x ⊆ tgtRBd t := fun x t hxt y hy => by
    rw [hRBd t]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, hxt, hy⟩)
  have hIEB : ∀ (i : Section34CompactEdgeArcIndex K K') (e : Section34CompactEdgeIndex K K'),
      i.1.2 = e → tgtI i ⊆ cEBd e := fun i e hie => by
    rw [← hie]
    exact hIsub i
  have hQEB : ∀ (q : Section34CompactOuterEdgeIndex K K') (e : Section34CompactEdgeIndex K K'),
      q.1 = e → tgtQ q ⊆ cEBd e := fun q e hqe y hy => by
    rw [hEtile e]
    exact Or.inr (mem_iUnion₂.mpr ⟨q, hqe, hy⟩)
  have hADB : ∀ (a : Section34CompactArcIndex K K') (s : Section34CompactSimplexIndex K 3),
      a.1.1 = s → tgtA a ⊆ tgtDBd s := fun a s has => by
    rw [← has, ← hAeq a]
    exact inter_subset_left
  have hAXB : ∀ (a : Section34CompactArcIndex K K') (x : Section34CompactPatchIndex K K'),
      a.1.2 = x.1.2 → Section34Incident a.1.1.1 x.1.1.1 → tgtA a ⊆ tgtXBd x :=
    fun a x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨h₁, h₂⟩, hy⟩)
  have hIXB : ∀ (i : Section34CompactEdgeArcIndex K K') (x : Section34CompactPatchIndex K K'),
      i.1.1 = x.1.1 → x.1.2.1 ⊆ i.1.2.1 → tgtI i ⊆ tgtXBd x :=
    fun i x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨h₁, h₂⟩, hy⟩)
  have hAOB : ∀ (a : Section34CompactArcIndex K K') (o : Section34CompactOuterVertexIndex K K'),
      a.1.2 = o.1 → convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space → tgtA a ⊆ tgtOBd o :=
    fun a o h₁ h₂ y hy => by
      rw [hOBd o]
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨h₁, h₂⟩, hy⟩)
  have hQOB : ∀ (q : Section34CompactOuterEdgeIndex K K')
      (o : Section34CompactOuterVertexIndex K K'), o.1.1 ⊆ q.1.1 → tgtQ q ⊆ tgtOBd o :=
    fun q o hoq y hy => by
      rw [hOBd o]
      exact Or.inr (mem_iUnion₂.mpr ⟨q, hoq, hy⟩)
  have hPIB : ∀ (p : Section34CompactMarkIndex K K') (i : Section34CompactEdgeArcIndex K K'),
      p.1.2 = i.1.2 → Section34Incident p.1.1.1 i.1.1.1 → tgtP p ⊆ tgtIBd i :=
    fun p i h₁ h₂ y hy => by
      rw [hIBd i]
      exact mem_iUnion₂.mpr ⟨p, ⟨h₁, h₂⟩, hy⟩
  have hPQB : ∀ (p : Section34CompactMarkIndex K K') (q : Section34CompactOuterEdgeIndex K K'),
      p.1.2 = q.1 → convexHull ℝ (p.1.1.1 : Set E3) ⊆ frontier K.space → tgtP p ⊆ tgtQBd q :=
    fun p q h₁ h₂ y hy => by
      rw [hQBd q]
      exact mem_iUnion₂.mpr ⟨p, ⟨h₁, h₂⟩, hy⟩
  have hPAB : ∀ (p : Section34CompactMarkIndex K K') (a : Section34CompactArcIndex K K'),
      p.1.1 = a.1.1 → a.1.2.1 ⊆ p.1.2.1 → tgtP p ⊆ tgtABd a := by
    intro p a h₁ h₂ y hy
    have hyP : y ∈ tgtDBd p.1.1 ∩ cEBd p.1.2 := by
      rw [hPeq p]
      exact hy
    have hyE : y ∈ cE p.1.2 := (hEcell p.1.2).boundary_subset hyP.2
    rw [hABd a, ← hAeq a, ← h₁]
    exact ⟨⟨hyP.1, (hVcell a.1.2).boundary_subset (hEVB p.1.2 a.1.2 h₂ hyE)⟩,
      mem_iUnion.mpr ⟨p.1.2, hyE⟩⟩
  cases m <;> cases l <;> (try exact False.elim h)
  · exact hEVB _ _ h
  · exact hDRB _ _ h
  · exact hXVB _ _ h
  · exact hXRB _ _ h
  · exact hADB _ _ h
  · exact hAXB _ _ h.1 h.2
  · exact hAOB _ _ h.1 h.2
  · exact hIEB _ _ h
  · exact hIXB _ _ h.1 h.2
  · exact hPAB _ _ h.1 h.2
  · exact hPIB _ _ h.1 h.2
  · exact hPQB _ _ h.1 h.2
  · exact hOVB _ _ h
  · exact hQEB _ _ h
  · exact hQOB _ _ h

theorem Section34CompactResidualPlus.boundedCell_boundary_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hEV : ∀ e w, ∀ y ∈ cE e, y ∈ cV w → w.1 ⊆ e.1)
    (hEint : ∀ e, cE e \ cEBd e ⊆ interior (⋃ w, cV w)) (hEU : ∀ e, ∃ w, cE e ⊆ cV w)
    (l : Section34CompactLabelOf K K') :
    section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) tgtOBd
        tgtQBd l ⊆
      ⋃ m, ⋃ (_ : Section34CompactCutStep m l),
        section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ m := by
  obtain ⟨hDcell, -, hDU, -, -, -, hAeq, -, -, -, -, hABd⟩ := id hdisk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hRBd, hIBd, hXBd, -, -, -, -, hVtile, hEtile,
    hOBd, hQBd⟩ := hres
  intro y hy
  cases l with
  | vertexBall w =>
    change y ∈ cVBd w at hy
    rw [hVtile w] at hy
    rcases hy with (hy | hy) | hy
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.splitDisk e, he, hye⟩
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.patch x, hx, hyx⟩
    · obtain ⟨o, ho, hyo⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.outerFace o, ho, hyo⟩
  | tetraBall t =>
    change y ∈ tgtRBd t at hy
    rw [hRBd t] at hy
    rcases hy with hy | hy
    · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.faceDisk s, hs, hys⟩
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.patch x, hx, hyx⟩
  | splitDisk e =>
    change y ∈ cEBd e at hy
    rw [hEtile e] at hy
    rcases hy with hy | hy
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.edgeArc i, hi, hyi⟩
    · obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.outerArc q, hq, hyq⟩
  | faceDisk s =>
    change y ∈ tgtDBd s at hy
    have hyU : y ∈ tgtD s ∩ ⋃ w, cV w := by
      rw [hDU s]
      exact hy
    obtain ⟨w, hyw⟩ := mem_iUnion.mp hyU.2
    obtain ⟨a, ha₁, -, hya⟩ := hdisk.exists_faceArc_of_mem hyU.1 hyw
    exact mem_iUnion₂.mpr ⟨.faceArc a, ha₁, hya⟩
  | patch x =>
    change y ∈ tgtXBd x at hy
    rw [hXBd x] at hy
    rcases hy with hy | hy
    · obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.faceArc a, ha, hya⟩
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.edgeArc i, hi, hyi⟩
  | faceArc a =>
    change y ∈ tgtABd a at hy
    rw [hABd a] at hy
    obtain ⟨hya, hyE⟩ := hy
    obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
    have hyA : y ∈ tgtDBd a.1.1 ∩ cV a.1.2 := by
      rw [hAeq a]
      exact hya
    obtain ⟨p, hp₁, hp₂, hyp⟩ :=
      hdisk.exists_markedPoint_of_mem hEint hEU ((hDcell a.1.1).boundary_subset hyA.1) hye
    have hap : a.1.2.1 ⊆ p.1.2.1 := by
      rw [hp₂]
      exact hEV e a.1.2 y hye hyA.2
    have hcond : p.1.1 = a.1.1 ∧ a.1.2.1 ⊆ p.1.2.1 := ⟨hp₁, hap⟩
    exact mem_iUnion₂.mpr ⟨.markedPoint p, hcond, hyp⟩
  | edgeArc i =>
    change y ∈ tgtIBd i at hy
    rw [hIBd i] at hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨.markedPoint p, hp, hyp⟩
  | markedPoint p => exact False.elim hy
  | outerFace o =>
    change y ∈ tgtOBd o at hy
    rw [hOBd o] at hy
    rcases hy with hy | hy
    · obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.faceArc a, ha, hya⟩
    · obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.outerArc q, hq, hyq⟩
  | outerArc q =>
    change y ∈ tgtQBd q at hy
    rw [hQBd q] at hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨.markedPoint p, hp, hyp⟩

theorem Section34CompactResidualPlus.boundedCell_inter_subset_ball_disk_patch
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ cV w, y ∈ cV w' → ∃ e, y ∈ cE e)
    (hEV : ∀ e w, ∀ y ∈ cE e, y ∈ cV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (cE e) (cE e')) (hEU : ∀ e, ∃ w, cE e ⊆ cV w)
    (hst : ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
      Section34Incident s.1 t.1) :
    (∀ (w : Section34CompactVertexIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .vertexBall w → cV w ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ cVBd w ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k) ∧
    (∀ (t : Section34CompactSimplexIndex K 4) (k : Section34CompactLabelOf K K'),
      k ≠ .tetraBall t → tgtR t ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtRBd t ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k) ∧
    (∀ (s : Section34CompactSimplexIndex K 3) (k : Section34CompactLabelOf K K'),
      k ≠ .faceDisk s → tgtD s ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtDBd s ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k) ∧
    (∀ (e : Section34CompactEdgeIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .splitDisk e → cE e ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ cEBd e ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k) ∧
    ∀ (x : Section34CompactPatchIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .patch x → tgtX x ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtXBd x ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
  obtain ⟨hDcell, -, hDU, -, hDD, -, hAeq, -, -, hPeq, -, hABd⟩ := id hdisk
  obtain ⟨-, hXcell, -, -, -, hXeq, -, -, -, hRR, hIeq, -, hIsub, hRBd, -, hXBd, -, -, -, -,
    hVtile, hEtile, -, -⟩ := id hres
  have hVB : ∀ w, cVBd w ⊆ cV w := fun w => (hVcell w).boundary_subset
  have hEB : ∀ e, cEBd e ⊆ cE e := fun e => (hEcell e).boundary_subset
  have hDB : ∀ s, tgtDBd s ⊆ tgtD s := fun s => (hDcell s).boundary_subset
  have hXB : ∀ x, tgtXBd x ⊆ tgtX x := fun x => (hXcell x).boundary_subset
  have hEVB : ∀ (e : Section34CompactEdgeIndex K K') (w : Section34CompactVertexIndex K K'),
      w.1 ⊆ e.1 → cE e ⊆ cVBd w := fun e w hwe y hy => by
    rw [hVtile w]
    exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hy⟩))
  have hXVB : ∀ x : Section34CompactPatchIndex K K', tgtX x ⊆ cVBd x.1.2 := fun x y hy => by
    rw [hVtile x.1.2]
    exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨x, rfl, hy⟩))
  have hOVB : ∀ o : Section34CompactOuterVertexIndex K K', tgtO o ⊆ cVBd o.1 :=
    fun o y hy => by
      rw [hVtile o.1]
      exact Or.inr (mem_iUnion₂.mpr ⟨o, rfl, hy⟩)
  have hQEB : ∀ q : Section34CompactOuterEdgeIndex K K', tgtQ q ⊆ cEBd q.1 := fun q y hy => by
    rw [hEtile q.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨q, rfl, hy⟩)
  have hXV : ∀ x : Section34CompactPatchIndex K K', tgtX x ⊆ cV x.1.2 := fun x => by
    rw [← hXeq x]
    exact inter_subset_right
  have hXR : ∀ x : Section34CompactPatchIndex K K', tgtX x ⊆ tgtR x.1.1 := fun x => by
    rw [← hXeq x]
    exact inter_subset_left
  have hAV : ∀ a : Section34CompactArcIndex K K', tgtA a ⊆ cV a.1.2 := fun a => by
    rw [← hAeq a]
    exact inter_subset_right
  have hAD : ∀ a : Section34CompactArcIndex K K', tgtA a ⊆ tgtD a.1.1 := fun a => by
    refine Subset.trans ?_ (hDB a.1.1)
    rw [← hAeq a]
    exact inter_subset_left
  have hIE : ∀ i : Section34CompactEdgeArcIndex K K', tgtI i ⊆ cE i.1.2 := fun i => by
    rw [← hIeq i]
    exact inter_subset_right
  have hPEB : ∀ p : Section34CompactMarkIndex K K', tgtP p ⊆ cEBd p.1.2 := fun p => by
    rw [← hPeq p]
    exact inter_subset_right
  have hPE : ∀ p : Section34CompactMarkIndex K K', tgtP p ⊆ cE p.1.2 :=
    fun p => (hPEB p).trans (hEB _)
  have hOV : ∀ o : Section34CompactOuterVertexIndex K K', tgtO o ⊆ cV o.1 :=
    fun o => (hOVB o).trans (hVB _)
  have hQE : ∀ q : Section34CompactOuterEdgeIndex K K', tgtQ q ⊆ cE q.1 :=
    fun q => (hQEB q).trans (hEB _)
  have hAXB : ∀ (a : Section34CompactArcIndex K K') (x : Section34CompactPatchIndex K K'),
      a.1.2 = x.1.2 → Section34Incident a.1.1.1 x.1.1.1 → tgtA a ⊆ tgtXBd x :=
    fun a x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨h₁, h₂⟩, hy⟩)
  have hIXB : ∀ (i : Section34CompactEdgeArcIndex K K') (x : Section34CompactPatchIndex K K'),
      i.1.1 = x.1.1 → x.1.2.1 ⊆ i.1.2.1 → tgtI i ⊆ tgtXBd x :=
    fun i x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨h₁, h₂⟩, hy⟩)
  have hDRB : ∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
      Section34Incident s.1 t.1 → tgtD s ⊆ tgtRBd t := fun s t h y hy => by
    rw [hRBd t]
    exact Or.inl (mem_iUnion₂.mpr ⟨s, h, hy⟩)
  have hXRB : ∀ x : Section34CompactPatchIndex K K', tgtX x ⊆ tgtRBd x.1.1 := fun x y hy => by
    rw [hRBd x.1.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, rfl, hy⟩)
  have hAVB : ∀ a : Section34CompactArcIndex K K', tgtA a ⊆ cVBd a.1.2 := fun a => by
    obtain ⟨x, hx₂, hax⟩ := hres.exists_patch_faceArc_subset hst a
    rw [← hx₂]
    exact (hax.trans (hXB x)).trans (hXVB x)
  have hDVB : ∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
      ∀ y ∈ tgtD s, y ∈ cV w → y ∈ tgtDBd s := by
    intro s w y hys hyw
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hyw⟩⟩
  have hDEV : ∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ tgtD s, y ∈ cE e → y ∈ tgtDBd s := by
    intro s e y hys hye
    obtain ⟨w, hw⟩ := hEU e
    exact hDVB s w y hys (hw hye)
  have hRRD : ∀ t t' : Section34CompactSimplexIndex K 4, t ≠ t' → ∀ y ∈ tgtR t, y ∈ tgtR t' →
      ∃ s, y ∈ tgtD s := fun t t' htt y hy hy' => mem_iUnion.mp (hRR t t' htt ⟨hy, hy'⟩)
  have hVVB : ∀ w w' : Section34CompactVertexIndex K K', w ≠ w' → ∀ y ∈ cV w, y ∈ cV w' →
      y ∈ cVBd w := by
    intro w w' hww y hy hy'
    obtain ⟨e, he⟩ := hVV w w' hww y hy hy'
    exact hEVB e w (hEV e w y he hy) he
  have hVEB : ∀ (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ cV w, y ∈ cE e → y ∈ cVBd w :=
    fun w e y hy he => hEVB e w (hEV e w y he hy) he
  have hRVB : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ∀ y ∈ tgtR t, y ∈ cV w → y ∈ tgtRBd t := by
    intro t w y hyt hyw
    obtain ⟨x, hx₁, -, hyx⟩ := hres.exists_patch_of_mem hyt hyw
    rw [← hx₁]
    exact hXRB x hyx
  have hRDB : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ∀ y ∈ tgtR t, y ∈ tgtD s → y ∈ tgtRBd t :=
    fun t s y hyt hys => hDRB s t (hres.incident_of_mem_tetraBall_faceDisk hyt hys) hys
  have hREB : ∀ (t : Section34CompactSimplexIndex K 4) (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ tgtR t, y ∈ cE e → y ∈ tgtRBd t := by
    intro t e y hyt hye
    obtain ⟨w, hw⟩ := hEU e
    exact hRVB t w y hyt (hw hye)
  have hXD : ∀ (x : Section34CompactPatchIndex K K') (s : Section34CompactSimplexIndex K 3),
      ∀ y ∈ tgtX x, y ∈ tgtD s → y ∈ tgtXBd x := by
    intro x s y hyx hys
    have hsx := hres.incident_of_mem_tetraBall_faceDisk (hXR x hyx) hys
    obtain ⟨a, ha₁, ha₂, hya⟩ := hdisk.exists_faceArc_of_mem hys (hXV x hyx)
    have hax : Section34Incident a.1.1.1 x.1.1.1 := by
      rw [ha₁]
      exact hsx
    exact hAXB a x ha₂ hax hya
  have hXE : ∀ (x : Section34CompactPatchIndex K K') (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ tgtX x, y ∈ cE e → y ∈ tgtXBd x := by
    intro x e y hyx hye
    obtain ⟨i, hi₁, hi₂, hyi⟩ := hres.exists_edgeArc_of_mem (hXR x hyx) hye
    have hxi : x.1.2.1 ⊆ i.1.2.1 := by
      rw [hi₂]
      exact hEV e x.1.2 y hye (hXV x hyx)
    exact hIXB i x hi₁ hxi hyi
  have hAE : ∀ (a : Section34CompactArcIndex K K') (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ tgtA a, y ∈ cE e → y ∈ tgtABd a := by
    intro a e y hya hye
    rw [hABd a]
    exact ⟨hya, mem_iUnion.mpr ⟨e, hye⟩⟩
  have hEsame : ∀ (e e' : Section34CompactEdgeIndex K K') (Z : Set E3), Z ⊆ cEBd e' →
      ∀ y ∈ cE e, y ∈ Z → y ∈ cEBd e := by
    intro e e' Z hZ y hye hyZ
    by_cases hee : e = e'
    · subst hee
      exact hZ hyZ
    · exact absurd (hEB e' (hZ hyZ)) (Set.disjoint_left.mp (hEE e e' hee) hye)
  have hswap : ∀ {A B Ab Bb : Set E3}, B ∩ A ⊆ Bb ∪ Ab → A ∩ B ⊆ Ab ∪ Bb :=
    fun h y hy => Or.symm (h ⟨hy.2, hy.1⟩)
  have rowV : ∀ (w : Section34CompactVertexIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .vertexBall w → cV w ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ cVBd w ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro w k hk y hy
    refine Or.inl ?_
    obtain ⟨hyw, hyk⟩ := hy
    cases k with
    | vertexBall w' => exact hVVB w w' (by rintro rfl; exact hk rfl) y hyw hyk
    | tetraBall t =>
      obtain ⟨x, -, hx₂, hyx⟩ := hres.exists_patch_of_mem hyk hyw
      rw [← hx₂]
      exact hXVB x hyx
    | splitDisk e => exact hVEB w e y hyw hyk
    | faceDisk s =>
      obtain ⟨a, -, ha₂, hya⟩ := hdisk.exists_faceArc_of_mem hyk hyw
      rw [← ha₂]
      exact hAVB a hya
    | patch x =>
      by_cases hxw : x.1.2 = w
      · rw [← hxw]
        exact hXVB x hyk
      · exact hVVB w x.1.2 (Ne.symm hxw) y hyw (hXV x hyk)
    | faceArc a =>
      by_cases haw : a.1.2 = w
      · rw [← haw]
        exact hAVB a hyk
      · exact hVVB w a.1.2 (Ne.symm haw) y hyw (hAV a hyk)
    | edgeArc i => exact hVEB w i.1.2 y hyw (hIE i hyk)
    | markedPoint p => exact hVEB w p.1.2 y hyw (hPE p hyk)
    | outerFace o =>
      by_cases how : o.1 = w
      · rw [← how]
        exact hOVB o hyk
      · exact hVVB w o.1 (Ne.symm how) y hyw (hOV o hyk)
    | outerArc q => exact hVEB w q.1 y hyw (hQE q hyk)
  have rowR : ∀ (t : Section34CompactSimplexIndex K 4) (k : Section34CompactLabelOf K K'),
      k ≠ .tetraBall t → tgtR t ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtRBd t ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro t k hk y hy
    refine Or.inl ?_
    obtain ⟨hyt, hyk⟩ := hy
    cases k with
    | vertexBall w => exact hRVB t w y hyt hyk
    | tetraBall t' =>
      obtain ⟨s, hys⟩ := hRRD t t' (by rintro rfl; exact hk rfl) y hyt hyk
      exact hRDB t s y hyt hys
    | splitDisk e => exact hREB t e y hyt hyk
    | faceDisk s => exact hRDB t s y hyt hyk
    | patch x => exact hRVB t x.1.2 y hyt (hXV x hyk)
    | faceArc a => exact hRVB t a.1.2 y hyt (hAV a hyk)
    | edgeArc i => exact hREB t i.1.2 y hyt (hIE i hyk)
    | markedPoint p => exact hREB t p.1.2 y hyt (hPE p hyk)
    | outerFace o => exact hRVB t o.1 y hyt (hOV o hyk)
    | outerArc q => exact hREB t q.1 y hyt (hQE q hyk)
  have rowD : ∀ (s : Section34CompactSimplexIndex K 3) (k : Section34CompactLabelOf K K'),
      k ≠ .faceDisk s → tgtD s ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtDBd s ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro s k hk
    cases k with
    | tetraBall t => exact hswap (rowR t (.faceDisk s) nofun)
    | vertexBall w => exact fun y hy => Or.inl (hDVB s w y hy.1 hy.2)
    | splitDisk e => exact fun y hy => Or.inl (hDEV s e y hy.1 hy.2)
    | faceDisk s' =>
      intro y hy
      exact absurd hy.2 (Set.disjoint_left.mp (hDD s s' (by rintro rfl; exact hk rfl)) hy.1)
    | patch x => exact fun y hy => Or.inl (hDVB s x.1.2 y hy.1 (hXV x hy.2))
    | faceArc a => exact fun y hy => Or.inl (hDVB s a.1.2 y hy.1 (hAV a hy.2))
    | edgeArc i => exact fun y hy => Or.inl (hDEV s i.1.2 y hy.1 (hIE i hy.2))
    | markedPoint p => exact fun y hy => Or.inl (hDEV s p.1.2 y hy.1 (hPE p hy.2))
    | outerFace o => exact fun y hy => Or.inl (hDVB s o.1 y hy.1 (hOV o hy.2))
    | outerArc q => exact fun y hy => Or.inl (hDEV s q.1 y hy.1 (hQE q hy.2))
  have rowE : ∀ (e : Section34CompactEdgeIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .splitDisk e → cE e ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ cEBd e ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro e k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.splitDisk e) nofun)
    | tetraBall t => exact hswap (rowR t (.splitDisk e) nofun)
    | faceDisk s => exact hswap (rowD s (.splitDisk e) nofun)
    | splitDisk e' =>
      intro y hy
      exact absurd hy.2 (Set.disjoint_left.mp (hEE e e' (by rintro rfl; exact hk rfl)) hy.1)
    | patch x =>
      intro y hy
      obtain ⟨i, -, hi₂, hyi⟩ := hres.exists_edgeArc_of_mem (hXR x hy.2) hy.1
      refine Or.inl ?_
      rw [← hi₂]
      exact hIsub i hyi
    | faceArc a => exact fun y hy => Or.inr (hAE a e y hy.2 hy.1)
    | edgeArc i => exact fun y hy => Or.inl (hEsame e i.1.2 _ (hIsub i) y hy.1 hy.2)
    | markedPoint p => exact fun y hy => Or.inl (hEsame e p.1.2 _ (hPEB p) y hy.1 hy.2)
    | outerFace o =>
      exact fun y hy =>
        Or.inl (hres.splitDisk_inter_outerFace_subset hVcell hEcell hEV o e ⟨hy.2, hy.1⟩)
    | outerArc q => exact fun y hy => Or.inl (hEsame e q.1 _ (hQEB q) y hy.1 hy.2)
  have rowX : ∀ (x : Section34CompactPatchIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .patch x → tgtX x ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtXBd x ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro x k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.patch x) nofun)
    | tetraBall t => exact hswap (rowR t (.patch x) nofun)
    | faceDisk s => exact hswap (rowD s (.patch x) nofun)
    | splitDisk e => exact hswap (rowE e (.patch x) nofun)
    | patch x' =>
      intro y hy
      refine Or.inl ?_
      have hxx : x ≠ x' := by
        rintro rfl
        exact hk rfl
      by_cases h₂ : x.1.2 = x'.1.2
      · have h₁ : x.1.1 ≠ x'.1.1 := fun h₁ => hxx (Subtype.ext (Prod.ext h₁ h₂))
        obtain ⟨s, hys⟩ := hRRD x.1.1 x'.1.1 h₁ y (hXR x hy.1) (hXR x' hy.2)
        exact hXD x s y hy.1 hys
      · obtain ⟨e, hye⟩ := hVV x.1.2 x'.1.2 h₂ y (hXV x hy.1) (hXV x' hy.2)
        exact hXE x e y hy.1 hye
    | faceArc a => exact fun y hy => Or.inl (hXD x a.1.1 y hy.1 (hAD a hy.2))
    | edgeArc i => exact fun y hy => Or.inl (hXE x i.1.2 y hy.1 (hIE i hy.2))
    | markedPoint p => exact fun y hy => Or.inl (hXE x p.1.2 y hy.1 (hPE p hy.2))
    | outerFace o =>
      intro y hy
      refine Or.inl ?_
      by_cases hxo : x.1.2 = o.1
      · exact (hres.patch_inter_outerFace_subset hVcell hxo hy).1
      · obtain ⟨e, hye⟩ := hVV x.1.2 o.1 hxo y (hXV x hy.1) (hOV o hy.2)
        exact hXE x e y hy.1 hye
    | outerArc q => exact fun y hy => Or.inl (hXE x q.1 y hy.1 (hQE q hy.2))
  exact ⟨rowV, rowR, rowD, rowE, rowX⟩

theorem Section34CompactResidualPlus.boundedCell_inter_subset
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ cV w, y ∈ cV w' → ∃ e, y ∈ cE e)
    (hEV : ∀ e w, ∀ y ∈ cE e, y ∈ cV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (cE e) (cE e'))
    (hEint : ∀ e, cE e \ cEBd e ⊆ interior (⋃ w, cV w)) (hEU : ∀ e, ∃ w, cE e ⊆ cV w)
    (hst : ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
      Section34Incident s.1 t.1)
    (k k' : Section34CompactLabelOf K K') (hkk : k ≠ k') :
    section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ k ∩
        section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ k' ⊆
      section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) tgtOBd
          tgtQBd k ∪
        section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) tgtOBd
          tgtQBd k' := by
  obtain ⟨rowV, rowR, rowD, rowE, rowX⟩ :=
    hres.boundedCell_inter_subset_ball_disk_patch hdisk hVcell hEcell hVV hEV hEE hEU hst
  obtain ⟨hDcell, -, -, -, hDD, -, hAeq, -, -, hPeq, -, hABd⟩ := id hdisk
  obtain ⟨-, hXcell, hIcell, -, -, -, -, -, -, hRR, hIeq, -, -, -, hIBd, hXBd, -, -, -, -,
    hVtile, hEtile, hOBd, -⟩ := id hres
  have hVB : ∀ w, cVBd w ⊆ cV w := fun w => (hVcell w).boundary_subset
  have hEB : ∀ e, cEBd e ⊆ cE e := fun e => (hEcell e).boundary_subset
  have hDB : ∀ s, tgtDBd s ⊆ tgtD s := fun s => (hDcell s).boundary_subset
  have hXB : ∀ x, tgtXBd x ⊆ tgtX x := fun x => (hXcell x).boundary_subset
  have hIB : ∀ i, tgtIBd i ⊆ tgtI i := fun i => (hIcell i).boundary_subset
  have hOV : ∀ o : Section34CompactOuterVertexIndex K K', tgtO o ⊆ cV o.1 := fun o y hy => by
    refine hVB o.1 ?_
    rw [hVtile o.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨o, rfl, hy⟩)
  have hQE : ∀ q : Section34CompactOuterEdgeIndex K K', tgtQ q ⊆ cE q.1 := fun q y hy => by
    refine hEB q.1 ?_
    rw [hEtile q.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨q, rfl, hy⟩)
  have hAV : ∀ a : Section34CompactArcIndex K K', tgtA a ⊆ cV a.1.2 := fun a => by
    rw [← hAeq a]
    exact inter_subset_right
  have hAD : ∀ a : Section34CompactArcIndex K K', tgtA a ⊆ tgtD a.1.1 := fun a => by
    refine Subset.trans ?_ (hDB a.1.1)
    rw [← hAeq a]
    exact inter_subset_left
  have hIE : ∀ i : Section34CompactEdgeArcIndex K K', tgtI i ⊆ cE i.1.2 := fun i => by
    rw [← hIeq i]
    exact inter_subset_right
  have hIR : ∀ i : Section34CompactEdgeArcIndex K K', tgtI i ⊆ tgtR i.1.1 := fun i => by
    rw [← hIeq i]
    exact inter_subset_left
  have hPE : ∀ p : Section34CompactMarkIndex K K', tgtP p ⊆ cE p.1.2 := fun p => by
    refine Subset.trans ?_ (hEB p.1.2)
    rw [← hPeq p]
    exact inter_subset_right
  have hPD : ∀ p : Section34CompactMarkIndex K K', tgtP p ⊆ tgtD p.1.1 := fun p => by
    refine Subset.trans ?_ (hDB p.1.1)
    rw [← hPeq p]
    exact inter_subset_left
  have hIXB : ∀ (i : Section34CompactEdgeArcIndex K K') (x : Section34CompactPatchIndex K K'),
      i.1.1 = x.1.1 → x.1.2.1 ⊆ i.1.2.1 → tgtI i ⊆ tgtXBd x :=
    fun i x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨h₁, h₂⟩, hy⟩)
  have hPIB : ∀ (p : Section34CompactMarkIndex K K') (i : Section34CompactEdgeArcIndex K K'),
      p.1.2 = i.1.2 → Section34Incident p.1.1.1 i.1.1.1 → tgtP p ⊆ tgtIBd i :=
    fun p i h₁ h₂ y hy => by
      rw [hIBd i]
      exact mem_iUnion₂.mpr ⟨p, ⟨h₁, h₂⟩, hy⟩
  have hQOB : ∀ (q : Section34CompactOuterEdgeIndex K K')
      (o : Section34CompactOuterVertexIndex K K'), o.1.1 ⊆ q.1.1 → tgtQ q ⊆ tgtOBd o :=
    fun q o hoq y hy => by
      rw [hOBd o]
      exact Or.inr (mem_iUnion₂.mpr ⟨q, hoq, hy⟩)
  have hRRD : ∀ t t' : Section34CompactSimplexIndex K 4, t ≠ t' → ∀ y ∈ tgtR t, y ∈ tgtR t' →
      ∃ s, y ∈ tgtD s := fun t t' htt y hy hy' => mem_iUnion.mp (hRR t t' htt ⟨hy, hy'⟩)
  have hAE : ∀ (a : Section34CompactArcIndex K K') (e : Section34CompactEdgeIndex K K'),
      ∀ y ∈ tgtA a, y ∈ cE e → y ∈ tgtABd a := by
    intro a e y hya hye
    rw [hABd a]
    exact ⟨hya, mem_iUnion.mpr ⟨e, hye⟩⟩
  have hID : ∀ (i : Section34CompactEdgeArcIndex K K') (s : Section34CompactSimplexIndex K 3),
      ∀ y ∈ tgtI i, y ∈ tgtD s → y ∈ tgtIBd i := by
    intro i s y hyi hys
    have hsi := hres.incident_of_mem_tetraBall_faceDisk (hIR i hyi) hys
    obtain ⟨p, hp₁, hp₂, hyp⟩ := hdisk.exists_markedPoint_of_mem hEint hEU hys (hIE i hyi)
    have hpi : Section34Incident p.1.1.1 i.1.1.1 := by
      rw [hp₁]
      exact hsi
    exact hPIB p i hp₂ hpi hyp
  have hIO : ∀ (i : Section34CompactEdgeArcIndex K K') (o : Section34CompactOuterVertexIndex K K'),
      tgtI i ∩ tgtO o ⊆ tgtOBd o := by
    rintro i o y ⟨hyi, hyo⟩
    have hoi : o.1.1 ⊆ i.1.2.1 := hEV i.1.2 o.1 y (hIE i hyi) (hOV o hyo)
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x : Section34CompactPatchIndex K K', x.1.1 = i.1.1 ∧ x.1.2 = o.1 :=
      ⟨⟨(i.1.1, o.1), Subset.trans (Finset.coe_subset.mpr hoi) i.2⟩, rfl, rfl⟩
    have hxi : x.1.2.1 ⊆ i.1.2.1 := by
      rw [hx₂]
      exact hoi
    exact (hres.patch_inter_outerFace_subset hVcell hx₂
      ⟨((hIXB i x hx₁.symm hxi).trans (hXB x)) hyi, hyo⟩).2
  have hAO : ∀ (a : Section34CompactArcIndex K K') (o : Section34CompactOuterVertexIndex K K'),
      a.1.2 = o.1 → tgtA a ∩ tgtO o ⊆ tgtOBd o := by
    rintro a o hao y ⟨hya, hyo⟩
    obtain ⟨x, hx₂, hax⟩ := hres.exists_patch_faceArc_subset hst a
    exact (hres.patch_inter_outerFace_subset hVcell (hx₂.trans hao)
      ⟨(hax.trans (hXB x)) hya, hyo⟩).2
  have hswap : ∀ {A B Ab Bb : Set E3}, B ∩ A ⊆ Bb ∪ Ab → A ∩ B ⊆ Ab ∪ Bb :=
    fun h y hy => Or.symm (h ⟨hy.2, hy.1⟩)
  have rowA : ∀ (a : Section34CompactArcIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .faceArc a → tgtA a ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtABd a ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro a k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.faceArc a) nofun)
    | tetraBall t => exact hswap (rowR t (.faceArc a) nofun)
    | faceDisk s => exact hswap (rowD s (.faceArc a) nofun)
    | splitDisk e => exact hswap (rowE e (.faceArc a) nofun)
    | patch x => exact hswap (rowX x (.faceArc a) nofun)
    | faceArc a' =>
      intro y hy
      refine Or.inl ?_
      have haa : a ≠ a' := by
        rintro rfl
        exact hk rfl
      by_cases h₁ : a.1.1 = a'.1.1
      · have h₂ : a.1.2 ≠ a'.1.2 := fun h₂ => haa (Subtype.ext (Prod.ext h₁ h₂))
        obtain ⟨e, hye⟩ := hVV a.1.2 a'.1.2 h₂ y (hAV a hy.1) (hAV a' hy.2)
        exact hAE a e y hy.1 hye
      · exact absurd (hAD a' hy.2) (Set.disjoint_left.mp (hDD a.1.1 a'.1.1 h₁) (hAD a hy.1))
    | edgeArc i => exact fun y hy => Or.inl (hAE a i.1.2 y hy.1 (hIE i hy.2))
    | markedPoint p => exact fun y hy => Or.inl (hAE a p.1.2 y hy.1 (hPE p hy.2))
    | outerFace o =>
      intro y hy
      by_cases hao : a.1.2 = o.1
      · exact Or.inr (hAO a o hao hy)
      · obtain ⟨e, hye⟩ := hVV a.1.2 o.1 hao y (hAV a hy.1) (hOV o hy.2)
        exact Or.inl (hAE a e y hy.1 hye)
    | outerArc q => exact fun y hy => Or.inl (hAE a q.1 y hy.1 (hQE q hy.2))
  have rowI : ∀ (i : Section34CompactEdgeArcIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .edgeArc i → tgtI i ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtIBd i ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro i k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.edgeArc i) nofun)
    | tetraBall t => exact hswap (rowR t (.edgeArc i) nofun)
    | faceDisk s => exact hswap (rowD s (.edgeArc i) nofun)
    | splitDisk e => exact hswap (rowE e (.edgeArc i) nofun)
    | patch x => exact hswap (rowX x (.edgeArc i) nofun)
    | faceArc a => exact hswap (rowA a (.edgeArc i) nofun)
    | edgeArc i' =>
      intro y hy
      refine Or.inl ?_
      have hii : i ≠ i' := by
        rintro rfl
        exact hk rfl
      by_cases h₂ : i.1.2 = i'.1.2
      · have h₁ : i.1.1 ≠ i'.1.1 := fun h₁ => hii (Subtype.ext (Prod.ext h₁ h₂))
        obtain ⟨s, hys⟩ := hRRD i.1.1 i'.1.1 h₁ y (hIR i hy.1) (hIR i' hy.2)
        exact hID i s y hy.1 hys
      · exact absurd (hIE i' hy.2) (Set.disjoint_left.mp (hEE i.1.2 i'.1.2 h₂) (hIE i hy.1))
    | markedPoint p => exact fun y hy => Or.inl (hID i p.1.1 y hy.1 (hPD p hy.2))
    | outerFace o => exact fun y hy => Or.inr (hIO i o hy)
    | outerArc q =>
      intro y hy
      by_cases hiq : i.1.2 = q.1
      · exact Or.inl (hres.edgeArc_inter_outerArc_subset hEcell hiq hy).1
      · exact absurd (hQE q hy.2) (Set.disjoint_left.mp (hEE i.1.2 q.1 hiq) (hIE i hy.1))
  have rowP : ∀ (p : Section34CompactMarkIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .markedPoint p → tgtP p ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ ∅ ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro p k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.markedPoint p) nofun)
    | tetraBall t => exact hswap (rowR t (.markedPoint p) nofun)
    | faceDisk s => exact hswap (rowD s (.markedPoint p) nofun)
    | splitDisk e => exact hswap (rowE e (.markedPoint p) nofun)
    | patch x => exact hswap (rowX x (.markedPoint p) nofun)
    | faceArc a => exact hswap (rowA a (.markedPoint p) nofun)
    | edgeArc i => exact hswap (rowI i (.markedPoint p) nofun)
    | markedPoint p' =>
      intro y hy
      have hpp : p ≠ p' := by
        rintro rfl
        exact hk rfl
      by_cases h₁ : p.1.1 = p'.1.1
      · have h₂ : p.1.2 ≠ p'.1.2 := fun h₂ => hpp (Subtype.ext (Prod.ext h₁ h₂))
        exact absurd (hPE p' hy.2) (Set.disjoint_left.mp (hEE p.1.2 p'.1.2 h₂) (hPE p hy.1))
      · exact absurd (hPD p' hy.2) (Set.disjoint_left.mp (hDD p.1.1 p'.1.1 h₁) (hPD p hy.1))
    | outerFace o =>
      intro y hy
      refine Or.inr ?_
      obtain ⟨a, -, ha₂, hya⟩ := hdisk.exists_faceArc_of_mem (hPD p hy.1) (hOV o hy.2)
      exact hAO a o ha₂ ⟨hya, hy.2⟩
    | outerArc q =>
      intro y hy
      refine Or.inr ?_
      by_cases hpq : p.1.2 = q.1
      · obtain ⟨t, ht⟩ := hst p.1.1
        obtain ⟨i, hi₁, hi₂⟩ : ∃ i : Section34CompactEdgeArcIndex K K',
            i.1.1 = t ∧ i.1.2 = p.1.2 :=
          ⟨⟨(t, p.1.2), Subset.trans p.2 (convexHull_min ht (convex_convexHull ℝ _))⟩, rfl, rfl⟩
        have hpi : Section34Incident p.1.1.1 i.1.1.1 := by
          rw [hi₁]
          exact ht
        have hyi : y ∈ tgtI i := hIB i (hPIB p i hi₂.symm hpi hy.1)
        exact (hres.edgeArc_inter_outerArc_subset hEcell (hi₂.trans hpq) ⟨hyi, hy.2⟩).2
      · exact absurd (hQE q hy.2) (Set.disjoint_left.mp (hEE p.1.2 q.1 hpq) (hPE p hy.1))
  have rowO : ∀ (o : Section34CompactOuterVertexIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .outerFace o → tgtO o ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtOBd o ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro o k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.outerFace o) nofun)
    | tetraBall t => exact hswap (rowR t (.outerFace o) nofun)
    | faceDisk s => exact hswap (rowD s (.outerFace o) nofun)
    | splitDisk e => exact hswap (rowE e (.outerFace o) nofun)
    | patch x => exact hswap (rowX x (.outerFace o) nofun)
    | faceArc a => exact hswap (rowA a (.outerFace o) nofun)
    | edgeArc i => exact hswap (rowI i (.outerFace o) nofun)
    | markedPoint p => exact hswap (rowP p (.outerFace o) nofun)
    | outerFace o' =>
      intro y hy
      refine Or.inl ?_
      have hoo : o ≠ o' := by
        rintro rfl
        exact hk rfl
      obtain ⟨e, hye⟩ :=
        hVV o.1 o'.1 (fun h => hoo (Subtype.ext h)) y (hOV o hy.1) (hOV o' hy.2)
      have hyB := hres.splitDisk_inter_outerFace_subset hVcell hEcell hEV o e ⟨hy.1, hye⟩
      rw [hEtile e] at hyB
      rcases hyB with hyI | hyQ
      · obtain ⟨i, -, hyi⟩ := mem_iUnion₂.mp hyI
        exact hIO i o ⟨hyi, hy.1⟩
      · obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hyQ
        have hoq : o.1.1 ⊆ q.1.1 := by
          rw [hq]
          exact hEV e o.1 y hye (hOV o hy.1)
        exact hQOB q o hoq hyq
    | outerArc q =>
      intro y hy
      exact Or.inl (hQOB q o (hEV q.1 o.1 y (hQE q hy.2) (hOV o hy.1)) hy.2)
  have rowQ : ∀ (q : Section34CompactOuterEdgeIndex K K') (k : Section34CompactLabelOf K K'),
      k ≠ .outerArc q → tgtQ q ∩ section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP
        tgtO tgtQ k ⊆ tgtQBd q ∪ section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd
          tgtIBd (fun _ => ∅) tgtOBd tgtQBd k := by
    intro q k hk
    cases k with
    | vertexBall w => exact hswap (rowV w (.outerArc q) nofun)
    | tetraBall t => exact hswap (rowR t (.outerArc q) nofun)
    | faceDisk s => exact hswap (rowD s (.outerArc q) nofun)
    | splitDisk e => exact hswap (rowE e (.outerArc q) nofun)
    | patch x => exact hswap (rowX x (.outerArc q) nofun)
    | faceArc a => exact hswap (rowA a (.outerArc q) nofun)
    | edgeArc i => exact hswap (rowI i (.outerArc q) nofun)
    | markedPoint p => exact hswap (rowP p (.outerArc q) nofun)
    | outerFace o => exact hswap (rowO o (.outerArc q) nofun)
    | outerArc q' =>
      intro y hy
      have hqq : q ≠ q' := by
        rintro rfl
        exact hk rfl
      exact absurd (hQE q' hy.2)
        (Set.disjoint_left.mp (hEE q.1 q'.1 fun h => hqq (Subtype.ext h)) (hQE q hy.1))
  cases k with
  | vertexBall w => exact rowV w k' (Ne.symm hkk)
  | tetraBall t => exact rowR t k' (Ne.symm hkk)
  | splitDisk e => exact rowE e k' (Ne.symm hkk)
  | faceDisk s => exact rowD s k' (Ne.symm hkk)
  | patch x => exact rowX x k' (Ne.symm hkk)
  | faceArc a => exact rowA a k' (Ne.symm hkk)
  | edgeArc i => exact rowI i k' (Ne.symm hkk)
  | markedPoint p => exact rowP p k' (Ne.symm hkk)
  | outerFace o => exact rowO o k' (Ne.symm hkk)
  | outerArc q => exact rowQ q k' (Ne.symm hkk)

theorem Section34CompactResidualPlus.boundedCell_recognition
    (hres : Section34CompactResidualPlus K K' H cV cVBd cE cEBd tgtD tgtA tgtP tgtR tgtRBd
      tgtX tgtXBd tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hdisk : Section34CompactFaceDiskFamily K K' cV cE cEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVcell : ∀ w, IsPLCellOn 3 (cV w) (cVBd w)) (hEcell : ∀ e, IsPLCellOn 2 (cE e) (cEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ cV w, y ∈ cV w' → ∃ e, y ∈ cE e)
    (hEV : ∀ e w, ∀ y ∈ cE e, y ∈ cV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (cE e) (cE e'))
    (hEint : ∀ e, cE e \ cEBd e ⊆ interior (⋃ w, cV w)) (hEU : ∀ e, ∃ w, cE e ⊆ cV w)
    (hst : ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
      Section34Incident s.1 t.1)
    {F : Section34CompactLabelOf K K' → Set (Section34CompactLabelOf K K')}
    (hF : ∀ l m, m ∈ F l ↔ Section34CompactCutLe m l) :
    (∀ l, section34BoundedCell cVBd tgtRBd cEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅)
        tgtOBd tgtQBd l =
      ⋃ m ∈ F l \ {l}, section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ m) ∧
    ∀ l m, section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ l ∩
        section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ m =
      ⋃ k ∈ F l ∩ F m, section34BoundedCell cV tgtR cE tgtD tgtX tgtA tgtI tgtP tgtO tgtQ k := by
  have hdim : ∀ m l : Section34CompactLabelOf K K', Section34CompactCutStep m l →
      section34BoundedDim m < section34BoundedDim l := fun m l h => by
    have := Section34CompactCutStep.dim_succ h
    omega
  refine boundary_eq_and_inter_eq_of_step (step := Section34CompactCutStep) hF hdim
    (hres.boundedCell_step_subset hdisk hVcell hEcell)
    (hres.boundedCell_boundary_subset hdisk hEV hEint hEU) (fun l => ?_)
    (hres.boundedCell_inter_subset hdisk hVcell hEcell hVV hEV hEE hEint hEU hst)
  obtain ⟨hDcell, -, -, -, -, hAcell, -⟩ := hdisk
  obtain ⟨hRcell, hXcell, hIcell, hOcell, hQcell, -⟩ := hres
  cases l with
  | vertexBall w => exact (hVcell w).boundary_subset
  | tetraBall t => exact (hRcell t).boundary_subset
  | splitDisk e => exact (hEcell e).boundary_subset
  | faceDisk s => exact (hDcell s).boundary_subset
  | patch x => exact (hXcell x).boundary_subset
  | faceArc a => exact (hAcell a).boundary_subset
  | edgeArc i => exact (hIcell i).boundary_subset
  | markedPoint p => exact empty_subset _
  | outerFace o => exact (hOcell o).boundary_subset
  | outerArc q => exact (hQcell q).boundary_subset

end Recognition

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem compactTargetRecognition (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hres : Section34CompactResidualPlus K K' H (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) tgtD tgtA tgtP tgtR tgtRBd tgtX tgtXBd
      tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hface : ∀ l m : Section34CompactLabelOf K K', src m ⊆ src l ↔ Section34CompactCutLe m l)
    (tc tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (htc : tc = section34BoundedCell (section34CompactVertexBallImage src f₁) tgtR
      (section34CompactSplitDiskImage src f₁) tgtD tgtX tgtA tgtI tgtP tgtO tgtQ)
    (htcBd : tcBd = section34BoundedCell (section34CompactVertexBallImage srcBd f₁) tgtRBd
      (section34CompactSplitDiskImage srcBd f₁) tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅)
      tgtOBd tgtQBd) :
    (∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m) ∧
      ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k := by
  obtain ⟨-, hf₁, -⟩ := id hgraph
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hst⟩ := id hcut
  subst htc htcBd
  refine hres.boundedCell_recognition hdisk (hcut.isPLCellOn_vertexBallImage hf₁)
    (hcut.isPLCellOn_splitDiskImage hf₁)
    (fun w w' hww y hy hy' => hcut.exists_mem_splitDiskImage_of_ne hf₁ hww hy hy')
    (fun e w y hye hyw => hcut.subset_of_mem_splitDiskImage hf₁ hye hyw)
    (fun e e' hee => hcut.disjoint_splitDiskImage hf₁ hee)
    (hcut.splitDiskImage_sdiff_subset_interior hf₁) (fun e => ?_) hst
    (F := section34Face src) hface
  obtain ⟨w, w', -, -, he⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  refine ⟨w, ?_⟩
  rw [he]
  exact inter_subset_left

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
