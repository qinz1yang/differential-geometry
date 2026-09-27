/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {f₁ : M₁ → M₂} {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

theorem Section34FaceDiskFamily.faceDisk_inter_splitDisk_subset
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦') :
    tgtD s ∩ tgtE e ⊆ tgtDBd s ∩ tgtEBd e := by
  obtain ⟨hcut, -, hgraph, -, -, hV, hE, -⟩ := id hdata
  have hf₁ := hgraph.2.2.1
  obtain ⟨-, -, hD3, hD4, -⟩ := id hdisk
  rintro z ⟨hzD, hzE⟩
  have hzE' : z ∈ section34SplitDiskImage src f₁ e := by rwa [hE e] at hzE
  obtain ⟨w, w', -, -, he⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have hzV : z ∈ ⋃ v, tgtV v := by
    rw [he] at hzE'
    refine mem_iUnion.mpr ⟨w, ?_⟩
    rw [hV w]
    exact hzE'.1
  have hzDb : z ∈ tgtDBd s := by rw [← hD3 s]; exact ⟨hzD, hzV⟩
  refine ⟨hzDb, ?_⟩
  by_contra hzb
  obtain ⟨c, hc, hVc⟩ := hdata.exists_chart_vertexBalls_of_edge e
  have hVci : ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34VertexBallImage src f₁ w ⊆ c.source := by
    intro w hw
    rw [section34VertexBallImage, ← hV w]
    exact hVc w hw
  have hznot : z ∉ section34SplitDiskImage srcBd f₁ e := by
    rwa [← hdata.splitDisk_boundary_eq_image e]
  have hzint := hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc hVci ⟨hzE', hznot⟩
  apply (hD4 s hzDb).2
  refine interior_mono (iUnion₂_subset fun w _ => ?_) hzint
  rw [section34VertexBallImage, ← hV w]
  exact subset_iUnion tgtV w

theorem Section34FaceDiskFamily.faceDisk_inter_splitDisk_eq
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (p : Section34MarkIndex 𝒦 𝒦') :
    tgtD p.1.1 ∩ tgtE p.1.2 = tgtP p := by
  have hsub := hdisk.faceDisk_inter_splitDisk_subset hdata p.1.1 p.1.2
  obtain ⟨hD, -, -, -, -, -, -, -, -, hP, -⟩ := hdisk
  obtain ⟨-, -, -, -, -, -, -, -, hE, -⟩ := hdata
  rw [← hP p]
  exact Subset.antisymm hsub
    (inter_subset_inter (hD p.1.1).boundary_subset (hE p.1.2).boundary_subset)

theorem Section34FaceDiskFamily.faceDisk_inter_splitDisk_eq_empty
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) {s : Section34SimplexIndex 𝒦 3} {e : Section34EdgeIndex 𝒦 𝒦'}
    (hse : ¬ Section34Incident e.1 s.1) : tgtD s ∩ tgtE e = ∅ := by
  have hsub := hdisk.faceDisk_inter_splitDisk_subset hdata s e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hP, -⟩ := hdisk
  exact subset_eq_empty hsub (hP s e hse)

omit [FiniteDimensional ℝ Ea] in
theorem Section34FaceDiskFamily.faceDisk_inter_vertexBall_eq
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (a : Section34ArcIndex 𝒦 𝒦') : tgtD a.1.1 ∩ tgtV a.1.2 = tgtA a := by
  obtain ⟨hD, -, hD3, -, -, -, hA, -⟩ := hdisk
  rw [← hA a]
  apply Subset.antisymm
  · rintro z ⟨hzD, hzV⟩
    refine ⟨?_, hzV⟩
    rw [← hD3 a.1.1]
    exact ⟨hzD, mem_iUnion.mpr ⟨a.1.2, hzV⟩⟩
  · exact inter_subset_inter_left _ (hD a.1.1).boundary_subset

omit [FiniteDimensional ℝ Ea] in
theorem Section34FaceDiskFamily.exists_mem_faceArc_notMem_splitDisk
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (a : Section34ArcIndex 𝒦 𝒦') : ∃ z ∈ tgtA a, ∀ e : Section34EdgeIndex 𝒦 𝒦', z ∉ tgtE e := by
  obtain ⟨-, -, -, -, -, hA, -, -, -, -, -, hAb⟩ := hdisk
  obtain ⟨z, hzA, hzB⟩ := (hA a).sdiff_boundary_nonempty
  refine ⟨z, hzA, fun e hze => hzB ?_⟩
  rw [hAb a]
  exact ⟨hzA, mem_iUnion.mpr ⟨e, hze⟩⟩

theorem Section34FaceDiskFamily.exists_faceDisk_inter_splitDisk_eq_singleton
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦')
    (hse : Section34Incident e.1 s.1) :
    ∃ p : M₂, tgtD s ∩ tgtE e = {p} ∧ p ∈ tgtEBd e := by
  have heq := hdisk.faceDisk_inter_splitDisk_eq hdata ⟨(s, e), hse⟩
  obtain ⟨-, -, -, -, -, -, -, -, hP9, hP10, -⟩ := hdisk
  obtain ⟨p, hp⟩ := (hP9 ⟨(s, e), hse⟩).exists_eq_singleton
  refine ⟨p, heq.trans hp, ?_⟩
  have hpm : p ∈ tgtP ⟨(s, e), hse⟩ := hp.symm ▸ mem_singleton p
  rw [← hP10 ⟨(s, e), hse⟩] at hpm
  exact hpm.2

end DifferentialGeometry.Topology.PiecewiseLinear
