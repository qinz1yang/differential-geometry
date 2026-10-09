/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellFaceRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Recognition

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {H : Finset Ea → Set M₂}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}
  {tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂}
  {tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂}
  {tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂}

theorem IsPLCellOn.interior_eq_empty_of_lt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (h : IsPLCellOn d S B)
    (hd : d < 3) : interior S = ∅ := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := h
  rw [← hu.image_interior, IsPLBall.interior_eq_empty_of_lt_finrank ⟨r, hr⟩ (by simpa using hd),
    image_empty]

theorem Section34CutStep.dim_lt {m l : Section34CutLabelOf 𝒦 𝒦'} (h : Section34CutStep m l) :
    section34Dim m < section34Dim l := by
  cases m <;> cases l <;> simp_all [Section34CutStep, section34Dim]

theorem Section34FaceDiskFamily.exists_faceArc_of_mem
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {s : Section34SimplexIndex 𝒦 3} {w : Section34VertexIndex 𝒦 𝒦'} {y : M₂}
    (hys : y ∈ tgtD s) (hyw : y ∈ tgtV w) :
    ∃ a : Section34ArcIndex 𝒦 𝒦', a.1.1 = s ∧ a.1.2 = w ∧ y ∈ tgtA a := by
  obtain ⟨-, -, hDU, -, -, -, hAeq, hDVout, -⟩ := hdisk
  have hinc : Section34Incident w.1 s.1 := by
    by_contra hn
    have h : y ∈ tgtD s ∩ tgtV w := ⟨hys, hyw⟩
    rw [hDVout s w hn] at h
    exact h
  have hyB : y ∈ tgtDBd s := by
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hyw⟩⟩
  refine ⟨⟨(s, w), hinc⟩, rfl, rfl, ?_⟩
  rw [← hAeq]
  exact ⟨hyB, hyw⟩

theorem Section34FaceDiskFamily.exists_markedPoint_of_mem
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧ tgtE e = tgtV w ∩ tgtV w')
    (hEint : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident e.1 s.1 → tgtE e \ tgtEBd e ⊆ interior (⋃ w, tgtV w))
    {s : Section34SimplexIndex 𝒦 3} {e : Section34EdgeIndex 𝒦 𝒦'} {y : M₂}
    (hys : y ∈ tgtD s) (hye : y ∈ tgtE e) :
    ∃ p : Section34MarkIndex 𝒦 𝒦', p.1.1 = s ∧ p.1.2 = e ∧ y ∈ tgtP p := by
  obtain ⟨-, -, hDU, hDBdF, -, -, -, hDVout, -, hPeq, -, -⟩ := hdisk
  obtain ⟨w, w', hew, hEeq⟩ := hEends e
  have hyVV : y ∈ tgtV w ∩ tgtV w' := by
    rw [← hEeq]
    exact hye
  have hinc : ∀ v : Section34VertexIndex 𝒦 𝒦', y ∈ tgtV v → Section34Incident v.1 s.1 := by
    intro v hyv
    by_contra hn
    have h : y ∈ tgtD s ∩ tgtV v := ⟨hys, hyv⟩
    rw [hDVout s v hn] at h
    exact h
  have hes : Section34Incident e.1 s.1 := by
    change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [hew]
    exact union_subset (hinc w hyVV.1) (hinc w' hyVV.2)
  have hyDB : y ∈ tgtDBd s := by
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hyVV.1⟩⟩
  have hyEB : y ∈ tgtEBd e := by
    by_contra hyB
    exact Set.disjoint_left.mp disjoint_interior_frontier (hEint e s hes ⟨hye, hyB⟩)
      (hDBdF s hyDB)
  refine ⟨⟨(s, e), hes⟩, rfl, rfl, ?_⟩
  rw [← hPeq]
  exact ⟨hyDB, hyEB⟩

theorem Section34ResidualPlus.exists_patch_of_mem
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    {t : Section34SimplexIndex 𝒦 4} {w : Section34VertexIndex 𝒦 𝒦'} {y : M₂}
    (hyt : y ∈ tgtR t) (hyw : y ∈ tgtV w) :
    ∃ x : Section34PatchIndex 𝒦 𝒦', x.1.1 = t ∧ x.1.2 = w ∧ y ∈ tgtX x := by
  obtain ⟨-, -, -, hXeq, hRVout, -⟩ := hres
  have hinc : Section34Incident w.1 t.1 := by
    by_contra hn
    have h : y ∈ tgtR t ∩ tgtV w := ⟨hyt, hyw⟩
    rw [hRVout t w hn] at h
    exact h
  refine ⟨⟨(t, w), hinc⟩, rfl, rfl, ?_⟩
  rw [← hXeq]
  exact ⟨hyt, hyw⟩

theorem Section34ResidualPlus.exists_edgeArc_of_mem
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    {t : Section34SimplexIndex 𝒦 4} {e : Section34EdgeIndex 𝒦 𝒦'} {y : M₂}
    (hyt : y ∈ tgtR t) (hye : y ∈ tgtE e) :
    ∃ i : Section34EdgeArcIndex 𝒦 𝒦', i.1.1 = t ∧ i.1.2 = e ∧ y ∈ tgtI i := by
  obtain ⟨-, -, -, -, -, -, -, -, hIeq, hREout, -⟩ := hres
  have hinc : Section34Incident e.1 t.1 := by
    by_contra hn
    have h : y ∈ tgtR t ∩ tgtE e := ⟨hyt, hye⟩
    rw [hREout t e hn] at h
    exact h
  refine ⟨⟨(t, e), hinc⟩, rfl, rfl, ?_⟩
  rw [← hIeq]
  exact ⟨hyt, hye⟩

theorem Section34ResidualPlus.incident_of_mem_tetraBall_faceDisk
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    {t : Section34SimplexIndex 𝒦 4} {s : Section34SimplexIndex 𝒦 3} {y : M₂}
    (hyt : y ∈ tgtR t) (hys : y ∈ tgtD s) : Section34Incident s.1 t.1 := by
  obtain ⟨-, -, -, -, -, -, hRDout, -⟩ := hres
  by_contra hn
  have h : y ∈ tgtR t ∩ tgtD s := ⟨hyt, hys⟩
  rw [hRDout t s hn] at h
  exact h

theorem Section34ResidualPlus.exists_patch_faceArc_subset
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hst : ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1)
    (a : Section34ArcIndex 𝒦 𝒦') :
    ∃ x : Section34PatchIndex 𝒦 𝒦', x.1.2 = a.1.2 ∧ tgtA a ⊆ tgtXBd x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hXBd, -⟩ := hres
  obtain ⟨t, ht⟩ := hst a.1.1
  refine ⟨⟨(t, a.1.2), Subset.trans a.2 (convexHull_min ht (convex_convexHull ℝ _))⟩, rfl, ?_⟩
  intro y hy
  rw [hXBd]
  exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨rfl, ht⟩, hy⟩)

theorem Section34ResidualPlus.cell_step_subset_of_tiling
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hVcell : ∀ w, IsPLCellOn 3 (tgtV w) (tgtVBd w))
    (hEcell : ∀ e, IsPLCellOn 2 (tgtE e) (tgtEBd e)) (m l : Section34CutLabelOf 𝒦 𝒦')
    (h : Section34CutStep m l) :
    section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP m ⊆
      section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) l := by
  obtain ⟨-, -, -, -, -, -, hAeq, -, -, hPeq, -, hABd⟩ := hdisk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hIsub, hRBd, hIBd, hXBd, -, -⟩ := hres
  have hEVB : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
      w.1 ⊆ e.1 → tgtE e ⊆ tgtVBd w := fun e w hwe y hy => by
    rw [hVtile w]
    exact Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hy⟩)
  have hXVB : ∀ (x : Section34PatchIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
      x.1.2 = w → tgtX x ⊆ tgtVBd w := fun x w hxw y hy => by
    rw [hVtile w]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, hxw, hy⟩)
  have hDRB : ∀ (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4),
      Section34Incident s.1 t.1 → tgtD s ⊆ tgtRBd t := fun s t hst y hy => by
    rw [hRBd t]
    exact Or.inl (mem_iUnion₂.mpr ⟨s, hst, hy⟩)
  have hXRB : ∀ (x : Section34PatchIndex 𝒦 𝒦') (t : Section34SimplexIndex 𝒦 4),
      x.1.1 = t → tgtX x ⊆ tgtRBd t := fun x t hxt y hy => by
    rw [hRBd t]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, hxt, hy⟩)
  have hIEB : ∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      i.1.2 = e → tgtI i ⊆ tgtEBd e := fun i e hie => by
    rw [← hie]
    exact hIsub i
  have hADB : ∀ (a : Section34ArcIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      a.1.1 = s → tgtA a ⊆ tgtDBd s := fun a s has => by
    rw [← has, ← hAeq a]
    exact inter_subset_left
  have hAXB : ∀ (a : Section34ArcIndex 𝒦 𝒦') (x : Section34PatchIndex 𝒦 𝒦'),
      a.1.2 = x.1.2 → Section34Incident a.1.1.1 x.1.1.1 → tgtA a ⊆ tgtXBd x :=
    fun a x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨h₁, h₂⟩, hy⟩)
  have hIXB : ∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (x : Section34PatchIndex 𝒦 𝒦'),
      i.1.1 = x.1.1 → x.1.2.1 ⊆ i.1.2.1 → tgtI i ⊆ tgtXBd x :=
    fun i x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨h₁, h₂⟩, hy⟩)
  have hPIB : ∀ (p : Section34MarkIndex 𝒦 𝒦') (i : Section34EdgeArcIndex 𝒦 𝒦'),
      p.1.2 = i.1.2 → Section34Incident p.1.1.1 i.1.1.1 → tgtP p ⊆ tgtIBd i :=
    fun p i h₁ h₂ y hy => by
      rw [hIBd i]
      exact mem_iUnion₂.mpr ⟨p, ⟨h₁, h₂⟩, hy⟩
  have hPAB : ∀ (p : Section34MarkIndex 𝒦 𝒦') (a : Section34ArcIndex 𝒦 𝒦'),
      p.1.1 = a.1.1 → a.1.2.1 ⊆ p.1.2.1 → tgtP p ⊆ tgtABd a := by
    intro p a h₁ h₂ y hy
    have hyP : y ∈ tgtDBd p.1.1 ∩ tgtEBd p.1.2 := by
      rw [hPeq p]
      exact hy
    have hyE : y ∈ tgtE p.1.2 := (hEcell p.1.2).boundary_subset hyP.2
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
  · exact hIEB _ _ h
  · exact hIXB _ _ h.1 h.2
  · exact hPAB _ _ h.1 h.2
  · exact hPIB _ _ h.1 h.2

theorem Section34ResidualPlus.cell_boundary_subset_of_tiling
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hEtile : ∀ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e =
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.2 = e), tgtI i)
    (hEV : ∀ e w, ∀ y ∈ tgtE e, y ∈ tgtV w → w.1 ⊆ e.1)
    (hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧ tgtE e = tgtV w ∩ tgtV w')
    (hEint : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident e.1 s.1 → tgtE e \ tgtEBd e ⊆ interior (⋃ w, tgtV w))
    (l : Section34CutLabelOf 𝒦 𝒦') :
    section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) l ⊆
      ⋃ m, ⋃ (_ : Section34CutStep m l),
        section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP m := by
  obtain ⟨hDcell, -, hDU, -, -, -, hAeq, -, -, -, -, hABd⟩ := id hdisk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hRBd, hIBd, hXBd, -, -⟩ := hres
  intro y hy
  cases l with
  | vertexBall w =>
    change y ∈ tgtVBd w at hy
    rw [hVtile w] at hy
    rcases hy with hy | hy
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.splitDisk e, he, hye⟩
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.patch x, hx, hyx⟩
  | tetraBall t =>
    change y ∈ tgtRBd t at hy
    rw [hRBd t] at hy
    rcases hy with hy | hy
    · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.faceDisk s, hs, hys⟩
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨.patch x, hx, hyx⟩
  | splitDisk e =>
    change y ∈ tgtEBd e at hy
    rw [hEtile e] at hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨.edgeArc i, hi, hyi⟩
  | faceDisk s =>
    change y ∈ tgtDBd s at hy
    have hyU : y ∈ tgtD s ∩ ⋃ w, tgtV w := by
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
    have hyA : y ∈ tgtDBd a.1.1 ∩ tgtV a.1.2 := by
      rw [hAeq a]
      exact hya
    obtain ⟨p, hp₁, hp₂, hyp⟩ :=
      hdisk.exists_markedPoint_of_mem hEends hEint ((hDcell a.1.1).boundary_subset hyA.1) hye
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

theorem Section34ResidualPlus.cell_inter_subset_ball_disk_patch_of_tiling
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hEcell : ∀ e, IsPLCellOn 2 (tgtE e) (tgtEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ tgtV w, y ∈ tgtV w' → ∃ e, y ∈ tgtE e)
    (hEV : ∀ e w, ∀ y ∈ tgtE e, y ∈ tgtV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (tgtE e) (tgtE e'))
    (hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧ tgtE e = tgtV w ∩ tgtV w')
    (hst : ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1) :
    (∀ (w : Section34VertexIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .vertexBall w → tgtV w ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtVBd w ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k) ∧
    (∀ (t : Section34SimplexIndex 𝒦 4) (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .tetraBall t → tgtR t ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtRBd t ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k) ∧
    (∀ (s : Section34SimplexIndex 𝒦 3) (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .faceDisk s → tgtD s ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtDBd s ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k) ∧
    (∀ (e : Section34EdgeIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .splitDisk e → tgtE e ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtEBd e ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k) ∧
    ∀ (x : Section34PatchIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .patch x → tgtX x ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtXBd x ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
  obtain ⟨hDcell, -, hDU, -, hDD, -, hAeq, -, -, hPeq, -, hABd⟩ := id hdisk
  obtain ⟨-, hXcell, -, hXeq, -, -, -, hRR, hIeq, -, hIsub, hRBd, -, hXBd, -, -⟩ := id hres
  have hEB : ∀ e, tgtEBd e ⊆ tgtE e := fun e => (hEcell e).boundary_subset
  have hDB : ∀ s, tgtDBd s ⊆ tgtD s := fun s => (hDcell s).boundary_subset
  have hXB : ∀ x, tgtXBd x ⊆ tgtX x := fun x => (hXcell x).boundary_subset
  have hEU : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w, tgtE e ⊆ tgtV w := fun e => by
    obtain ⟨w, w', -, hEeq⟩ := hEends e
    refine ⟨w, ?_⟩
    rw [hEeq]
    exact inter_subset_left
  have hEVB : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
      w.1 ⊆ e.1 → tgtE e ⊆ tgtVBd w := fun e w hwe y hy => by
    rw [hVtile w]
    exact Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hy⟩)
  have hXVB : ∀ x : Section34PatchIndex 𝒦 𝒦', tgtX x ⊆ tgtVBd x.1.2 := fun x y hy => by
    rw [hVtile x.1.2]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, rfl, hy⟩)
  have hXV : ∀ x : Section34PatchIndex 𝒦 𝒦', tgtX x ⊆ tgtV x.1.2 := fun x => by
    rw [← hXeq x]
    exact inter_subset_right
  have hXR : ∀ x : Section34PatchIndex 𝒦 𝒦', tgtX x ⊆ tgtR x.1.1 := fun x => by
    rw [← hXeq x]
    exact inter_subset_left
  have hAV : ∀ a : Section34ArcIndex 𝒦 𝒦', tgtA a ⊆ tgtV a.1.2 := fun a => by
    rw [← hAeq a]
    exact inter_subset_right
  have hAD : ∀ a : Section34ArcIndex 𝒦 𝒦', tgtA a ⊆ tgtD a.1.1 := fun a => by
    refine Subset.trans ?_ (hDB a.1.1)
    rw [← hAeq a]
    exact inter_subset_left
  have hIE : ∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtI i ⊆ tgtE i.1.2 := fun i => by
    rw [← hIeq i]
    exact inter_subset_right
  have hPEB : ∀ p : Section34MarkIndex 𝒦 𝒦', tgtP p ⊆ tgtEBd p.1.2 := fun p => by
    rw [← hPeq p]
    exact inter_subset_right
  have hPE : ∀ p : Section34MarkIndex 𝒦 𝒦', tgtP p ⊆ tgtE p.1.2 :=
    fun p => (hPEB p).trans (hEB _)
  have hAXB : ∀ (a : Section34ArcIndex 𝒦 𝒦') (x : Section34PatchIndex 𝒦 𝒦'),
      a.1.2 = x.1.2 → Section34Incident a.1.1.1 x.1.1.1 → tgtA a ⊆ tgtXBd x :=
    fun a x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨h₁, h₂⟩, hy⟩)
  have hIXB : ∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (x : Section34PatchIndex 𝒦 𝒦'),
      i.1.1 = x.1.1 → x.1.2.1 ⊆ i.1.2.1 → tgtI i ⊆ tgtXBd x :=
    fun i x h₁ h₂ y hy => by
      rw [hXBd x]
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨h₁, h₂⟩, hy⟩)
  have hDRB : ∀ (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4),
      Section34Incident s.1 t.1 → tgtD s ⊆ tgtRBd t := fun s t h y hy => by
    rw [hRBd t]
    exact Or.inl (mem_iUnion₂.mpr ⟨s, h, hy⟩)
  have hXRB : ∀ x : Section34PatchIndex 𝒦 𝒦', tgtX x ⊆ tgtRBd x.1.1 := fun x y hy => by
    rw [hRBd x.1.1]
    exact Or.inr (mem_iUnion₂.mpr ⟨x, rfl, hy⟩)
  have hAVB : ∀ a : Section34ArcIndex 𝒦 𝒦', tgtA a ⊆ tgtVBd a.1.2 := fun a => by
    obtain ⟨x, hx₂, hax⟩ := hres.exists_patch_faceArc_subset hst a
    rw [← hx₂]
    exact (hax.trans (hXB x)).trans (hXVB x)
  have hDVB : ∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
      ∀ y ∈ tgtD s, y ∈ tgtV w → y ∈ tgtDBd s := by
    intro s w y hys hyw
    rw [← hDU s]
    exact ⟨hys, mem_iUnion.mpr ⟨w, hyw⟩⟩
  have hDEV : ∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtD s, y ∈ tgtE e → y ∈ tgtDBd s := by
    intro s e y hys hye
    obtain ⟨w, hw⟩ := hEU e
    exact hDVB s w y hys (hw hye)
  have hRRD : ∀ t t' : Section34SimplexIndex 𝒦 4, t ≠ t' → ∀ y ∈ tgtR t, y ∈ tgtR t' →
      ∃ s, y ∈ tgtD s := fun t t' htt y hy hy' => mem_iUnion.mp (hRR t t' htt ⟨hy, hy'⟩)
  have hVVB : ∀ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' → ∀ y ∈ tgtV w, y ∈ tgtV w' →
      y ∈ tgtVBd w := by
    intro w w' hww y hy hy'
    obtain ⟨e, he⟩ := hVV w w' hww y hy hy'
    exact hEVB e w (hEV e w y he hy) he
  have hVEB : ∀ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtV w, y ∈ tgtE e → y ∈ tgtVBd w :=
    fun w e y hy he => hEVB e w (hEV e w y he hy) he
  have hRVB : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ∀ y ∈ tgtR t, y ∈ tgtV w → y ∈ tgtRBd t := by
    intro t w y hyt hyw
    obtain ⟨x, hx₁, -, hyx⟩ := hres.exists_patch_of_mem hyt hyw
    rw [← hx₁]
    exact hXRB x hyx
  have hRDB : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ∀ y ∈ tgtR t, y ∈ tgtD s → y ∈ tgtRBd t :=
    fun t s y hyt hys => hDRB s t (hres.incident_of_mem_tetraBall_faceDisk hyt hys) hys
  have hREB : ∀ (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtR t, y ∈ tgtE e → y ∈ tgtRBd t := by
    intro t e y hyt hye
    obtain ⟨w, hw⟩ := hEU e
    exact hRVB t w y hyt (hw hye)
  have hXD : ∀ (x : Section34PatchIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      ∀ y ∈ tgtX x, y ∈ tgtD s → y ∈ tgtXBd x := by
    intro x s y hyx hys
    have hsx := hres.incident_of_mem_tetraBall_faceDisk (hXR x hyx) hys
    obtain ⟨a, ha₁, ha₂, hya⟩ := hdisk.exists_faceArc_of_mem hys (hXV x hyx)
    have hax : Section34Incident a.1.1.1 x.1.1.1 := by
      rw [ha₁]
      exact hsx
    exact hAXB a x ha₂ hax hya
  have hXE : ∀ (x : Section34PatchIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtX x, y ∈ tgtE e → y ∈ tgtXBd x := by
    intro x e y hyx hye
    obtain ⟨i, hi₁, hi₂, hyi⟩ := hres.exists_edgeArc_of_mem (hXR x hyx) hye
    have hxi : x.1.2.1 ⊆ i.1.2.1 := by
      rw [hi₂]
      exact hEV e x.1.2 y hye (hXV x hyx)
    exact hIXB i x hi₁ hxi hyi
  have hAE : ∀ (a : Section34ArcIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtA a, y ∈ tgtE e → y ∈ tgtABd a := by
    intro a e y hya hye
    rw [hABd a]
    exact ⟨hya, mem_iUnion.mpr ⟨e, hye⟩⟩
  have hEsame : ∀ (e e' : Section34EdgeIndex 𝒦 𝒦') (Z : Set M₂), Z ⊆ tgtEBd e' →
      ∀ y ∈ tgtE e, y ∈ Z → y ∈ tgtEBd e := by
    intro e e' Z hZ y hye hyZ
    by_cases hee : e = e'
    · subst hee
      exact hZ hyZ
    · exact absurd (hEB e' (hZ hyZ)) (Set.disjoint_left.mp (hEE e e' hee) hye)
  have hswap : ∀ {A B Ab Bb : Set M₂}, B ∩ A ⊆ Bb ∪ Ab → A ∩ B ⊆ Ab ∪ Bb :=
    fun h y hy => Or.symm (h ⟨hy.2, hy.1⟩)
  have rowV : ∀ (w : Section34VertexIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .vertexBall w → tgtV w ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtVBd w ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowR : ∀ (t : Section34SimplexIndex 𝒦 4) (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .tetraBall t → tgtR t ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtRBd t ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowD : ∀ (s : Section34SimplexIndex 𝒦 3) (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .faceDisk s → tgtD s ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtDBd s ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowE : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .splitDisk e → tgtE e ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtEBd e ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowX : ∀ (x : Section34PatchIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .patch x → tgtX x ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtXBd x ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  exact ⟨rowV, rowR, rowD, rowE, rowX⟩

theorem Section34ResidualPlus.cell_inter_subset_of_tiling
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hEcell : ∀ e, IsPLCellOn 2 (tgtE e) (tgtEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ tgtV w, y ∈ tgtV w' → ∃ e, y ∈ tgtE e)
    (hEV : ∀ e w, ∀ y ∈ tgtE e, y ∈ tgtV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (tgtE e) (tgtE e'))
    (hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧ tgtE e = tgtV w ∩ tgtV w')
    (hEint : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident e.1 s.1 → tgtE e \ tgtEBd e ⊆ interior (⋃ w, tgtV w))
    (hst : ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1)
    (k k' : Section34CutLabelOf 𝒦 𝒦') (hkk : k ≠ k') :
    section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ∩
        section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k' ⊆
      section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) k ∪
        section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) k' := by
  obtain ⟨rowV, rowR, rowD, rowE, rowX⟩ :=
    hres.cell_inter_subset_ball_disk_patch_of_tiling hdisk hVtile hEcell hVV hEV hEE hEends hst
  obtain ⟨hDcell, -, -, -, hDD, -, hAeq, -, -, hPeq, -, hABd⟩ := id hdisk
  obtain ⟨-, -, -, -, -, -, -, hRR, hIeq, -, -, -, hIBd, -, -, -⟩ := id hres
  have hEB : ∀ e, tgtEBd e ⊆ tgtE e := fun e => (hEcell e).boundary_subset
  have hDB : ∀ s, tgtDBd s ⊆ tgtD s := fun s => (hDcell s).boundary_subset
  have hAV : ∀ a : Section34ArcIndex 𝒦 𝒦', tgtA a ⊆ tgtV a.1.2 := fun a => by
    rw [← hAeq a]
    exact inter_subset_right
  have hAD : ∀ a : Section34ArcIndex 𝒦 𝒦', tgtA a ⊆ tgtD a.1.1 := fun a => by
    refine Subset.trans ?_ (hDB a.1.1)
    rw [← hAeq a]
    exact inter_subset_left
  have hIE : ∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtI i ⊆ tgtE i.1.2 := fun i => by
    rw [← hIeq i]
    exact inter_subset_right
  have hIR : ∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtI i ⊆ tgtR i.1.1 := fun i => by
    rw [← hIeq i]
    exact inter_subset_left
  have hPE : ∀ p : Section34MarkIndex 𝒦 𝒦', tgtP p ⊆ tgtE p.1.2 := fun p => by
    refine Subset.trans ?_ (hEB p.1.2)
    rw [← hPeq p]
    exact inter_subset_right
  have hPD : ∀ p : Section34MarkIndex 𝒦 𝒦', tgtP p ⊆ tgtD p.1.1 := fun p => by
    refine Subset.trans ?_ (hDB p.1.1)
    rw [← hPeq p]
    exact inter_subset_left
  have hPIB : ∀ (p : Section34MarkIndex 𝒦 𝒦') (i : Section34EdgeArcIndex 𝒦 𝒦'),
      p.1.2 = i.1.2 → Section34Incident p.1.1.1 i.1.1.1 → tgtP p ⊆ tgtIBd i :=
    fun p i h₁ h₂ y hy => by
      rw [hIBd i]
      exact mem_iUnion₂.mpr ⟨p, ⟨h₁, h₂⟩, hy⟩
  have hRRD : ∀ t t' : Section34SimplexIndex 𝒦 4, t ≠ t' → ∀ y ∈ tgtR t, y ∈ tgtR t' →
      ∃ s, y ∈ tgtD s := fun t t' htt y hy hy' => mem_iUnion.mp (hRR t t' htt ⟨hy, hy'⟩)
  have hAE : ∀ (a : Section34ArcIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      ∀ y ∈ tgtA a, y ∈ tgtE e → y ∈ tgtABd a := by
    intro a e y hya hye
    rw [hABd a]
    exact ⟨hya, mem_iUnion.mpr ⟨e, hye⟩⟩
  have hID : ∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      ∀ y ∈ tgtI i, y ∈ tgtD s → y ∈ tgtIBd i := by
    intro i s y hyi hys
    have hsi := hres.incident_of_mem_tetraBall_faceDisk (hIR i hyi) hys
    obtain ⟨p, hp₁, hp₂, hyp⟩ := hdisk.exists_markedPoint_of_mem hEends hEint hys (hIE i hyi)
    have hpi : Section34Incident p.1.1.1 i.1.1.1 := by
      rw [hp₁]
      exact hsi
    exact hPIB p i hp₂ hpi hyp
  have hswap : ∀ {A B Ab Bb : Set M₂}, B ∩ A ⊆ Bb ∪ Ab → A ∩ B ⊆ Ab ∪ Bb :=
    fun h y hy => Or.symm (h ⟨hy.2, hy.1⟩)
  have rowA : ∀ (a : Section34ArcIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .faceArc a → tgtA a ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtABd a ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowI : ∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .edgeArc i → tgtI i ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        tgtIBd i ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  have rowP : ∀ (p : Section34MarkIndex 𝒦 𝒦') (k : Section34CutLabelOf 𝒦 𝒦'),
      k ≠ .markedPoint p → tgtP p ∩ section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k ⊆
        ∅ ∪ section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
          (fun _ => ∅) k := by
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
  cases k with
  | vertexBall w => exact rowV w k' (Ne.symm hkk)
  | tetraBall t => exact rowR t k' (Ne.symm hkk)
  | splitDisk e => exact rowE e k' (Ne.symm hkk)
  | faceDisk s => exact rowD s k' (Ne.symm hkk)
  | patch x => exact rowX x k' (Ne.symm hkk)
  | faceArc a => exact rowA a k' (Ne.symm hkk)
  | edgeArc i => exact rowI i k' (Ne.symm hkk)
  | markedPoint p => exact rowP p k' (Ne.symm hkk)

theorem Section34ResidualPlus.cell_recognition_of_tiling
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hEtile : ∀ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e =
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.2 = e), tgtI i)
    (hVcell : ∀ w, IsPLCellOn 3 (tgtV w) (tgtVBd w))
    (hEcell : ∀ e, IsPLCellOn 2 (tgtE e) (tgtEBd e))
    (hVV : ∀ w w', w ≠ w' → ∀ y ∈ tgtV w, y ∈ tgtV w' → ∃ e, y ∈ tgtE e)
    (hEV : ∀ e w, ∀ y ∈ tgtE e, y ∈ tgtV w → w.1 ⊆ e.1)
    (hEE : ∀ e e', e ≠ e' → Disjoint (tgtE e) (tgtE e'))
    (hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧ tgtE e = tgtV w ∩ tgtV w')
    (hEint : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident e.1 s.1 → tgtE e \ tgtEBd e ⊆ interior (⋃ w, tgtV w))
    (hst : ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1)
    {F : Section34CutLabelOf 𝒦 𝒦' → Set (Section34CutLabelOf 𝒦 𝒦')}
    (hF : ∀ l m, m ∈ F l ↔ Section34CutLe m l) :
    (∀ l, section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) l =
      ⋃ m ∈ F l \ {l}, section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP m) ∧
    ∀ l m, section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP l ∩
        section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP m =
      ⋃ k ∈ F l ∩ F m, section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP k := by
  refine boundary_eq_and_inter_eq_of_step (step := Section34CutStep) hF
    (fun m l h => Section34CutStep.dim_lt h)
    (hres.cell_step_subset_of_tiling hdisk hVtile hVcell hEcell)
    (hres.cell_boundary_subset_of_tiling hdisk hVtile hEtile hEV hEends hEint) (fun l => ?_)
    (hres.cell_inter_subset_of_tiling hdisk hVtile hEcell hVV hEV hEE hEends hEint hst)
  obtain ⟨hDcell, -, -, -, -, hAcell, -⟩ := hdisk
  obtain ⟨hRcell, hXcell, hIcell, -⟩ := hres
  cases l with
  | vertexBall w => exact (hVcell w).boundary_subset
  | tetraBall t => exact (hRcell t).boundary_subset
  | splitDisk e => exact (hEcell e).boundary_subset
  | faceDisk s => exact (hDcell s).boundary_subset
  | patch x => exact (hXcell x).boundary_subset
  | faceArc a => exact (hAcell a).boundary_subset
  | edgeArc i => exact (hIcell i).boundary_subset
  | markedPoint p => exact empty_subset _

end Recognition

section Diagram

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}
  {tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂}
  {tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂}
  {tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem section34TargetRecognition_of_tiling
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd
      tgtP)
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w ⊆
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x)
    (hEtile : ∀ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e ⊆
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.2 = e), tgtI i)
    (hface : ∀ l m : Section34CutLabelOf 𝒦 𝒦', src m ⊆ src l ↔ Section34CutLe m l)
    (tc tcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₂)
    (htc : tc = section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP)
    (htcBd : tcBd = section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
      fun _ => ∅) :
    (∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m) ∧
      ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k := by
  obtain ⟨hcut, hctrl, hgraph, hext, -, htgtV, htgtE, hVcell, hEcell, hEVBd, hVVE, -, -, -,
    -, -, -⟩ := hdata
  obtain ⟨-, -, hf₁, -⟩ := id hgraph
  have hinj : InjOn f₁ (section34CutNeighborhood src) := hf₁.injOn
  have hEc' : ∀ e, IsPLCellOn 2 (tgtE e) (section34SplitDiskImage srcBd f₁ e) := fun e => by
    rw [htgtE e]
    exact hcut.isPLCellOn_splitDiskImage hf₁ e
  have hEBd : ∀ e, tgtEBd e = section34SplitDiskImage srcBd f₁ e :=
    fun e => (hEcell e).boundary_eq (hEc' e)
  have hV : tgtV = section34VertexBallImage src f₁ := funext htgtV
  have hE : tgtE = section34SplitDiskImage src f₁ := funext htgtE
  subst hV hE htc htcBd
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, -, -, -, -, hchart⟩ := hctrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, hst⟩ :=
    id hcut
  obtain ⟨hRcell, hXcell, -, hXeq, -, -, -, -, -, -, hIsub, -⟩ := id hres
  have hEVB : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'), w.1 ⊆ e.1 →
      section34SplitDiskImage src f₁ e ⊆ tgtVBd w := by
    intro e w hwe
    obtain ⟨a, b, -, hab, hsrc⟩ := hends e
    refine hEVBd e w ?_
    rw [hsrc]
    rcases eq_or_eq_of_section34VertexIndex_subset e hab hwe with rfl | rfl
    · exact inter_subset_left
    · exact inter_subset_right
  have hXVB : ∀ x : Section34PatchIndex 𝒦 𝒦', tgtX x ⊆ tgtVBd x.1.2 := by
    intro x y hy
    have hy' : y ∈ tgtR x.1.1 ∩ section34VertexBallImage src f₁ x.1.2 := by
      rw [hXeq x]
      exact hy
    rw [(hVcell x.1.2).boundary_eq_frontier, (hVcell x.1.2).isCompact.isClosed.frontier_eq]
    refine ⟨hy'.2, fun hyi => ?_⟩
    obtain ⟨z, hzV, hzR⟩ := mem_closure_iff.mp ((hRcell x.1.1).subset_closure_interior hy'.1)
      _ isOpen_interior hyi
    have hsub : interior (section34VertexBallImage src f₁ x.1.2) ∩ interior (tgtR x.1.1) ⊆
        interior (tgtX x) := by
      refine interior_maximal ?_ (isOpen_interior.inter isOpen_interior)
      rw [← hXeq x]
      exact fun v hv => ⟨interior_subset hv.2, interior_subset hv.1⟩
    have hz := hsub ⟨hzV, hzR⟩
    rw [(hXcell x).interior_eq_empty_of_lt (by norm_num)] at hz
    exact hz
  have hVtile' : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w =
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), section34SplitDiskImage src f₁ e) ∪
        ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x := by
    refine fun w => Subset.antisymm (hVtile w) (union_subset
      (iUnion₂_subset fun e hwe => hEVB e w hwe) (iUnion₂_subset fun x hxw => ?_))
    rw [← hxw]
    exact hXVB x
  have hEtile' : ∀ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e =
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.2 = e), tgtI i := by
    refine fun e => Subset.antisymm (hEtile e) (iUnion₂_subset fun i hie => ?_)
    rw [← hie]
    exact hIsub i
  refine hres.cell_recognition_of_tiling hdisk hVtile' hEtile' hVcell hEcell
    (fun w w' hww y hy hy' => mem_iUnion.mp (hVVE w w' hww ⟨hy, hy'⟩))
    (fun e w y hye hyw => hcut.subset_of_mem_splitDiskImage hinj hye hyw)
    (fun e e' hee => hcut.disjoint_splitDiskImage hinj hee) (fun e => ?_) (fun e s hes => ?_)
    hst (F := section34Face src) hface
  · obtain ⟨w, w', -, hew, heq⟩ := hcut.splitDiskImage_eq_inter hinj e
    exact ⟨w, w', hew, heq⟩
  · obtain ⟨t, hst'⟩ := hst s
    obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
    have hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
        section34VertexBallImage src f₁ w ⊆ c.source := by
      intro w hwe x hx
      have hwt : Section34Incident w.1 t.1 := Subset.trans (Finset.coe_subset.mpr hwe)
        (Subset.trans hes (convexHull_min hst' (convex_convexHull ℝ _)))
      exact hHc (interior_subset (hext1 t (Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hx⟩))))
    rw [hEBd e]
    exact (hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc hVc).trans
      (interior_mono (iUnion₂_subset fun w _ => subset_iUnion (section34VertexBallImage src f₁) w))

end Diagram

end DifferentialGeometry.Topology.PiecewiseLinear
