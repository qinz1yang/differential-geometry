/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualVertexCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

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

theorem exists_section34ResidualBalls
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd
      tgtP) :
    ∃ (tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂)
      (tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂)
      (tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂),
      Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX tgtXBd
        tgtI tgtIBd := by
  classical
  have hVb : tgtVBd = section34VertexBallImage srcBd f₁ :=
    funext hdata.vertexBall_boundary_eq_image
  have hEb : tgtEBd = section34SplitDiskImage srcBd f₁ :=
    funext hdata.splitDisk_boundary_eq_image
  obtain ⟨-, -, -, -, -, hV, hE, -⟩ := id hdata
  have hVe : tgtV = section34VertexBallImage src f₁ := funext hV
  have hEe : tgtE = section34SplitDiskImage src f₁ := funext hE
  subst tgtV tgtE tgtVBd tgtEBd
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, hP9, -⟩ := id hdisk
  choose Rf hR hDR hfr hint hRH hio using fun t => hdata.exists_residualBall hdisk t
  have h7 : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34VertexBallImage src f₁ w = ∅ :=
    fun t w hw => hdata.residual_inter_vertexBallImage_eq_empty hdisk (hR t)
      (hfr t) (hint t) (hRH t) hw
  have h9 : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅ := fun t s hs =>
    hdata.residual_inter_faceDisk_eq_empty hdisk (hR t) (hfr t) (hint t) (h7 t) hs
  refine ⟨Rf, fun t => frontier (Rf t),
    fun x => Rf x.1.1 ∩ section34VertexBallImage src f₁ x.1.2,
    fun x => (⋃ (a : Section34ArcIndex 𝒦 𝒦')
      (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1), tgtA a) ∪
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
        Rf i.1.1 ∩ section34SplitDiskImage src f₁ i.1.2,
    fun i => Rf i.1.1 ∩ section34SplitDiskImage src f₁ i.1.2,
    fun i => ⋃ (p : Section34MarkIndex 𝒦 𝒦')
      (_ : p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1), tgtP p, ?_⟩
  unfold Section34ResidualPlus
  beta_reduce
  refine ⟨hR, fun x => ?_, fun i => ?_, fun x => rfl, h7, fun t s hs => ?_, h9,
    fun t t' htt => ?_, fun i => rfl, fun t e he => ?_, fun i => ?_, fun t => ?_,
    fun i => rfl, fun x => rfl, fun i p hpi hpI => ?_, hRH, fun w => ?_, fun e => ?_⟩
  · have hU : (⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
        Rf i.1.1 ∩ section34SplitDiskImage src f₁ i.1.2) =
        ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
          Rf x.1.1 ∩ section34SplitDiskImage src f₁ i.1.2 :=
      iUnion₂_congr fun i hi => by rw [hi.1]
    rw [hU]
    exact hdata.isPLCellOn_residualPatch_boundary hdisk (hR x.1.1) (hDR x.1.1)
      (hfr x.1.1) (hint x.1.1) (hio x.1.1) (h7 x.1.1) x.2
  · exact hdata.isPLCellOn_residualEdgeArc hdisk (hR i.1.1) (hDR i.1.1)
      (hfr i.1.1) (hint i.1.1) (hio i.1.1) (h7 i.1.1) i.2
  · exact inter_eq_right.mpr fun z hz =>
      (hR t).isCompact.isClosed.frontier_subset (hDR t s hs hz)
  · exact hdata.residual_inter_residual_subset hdisk hR hDR hfr hint h7 h9 htt
  · exact hcut.residual_inter_splitDiskImage_eq_empty hf₁.injOn (h7 t) he
  · exact hdata.residual_inter_splitDiskImage_subset (hR i.1.1) (hint i.1.1) (h7 i.1.1) i.1.2
  · apply Subset.antisymm
    · intro z hz
      rcases hfr t hz with hz' | hz'
      · obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hz'
        exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, w), hw⟩, rfl,
          (hR t).isCompact.isClosed.frontier_subset hz, hzw⟩)
      · exact Or.inl hz'
    · rintro z (hz | hz)
      · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz
        exact hDR t s hs hzs
      · obtain ⟨x, hxt, hzR, hzV⟩ := mem_iUnion₂.mp hz
        rw [hxt] at hzR
        refine ⟨subset_closure hzR, fun hzi => ?_⟩
        have hxw : Section34Incident x.1.2.1 t.1 := by
          rw [← hxt]
          exact x.2
        exact Set.disjoint_left.mp (hint t) hzi (mem_iUnion₂.mpr ⟨x.1.2, hxw, hzV⟩)
  · by_cases hpt : Section34Incident p.1.1.1 i.1.1.1
    · exact subset_iUnion₂_of_subset p ⟨hpi, hpt⟩ subset_rfl
    · exfalso
      obtain ⟨z, hz⟩ := (hP9 p).nonempty
      have hzD : z ∈ tgtD p.1.1 :=
        ((hdisk.faceDisk_inter_splitDisk_eq hdata p).symm.subset hz).1
      have h0 : z ∈ Rf i.1.1 ∩ tgtD p.1.1 := ⟨(hpI hz).1, hzD⟩
      rw [h9 i.1.1 p.1.1 hpt] at h0
      exact h0
  · intro z hz
    rcases hdata.vertexBallImage_frontier_subset_iUnion_residual hdisk hR hRH hDR hfr hint
      hio h7 h9 w hz with hzE | hzR
    · exact Or.inl hzE
    · obtain ⟨t, ht, hzR, hzV⟩ := mem_iUnion₂.mp hzR
      exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, w), ht⟩, rfl, hzR, hzV⟩)
  · intro z hz
    obtain ⟨t, het, hzR, hzE⟩ := mem_iUnion₂.mp
      (hdata.splitDiskImage_boundary_subset_iUnion_residual hdisk hR hRH hDR hfr hint hio h7 h9
        e hz)
    exact mem_iUnion₂.mpr ⟨⟨(t, e), het⟩, rfl, hzR, hzE⟩

end Diagram

end DifferentialGeometry.Topology.PiecewiseLinear
