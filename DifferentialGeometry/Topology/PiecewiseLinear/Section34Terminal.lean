/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetRecognitionOfTiling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceFaceOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Normalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem section34CellDiagram : Section34CellDiagram.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  rcases isEmpty_or_nonempty M₁ with hM | hM
  · have hUe : U = ∅ := eq_empty_iff_forall_notMem.mpr fun x _ => (hM.false x).elim
    refine ⟨PEmpty.{u + 1}, fun _ => 0, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ _ => 0,
      fun _ _ => 0, fun l _ => l.elim, fun l _ => l.elim, fun _ => ∅, fun _ => ∅, fun _ => ∅,
      fun l => l.elim, fun l => l.elim, fun l => l.elim, fun l => l.elim, fun l => l.elim,
      fun l => l.elim, fun l => l.elim, fun l => l.elim, fun l => l.elim, fun l => l.elim,
      fun l => l.elim, fun l => l.elim, ?_, ?_, ?_, fun l => l.elim, fun l => l.elim⟩
    · intro x hx
      simp at hx
    · intro y hy
      simp at hy
    · simp [hUe]
  · obtain ⟨N, 𝒦, 𝒦', src, srcBd, H, cr, f₁, tgtV, tgtVBd, tgtE, tgtEBd, fbl, fblBd, hdata⟩ :=
      section34NormalFamilyStatement hU hh hηc hηpos
    obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ := exists_section34FaceDisks hdata
    obtain ⟨tgtR, tgtRBd, tgtX, tgtXBd, tgtI, tgtIBd, hres⟩ :=
      exists_section34ResidualBalls hdata hdisk
    have hface := section34SourceFace_iff_cutLe hdata
    set tc : Section34CutLabelOf 𝒦 𝒦' → Set M₂ :=
      section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP with htcdef
    set tcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₂ :=
      section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) with htcbddef
    obtain ⟨-, -, -, -, -, -, -, hVcell₀, -, -, -, -, -, -, -, -, -⟩ := id hdata
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hVfr, hEtile⟩ := id hres
    have hVtile : ∀ w : Section34VertexIndex 𝒦 𝒦', tgtVBd w ⊆
        (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
          ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x := fun w => by
      rw [(hVcell₀ w).boundary_eq_frontier]
      exact hVfr w
    obtain ⟨htbd, htinter⟩ :=
      section34TargetRecognition_of_tiling hdata hdisk hres hVtile hEtile hface tc tcBd
        htcdef htcbddef
    obtain ⟨hcut, hctrl, hgraph, -, -, htgtVdef, -, hVcell, hEcell, -, -, htetraCar, -, -, -,
      -, -⟩ := id hdata
    obtain ⟨hDcell, -, -, -, -, hAcell, -, -, hPcell, -, -, -⟩ := id hdisk
    obtain ⟨hRcell, hXcell, hIcell, -, -, -, -, -, -, -, -, -, -, -, -, hresCar, -, -⟩ := id hres
    obtain ⟨-, -, -, hsc, hsbd, hsinter, hsdim, hsLF, hscover, -, -, -, -, -, -, -, -, hparent,
      -, hsupT, -, -, -, -, -⟩ := hcut
    obtain ⟨-, hHsub, hHlf, hHdiam, -, -⟩ := hctrl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hcrF, hsupV, hcrfib, hcrH⟩ := hgraph
    have htcell : ∀ l, IsPLCellOn (section34Dim l) (tc l) (tcBd l) := by
      intro l
      cases l with
      | vertexBall w => exact hVcell w
      | tetraBall t => exact hRcell t
      | splitDisk e => exact hEcell e
      | faceDisk s => exact hDcell s
      | patch x => exact hXcell x
      | faceArc a => exact hAcell a
      | edgeArc i => exact hIcell i
      | markedPoint p => exact hPcell p
    have hne : ∀ l, (src l).Nonempty := fun l => (hsc l).nonempty
    have hcpt : ∀ l, IsCompact (src l) := fun l => (hsc l).isCompact
    have hsubU : ∀ l, src l ⊆ U := fun l => hscover ▸ subset_iUnion src l
    choose Pp rr uu hrr huu hsceq hsbdeq using hsc
    choose Qq ss vv hss hvv htceq htbdeq using htcell
    choose par hpar3 hparsub using hparent
    have hsimplexface : ∀ m : Section34CutLabelOf 𝒦 𝒦', section34Dim m = 3 →
        section34LabelSimplex cr m ∈ 𝒦.complex.faces := by
      intro m hm
      rcases section34Dim_eq_three hm with ⟨w, rfl⟩ | ⟨t, rfl⟩
      · exact hcrF w
      · exact t.2.1
    have hsupport : ∀ m : Section34CutLabelOf 𝒦 𝒦', section34Dim m = 3 →
        src m ⊆ Section34CarrierSupport 𝒦 (section34LabelSimplex cr m) := by
      intro m hm
      rcases section34Dim_eq_three hm with ⟨w, rfl⟩ | ⟨t, rfl⟩
      · exact hsupV w
      · exact hsupT t
    have hcarS : ∀ m : Section34CutLabelOf 𝒦 𝒦', section34Dim m = 3 →
        h '' src m ⊆ H (section34LabelSimplex cr m) := by
      intro m hm
      rcases section34Dim_eq_three hm with ⟨w, rfl⟩ | ⟨t, rfl⟩
      · exact fun y hy => hcrH w (Or.inl hy)
      · exact htetraCar t
    have hcarY : ∀ m : Section34CutLabelOf 𝒦 𝒦', section34Dim m = 3 →
        H (section34LabelSimplex cr m) ⊆ h '' U := fun m hm => hHsub _ (hsimplexface m hm)
    have hsmall : ∀ m : Section34CutLabelOf 𝒦 𝒦', section34Dim m = 3 → ∀ x ∈ src m,
        ∀ y ∈ H (section34LabelSimplex cr m), ∀ z ∈ H (section34LabelSimplex cr m),
        dist y z < η x := fun m hm x hx y hy z hz =>
      hHdiam _ (hsimplexface m hm) x (hsupport m hm hx) y hy z hz
    have htgtsub : ∀ l, tc l ⊆ tc (par l) := by
      intro l y hy
      have hmem : y ∈ ⋃ k ∈ section34Face src l ∩ section34Face src (par l), tc k :=
        mem_iUnion₂.mpr ⟨l, ⟨Subset.rfl, hparsub l⟩, hy⟩
      rw [← htinter l (par l)] at hmem
      exact hmem.2
    have hcarTop : ∀ l, tc (par l) ⊆ H (section34LabelSimplex cr (par l)) := by
      intro l
      rcases section34Dim_eq_three (hpar3 l) with ⟨w, hw⟩ | ⟨t, ht⟩
      · rw [hw, htcdef]
        intro y hy
        refine hcrH w (Or.inr ?_)
        rw [← htgtVdef w]
        exact hy
      · rw [ht, htcdef]
        exact hresCar t
    obtain ⟨hcarrier, hsmallfin⟩ :=
      carrier_subset_and_dist_lt_of_parent src tc (fun m => H (section34LabelSimplex cr m)) par
        h η hparsub htgtsub (fun l => union_subset (hcarS (par l) (hpar3 l)) (hcarTop l))
        (fun l => hsmall (par l) (hpar3 l))
    have hfacefin : ∀ m, (section34Face src m).Finite := fun m =>
      finite_face_of_locallyFinite U src m hne (hcpt m) hsubU hsLF
    have hfib : ∀ m, {l | par l = m}.Finite := fun m =>
      (hfacefin m).subset fun l hl => hl ▸ hparsub l
    have hsimplexfib : ∀ σ : Finset (EuclideanSpace ℝ (Fin N)),
        {m : Section34CutLabelOf 𝒦 𝒦' | section34Dim m = 3 ∧
          section34LabelSimplex cr m = σ}.Finite := by
      intro σ
      have hT : {t : Section34SimplexIndex 𝒦 4 | t.1 = σ}.Finite :=
        Set.Subsingleton.finite fun a ha b hb => Subtype.ext (ha.trans hb.symm)
      refine (((hcrfib σ).image Section34Label.vertexBall).union
        (hT.image Section34Label.tetraBall)).subset ?_
      rintro m ⟨hm3, hmσ⟩
      rcases section34Dim_eq_three hm3 with ⟨w, rfl⟩ | ⟨t, rfl⟩
      · exact Or.inl ⟨w, hmσ, rfl⟩
      · exact Or.inr ⟨t, hmσ, rfl⟩
    have hparfib : ∀ σ : Finset (EuclideanSpace ℝ (Fin N)),
        {l : Section34CutLabelOf 𝒦 𝒦' | section34LabelSimplex cr (par l) = σ}.Finite := by
      intro σ
      refine ((hsimplexfib σ).biUnion fun m _ => hfib m).subset fun l hl => ?_
      exact mem_iUnion₂.mpr ⟨par l, ⟨hpar3 l, hl⟩, rfl⟩
    have hdown : ∀ m l : ULift.{u} (Section34CutLabelOf 𝒦 𝒦'), m.down = l.down → m = l := by
      rintro ⟨m⟩ ⟨l⟩ hml
      exact congrArg ULift.up hml
    have hfaceU : ∀ l m : ULift.{u} (Section34CutLabelOf 𝒦 𝒦'),
        m ∈ section34Face (fun k : ULift.{u} (Section34CutLabelOf 𝒦 𝒦') => src k.down) l \ {l} ↔
          m.down ∈ section34Face src l.down \ {l.down} :=
      fun l m => ⟨fun hm => ⟨hm.1, fun hd => hm.2 (hdown m l hd)⟩,
        fun hm => ⟨hm.1, fun he => hm.2 (congrArg ULift.down he)⟩⟩
    refine ⟨ULift.{u} (Section34CutLabelOf 𝒦 𝒦'), fun l => section34Dim l.down,
      section34Face (fun l : ULift.{u} (Section34CutLabelOf 𝒦 𝒦') => src l.down),
      fun l => Pp l.down, fun l => Qq l.down, fun l => rr l.down, fun l => ss l.down,
      fun l => uu l.down, fun l => vv l.down, fun l => src l.down, fun l => tc l.down,
      fun l => H (section34LabelSimplex cr (par l.down)), ?_, fun l => hrr l.down,
      fun l => hss l.down, fun l => huu l.down, fun l => hvv l.down, fun l => hsceq l.down,
      fun l => htceq l.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l => hcarrier l.down,
      fun l => hsmallfin l.down⟩
    · rintro ⟨l⟩
      cases l <;> simp [section34Dim]
    · intro l m hm
      rcases hsdim l.down m.down hm with hEq | hlt
      · exact Or.inl (hdown m l hEq)
      · exact Or.inr hlt
    · intro l
      refine ((hsbdeq l.down).symm.trans (hsbd l.down)).trans ?_
      exact (biUnion_ulift_down src _ _ (hfaceU l)).symm
    · intro l
      refine ((htbdeq l.down).symm.trans (htbd l.down)).trans ?_
      exact (biUnion_ulift_down tc _ _ (hfaceU l)).symm
    · intro l m
      refine (hsinter l.down m.down).trans ?_
      exact (biUnion_ulift_down src _ _ fun _ => Iff.rfl).symm
    · intro l m
      refine (htinter l.down m.down).trans ?_
      exact (biUnion_ulift_down tc _ _ fun _ => Iff.rfl).symm
    · intro x hx
      obtain ⟨l₀, hl₀⟩ := mem_iUnion.mp hx
      have hxU : x ∈ U := by
        rw [← hscover]
        exact mem_iUnion.mpr ⟨l₀.down, hl₀⟩
      obtain ⟨W, hW, hfin⟩ := hsLF x hxU
      exact ⟨W, hW, finite_ulift_down _ hfin⟩
    · refine exists_nhds_finite_of_subset_carriers (h '' U) _ H
        (fun l => section34LabelSimplex cr (par l.down))
        (fun l => (htgtsub l.down).trans (hcarTop l.down))
        (fun l => hcarY (par l.down) (hpar3 l.down))
        (fun σ => finite_ulift_down _ (hparfib σ)) ?_
      intro y hy
      obtain ⟨V, hV, hfin⟩ := hHlf y hy
      refine ⟨V, hV, hfin.subset ?_⟩
      rintro σ ⟨l, hl, hmem⟩
      exact ⟨hl ▸ hsimplexface (par l.down) (hpar3 l.down), hmem⟩
    · exact (iUnion_ulift_down src).trans hscover

end DifferentialGeometry.Topology.PiecewiseLinear
