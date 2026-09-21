/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of the terminal half of Section 34

The assembly `section34CellDiagram` below proves the endpoint `Section34CellDiagram` for real
from the four leaves of this file; every `sorry` is a leaf and none sits inside an assembly.
The chain is: the configuration after step P5 (`exists_section34NormalFamily`), the exterior
face disks of step P6 (`exists_section34FaceDisks`), the residual tetrahedron balls of step P7
(`exists_section34ResidualBalls`), the target recognition of step P8
(`section34TargetRecognition`), then the exporters, which are proved in `Section34Frame`.

All vocabulary is the one copy in `Section34Frame`.  The leaves now run over the typed cut
frame, so the eight index types are the incident pairs of a triangulation `𝒦` of `U` and a
subdivision `𝒦'` of it, and no projection is a free parameter; the label type of the diagram is
`ULift` of `Section34CutLabelOf 𝒦 𝒦'`, which lives in `Type 0` because a simplex is a finite
set of points of `EuclideanSpace ℝ (Fin 3)`.

Changes made after external review K, and hence unreviewed: `Section34NormalFamily` is replaced
by `Section34NormalPlus`, the conjunction of the cut frame, the carrier control of P0, the
graph frame of P1 with `V_v = f₁ '' C_v` and `E_e = f₁ '' D_e`, the exterior clause and the
Lemma 11 trace certificate with the remaining normal-family clauses; P7 produces
`Section34ResidualPlus`, with the three intrinsic boundary decompositions of the digest.  The
clauses of the old `Section34NormalFamily` that the typed cut frame supplies are dropped: the
cell, boundary, intersection, dimension-drop, local finiteness and cover clauses, the four
incidence inclusions with their projections `arV arF mkE mkF paT paV egT egE`, and the top-cell
clause.  The old free carrier `car : Λ → Set M₂` is dropped as well: carriers are now
`H (section34LabelSimplex cr l)`, with `H` the `𝒦`-simplex-indexed carrier system of
`Section34CarrierControl`, which is what makes local finiteness in `h '' U` real.

Index question for the external reviewer.  Dual balls and splitting disks are indexed by the
vertices and edges of `𝒦'` lying in `graphSkeletonSpace 𝒦`; face disks and residual balls by
the triangles and tetrahedra of `𝒦`, because `∂σ` has to lie in the one skeleton of `𝒦`.  The
digest's exact flags `Pa ≃ {(t,v) : v ∈ t}`, `Ar ≃ {(σ,v) : v ∈ σ}`, `Eg ≃ {(t,e) : e < t}`,
`Mk ≃ {(σ,e) : e < σ}` are therefore read through `Section34Incident`, membership of the
`𝒦'`-vertices in the closed `𝒦`-simplex.  Whether the reviewer intends the same reading is not
settled.

The leaves, with content, owner and review state.

`exists_section34NormalFamily` (P0--P5, owner the lead's workers, changed after review K,
unreviewed): the triangulation and its subdivision, the source cut diagram, the carrier system,
P1's neighbourhood and map, the target neighbourhood pieces, the face balls and everything
`Section34NormalPlus` asks.  It is also the endpoint of the other skeleton, which produces the
cut and graph frames only; the carrier control, the exterior clause and the trace certificate
are the obligations that remain on P0 and on Lemmas 9--11.

`exists_section34FaceDisks` (P6, owner the lead's workers, changed after review K, unreviewed):
the exterior face disks `Δ_σ ⊆ ∂C_σ`, each a piecewise linear 2-cell meeting `⋃ V_v` exactly in
its own boundary, that boundary lying on the frontier of `⋃ V_v`, pairwise disjoint, meeting
`V_v` in the arc `a''_{vσ}` for an incident pair and not at all otherwise, meeting the splitting
circle `∂E_e` in the single point `p''_{σe}` for an incident pair and not at all otherwise.

`exists_section34ResidualBalls` (P7, owner the lead's workers, changed after review K,
unreviewed): the residual tetrahedron balls `R_t` with the intrinsic boundary decomposition
`∂R_t = ⋃_{σ<t} Δ_σ ∪ ⋃_{v∈t} X_{tv}`, the patches `X''_{tv} = R_t ∩ V_v` with
`∂X_{tv} = ⋃_{v∈σ<t} a_{vσ} ∪ ⋃_{v∈e<t} I_{te}`, the arcs `I''_{te} = R_t ∩ E_e` with
`∂I_{te}` the marked points of the triangles of `t` through `e`, the no-other-marked-point
clause of page 245, and `R_t ⊆ H_t`.

`section34TargetRecognition` (P8, owner the lead's workers, changed after review K,
unreviewed): the whole labelled target family is a family of piecewise linear cells of the same
dimensions, with intrinsic boundary the union of its proper faces and with exact pairwise
intersections, for the face relation read off the source.

Proved here, not a leaf: the packaging of the eight kinds into the existential of
`Section34CellDiagram`, including the parametrisations, the charts, the `ULift` of the label
type and the carrier `fun l => H (section34LabelSimplex cr (par l))`, whose local finiteness
comes from the carrier control together with the finite fibres of `cr` and of the parent map.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Diagram

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))} {f₁ : M₁ → M₂}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}
  {tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂}
  {tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂}
  {tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂}

theorem exists_section34NormalFamily [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h)) (hηc : ContinuousOn η U)
    (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
      (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))) (f₁ : M₁ → M₂)
      (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
      (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂),
      Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd fbl fblBd := by
  sorry

theorem exists_section34FaceDisks
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) :
    ∃ (tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂)
      (tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂)
      (tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂),
      Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP := by
  sorry

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
  sorry

theorem section34TargetRecognition
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd
      tgtP)
    (hres : Section34ResidualPlus 𝒦 𝒦' H tgtV tgtE tgtEBd tgtD tgtA tgtP tgtR tgtRBd tgtX
      tgtXBd tgtI tgtIBd)
    (tc tcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₂)
    (htc : tc = section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP)
    (htcBd : tcBd = section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
      fun _ => ∅) :
    (∀ l, IsPLCellOn (section34Dim l) (tc l) (tcBd l)) ∧
      (∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m) ∧
      ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k := by
  sorry

end Diagram

theorem section34CellDiagram : Section34CellDiagram.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  obtain ⟨𝒦, 𝒦', src, srcBd, H, cr, f₁, tgtV, tgtVBd, tgtE, tgtEBd, fbl, fblBd, hdata⟩ :=
    exists_section34NormalFamily (η := η) hU hh hηc hηpos
  obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ := exists_section34FaceDisks hdata
  obtain ⟨tgtR, tgtRBd, tgtX, tgtXBd, tgtI, tgtIBd, hres⟩ :=
    exists_section34ResidualBalls hdata hdisk
  set tc : Section34CutLabelOf 𝒦 𝒦' → Set M₂ :=
    section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP with htcdef
  set tcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₂ :=
    section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) with htcbddef
  obtain ⟨htcell, htbd, htinter⟩ :=
    section34TargetRecognition hdata hdisk hres tc tcBd htcdef htcbddef
  obtain ⟨hcut, hctrl, hgraph, -, -, htgtVdef, -, -, -, -, -, htetraCar, -, -, -, -, -⟩ := hdata
  obtain ⟨hsc, hsbd, hsinter, hsdim, hsLF, hscover, -, -, -, -, -, -, -, -, hparent, -,
    hsupT, -, -, -⟩ := hcut
  obtain ⟨-, hHsub, hHlf, hHdiam⟩ := hctrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcrF, hsupV, hcrfib, hcrH⟩ := hgraph
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hresCar⟩ := hres
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
  have hsimplexfib : ∀ σ : Finset (EuclideanSpace ℝ (Fin 3)),
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
  have hparfib : ∀ σ : Finset (EuclideanSpace ℝ (Fin 3)),
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
