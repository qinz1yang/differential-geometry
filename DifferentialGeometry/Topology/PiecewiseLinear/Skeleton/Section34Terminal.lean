/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetRecognitionOfTiling

/-!
# Sorry-first skeleton of the terminal half of Section 34

The assembly `section34CellDiagram` below proves the endpoint `Section34CellDiagram` for real
from the five leaves of this file; every `sorry` is a leaf and none sits inside an assembly.
The chain is: the configuration after step P5 (`exists_section34NormalFamily`), the exterior
face disks of step P6 (`exists_section34FaceDisks`), the residual tetrahedron balls of step P7
(`exists_section34ResidualBalls`), the source face order of step P8
(`section34SourceFace_iff_cutLe`) and the target recognition it feeds
(`section34TargetRecognition`), then the exporters, which are proved in `Section34Frame`.

The realisation ambient is existential here, because this half *produces* the triangulation:
`exists_section34NormalFamily` outputs `N` together with `𝒦, 𝒦' : LocallyFinitePLPieceIn
(EuclideanSpace ℝ (Fin N)) 3 M₁ U`.  Fixing `N = 3` would ask that all of `U` embed in `ℝ³`,
which fails already for `U = S³` with `h` the antipodal map.  A fixed finite `N` keeps the label
type in `Type 0`, so its `ULift` lands in `Type u` and the endpoint `Section34CellDiagram.{u}`
still applies; the other leaves of this file are generic in the ambient `Ea`.

The other half of Section 34, `ControlledGraphNeighborhoodStatement`, is **not** a producer of
`Section34NormalPlus`: it supplies P1 only, the cut frame and the graph frame, conditional on
`Moise341`.  The carrier control of P0, the exterior clause and the Lemma 11 trace certificate
are the obligations that remain on P0 and on Lemmas 9--11 of Section 33.

Two face relations occur, and step P8 is split along them.  `section34Face src l` is the nesting
ideal of the source cells, which is what the terminal exporter consumes; `Section34CutLe` is the
reflexive transitive closure of the explicit codimension-one incidences of the cut diagram.
Their agreement on the source cut is `section34SourceFace_iff_cutLe`, a source-side obligation
about the remaining seam combinatorics.  A face disk inside a dual ball is *already* excluded by
the exact intersection `a_{vσ} = C_v ∩ d_σ` of the cut frame together with the cell clauses:
`d_σ ⊆ C_v` would make one set simultaneously a piecewise linear `1`-cell and a `2`-cell, and
for a non-incident vertex the intersection is empty by a further clause.
`section34TargetRecognition` consumes that bridge and no longer
concludes that the target family consists of piecewise linear cells, because each of the eight
kinds is already a cell by an input clause of `Section34NormalPlus`, `Section34FaceDiskFamily`
or `Section34ResidualPlus`; the assembly reads that off by cases.

Carriers are `H (section34LabelSimplex cr l)`, with `H` the `𝒦`-simplex-indexed carrier system
of `Section34CarrierControl`, which is what makes local finiteness in `h '' U` real.  Since
review N that system also asks `IsPLCellOn 3 (H t) (frontier (H t))`: a carrier names an
exterior in `Section34Exterior`, and for a carrier with a hole a component touching an inner
boundary passes the component test although it is not outside, which made P7 false.  Since
review S it also asks that each carrier lie in one piecewise linear chart of `M₂`; that clause
is what the other half of Section 34 needs in order to produce a common chart per triangle, and
it is free here because a carrier is already a closed piecewise linear ball.

`Section34CutFrame` further asks that every triangle of `𝒦` be a face of a tetrahedron of `𝒦`,
in the index form `∀ s, ∃ t, Section34Incident s.1 t.1`.  It is derivable from
`IsCombinatorialManifold 3 𝒦.complex` for a manifold without boundary, and it is free at every
intended call site, but the tree has no such derivation and `section34SourceFace_iff_cutLe`
silently entails it, so it is a clause for now.

The `IsPLCellOn` API owed to `PiecewiseLinear.PLCellOn` and used silently here: uniqueness of
the intrinsic boundary, `IsPLCellOn d S B → IsPLCellOn d S B' → B = B'`; its agreement with the
ambient frontier in codimension zero, `IsPLCellOn 3 S B → B = frontier S`, for which
`IsPLHomeomorphInto.image_frontier` is the natural tool but asks for an open domain; and
distinctness of the dimensions, so that a set is not both a `1`-cell and a `2`-cell.  The
first two are what `section34TargetRecognition` needs at the vertex balls and the splitting
disks, whose intrinsic boundaries `tgtVBd`, `tgtEBd` are pinned by no formula; the third is
what the exclusion of a face disk inside a dual ball appeals to.  The remaining five label
kinds have their intrinsic boundaries given by explicit formulas, so recognition there is
combinatorics only.

The leaves, with content and review state.

`exists_section34NormalFamily` (P0--P5): reviewed 2026-09-21 OK; statement changed only through
the two new clauses of the shared frame, so **unreviewed since**; the realisation ambient, the
triangulation and its subdivision, the source cut diagram, the carrier system, P1's
neighbourhood and map, the target neighbourhood pieces, the face balls and everything
`Section34NormalPlus` asks.  Review AF added `[Nonempty M₁]` to it, and the assembly below
therefore splits on `isEmpty_or_nonempty M₁`: the leaf outputs a `LocallyFinitePLPieceIn` whose
field `map : EuclideanSpace ℝ (Fin N) → M₁` is total while the ambient is nonempty for every `N`,
so it is false for `M₁ = ∅`, whereas the endpoint `Section34CellDiagram` is universally
quantified over `M₁` and stays true there, proved directly with the label type `PEmpty` — then
`U = ∅`, every labelled clause is vacuous, both cell unions are empty and the cover clause reads
`∅ = U`.

`exists_section34FaceDisks` (P6): reviewed 2026-09-21 OK, but the audit of digest Q found that
verdict **true but hollow**: of the four ingredients of the reviewer's cyclic seam argument
only the single crossing clause of `Section34Trace` is a field; "at least three seams", "the
seams cut `∂T_σ` into cyclic annuli" and "a single crossing is transverse and essential" are
not, and the innermost disk exclusion is present only as the two `→ False` assumptions inside
`Section34NormalPlus`, that is inside leaf 1.  The difficulty of P6 is relocated, not
discharged.  It produces the exterior face disks `Δ_σ ⊆ ∂C_σ` with their arcs and marked
points.  Its full input excludes a foreign face arc `a_{vτ} ⊆ d_σ` with `τ ≠ σ`; that exclusion
is the derived lemma `section34_faceArc_subset_faceDisk_iff`, owed to this file and not a
missing clause of the statement.

`exists_section34ResidualBalls` (P7): reviewed 2026-09-21 OK and confirmed by the audit of
digest Q; the residual tetrahedron balls `R_t` with the three intrinsic boundary
decompositions, the no-other-marked-point clause of page 245, and `R_t ⊆ H_t`, now with `H_t` a
closed piecewise linear ball.  The outer component test works because `frontier (H t)` is
connected and disjoint from the obstacle.

`section34SourceFace_iff_cutLe` (P8, source side): reviewed 2026-09-21 OK; on the source cut,
inclusion of cells is exactly the reflexive transitive closure of the codimension-one
incidences.  Its `←` half is a mechanical consequence of the frame; its `→` half needs the new
tetrahedron clause, because the only route from a face arc to a dual ball runs through a patch.

`section34TargetRecognition` (P8, target side): reviewed 2026-09-21 OK; the target family has
intrinsic boundary the union of its proper faces and exact pairwise intersections, for the face
relation read off the source.  It rests on the owed `IsPLCellOn` uniqueness and codimension
zero facts listed above.

Proved here, not a leaf: the packaging of the eight kinds into the existential of
`Section34CellDiagram`, including the cell clause by cases, the parametrisations, the charts,
the `ULift` of the label type and the carrier `fun l => H (section34LabelSimplex cr (par l))`,
whose local finiteness comes from the carrier control together with the finite fibres of `cr`
and of the parent map.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-23 with zero-diagnostic checks
and an axiom audit; statement byte-identical): `exists_section34FaceDisks` (P6, module
`Section34FaceDisks` over `BallWindingObstruction`, `Section34IncidentEdges`,
`Section34TargetCells`, `Section34TraceArcs`).  The proof uses neither `→ False` clause of
`Section34NormalPlus` and no
`H₁`: the "at least three seams" and the cyclic order come from the cut frame (`𝒦'` restricted to
the rim of `s` is a combinatorial circle), "single crossing ⇒ essential" is the winding lemma (a PL
ball cannot contain two connected pieces of `V` and `T` running from `E₀` to `E₁` when
`V ∩ T ⊆ E₀ ∪ E₁`, by a lift to `ℝ/ℤ`), and transversality is never needed; so the audit remark
of digest Q that P6 is "true but hollow" is withdrawn.  `Section34TargetCells` gives the
non-compact target-cell facts (the open splitting disk lies in the interior of its two end balls,
read in a chart) for P7 and P8.

Interface repair 2026-09-23 (owner decision): `Section34ResidualPlus` gained the two tilings that
its compact twin already had as clauses 21 and 22, stated with the ambient frontier since the bundle
has no `tgtVBd` parameter — `frontier (tgtV w) ⊆ ⋃ (e ∋ w) tgtE e ∪ ⋃ (x at w) tgtX x` and
`tgtEBd e ⊆ ⋃ (i on e) tgtI i`; the producer `exists_section34ResidualBalls` (P7, open) now owes
them, and the assembly turns the first into `tgtVBd w ⊆ …` by `IsPLCellOn.boundary_eq_frontier`.
With them `section34TargetRecognition` (P8) is proved: the conditional theorem
`section34TargetRecognition_of_tiling` (module `Section34TargetRecognitionOfTiling`, Opus 5.5 fill
worker, lead-accepted with zero-diagnostic checks and an audit) is the frozen statement with the
two tilings inserted after `hres`, and the assembly calls it; the leaf is deleted.
-/

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

theorem exists_section34NormalFamily [Nonempty M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h)) (hηc : ContinuousOn η U)
    (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ (N : ℕ) (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (H : Finset (EuclideanSpace ℝ (Fin N)) → Set M₂)
      (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin N))) (f₁ : M₁ → M₂)
      (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
      (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂),
      Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd fbl fblBd := by
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

theorem section34SourceFace_iff_cutLe
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) :
    ∀ l m : Section34CutLabelOf 𝒦 𝒦', src m ⊆ src l ↔ Section34CutLe m l := by
  sorry

end Diagram

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
      exists_section34NormalFamily (η := η) hU hh hηc hηpos
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
