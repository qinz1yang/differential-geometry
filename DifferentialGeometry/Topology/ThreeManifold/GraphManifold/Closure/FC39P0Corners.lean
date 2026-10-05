import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Faces

/-!
# FC39 producer, packet P0 (gate 1), §3 and §5.5: labelled corners and global face functions

Task-47 draft §3.2–§3.3 and §5.5 (dispositions D6, D8). The dry `CircleLink` only asked that every
corner centre be some rim base point; swapping the two corner axes kept it (regression test C).

* `GlobalFaceFunctions Rw` — the PREPARED output (open choice 5: not a raw row, not FDC03's local
  output) of one global defining function per actual face of the circle base, on a shrunk open base
  containing `C₁`: smooth, every zero regular on the whole shrunk base, `C₁ = {all ≤ 0}`, each face
  the zero set of its function INSIDE `C₁`, depth `≤ 2` and independence on the whole shrunk base,
  every double zero a registered labelled corner (the others strictly negative there), and the
  canonical functions `−X`, `−Y_e` on every corner base neighbourhood;
* `FC39Prepared` — the rows with the global face functions;
* `CircleRestrictionLink` (replacing the region / projection part of `CircleLink`): `circ.region =
  R.region`, a smooth open embedding `ι` of bases, `circ.domain` the WHOLE preimage of `range ι`,
  `R.proj = ι ∘ circ.proj`;
* `GlobalFaceLink` — the defining functions of `circ` are the global face functions through `ι`
  under a bijection `faceIndex`; `faceOfDefining` is derived from it, never a free function;
* `LabelledCornerCompatibility` — the ONE labelled corner contract: endpoint label of every corner
  (= the handle end), first label = the vertical face of the handle's component, second label = the
  actual horizontal face of that end, `X = λx` and `Y_e = λy` on the WHOLE rim chart source, the
  rim target = the full circle preimage of the corner chart target, inside the raw tube `U_e`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The labelled faces of the circle base of the rows. -/
abbrev FC39RowsV2.CircleFace (Rw : FC39RowsV2 W E) : Type u :=
  CircleFaceLabel Rw.slim.ResidualFace Rw.edge.EdgeBaseComponent

/-- The trace of a labelled face in the closed circle base: the base points of `C₁` whose whole
fibre lies in the face. -/
def FC39RowsV2.baseTrace (Rw : FC39RowsV2 W E) (f : Rw.CircleFace) : Set Rw.circle.Base :=
  {c | c ∈ Rw.circle.cbase ∧ Rw.circle.fibre c ⊆ circleFaceSet Rw.slim Rw.edge f}

/-- **§5.5 Global defining functions per actual face (NEW G2, prepared output).** -/
structure GlobalFaceFunctions (Rw : FC39RowsV2 W E) where
  base : TopologicalSpace.Opens Rw.circle.Base
  cbase_subset : Rw.circle.cbase ⊆ base
  Face : Type u
  finite : Finite Face
  actualFace : Face ≃ Rw.CircleFace
  fn : Face → Rw.circle.Base → ℝ
  smooth : ∀ f, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fn f) base
  zero_regular : ∀ f, ∀ c ∈ base, fn f c = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c ≠ 0
  base_eq : Rw.circle.cbase = {c | c ∈ base ∧ ∀ f, fn f c ≤ 0}
  face_eq : ∀ f, {c | c ∈ Rw.circle.cbase ∧ fn f c = 0} = Rw.baseTrace (actualFace f)
  depth_le_two : ∀ c ∈ base, Set.ncard {f | fn f c = 0} ≤ 2
  double_independent : ∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
    Surjective fun w : TangentSpace (𝓡 2) c =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f') c w)
  double_registered : ∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
    ∃ e : Rw.edge.EdgeEnd, c = Rw.junctions.rimBase e.1 ∧
      ((actualFace f = .vertical e.component ∧
          actualFace f' = .horizontal (Rw.junctions.horizontal e)) ∨
        (actualFace f = .horizontal (Rw.junctions.horizontal e) ∧
          actualFace f' = .vertical e.component)) ∧
      ∀ f'', f'' ≠ f → f'' ≠ f' → fn f'' c < 0
  canonical_near_corner : ∀ (e : Rw.edge.EdgeEnd) c, c ∈ Rw.labelledTubes.base e →
    fn (actualFace.symm (.vertical e.component)) c = -(Rw.labelledTubes.chart e c).1 ∧
      fn (actualFace.symm (.horizontal (Rw.junctions.horizontal e))) c =
        -(Rw.labelledTubes.chart e c).2

/-- **The prepared rows** (open choice 5): the raw rows and the global face functions. -/
structure FC39Prepared (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  rows : FC39RowsV2 W E
  globalFaces : GlobalFaceFunctions rows

/-- **§3.2 The restriction link of the final circle region to the row circle bundle.** -/
structure CircleRestrictionLink (R : CircleBundle W) (circ : CircleRegion W) where
  region_eq : circ.region = R.region
  ι : circ.Base → R.Base
  ι_isOpenEmbedding : Topology.IsOpenEmbedding ι
  ι_smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ ι
  ι_mfderiv : ∀ c, Bijective (mfderiv (𝓡 2) (𝓡 2) ι c)
  domain_eq : (circ.domain : Set W.Carrier) =
    Subtype.val '' {x : R.domain | R.proj x ∈ range ι}
  proj_eq : ∀ x : circ.domain, ∃ hx : (x : W.Carrier) ∈ R.domain,
    R.proj ⟨x, hx⟩ = ι (circ.proj x)

/-- **§3.2 `GlobalFaceLink`**: the defining functions of the final circle region are the global
face functions through `ι`, under a bijection of indices. -/
structure GlobalFaceLink {Rw : FC39RowsV2 W E} (GF : GlobalFaceFunctions Rw)
    (circ : CircleRegion W) (L : CircleRestrictionLink Rw.circle circ) where
  range_subset : range L.ι ⊆ GF.base
  faceIndex : Fin circ.definingCount ≃ GF.Face
  defining_eq : ∀ i c, circ.defining i c = GF.fn (faceIndex i) (L.ι c)

/-- The actual face of a defining function (derived from `faceIndex`, never a free function). -/
def GlobalFaceLink.faceOfDefining {Rw : FC39RowsV2 W E} {GF : GlobalFaceFunctions Rw}
    {circ : CircleRegion W} {L : CircleRestrictionLink Rw.circle circ}
    (G : GlobalFaceLink GF circ L) (i : Fin circ.definingCount) : Rw.CircleFace :=
  GF.actualFace (G.faceIndex i)

/-- **§3.3 The labelled corner compatibility with the final rim charts.** The scale of a corner is
`λ = cornerScale`; `X = T − 4Δ`, `Y_e = h_{horizontal e}`. -/
structure LabelledCornerCompatibility (Pr : FC39Prepared W E) (H : EdgeLayer W)
    (circ : CircleRegion W) (K : RimChartLayer W H circ) where
  edgeLink : EdgeComponentsLink Pr.rows.edge Pr.rows.edgeModels H
  circleLink : CircleRestrictionLink Pr.rows.circle circ
  globalFaces : GlobalFaceLink Pr.globalFaces circ circleLink
  endOfCorner : Fin circ.cornerCount ≃ Pr.rows.edge.EdgeEnd
  corner_center : ∀ k,
    circleLink.ι (circ.cornerChart k (0, 0)) = Pr.rows.junctions.rimBase (endOfCorner k).1
  endpoint_label : ∀ h b, edgeLink.endOfHandle h b = endOfCorner (K.handleCorner h b)
  first_label : ∀ h b, globalFaces.faceOfDefining (circ.cornerFirst (K.handleCorner h b)) =
    .vertical (edgeLink.componentOfHandle h)
  second_label : ∀ h b, globalFaces.faceOfDefining (circ.cornerSecond (K.handleCorner h b)) =
    .horizontal (Pr.rows.junctions.horizontal (edgeLink.endOfHandle h b))
  height_eq : ∀ h b p, p ∈ (K.rimChart h b).source →
    ∃ hx : K.rimChart h b p ∈ Pr.rows.edge.source,
      Pr.rows.edge.height ⟨K.rimChart h b p, hx⟩ - Pr.rows.edge.level =
        circ.cornerScale (K.handleCorner h b) * p.2.1
  horizontal_eq : ∀ h b p, p ∈ (K.rimChart h b).source →
    Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal (edgeLink.endOfHandle h b))
      (K.rimChart h b p) = circ.cornerScale (K.handleCorner h b) * p.2.2
  target_full : ∀ h b, (K.rimChart h b).target =
    Subtype.val '' (circ.proj ⁻¹' (circ.cornerChart (K.handleCorner h b)).target)
  target_in_raw_tube : ∀ h b,
    (K.rimChart h b).target ⊆ Pr.rows.labelledTubes.tube (edgeLink.endOfHandle h b)

/-- The vertex owner of the end `b` of the handle `h`, read from the SAME actual horizontal label
(the new S11b: no new owner choice). -/
def LabelledCornerCompatibility.handleEndOwner {Pr : FC39Prepared W E} {H : EdgeLayer W}
    {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool) :
    Pr.rows.slim.RowIndex :=
  Pr.rows.slim.residualOwner (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b))

end GC.GraphManifold.Assembly.FC39P0
