/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartLocalApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Sorry-first skeleton of the controlled form of Moise 35.1

The assembly `controlledGraphNeighborhood` proves the endpoint
`ControlledGraphNeighborhoodStatement` for real from the four leaves of this file; every `sorry`
is a leaf and none sits inside an assembly.  The chain is: the source cut diagram of a
subdivision together with the fine carriers (steps 1--5 of pages 248--249), the vertex stage
through the proved chart local `Moise341` (step 6, page 249), the edge stage carrying the
annulus package, conditions (2)--(8), Lemmas 1--3 and the deletion that produces the target
cells (steps 7--13, pages 249--251), the two control clauses of Section 34 Lemma 1(4) and
Lemma 2, and finally the locally finite pasting, which is proved here from
`exists_isPLHomeomorphInto_union_of_locallyFinite_pieces`.

Quantifier order is the content.  The triangulation `𝒦` and the carrier control `(η, H)` come
first, because Section 34 chooses them once for the whole approximation problem; only then the
prescribed neighbourhood `W` of the one skeleton and the free tolerance `ψ`, which Moise 35.2
supplies afresh; and the subdivision `𝒦'`, the cut diagram, the regular neighbourhood and `f₁`
stand in one existential, because Lemma 1's incidence clauses are read off a jointly chosen
neighbourhood and map and cannot be imposed on an arbitrary output of plain `Moise351`.

`Section34CutFrame` is the source cut diagram with exact flags: its index types are the actual
simplices of `𝒦'`, the vertices and edges of the one skeleton of `𝒦` being cut out by
`Section34GraphIndex`, and the patch, arc, edge arc and marked point types are the incident
pairs themselves, so no cell is empty and no incidence is a free parameter.  The face relation
is the nesting ideal `section34CutFace src l = {m | src m ⊆ src l}`.  `IsControlledPLCell d S B`
asks for a piecewise linear `d`-cell with *intrinsic* boundary `B`; ambient frontiers never
occur.  Local finiteness is asked only in the subspaces `U` and `h '' U`.
`Section34GraphFrame` is the jointly produced neighbourhood, map and conclusions (G).
`Section34CarrierControl` is the carrier system: the supports are the full stars
`Section34CarrierSupport 𝒦 t = ⋃_{v ∈ t} |closed star of v|`, the carriers satisfy
`h '' S_t ⊆ interior (H t)`, `H t ⊆ h '' U`, local finiteness in the subspace `h '' U`, and the
diameter bound `dist y z < η x` for `x ∈ S_t`.

`Section34Terminal.lean` could not be imported: the focused checker supplies an object for an
imported module only from a receipt with zero diagnostics, and that file carries four
`declaration uses 'sorry'` warnings, so its `Section34Label`, `IsPLCellOn`, `section34Dim` and
`section34Face` are restated here under the names `Section34CutLabel`, `IsControlledPLCell`,
`section34CutDim` and `section34CutFace`, with identical content, and must be identified with
them when that file becomes importable.

No forgetful corollary to `Moise351` is proved, and it is not short.  Three things block it.
`Moise351` starts from an arbitrary `K` with `IsLocallyFinitePolyhedralGraph (n := 3) K`, closed
in `U`, whereas the endpoint starts from a triangulation of `U` whose one skeleton is the graph;
producing one from the other is the relative triangulation theorem, absent here.  `Moise351`
supplies only the tolerance, whereas the endpoint also asks for a carrier control, whose
existence needs `h '' U` to be a neighbourhood of each `h '' S_t`, that is invariance of domain
for `h`, and a locally finite carrier family; both are separate producers.  And `Moise351`'s
local finiteness of `K` is carried relative to `K` itself while the conclusion needs it relative
to `U`; with `K` closed in `U` the two agree, but that reduction is nowhere in the tree.

The Lemma 2 clause is `CarriesFundamentalGroupOnto J T`, that is `J ⊆ T` together with
surjectivity of `FundamentalGroup.map` of the inclusion at every base point of `J`.  For `J` a
polygon and `T` a solid torus this is exactly "J carries a generator of `π(T)`"; no singular
homology statement is used.

The leaves, with content and review state.

`exists_section34CutFrame` (steps 1--5, unreviewed): the subdivision `𝒦'` of `𝒦` with the same
realisation map, the cut frame, the regular neighbourhood `N = ⋃ C_v` of the one skeleton of
`𝒦` inside `W`, the assignment `car` of a simplex of `𝒦` to every dual cell with
`C_v ⊆ S_(car v)` and finite fibres, and the fine carriers `Q v` with
`h '' C_v ⊆ interior (Q v)`, `Q v ⊆ H (car v)`, pairwise distances in `Q v` below `ψ`, and the
separation `Q v ∩ h '' σ ≠ ∅ → v ≤ σ` that conditions (2) and (3) are read off.

`Moise341.exists_section34VertexApproximation` (step 6, unreviewed): conditional on `Moise341`,
which is an explicit hypothesis of this leaf and of the endpoint theorem, the piecewise linear
embeddings of the disjoint locally finite family of dual balls confined to the fine carriers,
with piecewise linear cell images.  Its intended supplier is the proved chart local
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`.

`exists_section34EdgeMatching` (steps 7--13, unreviewed): the alteration that makes the family
match along the splitting disks, that is `EqOn` on `C_v ∩ C_w` and the exact meet
`G v '' (C_v ∩ C_w) = G v '' C_v ∩ G w '' C_w`, still confined to the fine carriers, with the
union a neighbourhood of `h '' |𝒦¹|`.  This is the leaf most likely to be mis-sized: it carries
the piercing alteration, the `A_e`/`B_e` package, 27.3, Lemmas 1--3 and the minimality argument
in one statement.

`section34MeridianAndNeighborhood` (Section 34 Lemma 1(4) and Lemma 2, unreviewed): for the
pasted map, the vertex point clause, `h '' ∂σ ⊆ interior (T_σ)` and the generator clause.

Proved here, not leaves: `IsControlledPLCell.isCompact` and `IsControlledPLCell.nonempty`;
`exists_nhds_finite_of_subset_carriers`, the conversion of carrier local finiteness in the
subspace `h '' U` into ambient local finiteness of the target cells, which uses `H t ⊆ h '' U`
exactly where it is needed; `exists_isPLHomeomorphInto_dualCellPaste`, the locally finite
pasting of the matched family into one `f₁`; and the assembly, which in particular proves
conditions (2) and (3) of Section 34 Lemma 1 from the carrier separation and the combinatorics
of the splitting disks, and the `ψ` estimate from the fine carriers.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

section Cell

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def IsControlledPLCell (d : ℕ) (S B : Set M) : Prop :=
  ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3) → M),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) P ∧ IsPLHomeomorphInto 3 u P ∧
      S = u '' P ∧ B = u '' (r '' stdSimplexBoundary d)

theorem IsControlledPLCell.isCompact {d : ℕ} {S B : Set M} (hS : IsControlledPLCell d S B) :
    IsCompact S := by
  obtain ⟨P, r, u, hr, hu, hcell, -⟩ := hS
  rw [hcell]
  exact ((IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact).image_of_continuousOn hu.continuousOn

theorem IsControlledPLCell.nonempty {d : ℕ} {S B : Set M} (hS : IsControlledPLCell d S B) :
    S.Nonempty := by
  obtain ⟨P, r, u, hr, -, hcell, -⟩ := hS
  rw [hcell]
  exact (IsPLBall.nonempty ⟨r, hr⟩).image u

end Cell

inductive Section34CutLabel (Vx Tt Ed Fc Pa Ar Eg Mk : Type v) : Type v
  | vertexBall (w : Vx)
  | tetraBall (t : Tt)
  | splitDisk (e : Ed)
  | faceDisk (s : Fc)
  | patch (x : Pa)
  | faceArc (a : Ar)
  | edgeArc (i : Eg)
  | markedPoint (p : Mk)

def section34CutDim {Vx Tt Ed Fc Pa Ar Eg Mk : Type v} :
    Section34CutLabel Vx Tt Ed Fc Pa Ar Eg Mk → ℕ
  | .vertexBall _ => 3
  | .tetraBall _ => 3
  | .splitDisk _ => 2
  | .faceDisk _ => 2
  | .patch _ => 2
  | .faceArc _ => 1
  | .edgeArc _ => 1
  | .markedPoint _ => 0

def section34CutFace {Λ : Type*} {M : Type*} (c : Λ → Set M) (l : Λ) : Set Λ :=
  {m | c m ⊆ c l}

def CarriesFundamentalGroupOnto {Y : Type*} [TopologicalSpace Y] (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ (hJT : J ⊆ T) (b : J),
    Function.Surjective
      (FundamentalGroup.map (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) b)

section Triangulation

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

def simplexBody (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  𝒦.map '' convexHull ℝ (t : Set Ea)

def simplexRim (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  ⋃ s ∈ {s : Finset Ea | s ⊂ t}, simplexBody 𝒦 s

def graphSkeletonSpace (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) : Set X :=
  ⋃ t ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2}, simplexBody 𝒦 t

def Section34CarrierSupport (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  ⋃ w ∈ (t : Set Ea), ⋃ s ∈ {s : Finset Ea | s ∈ 𝒦.complex.faces ∧ w ∈ s}, simplexBody 𝒦 s

abbrev Section34SimplexIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (k : ℕ) :=
  {t : Finset Ea // t ∈ 𝒦.complex.faces ∧ t.card = k}

abbrev Section34GraphIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) (k : ℕ) :=
  {t : Finset Ea // t ∈ 𝒦.complex.faces ∧ t.card = k ∧ simplexBody 𝒦 t ⊆ Γ}

abbrev Section34PatchIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) :=
  {p : Section34SimplexIndex 𝒦 4 × Section34GraphIndex 𝒦 Γ 1 // p.2.1 ⊆ p.1.1}

abbrev Section34ArcIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) :=
  {p : Section34SimplexIndex 𝒦 3 × Section34GraphIndex 𝒦 Γ 1 // p.2.1 ⊆ p.1.1}

abbrev Section34EdgeArcIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) :=
  {p : Section34SimplexIndex 𝒦 4 × Section34GraphIndex 𝒦 Γ 2 // p.2.1 ⊆ p.1.1}

abbrev Section34MarkIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) :=
  {p : Section34SimplexIndex 𝒦 3 × Section34GraphIndex 𝒦 Γ 2 // p.2.1 ⊆ p.1.1}

abbrev Section34CutLabelOf (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) :=
  Section34CutLabel (Section34GraphIndex 𝒦 Γ 1) (Section34SimplexIndex 𝒦 4)
    (Section34GraphIndex 𝒦 Γ 2) (Section34SimplexIndex 𝒦 3) (Section34PatchIndex 𝒦 Γ)
    (Section34ArcIndex 𝒦 Γ) (Section34EdgeArcIndex 𝒦 Γ) (Section34MarkIndex 𝒦 Γ)

end Triangulation

section Frames

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

def Section34CarrierControl (U : Set M₁)
    (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U) (h : M₁ → M₂) (η : M₁ → ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂) : Prop :=
  (∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t)) ∧
  (∀ t ∈ 𝒦.complex.faces, H t ⊆ h '' U) ∧
  (∀ y ∈ h '' U, ∃ V ∈ 𝓝[h '' U] y,
    {t | t ∈ 𝒦.complex.faces ∧ (H t ∩ V).Nonempty}.Finite) ∧
  ∀ t ∈ 𝒦.complex.faces, ∀ x ∈ Section34CarrierSupport 𝒦 t, ∀ y ∈ H t, ∀ z ∈ H t,
    dist y z < η x

def Section34CutFrame (U : Set M₁)
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (src srcBd : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁) : Prop :=
  (∀ l, IsControlledPLCell (section34CutDim l) (src l) (srcBd l)) ∧
  (∀ l, srcBd l = ⋃ m ∈ section34CutFace src l \ {l}, src m) ∧
  (∀ l m, src l ∩ src m = ⋃ k ∈ section34CutFace src l ∩ section34CutFace src m, src k) ∧
  (∀ l m, src m ⊆ src l → m = l ∨ section34CutDim m < section34CutDim l) ∧
  (∀ x ∈ U, ∃ V ∈ 𝓝 x, {l | (src l ∩ V).Nonempty}.Finite) ∧
  (⋃ l, src l) = U ∧
  (∀ a : Section34ArcIndex 𝒦' (graphSkeletonSpace 𝒦),
    src (.faceArc a) ⊆ src (.vertexBall a.1.2) ∩ src (.faceDisk a.1.1)) ∧
  (∀ p : Section34MarkIndex 𝒦' (graphSkeletonSpace 𝒦),
    src (.markedPoint p) ⊆ src (.splitDisk p.1.2) ∩ src (.faceDisk p.1.1)) ∧
  (∀ x : Section34PatchIndex 𝒦' (graphSkeletonSpace 𝒦),
    src (.patch x) ⊆ src (.tetraBall x.1.1) ∩ src (.vertexBall x.1.2)) ∧
  (∀ i : Section34EdgeArcIndex 𝒦' (graphSkeletonSpace 𝒦),
    src (.edgeArc i) ⊆ src (.tetraBall i.1.1) ∩ src (.splitDisk i.1.2)) ∧
  (∀ l, ∃ m, section34CutDim m = 3 ∧ src l ⊆ src m) ∧
  (∀ s : Section34SimplexIndex 𝒦' 3, src (.faceDisk s) ⊆ simplexBody 𝒦' s.1) ∧
  (∀ w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1,
    simplexBody 𝒦' w.1 ⊆ src (.vertexBall w)) ∧
  ∀ e : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 2,
    ∃ w w' : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1, w ≠ w' ∧
      e.1 = w.1 ∪ w'.1 ∧ src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')

def section34CutNeighborhood {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (src : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁) : Set M₁ :=
  ⋃ w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1, src (.vertexBall w)

def section34FaceTorus {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (src : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁) (f : M₁ → M₂)
    (s : Section34SimplexIndex 𝒦' 3) : Set M₂ :=
  ⋃ a : Section34ArcIndex 𝒦' (graphSkeletonSpace 𝒦), ⋃ (_ : a.1.1 = s),
    f '' src (.vertexBall a.1.2)

def Section34GraphFrame (U W : Set M₁) (h : M₁ → M₂) (ψ : M₁ → ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (src : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁)
    (car : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 →
      Finset (EuclideanSpace ℝ (Fin 3)))
    (f₁ : M₁ → M₂) : Prop :=
  IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
    (graphSkeletonSpace 𝒦) U ∧
  section34CutNeighborhood src ⊆ W ∧
  IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src) ∧
  f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) ∧
  (∀ x ∈ section34CutNeighborhood src, dist (f₁ x) (h x) < ψ x) ∧
  (∀ w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1,
    h '' simplexBody 𝒦' w.1 ⊆ interior (f₁ '' src (.vertexBall w))) ∧
  (∀ (e : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 2) (s : Section34SimplexIndex 𝒦' 3),
    (f₁ '' src (.splitDisk e) ∩ h '' simplexBody 𝒦' s.1).Nonempty → e.1 ⊆ s.1) ∧
  (∀ (w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1)
    (s : Section34SimplexIndex 𝒦' 3),
    (f₁ '' src (.vertexBall w) ∩ h '' simplexBody 𝒦' s.1).Nonempty → w.1 ⊆ s.1) ∧
  (∀ s : Section34SimplexIndex 𝒦' 3,
    h '' simplexRim 𝒦' s.1 ⊆ interior (section34FaceTorus src f₁ s)) ∧
  (∀ s : Section34SimplexIndex 𝒦' 3,
    CarriesFundamentalGroupOnto (h '' simplexRim 𝒦' s.1) (section34FaceTorus src f₁ s)) ∧
  (∀ w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1, car w ∈ 𝒦.complex.faces) ∧
  ∀ w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1,
    h '' src (.vertexBall w) ∪ f₁ '' src (.vertexBall w) ⊆ H (car w)

end Frames

def ControlledGraphNeighborhoodStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ 𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U,
      IsCombinatorialManifold 3 𝒦.complex →
    ∀ (η : M₁ → ℝ) (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂),
      Section34CarrierControl U 𝒦 h η H →
    ∀ {W : Set M₁}, IsOpen W → graphSkeletonSpace 𝒦 ⊆ W → W ⊆ U →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
    ∃ (𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁)
      (car : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 →
        Finset (EuclideanSpace ℝ (Fin 3))) (f₁ : M₁ → M₂),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
        Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        Section34GraphFrame U W h ψ H 𝒦 𝒦' src car f₁

section Leaves

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁}
  {car : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → Finset (EuclideanSpace ℝ (Fin 3))}
  {Q : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → Set M₂}
  {G : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → M₁ → M₂}

theorem exists_section34CutFrame [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (η : M₁ → ℝ) (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (hH : Section34CarrierControl U 𝒦 h η H)
    (hW : IsOpen W) (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hWU : W ⊆ U)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦) → Set M₁)
      (car : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 →
        Finset (EuclideanSpace ℝ (Fin 3)))
      (Q : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → Set M₂),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
        Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
          (graphSkeletonSpace 𝒦) U ∧
        section34CutNeighborhood src ⊆ W ∧
        (∀ w, car w ∈ 𝒦.complex.faces) ∧
        (∀ w, src (.vertexBall w) ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
        (∀ t : Finset (EuclideanSpace ℝ (Fin 3)), {w | car w = t}.Finite) ∧
        (∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) ∧
        (∀ w, Q w ⊆ H (car w)) ∧
        (∀ w, ∀ x ∈ src (.vertexBall w), ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
        ∀ (w : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1)
          (s : Section34SimplexIndex 𝒦' 3),
          (Q w ∩ h '' simplexBody 𝒦' s.1).Nonempty → w.1 ⊆ s.1 := by
  sorry

theorem Moise341.exists_section34VertexApproximation (h341 : Moise341) [T2Space M₁]
    [SecondCountableTopology M₁] [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) :
    ∃ G : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w))) ∧
        (∀ w, G w '' src (.vertexBall w) ⊆ Q w) ∧
        ∀ w, IsControlledPLCell 3 (G w '' src (.vertexBall w))
          (G w '' srcBd (.vertexBall w)) := by
  sorry

theorem exists_section34EdgeMatching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w)))
    (hGQ : ∀ w, G w '' src (.vertexBall w) ⊆ Q w)
    (hGcell : ∀ w, IsControlledPLCell 3 (G w '' src (.vertexBall w))
      (G w '' srcBd (.vertexBall w))) :
    ∃ G' : Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1 → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G' w) (src (.vertexBall w))) ∧
        (∀ w, G' w '' src (.vertexBall w) ⊆ Q w) ∧
        (∀ w w', EqOn (G' w) (G' w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        (∀ w w', G' w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          G' w '' src (.vertexBall w) ∩ G' w' '' src (.vertexBall w')) ∧
        (⋃ w, G' w '' src (.vertexBall w)) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
  sorry

theorem section34MeridianAndNeighborhood [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {f₁ : M₁ → M₂} (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (src (.vertexBall w)))
    (hGQ : ∀ w, G w '' src (.vertexBall w) ⊆ Q w)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hagree : ∀ w, EqOn f₁ (G w) (src (.vertexBall w)))
    (hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    (∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (f₁ '' src (.vertexBall w))) ∧
      (∀ s : Section34SimplexIndex 𝒦' 3,
        h '' simplexRim 𝒦' s.1 ⊆ interior (section34FaceTorus src f₁ s)) ∧
      ∀ s : Section34SimplexIndex 𝒦' 3,
        CarriesFundamentalGroupOnto (h '' simplexRim 𝒦' s.1) (section34FaceTorus src f₁ s) := by
  sorry

end Leaves

section Pasting

theorem exists_nhds_finite_of_subset_carriers {ι κ : Type*} {Y : Type*} [TopologicalSpace Y]
    (Y₀ : Set Y) (S : ι → Set Y) (Hc : κ → Set Y) (cr : ι → κ)
    (hSH : ∀ i, S i ⊆ Hc (cr i)) (hHY : ∀ i, Hc (cr i) ⊆ Y₀)
    (hfib : ∀ k, {i | cr i = k}.Finite)
    (hLF : ∀ y ∈ Y₀, ∃ V ∈ 𝓝[Y₀] y, {k | ∃ i, cr i = k ∧ (Hc k ∩ V).Nonempty}.Finite) :
    ∀ y ∈ ⋃ i, S i, ∃ V ∈ 𝓝 y, {i | (S i ∩ V).Nonempty}.Finite := by
  intro y hy
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hy
  obtain ⟨V, hV, hfin⟩ := hLF y (hHY i₀ (hSH i₀ hi₀))
  obtain ⟨O, hOopen, hyO, hOV⟩ := mem_nhdsWithin.mp hV
  refine ⟨O, hOopen.mem_nhds hyO, ((hfin.biUnion fun k _ => hfib k).subset ?_)⟩
  rintro i ⟨x, hx, hxO⟩
  have hxH : x ∈ Hc (cr i) := hSH i hx
  have hxV : x ∈ V := hOV ⟨hxO, hHY i hxH⟩
  exact mem_iUnion₂.mpr ⟨cr i, ⟨i, rfl, ⟨x, hxH, hxV⟩⟩, rfl⟩

theorem exists_isPLHomeomorphInto_dualCellPaste {ι : Type*} {M₁ M₂ : Type u}
    [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] (base : M₁ → M₂) (C : ι → Set M₁)
    (G : ι → M₁ → M₂) (hC : ∀ i, IsClosed (C i)) (hD : ∀ i, IsClosed (G i '' C i))
    (hG : ∀ i, IsPLHomeomorphInto 3 (G i) (C i))
    (hcompat : ∀ i j, EqOn (G i) (G j) (C i ∩ C j))
    (hmeet : ∀ i j, G i '' (C i ∩ C j) = G i '' C i ∩ G j '' C j)
    (hsrc : ∀ x ∈ ⋃ i, C i, ∃ V ∈ 𝓝 x, {i | (C i ∩ V).Nonempty}.Finite)
    (htgt : ∀ y ∈ ⋃ i, G i '' C i, ∃ V ∈ 𝓝 y, {i | (G i '' C i ∩ V).Nonempty}.Finite) :
    ∃ F : M₁ → M₂, IsPLHomeomorphInto 3 F (⋃ i, C i) ∧ (∀ i, EqOn F (G i) (C i)) ∧
      F '' (⋃ i, C i) = ⋃ i, G i '' C i := by
  obtain ⟨F, hF, -, hFG, hFim⟩ :=
    exists_isPLHomeomorphInto_union_of_locallyFinite_pieces (A := (∅ : Set M₁))
      (B := (∅ : Set M₂)) (S := C) (T := fun i => G i '' C i) (F₀ := base) (f := G)
      isClosed_empty isClosed_empty hC hD (isPLHomeomorphInto_empty base) (image_empty base)
      hG (fun _ => rfl) (fun _ x hx => absurd hx.1 (notMem_empty x))
      (fun i => by rw [empty_inter, image_empty, empty_inter]) hcompat hmeet
      (fun x hx => hsrc x (by rwa [empty_union] at hx))
      (fun y hy => htgt y (by rwa [empty_union] at hy))
  rw [empty_union] at hF
  rw [empty_union, empty_union] at hFim
  exact ⟨F, hF, hFG, hFim⟩

end Pasting

theorem controlledGraphNeighborhood (h341 : Moise341) :
    ControlledGraphNeighborhoodStatement.{u} := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh 𝒦 h𝒦 η H hH W hW hΓW hWU ψ hψc hψpos
  obtain ⟨hHint, hHsub, hHlf, hHdiam⟩ := hH
  obtain ⟨𝒦', src, srcBd, car, Q, hsubdiv, hmapeq, hframe, hN, hNW, hcarF, -, hcarfib,
    hQint, hQH, hQsmall, hQsep⟩ :=
    exists_section34CutFrame hU hh 𝒦 h𝒦 η H ⟨hHint, hHsub, hHlf, hHdiam⟩ hW hΓW hWU ψ hψc
      hψpos
  obtain ⟨G₀, hG₀, hG₀Q, hG₀cell⟩ :=
    h341.exists_section34VertexApproximation hU hh hframe hQint
  obtain ⟨G, hG, hGQ, hcompat, hmeet, hGnbhd⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hQint hG₀ hG₀Q hG₀cell
  obtain ⟨hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, hsplit⟩ := id hframe
  have hCclosed : ∀ w, IsClosed (src (Section34CutLabel.vertexBall w)) := fun w =>
    (hcell _).isCompact.isClosed
  have hDclosed : ∀ w, IsClosed (G w '' src (Section34CutLabel.vertexBall w)) := fun w =>
    ((hcell _).isCompact.image_of_continuousOn (hG w).continuousOn).isClosed
  have hsub : ∀ w, src (Section34CutLabel.vertexBall w) ⊆ U := fun w =>
    (subset_iUnion src (Section34CutLabel.vertexBall w)).trans hcover.subset
  have hsrcLF : ∀ x ∈ ⋃ w, src (Section34CutLabel.vertexBall w), ∃ V ∈ 𝓝 x,
      {w | (src (Section34CutLabel.vertexBall w) ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp hx
    obtain ⟨V, hV, hfin⟩ := hLF x (hsub w₀ hw₀)
    refine ⟨V, hV, Set.Finite.of_finite_image (f := fun w =>
      (Section34CutLabel.vertexBall w : Section34CutLabelOf 𝒦' (graphSkeletonSpace 𝒦)))
      (hfin.subset ?_) ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw
    · intro a _ b _ hab
      simpa using hab
  have htgtLF : ∀ y ∈ ⋃ w, G w '' src (Section34CutLabel.vertexBall w), ∃ V ∈ 𝓝 y,
      {w | (G w '' src (Section34CutLabel.vertexBall w) ∩ V).Nonempty}.Finite := by
    refine exists_nhds_finite_of_subset_carriers (h '' U) _ H car
      (fun w => (hGQ w).trans (hQH w)) (fun w => hHsub _ (hcarF w)) hcarfib ?_
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  obtain ⟨f₁, hf₁, hf₁G, hf₁im⟩ :=
    exists_isPLHomeomorphInto_dualCellPaste h (fun w => src (.vertexBall w)) G hCclosed
      hDclosed hG hcompat hmeet hsrcLF htgtLF
  have himg : ∀ w, f₁ '' src (Section34CutLabel.vertexBall w) =
      G w '' src (Section34CutLabel.vertexBall w) := fun w => (hf₁G w).image_eq
  have hf₁Q : ∀ w, f₁ '' src (Section34CutLabel.vertexBall w) ⊆ Q w := by
    intro w
    rw [himg w]
    exact hGQ w
  have hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hrw : f₁ '' section34CutNeighborhood src =
        ⋃ w, G w '' src (Section34CutLabel.vertexBall w) := hf₁im
    rw [hrw]
    exact hGnbhd
  obtain ⟨hvertexInt, hrim, hmeridian⟩ :=
    section34MeridianAndNeighborhood hU hh hframe hN hQint hG hGQ hf₁ hf₁G hnbhd
  refine ⟨𝒦', src, srcBd, car, f₁, hsubdiv, hmapeq, hframe, hN, hNW, hf₁, hnbhd, ?_,
    hvertexInt, ?_, ?_, hrim, hmeridian, hcarF, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    refine hQsmall w x hw (f₁ x) (hf₁Q w ⟨x, hw, rfl⟩) (h x) ?_
    exact interior_subset (hQint w ⟨x, hw, rfl⟩)
  · intro e s hne
    obtain ⟨w, w', hww', hunion, hdisk⟩ := hsplit e
    have hwsub : src (Section34CutLabel.splitDisk e) ⊆
        src (Section34CutLabel.vertexBall w) := hdisk ▸ inter_subset_left
    have hw'sub : src (Section34CutLabel.splitDisk e) ⊆
        src (Section34CutLabel.vertexBall w') := hdisk ▸ inter_subset_right
    have hw : w.1 ⊆ s.1 := by
      refine hQsep w s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w (image_mono hwsub hy₁), hy₂⟩
    have hw' : w'.1 ⊆ s.1 := by
      refine hQsep w' s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w' (image_mono hw'sub hy₁), hy₂⟩
    rw [hunion]
    exact Finset.union_subset hw hw'
  · intro w s hne
    obtain ⟨y, hy₁, hy₂⟩ := hne
    exact hQsep w s ⟨y, hf₁Q w hy₁, hy₂⟩
  · intro w
    refine union_subset ?_ ((hf₁Q w).trans (hQH w))
    exact fun y hy => hQH w (interior_subset (hQint w hy))

end DifferentialGeometry.Topology.PiecewiseLinear
