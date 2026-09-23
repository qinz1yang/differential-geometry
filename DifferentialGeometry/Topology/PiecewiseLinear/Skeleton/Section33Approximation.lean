/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists

/-!
# Sorry-first skeleton of Moise 33.1, the tube approximation

The assembly `moise331` proves the endpoint `Moise331` of `MoiseChain.lean` for real from the
twelve leaves of this file and the named propositions `Moise323`, `Moise324` (Section 32) and
`Moise264` (the extended loop theorem, cited on page 234 for the injectivity in Lemma 10); every
`sorry` is a leaf and none sits inside an assembly.  The dependency chain is therefore
`Moise323 → Moise324 → Moise264 → Moise331`, and the first review (digest AI) kept `Moise264`
explicit on purpose: the ledger plans only a *restricted* producer of the extended loop theorem
through the orientable loop route, so the parameter must not be deleted to hide that dependency
inside Lemma 10; at integration it may be narrowed to the `ℝ³` local version Lemma 10 needs,
and the proof of that leaf must then enclose the compact support of a null-homotopy in a
finite piecewise linear three-manifold inside `Int N' − K'`.  Source: Moise, *Geometric topology in
dimensions 2 and 3*, printed pages 230-238, read through `consult/AA-section33-construction-digest`.

The endpoint.  `Moise331` gives a finite connected one-dimensional complex `L` of `ℝ³` with no
end-points, an open `U ⊇ |L|`, an embedding `h` of `U` and a constant `ε`, and asks for a
subdivision `L'`, a finite complex `T ⊇ L'` which is a combinatorial three-manifold with
boundary, the derived neighbourhood `N` of `L'` in `T`, itself such a manifold, a neighbourhood
of `|L|` inside `U`, and a piecewise linear homeomorphism `f` on `N` whose image is a
neighbourhood of `h '' |L|` and which is `ε`-close to `h`.  Its combinatorial clauses come from
the frame, the `T.space` and `N` neighbourhood clauses are derived here from `IsTube` and
`IsSubdivision.space_eq`, and the `ε`-estimate is proved here by the triangle inequality of
page 231 through `h v`: for `x ∈ C v`, `dist (f x) (h v) < ε / 4` by the endgame leaf and
`dist (h v) (h x) < ε / 4` by the frame, so `dist (f x) (h x) < ε / 2`.

The frame and the joint choice of page 231.  The book chooses `N` so small that every
`C'_v = h '' C_v` has diameter below `ε / 4`, then chooses the pseudo-cells and the handle pieces
`C''_v` so that, by 32.3 (8), these too have diameter below `ε / 4`.  The leaf
`exists_section33TubeFrame` outputs in one existential the subdivision, `T`, the tube data
`C`, `D`, `Dbd` with `IsTube` for `N = (derivedNeighborhood T L').space` and `N' = h '' N`,
`N ⊆ U`, the no-end-point property of `L'`, the dual cells pinned to `graphDualCell T L'`, and
the bound `dist (h x) (h y) < ε / 4` on every `C v`; the tube clauses `dualBall`, `splitCell`,
`splitProper`, `splitSeparates` and `freeFaceConnected`, for which the tree has no producer, are
inside this leaf.  The handle decomposition is then obtained for real in
`exists_section33HandleFrame` from `Moise323`: for each vertex the prescribed neighbourhood is the
open thickening of the compact `h '' C v` by a third of the slack between its largest distance
and `ε / 4`, so every `Cpp v` inherits the pointwise bound `dist x y < ε / 4`.  This is provable
only because the tube leaf already carries the bound on the `C'_v`; a leaf taking an arbitrary
`N` and demanding small `C''_v` would be false, which is AA risk 1.

The five re-choices of `X` (Lemmas 2-7).  The polyhedral neighbourhood is carried as a finite
complex `XK` with `X = XK.space` and `Bd X = frontier X`, which equals the boundary complex by
`frontier_space_eq_boundaryComplex_space`.  The leaves `exists_isPolyhedralTubeNeighborhood`
(Lemma 2), `exists_hasSinglePolygonTraces` (Lemmas 3 and 4), `exists_hasConnectedHandlePieces`
(Lemmas 5 and 6) and `exists_hasNoHandleLoopTheoremDisk` (Lemma 7) each take the previous
conjunction as input and output a complex with the previous conjunction and the new clause, so
one `X` with all of Lemmas 2-7 reaches Lemma 9.  The descent measures, and why earlier clauses
survive: Lemma 3 lowers the total number of components of the traces `E ∩ Bd X` by splitting
`D_J ∪ Bd X` at an innermost disk `D_J ⊆ E − {P'}` with `E` fixed; Lemma 4 lowers the same count
by splitting off an annulus between two concentric trace polygons with `E` fixed, which
removes two polygons of that `E` and touches no other pseudo-cell, so Lemma 3 survives; Lemma 5
deletes the components of `X` not containing `K'` and fills the bounded complementary domains,
which shrinks each `E ∩ Bd X` inside the old trace while `E ∩ Bd X` stays non-empty because
`P' ∈ Int X` and `Bd E ⊆ Bd N'` miss `X`, so the single polygon and its disk survive; Lemma 6
modifies nothing; Lemma 7 lowers the first Betti number of `Bd X` by splitting at a loop theorem
disk pushed off every pseudo-cell, so the traces are untouched and Lemmas 3-5 are re-read off
the new frontier.  Lemma 9's leaf consumes Lemmas 2, 3, 4 and 7 only; Lemma 10's consumes all.

Definitions.  The neighborhood and trace vocabulary lives in
`PolyhedralTubeNeighborhood.lean`.  `IsLoopTheoremDisk Kimg N' BdX Δ` is the LTD of page 232:
a piecewise linear two-cell in `Int N' − K'` meeting `Bd X` exactly in its boundary, which is
not contractible in `Bd X`; the tree had no such notion, so it is defined here (to be hoisted).
`IsPolyhedralTubeNeighborhood` is Lemma 2 with the two consequences of `X ⊆ Int N'` that later
leaves read, `Bd E ∩ X = ∅` and the crossing `HasPLCrossingAt (Int E) (Bd X)` at every trace
point; AA question 3 is answered as it proposes: the trace lies in `Int E − {P'}`, the locally
polyhedral part, so only finite piecewise linear general position is involved.
`HasSinglePolygonTraces` renders Lemmas 3 and 4 together: `E ∩ Bd X` is one polygon and
`E ∩ X` is a topological two-cell with that polygon as boundary and the centre inside; by
Schoenflies in the open two-cell `Int E` this is equivalent to "one polygon which bounds no disk
in `Int E − {P'}`", and the disk `E ∩ X` is what the endgame replaces (AA question 4).
`HasConnectedHandlePieces` renders Lemmas 5 and 6 with the triangulation `AK v` of
`A'_v = C''_v ∩ Bd X` as an output, because Lemma 12 is stated as an Euler characteristic of it;
the boundary of `A'_v` is the union of the trace polygons of the edges at `v`, an equality and
not the book's inclusion, since `Bd X` crosses each `E` into `C''_u` and `C''_v`.
`HasNoHandleLoopTheoremDisk` is Lemma 7.  `edgesAt K v` is the set of edges at `v`.

Lemma 8.  Its printed clause (3), "`Δ` intersects no other set `C''_{v₂}`", contradicts clause
(1): `Bd Δ = Δ ∩ E₁` is non-empty and `E₁ = C''_{v₁} ∩ C''_{v₂}` lies in the other end's piece.
The proof of Lemma 9 supplies, and the proof of Lemma 8 uses, that `Δ` misses every pseudo-cell
other than `E₁`; `section33_disk_meets_graph` states that reading, which the first review
confirmed (the printed clause would be repaired most literally as "`Int Δ` meets no other
`C''_v`", and under the overlap clauses and `hbd` the two readings agree).  The printed "`E₁`
lying in `C''_{v₁}`" is implied and not assumed: `C''_{v₁} ∩ E_e = ∅` unless `v₁ ∈ e`.  The
leaf is the one consumer of the no-end-point hypothesis.

The remaining leaves.  `section33_not_isLoopTheoremDisk` (Lemma 9) takes Lemma 8 as a universal
hypothesis, as the tree's descent skeletons do.  `section33_tube_product` is the page 235
assertion `Bd N × (0,1) ≅ Int N' − K'`, marked [A] there; it follows from the product structure of
a derived neighbourhood minus its core, transported by `h`, which maps `Int N` onto `Int N'` by
invariance of domain.  `section33_fundamentalGroup_map_bijective` (Lemma 10) is stated into
`N' − K'` as printed; AA question 5 is answered by the collar of `Bd N'` in `N'`.
`section33_faceEulerChar_handlePiece` (Lemma 12) is the "direct computation": with `A'_v`
connected and bounded by `deg v` polygons, "no handles" is `χ(A'_v) = 2 − deg v`, which with
orientability from 26.8 forces a planar surface, and this replaces both 22.9 and the unproved
"sphere with holes and possible handles"; Lemma 11 has no consumer and is not stated.
`exists_section33BoundaryMatch` (Lemma 13) outputs the piecewise linear homeomorphism
`g : Bd N ↔ Bd X` with `g(A_v) = A'_v` and `g(Bd D_e) = E_e ∩ Bd X`; the second clause is not
a formal consequence of the first because `A_u ∩ A_v = Bd D_e` needs disjoint interiors of the
dual cells, which `IsTube` records only through its derived model.  `exists_section33Extension`
is the endgame of page 238: `E'_e` from `Moise324`, extension over the splitting disks, then
over each `C_v`; it carries the `ε`-estimate, `h v ∈ f '' C v` and `dist (f x) (f y) < ε / 4` on
`C v`, from `f '' C_v ⊆ C''_v ∪ ⋃ ball(P'_e, δ)` with `δ` chosen inside the slack of the frame's
bound (AA question 2).  AA question 1: the page 238 citation "Theorem 18.2" is a misprint; the
step is the `ℝ³` analogue of 5.4, extension of a piecewise linear homeomorphism between the
boundaries of two piecewise linear three-cells, which the tree's unconditional piecewise linear
Schoenflies supplies, and the leaf relies on that and not on Section 18.

Gaps of the book covered by leaves: Lemma 2 entirely, the concentricity of Lemma 4, the disk
`X_v ∩ E` of Lemma 6, the product structure of Lemma 10, the "evidently" and the "direct
computation" of Lemma 12, the vertex ordering of Lemma 13 (a spanning-tree order), the endgame's
`E ∩ X` disk and two-sphere claims, and the whole `ε`-estimate.

Vacuity and inhabitants.  `Moise331` has an edge, so `L'` has an edge and every tube clause is
exercised; `ε` is positive, so the bound `dist (h v) (h v) < ε / 4` is satisfiable and the
thickening radius is positive.  No new predicate is trivially satisfiable: `IsLoopTheoremDisk`
holds for a meridian disk of a second, unlinked solid torus inside a ball `N'`, and each of
`IsPolyhedralTubeNeighborhood`, `HasSinglePolygonTraces`, `HasConnectedHandlePieces` is met on
the triangle fixture by a polyhedral solid torus around `h '' |L|` whose frontier crosses each of
the three planar pseudo-cells in one polygon around the centre.  None of these inhabitants is
built here: all four are UNTESTED, and the missing brick is the one recorded in `PseudoCell`,
an inhabitant of `IsTube` (a verified `IsCombinatorialManifoldWithBoundary 3` certificate of a
finite complex of `ℝ³` with the graph as a subcomplex).

Leaves, in assembly order.  All twelve were reviewed **OK** on 2026-09-21 (digest AI) and are
frozen; the `hgD` output of the boundary match is derivable from `IsTube.interEdge`,
`splitProper` and the injectivity of `g` (`A_u ∩ A_v = Dbd e`), and is kept only as information
for the extension, not as an independent obligation:
`exists_section33TubeFrame` (frame, pages 230-231, deep), `exists_isPolyhedralTubeNeighborhood`
(Lemma 2, deep), `exists_hasSinglePolygonTraces` (Lemmas 3-4, deep),
`exists_hasConnectedHandlePieces` (Lemmas 5-6, deep), `exists_hasNoHandleLoopTheoremDisk`
(Lemma 7, deep), `section33_disk_meets_graph` (Lemma 8, deep), `section33_not_isLoopTheoremDisk`
(Lemma 9, deep), `section33_tube_product` (page 235, short),
`section33_fundamentalGroup_map_bijective` (Lemma 10, deep),
`section33_faceEulerChar_handlePiece` (Lemma 12, short), `exists_section33BoundaryMatch`
(Lemma 13, deep), `exists_section33Extension` (page 238, deep).

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical with the frozen leaf): `section33_tube_product`
(module `DerivedNeighborhoodRayEmbedding`).  In the first derived subdivision the derived
neighbourhood is the set where a core vertex carries a maximal barycentric weight; the ray towards
the subcomplex barycentric projection gives the source product `Bd N × (0,1) ≃ Int N \ |K|`, and
`h` transports it.  The core lies in the ambient interior because a positive core weight at a
boundary point would put a simplex of `K` into the boundary complex.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical with the frozen leaf):
`section33_faceEulerChar_handlePiece` (Lemma 12, module `HandlePieceEulerChar`).  A degree-one
Hurewicz factorisation over a field turns `hiso` into `b₁(Bd X) ≤ b₁(N' \ K')`; `N' \ K'` is
`Fr N × [0,1)` with `Fr N` connected; Euler additivity over the handle pieces and cone capping of
each piece's `deg v` boundary polygons give `χ(A'_v) ≤ 2 - deg v`, and the handshake identity
forces equality in every piece.  The route does not use the sorried `HurewiczLowDegrees`.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statement byte-identical with the frozen leaf):
`exists_isPolyhedralTubeNeighborhood` (Lemma 2, module `PolyhedralTubeNeighborhoodExists`), over
the new brick `LocalSurfaceLink` (a finite triangulation inside a chart of a topological
2-manifold has PL-circle vertex links, the torus recognition template with local charts).
Route: a manifold neighbourhood `X₀` of `K'` in `Int N'`, one combinatorial surface with boundary
matching the pseudo-cells near the relevant compact sets, `exists_small_homeomorph_generalPosition`
to put `Fr X₀` across it, and PL invariance.  Lemma 8 (`section33_disk_meets_graph`) is stuck on
an interface gap, escalated to the owner: `IsHandleDecompositionOfTube` does not record
`Ec e ∩ frontier N' = Ebd e`, which the book's 32.1/32.2 construction supplies; without it a bridge
edge lets the return path be blocked by `Bd N'`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Vocabulary

def IsLoopTheoremDisk (Kimg N' BdX Δ : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ interior N' \ Kimg ∧
    Δ ∩ BdX = r '' stdSimplexBoundary 2 ∧
    ∃ hb : r '' stdSimplexBoundary 2 ⊆ BdX,
      ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
        C(r '' stdSimplexBoundary 2, BdX)).Nullhomotopic

def HasNoHandleLoopTheoremDisk (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ v ∈ K.vertices, ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
    IsLoopTheoremDisk (h '' K.space) N' (frontier X) Δ → ¬ Δ ⊆ Cpp v

end Vocabulary

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

open Classical in
theorem exists_section33TubeFrame
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite L.faces]
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2) (hedge : ∃ e ∈ L.faces, e.card = 2)
    (hend : ∀ v : L.vertices, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hLU : L.space ⊆ U)
    (hh : Topology.IsEmbedding (U.domRestrict h)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
      (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))),
      T.faces.Finite ∧ IsSubdivision L' L ∧ L'.faces ⊆ T.faces ∧
      IsCombinatorialManifoldWithBoundary 3 T ∧
      IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
      (derivedNeighborhood T L').space ⊆ U ∧
      (∀ v : L'.vertices, ((SimplicialComplex.edgeGraph L').neighborSet v).ncard ≠ 1) ∧
      IsTube L' (derivedNeighborhood T L').space C D Dbd h
        (h '' (derivedNeighborhood T L').space) ∧
      (∀ v ∈ L'.vertices, C v = (graphDualCell T L' v).space) ∧
      ∀ v ∈ L'.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (h x) (h y) < ε / 4 := by
  sorry

theorem exists_hasSinglePolygonTraces
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) :
    ∃ XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space := by
  sorry

theorem exists_hasConnectedHandlePieces
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) :
    ∃ (XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space ∧
      HasConnectedHandlePieces K Ec Cpp XK'.space AK := by
  sorry

theorem exists_hasNoHandleLoopTheoremDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK) :
    ∃ (XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (AK' : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space ∧
      HasConnectedHandlePieces K Ec Cpp XK'.space AK' ∧
      HasNoHandleLoopTheoremDisk K h N' Cpp XK'.space := by
  sorry

theorem section33_disk_meets_graph (h324 : Moise324)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hend : ∀ v : K.vertices, ((SimplicialComplex.edgeGraph K).neighborSet v).ncard ≠ 1)
    {v₁ : EuclideanSpace ℝ (Fin 3)} (hv₁ : v₁ ∈ K.vertices)
    {e₁ : Finset (EuclideanSpace ℝ (Fin 3))} (he₁ : e₁ ∈ K.faces) (hcard : e₁.card = 2)
    {Δ : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ) (hΔ : Δ ⊆ Cpp v₁ ∩ interior N')
    (hbd : Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2)
    (hcenter : ∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
        DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint)
    (hmiss : ∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) :
    (Δ ∩ h '' K.space).Nonempty := by
  sorry

theorem section33_not_isLoopTheoremDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h7 : HasNoHandleLoopTheoremDisk K h N' Cpp XK.space)
    (h8 : ∀ v₁ ∈ K.vertices, ∀ e₁ ∈ K.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ → Δ ⊆ Cpp v₁ ∩ interior N' →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' K.space).Nonempty) :
    ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
      ¬ IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ := by
  sorry

theorem section33_fundamentalGroup_map_bijective (h264 : Moise264)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (h7 : HasNoHandleLoopTheoremDisk K h N' Cpp XK.space)
    (hnoLTD : ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
      ¬ IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    (hprod : Nonempty ((frontier N × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N' \ h '' K.space))) :
    ∀ hsub : frontier XK.space ⊆ N' \ h '' K.space, ∀ x : frontier XK.space,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C(frontier XK.space, ↥(N' \ h '' K.space))) x) := by
  sorry

theorem exists_section33BoundaryMatch
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (hχ : ∀ v ∈ K.vertices, ∀ [Finite (AK v).faces],
      SimplicialComplex.faceEulerChar (AK v).toPreAbstractSimplicialComplex =
        2 - ((edgesAt K v).ncard : ℤ)) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn g (frontier N) (frontier XK.space) ∧
      (∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ frontier XK.space) ∧
      ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ frontier XK.space := by
  sorry

theorem exists_section33Extension (h324 : Moise324)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (frontier N) (frontier XK.space))
    (hgA : ∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ frontier XK.space)
    (hgD : ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ frontier XK.space) {ε : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < ε / 4) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ nhdsSet (h '' K.space) ∧
      EqOn f g (frontier N) ∧ (∀ v ∈ K.vertices, h v ∈ f '' C v) ∧
      ∀ v ∈ K.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (f x) (f y) < ε / 4 := by
  sorry

end Leaves

section Assembly

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}

theorem exists_section33HandleFrame (h323 : Moise323) (ht : IsTube K N C D Dbd h N') {ε : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (h x) (h y) < ε / 4) :
    ∃ (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))),
      IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
      ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < ε / 4 := by
  have hcont : ContinuousOn h N :=
    continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous
  have key : ∀ v : EuclideanSpace ℝ (Fin 3), ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      v ∈ K.vertices → V ∈ nhdsSet (h '' C v) ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y < ε / 4 := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hCN : C v ⊆ N := by
        rw [ht.unionEq]
        exact subset_biUnion_of_mem (u := C) hv
      have hvC : v ∈ C v := by
        have hmem : v ∈ C v ∩ K.vertices := by
          rw [ht.dualVertex hv]
          exact mem_singleton v
        exact hmem.1
      have hSc : IsCompact (h '' C v) :=
        (ht.dualBall v hv).isPolyhedron.isCompact.image_of_continuousOn (hcont.mono hCN)
      have hne : (h '' C v).Nonempty := ⟨h v, mem_image_of_mem h hvC⟩
      obtain ⟨p, hp, hmax⟩ := (hSc.prod hSc).exists_isMaxOn (hne.prod hne)
        (continuous_dist.continuousOn (s := (h '' C v) ×ˢ (h '' C v)))
      obtain ⟨x₀, hx₀, hpx⟩ := (mem_prod.mp hp).1
      obtain ⟨y₀, hy₀, hpy⟩ := (mem_prod.mp hp).2
      have hm : dist p.1 p.2 < ε / 4 := by
        rw [← hpx, ← hpy]
        exact hsmall v hv x₀ hx₀ y₀ hy₀
      have hrpos : 0 < (ε / 4 - dist p.1 p.2) / 3 := by linarith
      refine ⟨Metric.thickening ((ε / 4 - dist p.1 p.2) / 3) (h '' C v), fun _ => ⟨?_, ?_⟩⟩
      · exact Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening hrpos _)
      · intro x hx y hy
        obtain ⟨s, hs, hxs⟩ := Metric.mem_thickening_iff.mp hx
        obtain ⟨s', hs', hys⟩ := Metric.mem_thickening_iff.mp hy
        have hss' : dist s s' ≤ dist p.1 p.2 :=
          isMaxOn_iff.mp hmax (s, s') (mk_mem_prod hs hs')
        have h4 := dist_triangle4 x s s' y
        rw [dist_comm s' y] at h4
        linarith
    · exact ⟨univ, fun hv' => absurd hv' hv⟩
  choose V hV using key
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hsub⟩ :=
    h323 K N C D Dbd h N' ht V fun v hv => (hV v hv).1
  exact ⟨Ec, Eint, Ebd, Cpp, hd,
    fun v hv x hx y hy => (hV v hv).2 x (hsub v hv hx) y (hsub v hv hy)⟩

open Classical in
theorem moise331 (h323 : Moise323) (h324 : Moise324) (h264 : Moise264) : Moise331 := by
  intro L hfin hdim hedge hconn hend U hU hLU h hh ε hε
  obtain ⟨T, L', C, D, Dbd, hTfin, hsub, hLT, hT, hDN, hNU, hend', ht, -, hCsmall⟩ :=
    exists_section33TubeFrame L hdim hedge hend hU hLU hh hε
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hCppSmall⟩ := exists_section33HandleFrame h323 ht hCsmall
  have hconn' : IsConnected L'.space := by
    rw [hsub.space_eq]
    exact hconn
  obtain ⟨XK₀, h2₀⟩ := exists_isPolyhedralTubeNeighborhood hd
  obtain ⟨XK₁, h2₁, h34₁⟩ := exists_hasSinglePolygonTraces hd h2₀
  obtain ⟨XK₂, AK₂, h2₂, h34₂, h56₂⟩ := exists_hasConnectedHandlePieces hd hconn' h2₁ h34₁
  obtain ⟨XK, AK, h2, h34, h56, h7⟩ := exists_hasNoHandleLoopTheoremDisk hd h2₂ h34₂ h56₂
  have h8 : ∀ v₁ ∈ L'.vertices, ∀ e₁ ∈ L'.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ →
        Δ ⊆ Cpp v₁ ∩ interior (h '' (derivedNeighborhood T L').space) →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ L'.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' L'.space).Nonempty :=
    fun _ hv₁ _ he₁ hcard _ _ hr hΔ hbd hcenter hmiss =>
      section33_disk_meets_graph h324 hd hend' hv₁ he₁ hcard hr hΔ hbd hcenter hmiss
  have h9 := section33_not_isLoopTheoremDisk hd h2 h34 h7 h8
  have hprod := section33_tube_product ht
  have h10 := section33_fundamentalGroup_map_bijective h264 hd h2 h34 h56 h7 h9 hprod
  have h12 := section33_faceEulerChar_handlePiece hd h2 h34 h56 h10
  obtain ⟨g, hg, hgA, hgD⟩ := exists_section33BoundaryMatch hd hconn' h2 h34 h56 h12
  obtain ⟨f, hf, hfN, -, hfv, hfsmall⟩ :=
    exists_section33Extension h324 hd h2 h34 h56 hg hgA hgD hCppSmall
  refine ⟨T, L', hTfin, hsub, hLT, hT, ?_, hDN, ?_, hNU, f, hf, ?_, ?_⟩
  · rw [← hsub.space_eq]
    exact Filter.mem_of_superset ht.isNeighborhood (derivedNeighborhood_space_subset T L')
  · rw [← hsub.space_eq]
    exact ht.isNeighborhood
  · rw [← hsub.space_eq]
    exact hfN
  · intro x hx
    have hx' : x ∈ ⋃ v ∈ L'.vertices, C v := by
      rw [← ht.unionEq]
      exact hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx'
    have hvC : v ∈ C v := by
      have hmem : v ∈ C v ∩ L'.vertices := by
        rw [ht.dualVertex hv]
        exact mem_singleton v
      exact hmem.1
    obtain ⟨y, hy, hfy⟩ := hfv v hv
    calc dist (f x) (h x) ≤ dist (f x) (f y) + dist (f y) (h x) := dist_triangle _ _ _
      _ = dist (f x) (f y) + dist (h v) (h x) := by rw [hfy]
      _ < ε / 4 + ε / 4 := add_lt_add (hfsmall v hv x hxv y hy) (hCsmall v hv v hvC x hxv)
      _ < ε := by linarith

end Assembly

end DifferentialGeometry.Topology.PiecewiseLinear
