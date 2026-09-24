/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSphereImageSplitRim
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatesOfLocallyEventuallyEq
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceSubsetOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.EdgeCollarFamily
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.InitialSurfaceSeparates
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionBallPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.ReducedDiskPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerExists
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalDescentSequence

/-!
# Section 32 pseudo-cells and handle decompositions of tubes

The assemblies `moise322`, `moise321`, `moise323`, `moise324` below prove the four named
propositions of `PseudoCell.lean` for real from the leaves of this file and from the named
propositions `Moise307`, `Moise314` of the earlier sections and `Moise303`, `Moise286`,
`Moise267`, now stated in `MoiseChain.lean` and still unproved (digest
`AD` §5); `Moise267` carries the book's implicit premise that the common boundary of the three
surfaces is non-empty, since its printed proof starts from an edge of `Bd M_i`.
All leaves are proved in their imported topic modules; the assemblies remain
conditional on the named earlier Moise inputs.  Theorem 30.1 is the proved
`separates_or_separates_of_union` and Theorem 30.2 the proved `exists_separates_of_finite_iUnion`;
both are consumed inside leaves.  Book pages 223-229, in the notation of `PseudoCell.lean`;
`P'` is the image of the edge midpoint, `I` the ambient interior of `C'₁ ∪ C'₂`.

The frozen leaves in this module are proved and imported.  `separates_of_locally_eventually_eq` and
`isTopologicalSphere_image_splitRim` are proved in the imported real modules, with their frozen
statements unchanged.  The former reuses the general separating-limit theorem on `closure {p}`.

The route of 32.1 and 32.2 (one producer, digest `AD` §6, §7.13).  Arcs from the two vertices to
the free faces are drawn first (`exists_compact_connected_to_freeFace`); the bi-infinite tower of
canonical configurations of page 224 is then chosen inside `W` and away from the arcs, as one
joint choice (`exists_canonicalTower`, output `IsCanonicalTower`); Lemmas 1 and 3 give the
initial separator `initialSurface` (`separates_initialSurface`); Steps 1-4 and the deletion of
one half of each even torus are one producer of one set, `annularChain H B P'`, together with
the sequence of intermediate separators that is locally eventually constant away from `P'`
(`exists_descentSequence`, output `IsAnnularChain`); the limit step, the book's three-line
broken-line argument of pages 226-227, is the general lemma `separates_of_locally_eventually_eq`;
the topology of the chain, page 227's unproved "`U` is an open two-cell and `U - P'` is a
polyhedron, `Ū = U ∪ Bd D'`", together with the polyhedral three-cell pairs around the points of
`Int E - P'` that page 227 asserts, is `isOpenTopologicalCell_annularChain`; the two components
and clauses (5), (6) are `exists_twoComponents_of_pseudoCell`.  The book re-chooses `W` after
the arcs exist; here `W` stays fixed and the tower avoids the arcs, which is what the re-choice
achieves, since the arcs are compact and disjoint from `D'` while the tori are chosen in small
neighbourhoods of the annuli.

The route of 32.3.  The three-cells `C_{e,1}, C_{e,2}` of page 228 are replaced by closed collars
`W e` of the splitting disks, admissible for 32.2, pairwise disjoint, inside the prescribed
neighbourhoods, and with connected complement in each adjacent dual cell
(`exists_edgeCollarFamily`, output `IsEdgeCollarFamily`).  `moise322` is applied per edge, its
output pinned by `SplitsDualCellsAlong`, and the handle pieces are `handlePiece`, page 228's
closure of the component.  Clauses (7), (9), (10) are `isHandleDecomposition_of_edgeCollars`;
clause (8), never argued in the book, is `handlePiece_subset_of_edgeCollars`, whose hypotheses
are exactly the collar choices: its proof must show that the component of `N' - ⋃ E_e`
containing `h v` leaves `C'_v` only through the collars `W e`, `e ∋ v`, because `C'_w \ W e` is
connected and contains `h w`, so lies on the `h w` side of `E_e`.  The remaining fields are
proved in the assembly.

The route of 32.4.  The missing notion "`Bd C³` in general position relative to `E`" is
`CrossesPseudoCell`: the intersection is a finite union of disjoint polygons inside
`Int E - P'`, at which the two surfaces cross in the sense of `HasPLCrossingAt`.  The ball is
`exists_generalPosition_ball_pseudoCell`; the irreducible disk and the innermost removals are
`exists_reducedDisk_of_crossesPseudoCell`.

The leaves, all owned by lane c, with the printed assertions, the digest `AD` §7 discrepancies
each one covers, and their state after the first external review (digest `AK`, of snapshot
`942bf787`): OK freezes the statement byte for byte, and whoever proves it first tries to refute
it; REPAIRED means restated after that review and passed by the second review (digest AM) in
the repaired form, so all thirteen leaves and the corrected `Moise267` are frozen.  The second
review adds: no connectedness of the common boundary may be required of `Moise267` (it would
exclude the two-circle model of Type 2), and the descent's schedule must complete all four
surgery stages on every compact set away from `P'` — pointwise convergence does not give the
promised local eventual equality.  The review's three counter-models, each checked against
the Lean hypotheses before the restatement: three disjoint, mutually non-enclosing
triangulated cube surfaces met
every former hypothesis of `Moise267` with all common boundaries empty, while the frontier of the
unbounded component is all three surfaces; a compactly supported ambient PL homeomorphism fixing
`D'` and moving the tower only puts a point of an even `T''` onto `h u` while keeping every field
of `IsCanonicalTower`, and then `h u ∈ initialSurface` contradicts `separates_initialSurface`,
because separated points lie off the separator; without tube data the chain leaf admitted
`I = univ` and `h '' Dbd {u, v} = {P'}`, so both tails of the tower converge to `P'` and
`annularChain` is a pinched sphere, not a two-manifold at `P'`.

`exists_canonicalTower` (deep, OK): §7.6 the round-disk reduction, §7.7 the joint bi-infinite
choice including the closure equations, §7.2-7.3 the sequential construction of the `S''_i` from
30.7 (`Moise311` per triple does not compose across overlapping triples, so `Moise307` is
taken), §7.1 the revolved cells being solid tori (fields of `IsRevolvedTorusChain`), and the
avoidance of a closed set disjoint from `D'`, which is §7.13; the tori are chosen inside
`W ∩ Zᶜ`, and the proof must complete adjacent general position and the bridge from the
cylindrical diagram to the annular chain.

`separates_initialSurface` (medium, REPAIRED): Lemma 1 with §7.8's local finiteness, Lemma 3
with the printed slip `{P}` for `{P'}`, the transport of `IsTube.splitSeparates` through `h`
(§7.18).  It now receives `havoid`, the tower's avoidance of `{h u, h v}`, which `moise322`
reads off the tower's avoidance of `Bu ∪ Bv`; without it an even torus may pass through `h u`.

`exists_descentSequence` (deep, REPAIRED): Step 1 with 30.3 and §7.9, Steps 2-4 with the
classification `k ∈ {0, 2}` from 28.6, 30.1, 26.7 and 31.4 and §7.10, §7.8's "`L` is a
two-manifold with boundary", §7.11's cutting of each even torus into two annuli, the deletion of
one of them, and the closedness of the limit set.  It now receives `havoid` as well, and
`Moise267` has the non-empty common boundary premise, which its Type 2 use supplies with the
two seam circles of the annulus `C'` and the two halves `B₁, B₂` of `T''_{2i}`.  Its proof must
show the surgery supports locally finite away from `Bd D'` and `P'`, so that the limit set is
closed and the local stabilisation holds.  `IsAnnularChain` needs no essentiality field: a seam
circle bounding a disk on an even torus has trivial image in the fundamental group of that solid
torus, contradicting `loGenerator` and `hiGenerator`.

`separates_of_locally_eventually_eq` (short, OK): the limit argument of §7.9-7.10; compactness
along the contradiction path gives a finite cover and a uniform stabilisation time, so no
monotonicity of the `M n` is assumed.

`isOpenTopologicalCell_annularChain` (deep, REPAIRED): §7.12, wholly unproved in the book, and
the three-cell pairs of page 227.  It now receives the tube data of `exists_canonicalTower`,
which makes `h '' Dbd {u, v}` a genuine circle carrying the upper end of the chain, and the
separation of the chain itself, the book's route to the closure equality; `moise322` obtains that
separation from `separates_of_locally_eventually_eq` on the descent's closedness output before
calling this leaf, and neither depends on `IsPseudoCell`, so there is no circularity.

`exists_compact_connected_to_freeFace` (medium, OK): page 227's "evidently `v'_i` can be
joined"; a vertex interior point, the cell model and a non-empty free face suffice.

`isTopologicalSphere_image_splitRim` (short, OK): the image rim is a topological circle.

`exists_twoComponents_of_pseudoCell` (medium, OK): §7.14 through `IsTube.freeFaceConnected`,
the "all or none" step and the exclusion of a third component, §7.18.

`exists_edgeCollarFamily` (medium, OK): §7.15-7.16, the finite collar family, chosen jointly and
tapering at the centres.

`isHandleDecomposition_of_edgeCollars` (deep, OK): §7.15, clauses (7), (9), (10).

`handlePiece_subset_of_edgeCollars` (medium, OK): §7.15, clause (8); a finite closed local
envelope controls the closure and `W e ⊆ V v` gives the metric clause.

`exists_generalPosition_ball_pseudoCell` (deep, REPAIRED): §7.17, general position against a
set that is not a polyhedron at `P'`, finiteness of `Bd C³ ∩ E`.  It now also concludes
`Dc ⊆ Metric.ball P δ`, the co-domain control that the finitely many later pushes need.

`exists_reducedDisk_of_crossesPseudoCell` (medium, REPAIRED): §7.17, the irreducible disk
without a well-founded measure, the separating polygon by 30.2, the innermost removals.  The
replacement disk of page 229 lies in `Dc` and not necessarily in `Bl`, so the leaf now takes a
common open set `Ω` containing `Bl` and `Dc` and concludes `Δ ⊆ Ω`; `moise324` takes
`Ω = Metric.ball P δ`.  `CrossesPseudoCell` is the notion of 32.4 and is unchanged: no
piecewise linear condition at the centre.

The three named inputs `Moise303`, `Moise286`, `Moise267` remain registered OPEN dependencies;
the endpoint is not closed by them.  `Moise303` is the Euclidean local form of 30.3, with `Ω`
controlling the small regular neighbourhood and the deleted part the intrinsic interior of the
annulus, and `Moise286`'s `1 < n` is right.

Untested.  `IsTube` has no inhabitant in the tree, and every leaf with a tube hypothesis is
UNTESTED until it has one, which is not vacuity: the tower, the initial surface, the descent,
the chain topology, the arcs, the rim, the two components, the collar family and both handle
leaves.  Not tube-dependent: the limit lemma and both leaves of 32.4, which hold for the tame
`isPseudoCell_planarSquare`: the boundary of a small cube around the origin meets the square in
one polygon, crossing it everywhere, and every hypothesis of `moise324`'s chain is then
supplied.  Inhabiting `IsTube` is not cheap: it needs a finite complex of `ℝ³` with a verified
`IsCombinatorialManifoldWithBoundary 3` certificate, `IsPLBall 3` of its graph dual cells, which
the tree derives only from the boundaryless case, and producers of `splitSeparates` and
`freeFaceConnected`, which do not exist.  No vertex-interior field is needed: the proved
`IsTube.mem_interior_dualCell` below gives `v ∈ Int N ∖ ⋃_{w ≠ v} C_w ⊆ C_v` from
`isNeighborhood`, `unionEq`, `dualVertex` and the closedness of the finitely many dual cells,
and invariance of domain (`InvarianceOfDomain.lean`) transports it to
`h v ∈ interior (h '' C v)`, so the two vertex preimages in every `Separates` clause are
non-empty.  The new predicates `IsCanonicalTower`, `IsAnnularChain`, `IsPLAnnulusWithEnds`,
`IsEdgeCollarFamily` and `CrossesPseudoCell` are pinned producer outputs and are untested;
`SplitsDualCellsAlong` is inhabited by `Moise322.exists_splitsDualCellsAlong`, conditionally.
Every hypothesis of every leaf is supplied by a named producer: the tower's avoidance set by the
arc leaf, the vertex avoidance of the initial surface and the descent by the tower's avoidance
of `Bu ∪ Bv`, the chain separation of the chain topology leaf by the limit lemma, the cell pairs
by the chain leaf, the arcs' disjointness from `E` by the tower's avoidance clause, the collars
by the collar leaf, the per-edge pseudo-cells by `moise322`, and the common open set of the
reduced disk leaf by the ball of the general position leaf.  The `W`-hypotheses of `Moise321`
are satisfiable because `Int D_e` lies in the ambient interior of `C_u ∪ C_v` (finitely many
dual cells, `splitDisjoint`) and `h` preserves interiors by invariance of domain; this is a
fact about `IsTube`, needed by the collar leaf and not carried as a field.

What Section 33 consumes (digest `AD` §8): 32.1(1) in the endgame, (2) at page 231, (3) in
Lemmas 6 and 8, (4) in Lemmas 3, 4, 8; 32.2(5)(6) in Lemmas 6 and 8; 32.3(7)(9)(10) in Lemmas 6,
8, 12, 13 and the endgame; 32.3(8) in Lemma 1, the whole `ε`-budget; 32.4 in Lemma 8 and the
endgame.

The tower, annular-chain and edge-collar predicates, `initialSurface`, `annularChain`,
`handlePiece`, `CrossesPseudoCell`, `SplitsDualCellsAlong`, and the proved
`IsTube.mem_interior_dualCell` and `Moise322.exists_splitsDualCellsAlong` live in
`PseudoCell.lean`. Their producers remain open.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical): `handlePiece_subset_of_edgeCollars` — the
pinned clause of `SplitsDualCellsAlong` makes each side closed and open in `N' \ ⋃ E`, and
`IsPreconnected.constant` on the component does the rest; `IsTube` still has no inhabitant, so the
theorem is proved but untested on an instance.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statements byte-identical with the frozen leaves):
`exists_compact_connected_to_freeFace` (module `FreeFaceArc`, the image of a model segment from
the vertex to a free-face point), `exists_twoComponents_of_pseudoCell` (module
`TwoComponentsOfPseudoCell`: separation extends to frontier points through small model
neighbourhoods and each rim circle lies in the closure of the free face), `exists_edgeCollarFamily`
(module `EdgeCollarFamily`, radial collars in the model simplex tapering at the midpoint) and
`isHandleDecomposition_of_edgeCollars` (module `HandleDecompositionOfEdgeCollars`; the connectivity
step is Theorem 30.2 inside the ball `C w`).  `FreeFaceArc` also carries the shared tube-topology
layer the other three modules import.  `IsTube` still has no inhabitant.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statement byte-identical with the frozen leaf): `separates_initialSurface`
(lane F's entry 11, module `InitialSurfaceSeparates`): the split-disk separation is moved into
the interior through `h` and the separator is swapped inside the closed set `⋃ S''ᵢ ∪ {P'}` by
`Separates.of_frontier_subset_replacement`; no limit argument is needed.

Interface change by owner decision (2026-09-22, option A for Section 33's Lemma 8):
`IsHandleDecompositionOfTube` gained the field `rimFrontier : Ec e ∩ frontier N' = Ebd e`, so the
frozen `Moise323` conclusion is wider.  The assembly `moise323` supplies it from the collar clause
`W ∩ frontier (C'_u ∪ C'_v) = h '' Dbd` of `IsEdgeCollarFamily`, `Ec ⊆ W` of
`SplitsDualCellsAlong`, and `IsTube.disjoint_image_rim_interior`; no leaf statement changed.

Proved and imported (external collaborator, PR #10, lead-accepted on 2026-09-23 with zero-diagnostic
checks and an axiom audit; statements byte-identical): `isOpenTopologicalCell_annularChain`
(module `AnnularChainPseudoCell` over the `AnnularChain*` modules: the two-ended open-cell
compactification, local polyhedrality off the centre, the closure adding exactly the intrinsic rim
of the splitting disk, the local pair of PL 3-balls meeting in a PL disk, and the control of
accumulation of canonical annular chains), `exists_generalPosition_ball_pseudoCell` (module
`GeneralPositionBallPseudoCell`: a small PL ball around the centre whose frontier has a finite
transverse polygon trace, and a clean trace disk on the ball frontier) and
`exists_reducedDisk_of_crossesPseudoCell` (module `ReducedDiskPseudoCell` over the `PseudoCell*`
modules: an outermost PL disk with its intrinsic rim, supported disk surgery along regular
pseudo-cell patches, a central sphere disk and an innermost non-central trace disk, finite circle
surgery).  The three reconnaissance probes `Skeleton/Section32*Probe.lean` are deleted as
superseded.  The two leaves left in this file are the canonical tower and the descent.

Proved and imported (Opus 5.5 worker on lease b, Batch 9 of `Skeleton/OPUS_FILL_LOG_B.md`,
lead-accepted on 2026-09-24 with zero-diagnostic checks and an axiom/linter audit; statement
byte-identical): `exists_canonicalTower` (module `CanonicalTowerExists` over
`CenteredDiskSimplexMap`, `RevolvedTorusTower` and `SplitDiskCylinderCoordinates`: the model tower
of revolved squares in the unit cylinder with exact tail closures and local finiteness, cylinder
coordinates on the two dual cells of the edge from `h` and the centred prism, the fitting and
general-position lemmas adapted from the reconnaissance probe
`Skeleton/CanonicalTowerReduction.lean`, whose descent stages remain a route record for the last
leaf).  `Moise307` enters once per integer index through the named input `h307`.
The descent leaf is proved in `CanonicalDescentSequence` and imported here.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

end Leaves

section Assemblies

open Classical in
theorem moise322 (h307 : Moise307) (h303 : Moise303) (h286 : Moise286) (h267 : Moise267)
    (h314 : Moise314) : Moise322 := by
  intro K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub hWfr hWK
  set P' : E3 := h (({u, v} : Finset E3).centroid ℝ id) with hP'
  have hcard : ({u, v} : Finset E3).card = 2 := Finset.card_pair huv
  obtain ⟨Bu, hBuc, hBucon, hBuu, hBuC, hBuD, hBuF⟩ :=
    exists_compact_connected_to_freeFace ht hu he hcard (Finset.mem_insert_self u {v})
  obtain ⟨Bv, hBvc, hBvcon, hBvv, hBvC, hBvD, hBvF⟩ :=
    exists_compact_connected_to_freeFace ht hv he hcard
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  obtain ⟨φ, Pt, Dp, Dpint, J, A, S, T, S'', T'', htw, hZ⟩ :=
    exists_canonicalTower ht hu hv huv he hP' hW hWint hWsub hWfr hWK h307
      (hBuc.isClosed.union hBvc.isClosed) (Disjoint.union_left hBuD hBvD)
  have havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3) := fun i =>
    (hZ i).mono_right (insert_subset_iff.mpr
      ⟨mem_union_left _ hBuu, singleton_subset_iff.mpr (mem_union_right _ hBvv)⟩)
  obtain ⟨hcl₁, hsep₁⟩ := separates_initialSurface ht hu hv huv he hP' htw havoid
  obtain ⟨H, B, Jlo, Jhi, M, hch, -, hMcl, hMsep, hMP, hLcl, hloc⟩ :=
    exists_descentSequence ht hu hv huv he hP' htw havoid hcl₁ hsep₁ h303 h286 h267 h314
  have hP'U : P' ∈ annularChain H B P' := by
    change P' ∈ (⋃ i, H i ∪ B i) ∪ {P'}
    exact mem_union_right _ (mem_singleton _)
  have hsing : ∀ y : E3,
      IsPreconnected (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {y}) := by
    intro y
    refine Set.Subsingleton.isPreconnected ?_
    intro a ha b hb
    exact Subtype.ext ((mem_singleton_iff.mp (mem_preimage.mp ha)).trans
      (mem_singleton_iff.mp (mem_preimage.mp hb)).symm)
  have hsepU : Separates
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' annularChain H B P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}) := by
    have : LocallyPathConnectedSpace (interior (h '' C u ∪ h '' C v)) :=
      isOpen_interior.locallyPathConnectedSpace
    refine separates_of_locally_eventually_eq (p := ⟨P', htw.centerMemInterior⟩) hMcl hMsep
      (fun n => hMP n) (hsing (h u)) (hsing (h v)) hLcl hP'U ?_
    rintro ⟨x, hxI⟩ hxp
    have hxP : x ≠ P' := fun hx => hxp (Subtype.ext hx)
    obtain ⟨U, hU, n₀, hn⟩ := hloc x hxI hxP
    refine ⟨((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' U,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU, n₀, fun n hn' => ?_⟩
    simp only [← preimage_inter, hn n hn']
  obtain ⟨hcell, hlp, hclos, hpairs⟩ :=
    isOpenTopologicalCell_annularChain ht hu hv huv he hP' htw hch hsepU
  have hsph : IsTopologicalSphere 1 (h '' Dbd {u, v}) :=
    isTopologicalSphere_image_splitRim ht he hcard
  have hmid : ({u, v} : Finset E3).centroid ℝ id ∈ D {u, v} ∩ K.space := by
    rw [ht.splitMidpoint he hcard]
    exact mem_singleton _
  have hP'K : P' ∈ h '' K.space := ⟨_, hmid.2, hP'.symm⟩
  have hP'D : P' ∈ h '' D {u, v} := ⟨_, hmid.1, hP'.symm⟩
  have hP'W : P' ∈ W := by
    have hmem : P' ∈ W ∩ h '' K.space := by
      rw [hWK]
      exact mem_singleton _
    exact hmem.1
  have hDbdD : h '' Dbd {u, v} ⊆ h '' D {u, v} := by
    refine image_mono ?_
    rw [← ht.splitProper _ he hcard]
    exact inter_subset_left
  have hDbdfr : h '' Dbd {u, v} ⊆ frontier (h '' C u ∪ h '' C v) := by
    rw [← hWfr]
    exact inter_subset_right
  have hUI : annularChain H B P' ⊆ interior (h '' C u ∪ h '' C v) := by
    change (⋃ i, H i ∪ B i) ∪ {P'} ⊆ _
    refine union_subset (iUnion_subset fun i => union_subset ?_ ?_)
      (singleton_subset_iff.mpr htw.centerMemInterior)
    · exact (hch.halfSubsetTorus i).trans (htw.subsetInterior _)
    · exact (hch.bridgeSubset i).trans (union_subset
        (union_subset (htw.subsetInterior _) (htw.subsetInterior _)) (htw.subsetInterior _))
  have hUW : annularChain H B P' ∪ h '' Dbd {u, v} ⊆ W := by
    refine union_subset ?_ ?_
    · change (⋃ i, H i ∪ B i) ∪ {P'} ⊆ W
      refine union_subset (iUnion_subset fun i => union_subset ?_ ?_)
        (singleton_subset_iff.mpr hP'W)
      · exact (hch.halfSubsetTorus i).trans (htw.subsetW _)
      · exact (hch.bridgeSubset i).trans (union_subset
          (union_subset (htw.subsetW _) (htw.subsetW _)) (htw.subsetW _))
    · rw [← hWfr]
      exact inter_subset_left
  have hEK : (annularChain H B P' ∪ h '' Dbd {u, v}) ∩ h '' K.space = {P'} := by
    refine Subset.antisymm (fun x hx => ?_)
      (singleton_subset_iff.mpr ⟨mem_union_left _ hP'U, hP'K⟩)
    rw [← hWK]
    exact ⟨hUW hx.1, hx.2⟩
  have hE : IsPseudoCell (annularChain H B P' ∪ h '' Dbd {u, v}) (annularChain H B P')
      (h '' Dbd {u, v}) P' :=
    ⟨rfl, hcell, hsph, disjoint_interior_frontier.mono hUI hDbdfr, hclos, hP'U, hlp⟩
  have hdisjE : ∀ Bx : Set E3, Bx ⊆ Bu ∪ Bv → Disjoint Bx (h '' D {u, v}) →
      Disjoint Bx (annularChain H B P' ∪ h '' Dbd {u, v}) := by
    intro Bx hBx hBxD
    have hBxS : ∀ i, Disjoint Bx (φ '' S i) := fun i => ((hZ i).mono_right hBx).symm
    refine disjoint_union_right.mpr ⟨?_, hBxD.mono_right hDbdD⟩
    change Disjoint Bx ((⋃ i, H i ∪ B i) ∪ {P'})
    refine disjoint_union_right.mpr ⟨disjoint_iUnion_right.mpr fun i => ?_,
      disjoint_singleton_right.mpr fun hP => disjoint_left.mp hBxD hP hP'D⟩
    refine disjoint_union_right.mpr ⟨(hBxS _).mono_right (hch.halfSubsetTorus i), ?_⟩
    exact Disjoint.mono_right (hch.bridgeSubset i) (disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hBxS _, hBxS _⟩, hBxS _⟩)
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hd, hcover, hpre, hf₁, hf₂, hF₁, hF₂⟩ :=
    exists_twoComponents_of_pseudoCell ht hu hv huv he hP' hWsub hWfr hE rfl hUW hsepU hpairs
      ⟨hBuc, hBucon, hBuu, hBuC, hdisjE Bu subset_union_left hBuD, hBuF⟩
      ⟨hBvc, hBvcon, hBvv, hBvC, hdisjE Bv subset_union_right hBvD, hBvF⟩
  exact ⟨_, _, _, U₁, U₂, hE, rfl, hUW, hsepU, hEK, hU₁, hU₂, hc₁, hc₂, hd, hcover, hpre,
    hf₁, hf₂, hF₁, hF₂⟩

theorem moise321 (h307 : Moise307) (h303 : Moise303) (h286 : Moise286) (h267 : Moise267)
    (h314 : Moise314) : Moise321 := by
  intro K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub hWfr hWK
  obtain ⟨Ec, Eint, Ebd, -, -, hpc, hbd, hsub, hsep, hK, -⟩ :=
    moise322 h307 h303 h286 h267 h314 K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub
      hWfr hWK
  exact ⟨Ec, Eint, Ebd, hpc, hbd, hsub, hsep, hK⟩

open Classical in
theorem moise323 (h307 : Moise307) (h303 : Moise303) (h286 : Moise286) (h267 : Moise267)
    (h314 : Moise314) : Moise323 := by
  intro K N C D Dbd h N' ht V hV
  obtain ⟨W, hW⟩ := exists_edgeCollarFamily ht V hV
  have hall : ∀ e : Finset E3, ∃ Ec Eint Ebd : Set E3, e ∈ K.faces → e.card = 2 →
      ∃ u v : E3, u ∈ K.vertices ∧ v ∈ K.vertices ∧ u ≠ v ∧ e = {u, v} ∧
        SplitsDualCellsAlong K N C Dbd h (W e) Ec Eint Ebd u v := by
    intro e
    by_cases hedge : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨he, hc⟩ := hedge
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
      have hu : u ∈ K.vertices := K.down_closed he
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self u {v}))
        (Finset.singleton_nonempty u)
      have hv : v ∈ K.vertices := K.down_closed he
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)))
        (Finset.singleton_nonempty v)
      obtain ⟨hWcl, hWint, hWK, hWpair, -, -⟩ := hW _ he hc
      obtain ⟨hWsub, hWfr⟩ := hWpair u (Finset.mem_insert_self u {v}) v
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) huv
      obtain ⟨Ec, Eint, Ebd, hS⟩ :=
        (moise322 h307 h303 h286 h267 h314).exists_splitsDualCellsAlong ht hu hv huv he hWcl
          hWint hWsub hWfr hWK
      exact ⟨Ec, Eint, Ebd, fun _ _ => ⟨u, v, hu, hv, huv, rfl, hS⟩⟩
    · exact ⟨∅, ∅, ∅, fun he hc => absurd ⟨he, hc⟩ hedge⟩
  choose Ec Eint Ebd hE using hall
  obtain ⟨hone, hcover, hedge, hnonedge⟩ := isHandleDecomposition_of_edgeCollars ht hW hE
  have hsub := handlePiece_subset_of_edgeCollars ht hW hE
  refine ⟨Ec, Eint, Ebd, handlePiece K N' Ec h,
    ⟨ht, ?_, ?_, ?_, ?_, ?_, hone, hcover, fun _ _ => rfl, hedge, hnonedge⟩, ?_⟩
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.1
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.2.1
  · intro e he hc
    obtain ⟨u, v, hu, hv, huv, rfl, hS⟩ := hE e he hc
    obtain ⟨-, -, -, hWpair, -, -⟩ := hW _ he hc
    obtain ⟨hWsub, hWfr⟩ := hWpair u (Finset.mem_insert_self u {v}) v
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) huv
    have hY : h '' C u ∪ h '' C v ⊆ N' := by
      rw [ht.imageEq, ← image_union]
      exact image_mono (union_subset (ht.dualCell_subset hu) (ht.dualCell_subset hv))
    refine Subset.antisymm ?_ ?_
    · intro x hx
      have hxW : x ∈ W {u, v} := hS.2.2.1 hx.1
      have hxY : x ∈ h '' C u ∪ h '' C v := hWsub hxW
      have hxc : x ∈ closure (h '' C u ∪ h '' C v)ᶜ :=
        closure_mono (compl_subset_compl.mpr hY)
          (frontier_eq_closure_inter_closure.subset hx.2).2
      have hxfr : x ∈ frontier (h '' C u ∪ h '' C v) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hxY, hxc⟩
      rw [hS.2.1, ← hWfr]
      exact ⟨hxW, hxfr⟩
    · intro x hx
      have hxE : x ∈ Ec {u, v} := by
        rw [hS.1.carrierEq]
        exact Or.inr hx
      have hxN' : x ∈ N' := hY (hWsub (hS.2.2.1 hxE))
      have hN'cl : IsClosed N' := by
        rw [ht.imageEq]
        exact (ht.isCompact.image_of_continuousOn ht.continuousOn).isClosed
      refine ⟨hxE, ?_⟩
      rw [frontier, hN'cl.closure_eq]
      refine ⟨hxN', fun hint => ?_⟩
      rw [hS.2.1] at hx
      exact disjoint_left.mp (ht.disjoint_image_rim_interior he hc) hx hint
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.2.2.2.2.1
  · intro e he hc f hf hfc hef
    obtain ⟨-, -, -, -, -, hdisj⟩ := hW e he hc
    refine (hdisj f hf hfc hef).mono ?_ ?_
    · obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
      exact hS.2.2.1
    · obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE f hf hfc
      exact hS.2.2.1
  · intro v hv
    refine (hsub v hv).trans (union_subset (subset_of_mem_nhdsSet (hV v hv))
      (iUnion₂_subset fun e he => ?_))
    obtain ⟨he₁, he₂, he₃⟩ := he
    obtain ⟨-, -, -, -, hVe, -⟩ := hW e he₁ he₂
    exact (hVe v he₃).2

theorem moise324 : Moise324 := by
  intro Ec Eint Ebd P hE δ hδ
  obtain ⟨Bl, Dc, Dcint, hBl, hBδ, hPB, hDc, hDcE, hDcδ, hPDc, hBE, hgp⟩ :=
    exists_generalPosition_ball_pseudoCell hE hδ
  obtain ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩ :=
    exists_reducedDisk_of_crossesPseudoCell hE hBl hPB hDc hDcE hPDc hBE hgp
      Metric.isOpen_ball hBδ hDcδ
  exact ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩

end Assemblies

end DifferentialGeometry.Topology.PiecewiseLinear
