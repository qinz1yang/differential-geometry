# Spine carrier reduction: decision note

Status: reconnaissance only, 2026-09-22. The five new leaves are **UNREVIEWED**. This file neither
freezes them nor accepts a worker delivery. No existing source, queue, ledger, import aggregate,
compiler lease, Git state, or running process is changed by this probe.

Source snapshot: `0642f2e7deaa33a527f3c08fe058b08ff0ee0187`. The inspected
`Section31CanonicalConfiguration.lean` SHA-256 is
`6C38CED42DEA555D3FD55F0EE8BA50C2DA3BB233DC772456BF92EBB5E41A7C7D`.
The complete frozen `exists_polygon_carrier_of_spine` declaration header, including all hypotheses
and its conclusion, is copied byte-for-byte into the isolated namespace
`DifferentialGeometry.Topology.PiecewiseLinear.SpineCarrier`. No shared vocabulary was copied:
all chains, homology, carrying, PL circle, solid-torus and spine predicates are real imports.
The probe is never imported by another module.

## What changed since the AP assessment

The comment that the tree has no chain-level integral first homology is obsolete.
`FirstHomologyCarrying.lean` now provides `integralOneCycleClass_surjective` (line 49),
`hurewiczOne_map` (114), `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto` (131),
`CarriesFirstHomologyOnto.exists_cycle` (190), and
`exists_boundary_sub_mem_integralSingularChainsIn_inter` (271).
These are used as actual imports, not restated as new assumptions.
`Homology/HurewiczOne.lean:118` proves surjectivity of the Hurewicz map; it does not by itself prove
injectivity. The forbidden sorry-bearing `HurewiczLowDegrees` is not imported.

There is also a proved product-coordinate theorem for finite disjoint essential polygons in
`EssentialPolygonProductCoordinates.lean:358`. Thus the extraction after normalization does not
need a new torus-classification theorem. The genuinely new geometric bridge is controlled
chain cutting, followed by polygonal resolution inside the prescribed relatively open patch.

## Dependency sequence and classification

| Declaration | Classification | Exact obligation and available route |
| --- | --- | --- |
| `integralFirstHomology_interior_injective` | `SMALL_NEW_LEMMA` | The actual inclusion `interior S → S` is injective on integral H1 for a topological solid torus in E3. Use the closed-disk times circle homeomorphism, identify the ambient interior, and radially contract the disk coordinate. `InnerSolidTorusToroidalShell.lean:66` already implements this interior identification in its proof, using `mem_interior_of_homeomorph_closedBall_prod_sphere`; `Homology/Homotopy.lean:19` transports homology and `Integral.lean:56` provides homotopy invariance. A reusable public inclusion homotopy equivalence remains to be exposed. |
| `exists_frontier_cycle_of_boundary_in_open` | `NEW_THEORY` | Given a supported 2-chain in an open A with boundary z - w, with z inside S and w outside S, cut it at the PL frontier to produce v supported in `frontier S ∩ A`, homologous to z through a chain in S. Only chain support, boundary equations, openness and CST geometry are inputs. Small-chain subdivision and two-open-set splitting already exist in `FirstHomologyCarrying.lean:271`; the remaining work is a PL bicollar push/excision argument that lands exactly on the frontier and retains A-control. This is the relative chain-cut theorem, not the polygon-carrier endpoint under another name. |
| `nonempty_integralFirstHomology_equiv_int` | `CURRENT_API` | Its proof body is supplied: contract the disk factor via `HomotopyEquiv.productConvex`, transport with `integralSingularHomologyHomotopyEquiv`, then use `integralSphereTopHomologyEquiv 0 E2` from `Homology/SphereTopHomology.lean:17`. No sorry here. |
| `exists_disjoint_oriented_polygons_of_cycle` | `NEW_THEORY` | A nonzero ambient homology class represented in `frontier S ∩ U`, U open, becomes a finite nonempty family of pairwise disjoint PL circles in that SAME patch. Each circle receives an integral generator cycle and an integer weight; the sum of their included classes equals the original class in H1(S). Required construction: finite subordinate triangulation/PL approximation, oriented edge-cycle resolution at vertices, local crossing smoothing, and a supported homology witnessing preservation. Compact support must provide the margin inside U. No already-disjoint input and no ambient-only approximation suffices. |
| `exists_maximal_firstHomology_image_of_disjoint_polygons` | `SMALL_NEW_LEMMA` | Among finitely many disjoint boundary polygons, one inclusion-image subgroup contains every other inclusion-image subgroup in H1(S). Remove boundary-disk-bounding circles, whose image is zero; if at least two essential circles remain, use the proved `exists_product_coordinates_for_disjoint_essential_polygons` and transport between its level circles by a homotopy. Zero or one essential circle are separate easy cases. This is strictly weaker than asserting one polygon carries a generator. The proof must compare the image subgroups themselves, not use the existing carrier theorem that already assumes one polygon is surjective. |
| `hurewiczOne_injective_of_isTopologicalSolidTorus` | `SMALL_NEW_LEMMA` | Only the solid-torus case is needed. `Moise308Nested.lean:60` already proves a PRIVATE `fundamentalGroupSolidTorusEquivInt`; the preceding H1 equivalence and `hurewiczOne_surjective` turn the map into a surjective endomorphism of Z, hence an injective one. Expose the existing private fundamental-group equivalence coherently or repeat its argument locally. A full degree-one Hurewicz/abelianization development is unnecessary for this decision. |

`SMALL_NEW_LEMMA` means a bounded derivation from identified mathematical infrastructure, not an
already compiled result or a promise of a completion time. The interior transport and restricted
Hurewicz leaves are suitable first attempts today. The common-image leaf is also feasible with
current theory, but filtering circles and transporting the inclusions are substantive API work.
The two `NEW_THEORY` leaves should be budgeted as separate developments.

## Assembly actually written

1. `carriesFirstHomologyOnto_subset_of_injective` proves the restriction-to-interior step by
   injectivity and functoriality. It does not assume the desired interior carrier.
2. `carriesFirstHomologyOnto_frontier_inter_of_cutting` starts with ANY target integral 1-cycle.
   Existing carrier APIs replace it by a cycle q in the common interior set, then replace q by
   a cycle p in the outside carrier. They supply the two actual bounding chains. The cut leaf
   returns a frontier cycle v, and the proof adds the two chains to show the original cycle is
   homologous to v. This is the all-classes statement, not merely a nonzero-class assertion.
3. `exists_polygon_carrier_of_firstHomology` chooses the class corresponding to 1 under H1(S) ≃ Z,
   takes a cycle representative, normalizes it, and uses the maximal image subgroup. That subgroup
   contains the weighted sum, hence contains 1, hence is all of Z. The integer-span argument is
   in the proof body; it is not a new sorry or a “some summand is a generator” assumption.
4. `carriesFundamentalGroupOnto_of_firstHomology` uses Hurewicz naturality, surjectivity for the
   polygon, and the restricted injectivity for S to recover the required SURJECTIVITY of the
   fundamental-group inclusion at every basepoint.
5. The endpoint obtains the common spine's fundamental-group surjectivity in each S_i from the
   real `fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus`
   (`Moise308Nested.lean:395`). It obtains nonemptiness directly from the spine homeomorphism,
   transports Z0 to interior S1 on H1, invokes the chain-cut assembly, and extracts the polygon.

The S1-side spine generator certificate is derived explicitly to preserve the frozen hypotheses,
but the chain-cut route only needs Z1 to carry S2 and to lie inside S1. Thus the extra T1 data are
not newly needed assumptions. The reduction potentially proves a more general theorem, but the
frozen external signature is deliberately unchanged.

The normalization output contains genuinely oriented circle classes (`zmultiples = top`) and
integer multiplicities. Extraction needs only their image-subgroup membership; retaining the
stronger orientation output makes the intended geometric normalization precise. For arbitrary
classes, mere nonzero image is insufficient: for instance image subgroups 2Z and 3Z generate Z
without either being Z. The disjoint-torus common-image step is exactly what excludes that failure.

## Edge cases and joint paper fixture

- Z0 is not assumed closed, PL, connected, or itself a polygon. Nonemptiness is essential before
  using its fundamental-group carrier to infer homology surjectivity. Only the finite singular
  cycles obtained from it have compact support.
- U is ambient open; `frontier S ∩ U` is relatively open in the boundary. Normalization must stay
  there. It must not take ambient interior of the two-dimensional boundary.
- The nonzero selected class forces a nonempty polygon family. Null-homologous polygons, negative
  weights, repeated singular-simplex multiplicities and opposite orientations are all permitted.
  The output GEOMETRIC circles are pairwise disjoint, not merely distinct labels.
- S1 and S2 need no mutual general position. They may be nested and their boundaries may be disjoint.
  Chain cutting is an independent construction; it cannot borrow transverse intersection polygons.
- H1 on the carrier is integral. Rational nonzero classes would not certify a generator of Z.
- Polygon essentiality on the boundary differs from nonzero class in the solid torus: meridians are
  essential boundary curves whose image in H1(S) is zero. The common-image proof must include them.

A single nondegenerate paper model is the square torus
`C_a = { (x,y,z) | 4-a ≤ max(|x|,|y|) ≤ 4+a, |z| ≤ a }`.
Take `S1=C_2`, `S2=C_1`, `T1=C_3`, `T2=C_(5/2)`, common spine
`Z1={max(|x|,|y|)=4,z=0}`, and outside carrier
`Z0={max(|x|,|y|)=11/2,z=0}`. These finite cubical polyhedra admit compatible triangulations;
the common square core is a spine of both larger tori. Z0 lies in interior S1, avoids S2 and carries
its longitudinal generator. The planar square annulus from radii 4 to 11/2 gives the cutting chain;
its cut at radius 5 is a longitudinal polygon in `frontier S2 ∩ interior S1`. Thus the cut,
normalization and generator extraction can be instantiated together. Both larger-torus inclusions
are strict. Additional small null-homologous circles and opposite weights test cancellation.
This is a paper model only: **the joint Lean inhabitant is UNTESTED**.

## Verification boundary

The preserved endpoint header was compared as a raw string with the current frozen source and was
identical. Five sorry occurrences are confined to the five listed mathematical subleaves; the
homology computation and all carrier/chain/integer/basepoint assemblies have explicit proof bodies.
The parent session coordinates the permitted private compiler lane. Compilation evidence is to be
recorded after that check; source-written assembly alone is not an elaboration or axiom certificate.
No whole-library build, integration, ledger change, acceptance, commit, push, or worker dispatch is
part of this reconnaissance request.
