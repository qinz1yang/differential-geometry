# Meridian exclusion: minimal integral linking reconnaissance

Date: 2026-09-22. Source baseline: `0642f2e7deaa33a527f3c08fe058b08ff0ee0187`.
Scope: reconnaissance only; no integration, leaf acceptance, ledger change, or worker dispatch.
Companion: [TorusLinkingReduction.lean](TorusLinkingReduction.lean).

The exact endpoint is copied from
`Section31CanonicalConfiguration.exists_isPLCell_frontier_of_polygon_nullhomotopic` into the
isolated namespace `DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking`. The copy retains
every input and the exact disk parametrization `G = r' '' stdSimplexBoundary 2`. Its proof and
the carrying/vanishing diagrams contain no `sorry`. Four strictly smaller mathematical leaves
contain the authorized `sorry`s. These new interfaces are **UNREVIEWED**, not newly frozen.

## Decision

There is no remaining surface-disk recognition problem in this endpoint. The existing
`IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff` already returns the required
PL parametrization and exact intrinsic rim. The only obstruction to applying it is the
nonseparating case. An integral first-homology calculation excludes that case.

The smallest useful reusable linking interface here is an integer character on the complement
of the **boundary polygon G**, not a linking number assigned to the set Z. The endpoint permits
arbitrary nonempty Z, with no compactness, polyhedrality, connectedness, or embedded-circle
certificate. Its only geometric requirement is `Z ⊆ interior S`, and its only carrying
requirement is surjectivity on fundamental groups. Existing Hurewicz naturality turns that into
the exact homology surjectivity used below.

The probe uses an additive equivalence `H₁(Gᶜ; ℤ) ≃+ ℤ`. Choosing it fixes linking up to sign;
the proof needs no sign convention. For the endpoint alone a surjective integer character and a
nonzero restriction would suffice. The equivalence and surjective restriction state the standard
computations independently and make the missing producer obligations explicit.

## Four open subleaves

| Declaration | Classification | Exact content | Assessment |
|---|---|---|---|
| `exists_integer_linking_equiv_of_isPLSphere` | `NEW_THEORY` | Integral H₁ of the complement of any PL circle in R³ is Z. | A complement/linking calculation is missing. No unknot hypothesis is added. |
| `subsingleton_firstHomology_complement_of_isPLBall` | `NEW_THEORY` | Integral H₁ of the complement of a PL two-disk in R³ vanishes. | It needs a complement argument; disk contractibility alone says nothing about its complement. Could share a narrow Alexander-duality or signed-intersection development with the previous leaf. |
| `injective_firstHomologyInclusion_interior_solidTorus` | `SMALL_NEW_LEMMA` | The **actual inclusion** `Int S → S` is injective on H₁. | Plausible same-day work: transport the radial product homotopy through the existing topological solid-torus coordinates, prove the interior stays interior, then use homotopy invariance. |
| `surjective_firstHomologyInclusion_complement_of_null_meridian` | `NEW_THEORY` | For a nonseparating boundary polygon killed in π₁(S), the **actual inclusion** `Int S → Gᶜ` is onto on H₁. | The geometric normalization: a primitive null slope is a meridian and links the core with degree ±1. Abstract group types Z² and Z do not compute this inclusion. |

The fourth leaf is independent of the spanning disk Δ and the carrier Z. The second leaf is
independent of S and G. The first leaf applies equally to knotted polygons. None is the original
disk-existence conclusion hidden in a hypothesis or renamed as a leaf.

The fourth leaf still has two implementation layers, which should not be conflated:

1. Identify the primitive class of a nonseparating embedded polygon in the boundary torus. The
   vanishing map to π₁(S) puts it on the primitive meridian slope. One must identify the actual
   boundary inclusion; `Z² → Z` having some kernel is insufficient.
2. Normalize the complement generator by an oriented meridian/core intersection, and prove
   naturality under the chosen PL/topological transport. This yields degree ±1 and hence the
   surjective H₁ map in the leaf. A possibly knotted solid torus is allowed; an ambient
   homeomorphism taking it to the standard unknotted torus cannot be assumed.

A broad knot classification, a full linking form for arbitrary compact sets, and a general
Alexander-duality library are not endpoint requirements. A finite PL chain/intersection
construction proving these specific complement computations would suffice. The probe does not
pretend the interface declarations are their constructions.

## Real assembly

Write `I = Int S`, `C = Gᶜ`, and `D = Δᶜ`. All arrows below are the literal inclusion maps:

```text
H₁(Z) ───────► H₁(I) ───────► H₁(S)
  │               │            ↑ injective from H₁(I)
  │               └──────────► H₁(C) ≃ Z
  └──────────► H₁(D)=0 ──────► H₁(C)
```

1. `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto` gives `H₁(Z) → H₁(S)` onto. This
   uses Z's nonemptiness and S's path connectedness, without assuming Z path connected.
2. Injectivity of `H₁(I) → H₁(S)` and functoriality force `H₁(Z) → H₁(I)` onto. This
   cancellation is proved in `surjective_firstHomologyInclusion_of_carries_of_injective`.
3. In the nonseparating branch, the meridian leaf makes `H₁(I) → H₁(C)` onto. Thus Z supplies
   a preimage of the class with integer linking value 1.
4. `Disjoint Δ Z` gives `Z ⊆ D`, and the exact parametrized rim gives `G ⊆ Δ`, hence
   `D ⊆ C`. Therefore the same Z class maps through the zero group H₁(D). This factorization
   is proved in `firstHomologyInclusion_eq_zero_of_factorization`.
5. Applying the integer character gives `1 = 0`. Thus the polygon separates the boundary
   torus; the existing separating-polygon theorem returns the exact required disk.

`hIG : interior S ⊆ Gᶜ` is explicitly proved from `G ⊆ frontier S` and disjointness of interior
and frontier. It is a transport inclusion, not an added mathematical premise at the endpoint.
The proof uses the existing integral singular homology objects and maps; there is no substitute
homology type with the desired laws postulated as fields.

## Current API evidence and work that can start now

| Current source | Reusable fact | Classification |
|---|---|---|
| `FirstHomologyCarrying.lean:131` | `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto` with no connectedness requirement on Z | `CURRENT_API` |
| `FirstHomologyCarrying.lean:114` | `hurewiczOne_map`, naturality on actual continuous maps | `CURRENT_API` |
| `Section34Frame.lean:312` | Exact carrier definition, including the basepoint quantifier; emptiness would be vacuous without `hZ` | `CURRENT_API` |
| `NonseparatingPolygonCarrier.lean:142` | A topological solid torus is path connected | `CURRENT_API` |
| `Homology/Integral.lean:50` | Functoriality of integral singular homology maps | `CURRENT_API` |
| `Homology/Homotopy.lean:19` | Homotopy equivalence induces integral homology equivalence | `CURRENT_API` |
| `NontrivialKernelInSolidTorus.lean:50` | Interior containment of product-coordinate points with disk norm less than one | `CURRENT_API` |
| `NontrivialKernelInSolidTorus.lean:88-158` | Concrete radial product homotopy, including the time-zero interior check | `CURRENT_API` ingredient for the small new inclusion lemma |
| `ExistsGeneralPositionSolidTorusRelative.lean:272` | The ambient frontier is exactly the disk-coordinate norm-one set | `CURRENT_API` |
| `ExistsGeneralPositionSolidTorusRelative.lean:336` | A CST has a PL torus as its frontier | `CURRENT_API` |
| `BallReplacement.lean:12` | The image of `stdSimplexBoundary 2` under the disk parametrization is a PL circle | `CURRENT_API` |
| `SeparatingPolygonDisk.lean:60` | Separating PL circles on a PL torus bound an exactly parametrized disk | `CURRENT_API` |

The proof-bearing carrier cancellation, complement factorization, subtype inclusions, integer
contradiction, and final disk conversion are already written in this probe. The interior H₁
injection is the most bounded next proof task. A source search found no existing integral H₁
of polygon/disk complements or linking-number API in `Topology/PiecewiseLinear` or
`Topology/Homology`. There **is** sphere-separation machinery named Alexander duality elsewhere:
`SphereSeparation/TubularExcision.lean:170` produces an H₀ separation certificate from bicollar
data. Its name does not supply either of the H₁ complement computations above.

Source inspection is not a transitive axiom audit. The statuses in this table mean definitions
and proof bodies were found in current real modules, not that this reconnaissance independently
reaccepted the underlying modules.

## Joint paper tests and failure modes

Use the square solid torus `S = {1 ≤ max(|x|,|y|) ≤ 3, |z| ≤ 1}` and its square core
`Z = {max(|x|,|y|)=2, z=0}`, with a compatible finite triangulation. The core carries π₁(S).

For the meridian-computation test take `Δm = {[1,3] × {0} × [-1,1]}` and its rectangular
intrinsic rim Gm. The rim is nonseparating in the boundary, killed by inclusion into S, and the
core has linking value ±1. The polygon-complement character, disk-complement vanishing, interior
inclusion, and meridian-surjectivity leaves all apply to this one configuration. Crucially,
`Δm ∩ Z = {(2,0,0)}`: the endpoint's disjointness assumption fails, exactly as the obstruction
predicts. No fake simultaneous witness of contradictory premises is claimed.

For a complete endpoint test use the small square disk
`Δ0 = {x=3, |y|≤1/4, |z|≤1/4}` on one boundary face, with intrinsic rim G0. It avoids the core
and inclusion G0→S kills π₁. The output disk can be Δ0 itself; G0 separates the boundary.
Both disks admit finite PL parametrizations by the standard two-simplex. These are paper tests,
not compiled Lean inhabitants; joint fixture status is **UNTESTED**.

Do not replace the intrinsic rim by the ambient frontier of a two-disk in R³: that frontier is
the whole disk. Do not assume that Z is itself a loop, or choose a single path component and
silently assume it carries homology. Do not infer a zero complement invariant just from Δ being
contractible. Do not infer a linking value from an abstract Z²/Z rank calculation. Do not call
28.7 backwards to establish the 28.6 producer; the present endpoint uses the independently
available 28.9 separating-disk theorem. Reviews AP and BB support those interface distinctions,
but do not constitute proofs of the four newly proposed leaves.

## Verification boundary

The initial draft was written without launching Lean. A permitted private checker run, if
assigned, must check that the only diagnostics are the four authorized leaf `sorry` warnings,
and compare the copied endpoint's full header against the current frozen source. No root import,
ledger entry, public module promotion, or theorem completion is implied by a successful probe.
