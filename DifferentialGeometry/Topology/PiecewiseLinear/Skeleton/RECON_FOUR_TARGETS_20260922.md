# Four Moise bottlenecks: reconnaissance reductions

This is decision material, not lead acceptance or integration. The four probes use isolated
namespaces, import only real modules, and leave the existing frozen declarations untouched.
Their open mathematical subleaves are UNREVIEWED. Compilation of an assembly does not prove
those subleaves or close the original endpoints. Paper fixtures are not Lean inhabitants.

Starting checkout: `D:\differential-geometry-moise-int`, branch `codex/moise-integration`,
commit `0642f2e7deaa33a527f3c08fe058b08ff0ee0187`. Other workers' files and processes are untouched.
The owner explicitly authorized adding the separate `codex-moise-recon` compiler lane during
this task; existing a-e leases and private outputs are unchanged. The E: checkout is read-only.

## Probes and decisions

| Target | Source and detailed note | Decision |
| --- | --- | --- |
| 28.11, `exists_polygon_carrier_of_spine` | [Lean](SpineCarrierReduction.lean), [note](SpineCarrierReduction.md) | Chain-level H1 and the integer extraction assembly already work with current APIs. First expose interior-inclusion homology injectivity and solid-torus Hurewicz injectivity. Controlled frontier cutting and polygonal resolution inside the prescribed open patch are the new geometric developments. |
| `exists_isPLCell_frontier_of_polygon_nullhomotopic` | [Lean](TorusLinkingReduction.lean), [note](TorusLinkingReduction.md) | The required linking interface is small: polygon-complement H1 is Z, disk-complement H1 vanishes, the actual meridian inclusion is surjective, and interior inclusion is injective. No general link invariant, polygonal assumption on the carrier, or carrier connectedness is added. |
| Section 32 tower and descent | [Lean](CanonicalTowerReduction.lean), [note](CanonicalTowerReduction.md) | The single-torus producer and coherent even/odd selection use current APIs. The controlled source exhaustion remains geometric work. The descent stage probes expose protected seams and actual local operations; an abstract decreasing counter alone does not supply a geometric transition or a global descent sequence. |
| CGN matching and one-step removal | [Lean](ControlledGraphNeighborhoodReduction.lean), [note](ControlledGraphNeighborhoodReduction.md) | Matching separates joint oriented boundary maps, existing cell extension, rim localization, and recognition of the actual target torus. Removal must preserve carrier, tube, and whole-overlap conditions in addition to reducing circles; the note accounts for all 22 piercing clauses. |

`CURRENT_API` in the individual notes means an identified implementation is available.
`SMALL_NEW_LEMMA` means a bounded derivation from named infrastructure, not a time guarantee.
`NEW_THEORY` means a substantive missing construction or compatibility theorem. None of these
labels substitutes for compiler or transitive-axiom evidence.

## Scope of the reductions

The 28.11, nullhomotopic-polygon, canonical-tower, and edge-matching endpoints have actual
assembly bodies. The difficult interfaces are placed below them. The descent-sequence and
protected-removal investigations must additionally identify concrete, mutually compatible
geometric states: merely packaging the final endpoint as a finite-window oracle or assuming
all 22 clauses again would give no useful reduction. Any partial boundary of those two
investigations is stated explicitly in the corresponding notes.

There is no root-aggregate registration, ledger update, frozen-signature change, proof
acceptance, mirror synchronization, commit, or push in this reconnaissance task.

## Verification

All four final sources passed the authorized private checker with Lean exit code 0 and
`sourceStable = true`. Their only compiler diagnostics are the explicit child-leaf warnings:

| Probe | Child sorry warnings | Other diagnostics | SHA256 |
| --- | ---: | ---: | --- |
| SpineCarrierReduction | 5 | 0 | `76cde558e20b9053c8cac508c4c3afae377e7b8a98fa1c2d8a9460e147fbe8cc` |
| TorusLinkingReduction | 4 | 0 | `6fd27bddc2e472ba7b8765b06ae49e9b4b2fa292e996e4d93da6a7c0d5b16d3c` |
| CanonicalTowerReduction | 2 | 0 | `f402c9cdb20349317716d909d765ab0d78a77f335502a1da3ff1a123786a6190` |
| ControlledGraphNeighborhoodReduction | 3 | 0 | `c46fa298604f4388f6e644d084a4233f923562f1a67a97bc53d0fd339f1ded5f` |

The checker deliberately exits nonzero on every diagnostic, including authorized skeleton
warnings. Each raw receipt and log was separately checked for Lean exit 0, an unchanged source
hash, the exact warning count above, and absence of other diagnostics. Receipts live under
`C:\Users\liao9\AppData\Local\Temp\codex-moise-recon\DifferentialGeometry\Topology\PiecewiseLinear\Skeleton`.

The four assembled endpoint declaration headers match the frozen source bytes, including
whitespace: `exists_polygon_carrier_of_spine`,
`exists_isPLCell_frontier_of_polygon_nullhomotopic`, `exists_canonicalTower`, and
`exists_section34EdgeMatching`. All four files have no Skeleton imports, forbidden proof
devices, budget overrides, overlong lines, or trailing whitespace. The source manifest is
`C:\Users\liao9\AppData\Local\Temp\codex-moise-recon\probe-source-manifest.json`.

A consolidated source audit also returned Lean exit 0, with the same 14 authorized warnings
and no unexpected diagnostics. Among 23 explicitly audited declarations, 16 use only a subset
of `propext`, `Classical.choice`, and `Quot.sound`; seven correctly retain `sorryAx` through the
open geometric subleaves. In particular, the single-torus producer, even/odd general-position
selection, finite-rank induction, compatible recursion, local stabilization, cell-boundary
extension, and sampled support-transport lemmas have no `sorryAx`. The assembled open endpoints
still do. No claim of endpoint completion follows from this audit.

The audit concatenated the four final sources with normalized line endings and their combined
real imports, then printed the 23 axiom closures. Its source SHA256 was
`2f6612bca5bc1666a15ae516039e18ef68d260062ac6fbffde135cadac4913e2`.
Detailed names, source hashes and axiom sets are recorded in
`C:\Users\liao9\AppData\Local\Temp\codex-moise-recon\four-probe-verification.json`;
the adjacent `four-probe-axioms-20260922.log` and `.json` preserve the raw evidence.
The external diagnostic source was removed after the check.

The simultaneous integration task independently committed three earlier drafts in
`0872dfa10c8dd503235d5b9504157b990fcaa3d8` while reconnaissance was running. This task did not
make that commit or edit its ledger. The hashes above identify the final checked artifacts;
the commit is not the final four-probe verification snapshot.

## Immediate next attempts

1. Unify the two probes' interior-inclusion H1 obligation in a real module. The actual inclusion
   homotopy, rather than an unrelated homology equivalence, is the required output.
2. Prove solid-torus Hurewicz injectivity using the existing fundamental-group equivalence,
   the checked H1 equivalence, and surjectivity of Hurewicz.
3. Implement common-image subgroup comparison for disjoint boundary polygons using the existing
   product coordinates. Keep the difference between meridians and longitudinal generators.
4. Implement the CGN rim-localization and radial inner-torus bridges before attempting the
   finite marked-sphere matching or cyclic-union recognition.

These are bounded implementation candidates. The new-theory queue is controlled frontier
cutting, open-patch polygonal resolution, complement H1 and its actual meridian map, controlled
outer exhaustion, compatible geometric descent states, and protected local circle cancellation.
The two partial stage probes do not yet justify dispatching a worker merely to fill one
well-specified residual leaf: their joint geometric producer interfaces still need design.
