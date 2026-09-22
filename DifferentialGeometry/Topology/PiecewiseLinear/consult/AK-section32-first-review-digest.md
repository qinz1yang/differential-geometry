# Digest — first external review of `Skeleton/Section32PseudoCell.lean` (snapshot `942bf787`)

Marks: **[V]** checked by the lead against the Lean text; **[–]** not independently verified.

**Docstring corrections.** "No inhabitant theorem, hence the tube leaves are vacuous" is wrong:
the right label is **UNTESTED** [V, line 96]. ⑤ No vertex-interior field is needed: from
`isNeighborhood`, `unionEq`, `dualVertex` and finitely many closed cells,
`v ∈ Int N ∖ ⋃_{w ≠ v} C_w ⊆ C_v` is an open neighbourhood of `v`, and invariance of domain
transports it to the image — the separation clause has no empty-preimage vacuity.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_canonicalTower` | **OK** | ② choose inside `W ∩ Zᶜ`; must complete adjacent general position and the cylindrical-diagram → annular-chain bridge |
| `separates_initialSurface` | **FALSE [V]** | the tower it receives carries no vertex-avoidance certificate; the initial surface may pass through `h u` |
| `exists_descentSequence` | **VACUOUS [V]** | `Moise267` is false as stated, so `h267` is unsatisfiable; acceptable once repaired |
| `separates_of_locally_eventually_eq` | **OK** | ③ compactness along the contradiction path gives a finite cover and a uniform stabilisation time; no monotonicity needed |
| `isOpenTopologicalCell_annularChain` | **FALSE [V]** | receives no tube data; both ends may converge to `P'` |
| `exists_compact_connected_to_freeFace` | OK | vertex interior point, cell model and a non-empty free face suffice |
| `isTopologicalSphere_image_splitRim` | OK | the intrinsic boundary of `splitCell` stays a circle under the embedding |
| `exists_twoComponents_of_pseudoCell` | OK | local two-sidedness, free-face connectedness and the two labelled connecting sets suffice |
| `exists_edgeCollarFamily` | OK | finitely many disjoint collars tapering at the centres can be chosen jointly |
| `isHandleDecomposition_of_edgeCollars` | OK | disjoint collars, connected complements and side labels assemble |
| `handlePiece_subset_of_edgeCollars` | OK | ⑥ a finite closed local envelope controls the closure; `W e ⊆ V v` gives (8) |
| `exists_generalPosition_ball_pseudoCell` | **FIX** | general position right; add the co-domain control of `Dc` for the later finite surgery |
| `exists_reducedDisk_of_crossesPseudoCell` | **FIX** | `Δ ⊆ Bl` is stronger than what cleaning a fixed sphere supplies |

## Leaf 2 — pass the vertex-avoidance certificate
Counter-model [–]: a genuine tube with a flat splitting disk, `W` the whole cell pair; a
compactly supported ambient PL homeomorphism off the disk, fixing `D'`, moving a point of an even
`T''` on one side onto `h u` — *moving the tower only*. All canonical, closure and local-finiteness
conditions survive, but `h u ∈ initialSurface`, contradicting `Separates` (separated points lie in
the complement). Repair for leaves 2 and 3: `(havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))`,
supplied by the tower's avoidance of `Bu ∪ Bv`; no new endpoint hypothesis.

## Leaf 3 — the real vacuity is `Moise267` [V]
Three disjoint, mutually non-enclosing triangulated cube surfaces satisfy every present
hypothesis (common boundaries all empty), but the frontier of the unbounded component is the union
of all **three**. Repair: add `(boundaryComplex 2 (M 0)).space.Nonempty →`; Type 2's two common
boundary circles supply it. ① `Moise303` is acceptable as the Euclidean local form of 30.3 (`Ω`
controls the small regular neighbourhood; the deleted part is the *intrinsic* interior of the
annulus); `Moise286`'s `1 < n` is right. The three named inputs stay **registered OPEN
dependencies**; the endpoint is not closed by them. ③ The four-step package is fine in principle
but the surgery supports must be shown locally finite. ④ No essentiality field: a seam circle
bounding a disk on an even torus has zero `π₁`-map to the solid torus, contradicting the present
`loGenerator`/`hiGenerator` surjections onto `ℤ`.

## Leaf 5 — the two ends cannot be capped by the same point [V-hypotheses]
Without `ht` the leaf admits `I = W = univ`, `Dbdimg = {P'}`: a planar open arc with both ends tending
to `P'` on the axis, a thin torus tower along it, polygonised circles, adjacent longitudinal annuli
— both tail closures add exactly `P'`, locally finite away from `P'`, seams and generators hold,
but the chain is a **pinched sphere** (a cylinder with both ends compactified at one point), not a
2-manifold at `P'`. Repair: add the same `ht hu hv huv he hP'` as `exists_canonicalTower`, and,
following the book's proof of the closure equality, receive the separation of the same chain
`hsep : Separates (I ⁻¹' L) (I ⁻¹' {h u}) (I ⁻¹' {h v})` with `I := interior (h '' C u ∪ h '' C v)`,
`L := annularChain H B P'`. Assembly: call the limit leaf on the descent's closedness output first,
then this leaf — no dependence on `IsPseudoCell`, no circularity.

## Leaves 12, 13 — the support domain, not the crossing notion
⑦ `CrossesPseudoCell` is the 32.4 notion; no PL condition at the centre. The replacement disk of
p. 229 lies in `Dc`, not necessarily in `Bl`. Repair (a task split, not a refutation): leaf 12's
conclusion adds `Dc ⊆ Metric.ball P δ`; leaf 13 takes a common open `Ω` with `Bl ⊆ Ω`, `Dc ⊆ Ω` and
concludes `Δ ⊆ Ω`; the assembly uses `Ω = Metric.ball P δ` and the finitely many pushes use the
slack inside it.

**Owed:** passing the avoidance certificate; genuine end carriers of the chain; unconditional
proofs of the three named inputs. **Fixture:** a one-edge regular neighbourhood after a non-affine
PL bend, a thin torus tower, longitudinal annuli, tapering collars, a non-empty crossing circle.
**Likely surprise:** the false `Moise267` would have made the whole descent interface "provable",
hiding the remaining construction gaps.
