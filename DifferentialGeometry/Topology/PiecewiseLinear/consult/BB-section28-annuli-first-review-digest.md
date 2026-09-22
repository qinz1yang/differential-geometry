# Annuli between essential polygons: first review and lead due diligence

Date: 2026-09-22. Owner-supplied answer to [AV](AV-section28-annuli-review-request.md),
against mirror `510a3d1015405d12ca480a4bbb9134b9666077ea`.

**Both statements OK and frozen; both proofs OPEN.** The lead and an independent read-only
reviewer found no missing external assumption, complete counterexample or disagreement.
The assembly retains the exact `Moise286` conclusion, actual component closures and labels.

| Leaf | Verdict | Checked meaning |
|---|---|---|
| `exists_product_coordinates_for_disjoint_essential_polygons` | OK | One PL boundary product chart simultaneously sends the entire finite family to distinct fibers; it need not extend over the solid torus. |
| `exists_annulus_parametrization_of_product_circle_cut` | OK | The ambient closure of the actual component is parametrized by an annulus whose ends have two distinct original labels, chosen by circular adjacency. |

## The three obligations inside the first leaf

The statement is stronger than printed 28.3, which gives standard position. Its proof must
independently provide all of the following:

1. A PL identification of the boundary of the current combinatorial solid torus with a PL
   product torus. A topological solid-torus certificate alone is not the requested PL chart.
2. The bridge from the exact no-PL-disk condition to nonzero homotopy of each boundary circle.
   The forbidden disk lies **in `frontier S`** and has boundary `r '' stdSimplexBoundary 2`.
   A meridian may bound a compression disk inside the solid torus without violating this
   premise. The ambient frontier of a two-dimensional disk in three-space is not its circle.
3. Compatible relative PL straightening of all the disjoint essential circles, including
   fixed earlier circles and all seams. Equal unoriented primitive slopes and individual
   isotopies do not themselves supply the single map required by the conclusion.

The lead visually checked printed pp.203–204. The proof of 28.9 uses 28.2 and 28.4, so it can
support the no-disk bridge without using 28.6. By contrast, 28.7 explicitly follows from 28.6:
it cannot be used to fill a gap in this producer. The review proposes torus unfolding and
relative PL bigon elimination; no whole-surface-classification assumption is added.

## The second leaf and the assembly

All coordinates, circles, marks and injectivity are supplied by the first leaf. `hn` and
the basepoint membership `hx` come from the endpoint. A complementary component in product
coordinates is `J × a` for one component `a` of the punctured circle. Compactness makes the
target closed, and the existing closure-transport API preserves the **ambient** closure.

The missing construction is finite-mark adjacency and actual component identification;
the existing two-point `CircleArcs` decomposition is only an ingredient. The indices are not
presorted. For `n=2`, both arcs have the same two distinct endpoint labels, which is correct.
Arbitrarily short intervals and arbitrary permutations require no extra assumptions.
The assembly rewrites the entire family by one `funext` equality and directly returns the
second leaf's parametrization and two endpoint equations. It does not weaken the conclusion.

## A genuinely PL shared fixture

Take `R=[1,3]×[-1,1]`, the rectangle boundary `J={(r,0,z):(r,z)∈∂R}`, and the square circle
`Q={(u,v,0):max(|u|,|v|)=1}` subdivided at all four side midpoints. Its eight vertices include
`q±=(±1,0,0)`. On every edge `[u,v]`, send the four strip vertices

\[
(1,u),(1,v),(3,v),(3,u)\quad\mapsto\quad u,v,3v,3u
\]

and extend affinely on the two triangles determined by the `(1,u)` to `(3,v)` diagonal.
For consecutive counterclockwise vertices, `det(u,v)=1`; the two image triangle determinants
are `-2` and `-6`. All triangles are nondegenerate, adjacent strips agree on radial seams,
and the eight convex trapezoids tile the square annulus of area `32`.

This is not the bilinear formula `h(r,u)=r*u`: for example, on the edge `(1,0)` to `(1,1)`,
`h(2,(1,1/2))=(2,3/2)`. The selected marks are subdivision vertices, however, so their radial
seams satisfy `h(r,q±)=r*q±` exactly. Product with `z` gives the required PL solid-torus map
and boundary restriction `f`; the selected fibers are exactly the two rectangular meridians.
Compatible prism triangulations give eight CST blocks, while the polygon family has `n=2`.
These are different counts. The basepoint `(0,3,0)` avoids both meridians.

The map `prJ ∘ f⁻¹` is a homeomorphism on each meridian. A disk satisfying the complete
forbidden package would extend a degree `±1` circle map across a disk, contradicting the
disk's vanishing first homology. This verifies the paper no-disk argument without excluding
interior compression disks. **The joint Lean fixture remains UNTESTED.**

## Verification boundary

Only module documentation changes. Both leaves, scopes, the assembly and the named endpoint
are unchanged. The private lead evidence directory
`claude-moise-agent-c/fill-interface-evidence-20260922` retains
`four-producer-review-snapshot-comparison.json`, `four-producer-frozen-review.json` and the
unchanged-source `Section28Annuli-audit.json`. The final lease-c check passed with Lean exit 0,
a stable source hash and exactly two authorized leaf-sorry warnings and no other diagnostics. No completed producer, root build
or joint Lean fixture is claimed. Both geometric proofs remain OPEN in `FREE_INPUTS.md` B1.j.

Final check UTC: `2026-09-22T13:27:26.6739508Z`. Checked source SHA-256:
`65cdee8410eba6dec51c7ff871b1af19648e499bfb051a0fabedbfe912327d41`.
