# Three surfaces: first statement review and lead due diligence

Date: 2026-09-22. Owner-supplied answer to [AX](AX-section26-three-surfaces-review-request.md),
against mirror `df6cbdc7481ef9b3a57cb72df280dff9718fd918`.

**All four statements OK and frozen; all four proofs OPEN.** The lead and an independent
read-only reviewer checked the actual clauses, assembly and paper fixture. No missing
endpoint assumption, complete counterexample or substantive disagreement was found.

| Leaf | Verdict | Checked meaning |
|---|---|---|
| `exists_triod_chart_at_common_boundary` | OK | Choose one regular common-boundary point and a genuine PL chart with all three membership equivalences. Finiteness permits avoiding vertices and other simplices. |
| `exists_surface_interior_frontier_contact` | OK | Every complementary component, including bounded ones, has an interior contact on some surface. A finite one-dimensional boundary cannot carry its entire frontier. |
| `isOpen_preimage_frontier_component_surface_interior` | OK | Contact is relatively open on the surface interior away from the other closed obstacle. If the basepoint lies in the obstacle, the component and frontier are empty. |
| `exists_frontier_pair_witnesses_of_triod_chart` | OK | Two contacts and a third point on the opposite side follow using full separation of each closed surface pair. The output is not the final frontier or boundedness formula. |

## Supply and global sides

The first leaf does not promise a chart at every prescribed boundary point. It chooses a
point away from the finitely many vertices, where the three distinct half-plane germs can
be straightened together. The common boundary need not be connected.

The fourth leaf's `hpair` is produced by the assembly using
`exists_isCombinatorialManifold_space_union`, finite triangulations, the exact common-boundary
intersection and connectedness. The full closed-surface separation result in
`BoundedSurfaceComponent.lean:11` gives two complementary components, each with the entire
surface as frontier. Both therefore approach the chart point. Since each of the two local
sides is connected, they must belong to different global components. Merely having three
local sectors, or merely knowing the complement is disconnected, would not justify this.

`hpfront` is already produced before the fourth call: the second leaf gives an interior
contact; the third makes the contact set open on the connected surface interior; frontier
closedness makes it clopen; density extends contact to the whole surface and hence to the
point chosen by the first leaf. No new endpoint hypothesis is needed. The assembly repeats
this propagation for the two output contacts, excludes the third interior, proves the full
frontier equality and only then uses unboundedness to select the bounded opposite side.

## The shared two-boundary-component fixture

Put `r = max (abs X) (abs Y)`, `A = {1 <= r <= 2}`, `C = A × [-1,1]` and
`f(r) = 1 - min(r-1,2-r)`. The surfaces are

\[
S_0=A\times\{1\},\quad
S_1=(\partial A\times[-1,1])\cup(A\times\{-1\}),\quad
S_2=\{(X,Y,f(r)):(X,Y)\in A\}.
\]

They are connected polyhedral annuli with the same two intrinsic boundary circles
`B = ∂A × {1}`, disjoint interiors, and closed connected torus pairwise unions.
At `p=(2,0,1)`, use `(a,b,t)=(2-X,1-Z,Y)` in the cube `|a|,|b|,|t|<1/4`.
The review's fan map can be written

\[
(a,b,t)\longmapsto(a-b,\min(a,b),t).
\]

This is an invertible PL map. Its four listed rays have exactly the stated images; the
surface germs are `b=0,a>=0`, `a=0,b>=0` and `a=b>=0`, giving all three equivalences.
For `δ=1/16`, the proposed points `u`, `v`, `w` map to `(δ,0,0)`, `(-δ,0,0)` and `(0,δ,0)`.
The first two touch the unbounded component and the third lies in the interior of `C`.

Precisely, the unbounded component is `Cᶜ`, and its frontier is `S₀ ∪ S₁`.
The two bounded components are `1<r<2, f(r)<Z<1` and `1<r<2, -1<Z<f(r)`; their
frontiers are respectively `S₀ ∪ S₂` and `S₁ ∪ S₂`. This also tests the second leaf on bounded
components. These are checked paper models, **not a joint Lean inhabitant: UNTESTED remains**.

## Book and remaining work

The lead visually checked printed pp.20–21 and p.195 in the local Moise PDF. The proof of
26.7 refers to the three-arc proof of 2.7; that proof uses the different global sides of a
closed pair. The local-to-global argument above makes explicit the step compressed there.

Still owed: all four proofs, including finite-graph complement connectedness, local contact
openness and the full local/global-side bridge, plus a common finite triangulation and joint
Lean fixture. These are internal proof obligations, not additional leaves or endpoint inputs.

Only module documentation is updated. All leaf statements, scopes and assembly are unchanged
from AX. The private lead evidence directory `claude-moise-agent-c/fill-interface-evidence-20260922`
contains `four-producer-review-snapshot-comparison.json` and `four-producer-frozen-review.json`,
with exact source comparisons and final lease-c receipts. The final check passed with
Lean exit 0, a stable source hash and four leaf-sorry warnings only. Existing unchanged-source endpoint/axiom evidence is
`Section26ThreeSurfaces-audit.json`; this review does not claim a new proof or full root build.
Acceptance and debt remain in `FREE_INPUTS.md` B1.l.

Final check UTC: `2026-09-22T13:27:12.3775668Z`. Checked source SHA-256:
`d872cb94e7e16865936e11f00973f3dd54d7f4feadd141494df4c701812a6988`.
