# CGN edge matching, the orientation character: review digest (answer to request BN)

Owner supplied the review on 2026-09-23 (request BN). Marks: **[V]** checked against the Lean
source by the lead; **[P]** the reviewer's paper argument; **[OPEN]** proof obligation.

## Verdicts

| Object | Review | Lead disposition |
|---|---|---|
| `exists_section34EdgeMatching` | **OK** as stated; the full hypotheses give another orientation-comparison route; none of the candidates A/B/C is needed | Statement unchanged; no interface repair |
| Bridge note items 2 and 5 (`Skeleton/OrientationCharacterBridge.md`) | **FIX**: set correspondence, orientation matching and pointwise matching must be separated; item 2's "pointwise agreement on shared disks" assumes what item 5 proves | Codex re-plans the bridge as below |
| Clause (f) via the existing tools | **FIX**: `Section34FaceTorusCycle` takes the whole `Section34GraphFrame` (which contains the generator clause) and may not be used to prove (f) circularly; the toroidal-shell lemma does not keep a prescribed spine | Lead owes the weakening; Codex builds the spine-preserving small torus |

## What the review established, with the lead's checks

**[V] The marker lies inside its own deleted ball, from the leaf's inputs alone.**
`Section34VertexMarkerInterior.section34_vertex_marker_interior_of_deleted_family` (Codex, accepted)
proves `∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w)` from clause 22 of `hpack` (`hsep`),
`Dv w ⊆ G w '' Cp w` (from `hDvdef`), `hDv`, `hDvQ`, `hQlf`, `hDnbhd`. So the call site's
`hDmark` not being passed is immaterial; it is derivable.

**[V] One chart covers both ends of an edge.** `Section34OuterTorus` (`Section34Frame.lean` 903),
clause 1: for every triangle `s`, `ct s` is a maximal-atlas chart and
`⋃ (w incident to s), Q w ⊆ (ct s).source`. **[P]** Every graph edge has both endpoints incident
to a common triangle of `𝒦` (the graph skeleton lies in the 2-skeleton and `𝒦'` subdivides it;
the 3-manifold is pure). **[P]** `A_w := h '' src (.vertexBall w) ∪ Dv w ⊆ Q w` (uses
`src (.vertexBall w) ⊆ Cp w ⊆ Cc w` from the preparation's `hsubs` and `h '' Cc w ⊆ interior (Q w)`,
clause 940, with `hDvQ`); `A_w` is connected (two connected balls sharing the marker).

**[P] The bridge to prove.** Choose a chart orientation on each `A_w`. The transfer sign between
the chart of `A_w` and the edge chart `ct s` is constant on the connected `A_w`, hence equal on
`h '' C_w` and on `Dv w`; counting both boundary-normal reversals, the source and target edge
transfers coincide, and changing to arbitrary reference sphere orientations only introduces
vertex signs:

```lean
∃ σ : Section34VertexIndex 𝒦 𝒦' → ZMod 2,
  ∀ e, sourceSign e + targetSign e = σ (ends e).1 + σ (ends e).2
```

Summing over a finite mod-two cycle gives zero. The absolute source and target characters may
both be nonzero (solid Klein bottle cycles are not excluded and need not be), and no relative
degree `+1` of `G` is forced.

**[V] Why the closeness route of BN does not work as written.** `ball (h x) (ε w) ⊆ interior (Q w)`
gives neither a displacement bound in chart coordinates nor an avoidance bound for the boundary
map at a fixed base point; closeness on an arbitrarily small open piece does not compare degrees;
the stability clause 999 only gives containment of the core. Candidate A is not "immediately
forwardable" either: `hoff₂` is stated with the old `G₁` (`{x ∈ Cc w | ∀ e, G₁ w x ∉ interior (Sp e)}`),
so the antecedent with the new `G₂` needs a separate non-escape argument. All three candidates
are withdrawn.

**[P] Order of the matching (item (b)).** First choose reference sphere maps requiring only SET
correspondence on the marked disks; solve the vertex signs `σ`; correct the reference
orientations; then choose or flip the orientation of each shared edge map `φ e` so that both
ends' relative corrections satisfy `IsPLCirclePositive`; then the circle corrections, disk gluing
and ball extension (`SphereHoledBoundaryExtension`, `exists_extension_of_cell_boundary`). Flipping
one vertex's reference orientation flips all its incident disk signs, so arbitrary pre-fixed
mixed disk signs cannot be repaired afterwards; the existing planar tools already separate
"reference map" from "positive relative correction".

**[V] Clause (f).** `Section34FaceTorusCycle.isCombinatorialSolidTorus_image_section34FaceTorus`
(line 87) takes `hgraph : Section34GraphFrame …` and destructures only `hf₁` (line 97). It must
not be fed the frozen leaf's frame to prove (f) (the frame contains the generator clause). Owed
lead cleanup: weaken its hypothesis to `hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src)`
(a strict generalisation; module and consumers rechecked), or Codex proves a cyclic-ball-family
version for the `Dv w` directly. **[P]** The toroidal-shell lemma
(`IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior`) does not keep the
prescribed spine; use the product parametrisation inside `htor`'s `IsSpine (Sd s) J`
(`MoiseChain.lean` 254): move the marked interior point to the disk centre, shrink the disk
radius so `S₁ ⊆ interior Te`; the same radial parameter gives the shell and `IsSpine S₁ J`. No
unknottedness or generator hypothesis is needed.

## Obligations and warnings

- **[OPEN]** the orientation-transfer bridge on the connected common carriers `A_w` (the `σ`
  above); the joint matching with adjustable edge-disk orientations; the spine-preserving small
  torus. Frozen leaf unchanged.
- **[OPEN, lead]** weaken `Section34FaceTorusCycle` to consume `hf₁` only (owed cleanup; until
  then Codex must not import it for (f)).
- Joint example (reviewer, unverified): a Euclidean periodic triangulation, small dual balls with
  transverse piercings, a non-identity affine `h` and `G` a sufficiently small nonzero
  translation of it; a geometric scheme, not a clause-by-clause Lean instance.
- Most likely surprise (reviewer): mistaking "one arbitrary shared disk map per edge" for "all
  vertex boundary conditions already compatible", i.e. assuming in bridge item 2 what item 5 proves.
- The reviewer could not locate the "Codex item 7" log section in its snapshot; the eleven
  modules are accepted by the lead's own checks (commit 39cf41b9a), not by this review.
