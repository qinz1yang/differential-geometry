# Compact Section 34: second review and due diligence

Owner supplied the review on 2026-09-22 (ChatGPT share `6ab34779-8854-83e8-a64a-74b0ee72ea8b`),
addressing mirror `a43963103` exactly as requested in BF. Marks: **[V]** checked against the
current Lean source; **[P]** a paper argument, not a Lean certificate; **[OPEN]** outstanding proof.

## Verdicts

| Leaf | Review | Lead disposition |
|---|---|---|
| `exists_compactFaceEnvelopes` (with `hV : IsOpen V`) | OK | FROZEN. `hV` is the endpoint's own parameter; the inward push supplies `isOpen_interior` for `V := interior C`. |
| `exists_compactCompression` (with `hcar`) | OK | FROZEN. `hcar` is passed at every compression of the descent; per-carrier filling, no joint-intersection ball needed. |
| the ten unchanged leaves | OK (one line each) | FROZEN, as after AS. |

**All twelve leaf statements are frozen** and may be handed to proving workers. All twelve proofs
and the joint fixture remain open; the review does not close any of them.

## Checks

**[V] Envelope call.** `Skeleton/Section34Compact.lean:1270` reads
`exists_compactFaceEnvelopes h305 hV hCV hh hcut hcar hgraph`, and the inward push at line 1398
calls `moise341OnNeighborhood h331 h305 (p '' C) (interior C) hpball isOpen_interior …`, so the
new hypothesis is supplied by the endpoint and by the push. **[P]** Compactness is not missing: the
finite complex of `hcut` with `K.space = C` gives source compactness; auxiliary disks and nested
balls are chosen in `V`, the two collars shrink to compact bands whose closures stay in `V`, and
invariance of domain makes `h '' V` open, so shells, boundaries and collars transport inside the
open image without extending `h`. The spherical shell and the outer bicollar that `Moise305Tame`
consumes are still constructed inside the leaf; the transport interface is not their producer.

**[V] Compression call.** `hcar` comes from `exists_compactCutAndGraph` and the descent at line
1299 calls `exists_compactCompression hcut hcar hgraph hg s hop`, so it is not lost across the
iteration. **[P]** With `hinv` placing the old ball in every incident `interior (H t)`, a nonempty
compression-disk boundary and the non-incident avoidance force the disk's vertex to be incident
to `s`, and the vertex-carrier field of `hgraph` puts the whole disk in those interiors; the PL
three-cell certificate of `hcar` makes `(interior (H t))ᶜ` connected and unbounded, so the bounded
side of a surgery sphere inside that interior stays inside it, carrier by carrier. The punctured
carrier of the earlier counter-model fails the certificate and is excluded; it never satisfied the
full old leaf either.

**[V] Generator export.** Line 580: `carriesFundamentalGroupOnto_of_nestedSolidTorus hsub
(Homeomorph.refl _)`, taking the surjective half of `moise308Nested`; the assembly at line 1290
passes `(hgen s)` to `compactTraceHomology`. This is derived input, not a new free hypothesis.
**[OPEN]** The integral `H₁` surjection onto the whole trace remains internal to
`compactTraceHomology`: the abelianised generator only handles the rim's `H₁`, and the transfer
to the trace through the auxiliary ball and the crossing condition is that leaf's proof.

## Reviewer's warning to carry into the proof

Do not mistake the existence of a nonzero class in the trace for integral surjectivity: the image
could be `kℤ` with `|k| > 1`. The closed generator export does not remove this check.

## Fixture

Unchanged from AS: the subdivided tetrahedral ball, bivalent vertices, small convex PL carriers,
a nonzero translation `g` and the candidate `h = g ∘ ψ`; the joint Lean certificate is UNTESTED.
