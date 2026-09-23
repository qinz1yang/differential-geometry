# Section 34 P4, case (b): review digest (answer to request BH)

Owner supplied the review on 2026-09-23. The reviewer's full coordinate model and field-by-field
check live only in the reviewer's sandbox (`P4_case_b_review_457dbdb.md`, not in this tree); the
text below records what was stated. Marks: **[P]** paper argument; **[V]** checked by the lead;
**[OPEN]** proof obligation.

## Verdict

| Leaf | Review | Lead disposition |
|---|---|---|
| `exists_section34Compression` | OK as a statement; the book's "fill the pocket" construction fails in case (b) | Statement unchanged and stays FROZEN; prove case (b) by the thin-shell / through-tube route below; one new controlled lemma required. |

**[P] The position is possible.** Straighten the free face of the common vertex ball to
`V_w = {z ≤ 0}`. The first face ball has a concave pocket with a square opening `Dj ⊆ {z = 0}`,
rising and then descending through a side chamber to `z = -1/2`; a closing finger of the second
face ball enters `E` through that negative-height entrance and rises inside the pocket to
`z = 1/2`. The two old balls meet only in `z < 0`; after filling the pocket the intersection
contains the fingertip at `z > 0`, so field 4 fails for the filled ball. Fields 1-3, 5-10 of the
model were checked by the reviewer against the cut frame (25 clauses), the graph frame (14
clauses), the ten invariants and the compression predicate; graph-frame clause 8 constrains the
original `h '' simplexBody`, not the modified face balls, so it does not exclude the position.
This is a mathematical model, not a compiled Lean fixture. Book Lemma 5(5) constrains the whole
ball while Lemma 6 checks only boundaries, which is why the book's step does not transfer.

## Why P4 needs no change (the route to prove case (b))

Let `N = ⋃ w, tgtV w` and `B = fbl s`. First add only a thin 2-handle along `Dj`, obtaining a shell
`W = P \ Int X₀` with two boundary spheres, avoiding the other face balls; the traces of the two
boundaries together are the old trace minus `Jd`. Do not fill the inner ball `X₀` yet.

Escape: the triangle `s` lies on two tetrahedra; a vertex not incident to `s` is non-incident to
at least one of them, and that carrier's `Section34Exterior` links its marker to the carrier
boundary, so the marker cannot be trapped by `P`; with connectedness of the vertex balls, no
non-incident vertex ball hides in the inner ball.

- If the inner ball meets `Int N`: from an incident vertex ball inside it, through the vertex
  marker, the rim and the original graph edges, walk inside `Int N` to a marker outside the
  pocket; take the segment crossing the shell, avoid the rim, PL-approximate it, and obtain an arc
  joining the two boundary spheres. Removing its thin regular tube turns the shell into a ball
  `G ⊆ W` without swallowing the other face balls; the tube lies in `Int N`, so
  `c_G + 1 = c_B` and `p_G = p_B`; all other traces are kept, and deleting `Jd` (which bounds a
  disk in the incident vertex ball) does not change the trace's homology image in the face torus.
- If the inner ball misses `Int N`: transversality leaves no trace on the inner sphere, the other
  face balls each have a marker outside the pocket and cannot hide inside, so filling is safe.

**[V] Interface.** P5 (Zorn), the bigon slide, the two trace leaves and `Section34Terminal` keep
their signatures: still a single-label rank drop under the original predicate with the other balls
unchanged. The suggested restriction `Dj ⊆ ⋃ w, tgtV w` already holds and repairs nothing.

## Obligations and warning

- **[OPEN]** A controlled thin-shell / through-tube lemma: a PL arc in the shell, inside `Int N`,
  avoiding the (possibly non-PL) rim, with a regular neighbourhood small enough that the counts
  drop by exactly one; an arbitrary ambient arc does not guarantee the count drop.
- **[OPEN]** The two-tetrahedra escape argument as a lemma of the cut/graph frames.
- Assignment: worker a (currently on the torus lemmas, the bigon drag map and the local
  neighbourhood lemma) takes case (b) by this route next; Codex may prepare the through-tube
  lemma as a probe overnight.
