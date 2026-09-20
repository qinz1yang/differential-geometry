# A2. Follow-up to A: the §34 contracts, now with the lemma list in hand

*Consultation prompt. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only. Lean paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

In your answer to prompt A (digest: `consult/A-answer-digest.md`) you declined to certify a
replacement DAG for `Moise352SkeletonExtension` because you could not see printed pp. 241–246
and 249–250. We have now written those pages up:

> **`consult/A-section34-lemma-list.md`** — standing notation of §34; every lemma of §34
> (there are **eleven**, not thirteen — thirteen is §33's count) and Operations 1–2 with every
> numbered sub-clause, the results each proof invokes, and each use of ℝ³ or of finiteness; the
> seven-stage extension (domain / target / already defined / supplying lemma); 35.1 with its
> 14-step proof structure and 35.2's two reductions; a table of the invariants Operations 1–2
> must preserve; the 22 claims asserted without proof or by reference to a figure.

It is *our reading* of the book, in our own words. Treat it as data, and tell us wherever it is
internally inconsistent or cannot be what Moise means.

What the write-up found that bears on your earlier answer:

1. Your seven-stage left column is right at all seven rows and the right column is right in
   substance, but **rows 2 and 5 have no producer in the book**: the cyclic-order compatibility
   on `Bd D_e` is asserted, and the splitting disks `D_e` are never assigned a stage although
   `Bd C_v` contains them.
2. Your convention `Â = f₁(A)` holds only for `N, C_v, D_e, N_σ`; `D''_σ`, `C''(σ³)`,
   `X''(σ³,v)` are *chosen* (pp. 244–245), not `f₁`-images — which is why Moise's closing Query
   (p. 246) is open and the contract must not require `F|N = f₁`.
3. Lemma 5(7) is consumed exactly once, on p. 245, to show `Int C''(σ³)` meets no `C''_v` with
   `v ∉ σ³` — the injectivity input of stage 7. Its preservation under **Operation 2** is
   asserted without argument (Lemma 6's small-displacement argument covers Operation 1 only);
   together with 5(6) under both operations these are the two soft spots.
4. Consumption map completing your Q4: 28.8 → p. 244 (Lemma 11; the proof cites 28.8 for a
   dichotomy 28.8 does not state — it needs 28.9 and an exclusion of meridians); 27.3 → p. 250;
   26.4 → p. 234 (§33); 32.1–32.3 → p. 231; 32.4 → pp. 233, 238. **30.6 and 30.7 are cited
   nowhere in §§33–35.**
5. §34 Lemma 9 uses "`K` is a triangulated 3-cell" (false under 35.2); Lemma 8's termination
   counts are finite only for a finite complex.
6. The tree's `Moise308` (`MoiseChain.lean:257`) is **not** book 30.8: it takes `J` a spine of
   `S` itself and concludes that `J` generates `π₁(S)`; the book takes `J` a spine of the *inner*
   torus `S₁` of a nested pair and concludes about the *middle* `S` (p. 218). As stated it cannot
   serve §34 Lemma 2.

### The questions

**Q1. The DAG.** With the lemma list in hand, give the replacement for
`Moise352SkeletonExtension 3`: obligations each strictly weaker than 35.2, each statable in the
tree's vocabulary, with a reduction to `Moise352 3`. For each of the seven stages give the
exact extension contract (input clauses, output clauses, and which earlier stage's output it
consumes), using your (Ball extension) and (PL gluing with incidence) lemmas where they apply.
Separate explicitly the *preparation* obligations (producing target cells with the right
incidences) from the *extension* obligations.

**Q2. The two rows without a producer (item 1).** State what must be proved for rows 2 and 5 —
is the cyclic-order compatibility on `Bd D_e` a consequence of something already established
(orientation? the generator condition of Lemma 2?), and at which stage do the splitting disks
`D_e` get their map?

**Q3. The soft spots (item 3).** Give an argument, or a counterexample, for the preservation of
Lemma 5(6) and 5(7) under Operation 2. If preservation fails as stated, what is the correct
invariant?

**Q4. Locally finite and chart-local (item 5).** Replace Lemma 9's use of "`K` is a 3-cell" and
Lemma 8's finite termination in the locally finite, manifold-target setting: exact statements,
using your interaction regions, (Control), and relative target local finiteness. Your
ℝ³-counterexample showed target local finiteness must be relative to the image — state the
condition the reconstruction should carry.

**Q5. 30.8 (item 6).** Give the correct statement of 30.8 in the tree's vocabulary
(`IsTopologicalSolidTorus`, `IsToroidalShell`, `IsSpine`, `HasCylindricalDiagram`,
`IsCombinatorialSolidTorus` at `CombinatorialSolidTorus.lean:19`) in the form §34 Lemma 2
consumes, and say whether the tree's current `Moise308` is a lemma on the way or irrelevant.

### Constraints

Exact statements (Lean-ish welcome); say what you could not verify; do not weaken existing
statements (several are consumed verbatim by proved reductions). "This is false, here is the
counterexample" remains the most valuable answer.
