# Digest — external review of `Skeleton/DescentStepOrientable.lean` (snapshot `06a96eb1de64`)

Verdicts: 5 OK, **3 FALSE**. "OK" = a non-circular proof route exists, not that the `sorry` is filled.

| Leaf | Verdict | Reason |
|---|---|---|
| `not_branchPreimage_eq_of_isOrientable` | OK | marked-link sign on the connected preimage circle |
| `isPLBoundaryTubeProducer_double` | **FALSE** | `BdM` is universally quantified and controlled only near `D(∂P)` |
| `NormalSystem.exists_boundaryNeighborhood_realization` | OK | canonical inclusion and its inverse on its image |
| `exists_descendingSurgery_of_disjoint_innermost_cleanDisk` | **FALSE** | same set-parameter defect; also too coarse — split at the cap data |
| `exists_boundaryWordWitnesses_of_cut` | OK | existential: choose the actual candidates of the cut; prove from source-arc data |
| `exists_plCrossSeamReading_of_isCrossRegluedCell` | **FALSE** | an unmarked quarter turn of the tube chart; and no boundary-end hypothesis |
| `…side_buffer…reversing`, `…preserving` | OK | inherit side and buffer from the image bounds of the two candidates |

## The three defects and their repairs

**1. Boundary separation (tube leaf and 2b leaf; also the committed `IsPLBoundaryTubeProducer`).**
Counterexample: a product model `D(s,t) = (ℓ s, t)` properly inside a compact PL side `W`, `H = ∂W`,
`V` a small open ball round an interior point of the double branch with `closure V ∩ D(∂P) = ∅`,
`BdM_* := H ∪ (V \ D(P))`, `B_* := BdM_*`. Every hypothesis holds (properness, crossings, side
condition near `D(∂P)`, buffer), yet the interior of any tube round that branch has open image,
which meets `V \ D(P) ⊆ BdM_*`: `cylinder ∩ BdM = end disks` is impossible. For 2b the same trick
(`BdM_* := H ∪ (C \ (F ∪ A))`, `A` a collar of the boundary curve, on the two-box fixture) forces a
complexity-zero surgery into `F ∪ A`, where no embedded disk with that boundary exists (it would
contain the once-punctured torus core).
*Repair (either one):* add `IsClosed BdM` to the side interface — with properness and
`D(open cell) ⊆ interior W` it gives `D(open cell) ⊆ interior (W \ BdM)` — or use
`IsPLBoundarySideSeparated := IsPLBoundarySide ∧ D '' (domain \ frontier) ⊆ interior (W \ BdM)`.
The double supplies it (`frontier C = Bd`, `interior C = C \ Bd` are already proved inside
`isPLBoundarySide_double`). The 2b leaf then needs only `D '' Q ⊆ interior (C \ BdM)`, derivable.

**2. Split 2b at the geometric cap data.** Producer (geometry, no surgery assumed): for every open
`V` with `D(Q) ⊆ V ⊆ interior (C \ BdM)` there are a larger source disk `E'` and a PL embedded cap
`Δ' ⊆ V` with `E ⊆ interior E'`, `E' ⊆ interior P`, `Q ∩ E' = ∅`, `(E' \ E) ∩ Σ̃_D = ∅`,
`∂Δ' = D(∂E')`, `Δ' ∩ D(P) = ∂Δ'`, and a PL attaching parametrisation. Consumer (cut-and-paste, like
2a): surgery, whole-or-nothing branch retention, the three invariants. The expensive step is the
adapted-neighbourhood trace theorem.

**3. The reading leaf.** `R(x,y,t) = (−y, x, t)` preserves cylinder, crossing figure, core, lateral
wall and end disks, hence every set-level tube condition, but turns the bent-sheet pairing
`(X⁺∪Y⁻), (X⁻∪Y⁺)` into the other adjacent pairing; the two source pieces of a
`PLCrossSeamReading` are compact, disjoint and carry constant labels, so no relabelling repairs it.
Also the reading's `boundary ↔ end` clause needs the tube's boundary equality, which the leaf did
not receive. *Repair:* `def crossQuarterTurn (p) := ((-p.1.2, p.1.1), p.2)`; add the hypothesis
`T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks`; conclude
`Nonempty (PLCrossSeamReading T.chart G) ∨ Nonempty (PLCrossSeamReading (T.chart ∘ crossQuarterTurn) G)`.
In the rotated alternative repackage the tube with the rotated chart (images unchanged, so side,
boundary and buffer transfer). The proof goes through the existing
`exists_plCrossSeamReading_of_four_source_pages` after identifying which pairing the source gluing
behind `IsCrossRegluedCell` induces, constant along the branch interval.

## Keep as they are
* **The preserving word.** As walked `r = τ σ⁻¹ φ υ⁻¹`; `r⁻¹ = υ φ⁻¹ σ τ⁻¹`, a cyclic rotation of
  `σ τ⁻¹ υ φ⁻¹`. `BoundaryWordWitness.param` is existential with no orientation restriction, so
  reverse it (`ofReversedWord`). Do not add an orientation-preserving comparison.
* **The direct half of the witness leaf.** It is existential: choose the actual direct candidate
  of the cut. Proof: keep the PL gluing maps of the two caps, restrict them to the retained
  boundary arcs, record source arc and ordered end points, compare inside the source interval
  (`H (s,t) = f (P₀ ((1−s) r t + s t))`), compose with `f`, concatenate in `X`. Not from image
  ranges, and not through the set-theoretic `pullback`, which is not continuous.
* **F10 leaves.** Bounds `G_d(P_d) ⊆ D(P)`, `G_res(P_G) ⊆ D(P) ∪ T(cylinder)`,
  `G_res(∂P_G) ⊆ D(∂P) ∪ T(end disks)`. The old selector hides which candidate it chose: reopen
  that short proof or strengthen its output; both leaves share one inheritance lemma.

## Fixture for the joint test (F11)
The preserving product immersion with one extra transverse curl in a retained cap; a genuine
compact PL side and its actual boundary; `B` a regular neighbourhood of the boundary image graph;
`X = B`, `N = {1}`; a small boundary-adapted tube; the correct quarter-turn convention. It tests
reading, witnesses, buffer and branch retention on one tuple, with a non-injective target boundary
arc. The reversing model tests the other word.
