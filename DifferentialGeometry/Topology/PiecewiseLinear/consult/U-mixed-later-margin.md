# U. Consult — the last open mathematical obligation of A1: later-chart margins at mixed germs

*请用中文回答；Lean 标识符与公式保持原样。先给结论，再给构造或反例；总长约 1500 字。
这是 consult L、O 和第七轮骨架审查的追问，不要重复它们。*

**Where.** Repository https://github.com/liao9yuan/differential-geometry-dev, branch
`moise-integration`, directory `DifferentialGeometry/Topology/PiecewiseLinear/`:
`Skeleton/GeneralPositionInDouble.lean`; digests `consult/V-generalposition-seventh-review-digest.md`
(your last review), `consult/O-answer-digest.md`, `consult/L-answer-digest.md`.

**State.** Eight of the ten leaves of the chart-by-chart general position skeleton are frozen. The
induction invariant after step `k` is: (a) PL normal double crossings over `Z_k = ⋃_{j<k} closure W_j`;
(b) for every later chart `m ≥ k`, margin-stable genuine-sheet blocks (`IsStableCrossingBlock`) in the
chart `ec_m` over `Z_k ∩ P_m`, `P_m = closure (V_m \ closure W_m)`. A step moves only the free vertices
of a fixed subdivision `R` of the cut-out piece `Rc ⊆ D.domain`, by less than `τ` (chosen after `R`);
the outer ring `Ac` is frozen; simplices with a frozen vertex stay off `closure W_k` (`hsep`);
everything off a compact `K ⊆ V_k` is untouched (fibres unchanged). Strata of the new map's double
points over `(Z_k ∪ closure W_k) ∩ K`:
1. **free interior germs** (all fibre points have `R.space` as a source neighbourhood, no frozen
   vertex nearby, off `BdM`) — handled by genericity + wall conditions against the affine pieces
   of the transitions `ec_m ∘ ec_k⁻¹`;
2. **free boundary germs** — handled by genericity inside `ker ℓ` + avoiding the 1-skeleton of the
   boundary-induced transition complex;
3. **non-free (mixed or frozen) germs** — a fibre point lies in a simplex with a frozen vertex, or
   outside `R` altogether (an unmoved sheet). Your review: these "belong to the protection layer";
   `hprot` gives normality, `hpersist` gives the **current** chart's margin with `η/2`, `hlater`
   concerns the **old** map; *nothing gives the later-chart margin of the new map*, and "this needs
   an independent relative construction proof".

**The question is stratum 3 only.** In the skeleton it is now one leaf
(`exists_laterMarginBlocks_of_mixedGerms`, NEEDS_PROOF): for every admissible controlled vertex map,
every non-free double point of the glued map over `(Z_k ∪ closure W_k) ∩ P_m ∩ K` has a genuine margin
block in `ec_m`, for each later `m`.

1. **Is it true as stated — for EVERY admissible vertex map with error `< τ`?** Sub-cases:
   (i) *old* non-free double points over `Z_k ∩ P_m ∩ K`: the old map has a later-chart margin `η`
   there by (b); the new map differs by `< τ` in the chart `ec_k`, on the free vertices of the mixed
   simplices only. Consult O §3 showed that a later-chart margin is not open under *translations of
   both whole sheets across a wall of the transition*. Does it become open when at least one sheet
   is frozen near the point and `τ` is small against the mesh of `R` **and** against the distance
   from the old double point to the walls of `𝒬_m` — i.e. if the old invariant also records that
   old double points over the transition zones avoid `|𝒬_m^(1)|` and cross the 2-faces
   transversally (which the free strata already guarantee for the double points *they* created)?
   (ii) *new* non-free double points (one preimage moved, the other on a frozen or unmoved sheet):
   can they occur over `(Z_k ∪ closure W_k) ∩ P_m ∩ K` at all, given `hsep` and the fact that the
   unmoved sheet was there before? If yes, is the margin in `ec_m` generic in the moved vertices —
   the frozen sheet being piecewise affine in `ec_m` with its own fixed fold lines — and what finite
   list of conditions on the free vertices (relative to the frozen sheet's `ec_m`-fold lines and to
   the walls) makes it hold?
2. **If it is false for every admissible map, is it true for a relatively open dense set** of the
   constrained vertex parameters? Then the leaf should be merged into the generic production leaf
   as additional open-dense conditions; please list them.
3. **Or should the induction avoid stratum 3 over later transition zones altogether?** E.g. choose
   the cover and the order so that for every `k < m` the frozen ring of step `k` does not meet
   `P_m ∩ Z_k`-double points; or make each step's frozen ring lie over a region where **all**
   relevant later transitions are affine (a finite atlas refinement chosen before the induction:
   is "each `V_k \ closure W_k` is covered by finitely many open sets on which every later
   transition is affine" obtainable by subdividing the `W_j`, since the transitions are PL and the
   double is compact?). Which of these is cheapest, and does any of them make stratum 3 disappear
   rather than merely smaller?
4. Anything in strata 1–2 that you expect to break once stratum 3 is settled.
