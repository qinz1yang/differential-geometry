# X. Design consult — the multi-chart core of general position in the double, as ONE package

*请用中文回答；Lean 标识符与公式保持原样。这次不是逐叶审查，而是请你给出一个完整、自洽的设计：
不变量 + 单步定理的精确数学陈述 + 证明梗概。篇幅可到 3000 字；先给结论。*

**Where.** https://github.com/liao9yuan/differential-geometry-dev, branch `moise-integration`,
`DifferentialGeometry/Topology/PiecewiseLinear/`: `Skeleton/GeneralPositionInDouble.lean`
(12 leaves, 8 frozen), digests `consult/W-consultU-and-fifth-351-review-digest.md` (Part 1),
`V-…`, `R-…`, `O-answer-digest.md`, `L-answer-digest.md`, `J-…` (history of eight rounds).

**Why a design consult.** Eight leaf-by-leaf rounds converged on everything except one thing, which
keeps reappearing under new names (pairing seed → later-chart margin → mixed germs): **how the
induction carries normality across charts whose transitions are only PL**. Each local repair was
refuted in the next round (U's answer: the mixed-layer leaf is false for every admissible `φ`, even
with one sheet frozen). We now want the whole mechanism designed at once.

**Fixed data (please keep).** `M` = the double, a compact metric PL 3-manifold; `D` a proper,
locally injective, ≤ 2-to-1 PL singular disk on one side `C`; a finite cover fixed before the
induction: `closure W_j ⊆ V_j`, `closure V_j ⊆ (ec_j).source`, `⋃ W_j = M`, adapted charts `ec_j`, `ℓ_j`;
step `k` cuts out `Rc_k ∋` all sheets through `closure W_k`, freezes an outer collar `Ac_k` whose
image misses `closure W_k`, takes a subdivision `R` with `ec_k ∘ D` facewise affine, moves the free
vertices by `< τ` (τ after `R`), glues. Frozen leaves (reviewed OK, prefer not to change): adapted
charts; cut-out piece; literal gluing; global invariants (fibres ≤ 2, `StarInj T`, properness,
buffered boundary homotopy) from a predetermined control complex; preparation; transition
subdivision covering a neighbourhood; stable block ⇒ normal; protected subdivision (every admissible
map keeps normality at frozen-vertex fibres over `Z ∩ K` and keeps the current chart's blocks with
`η/2`). Block predicate: `IsStableCrossingBlock` (graph form, margin `La·Lb ≤ 1−η`, genuine source
sheets, inner/outer block).

**Established facts (all with verified counterexamples).** (1) A later-chart margin is not open in
the current chart's vertex parameters: translating both sheets, or one sheet with the other frozen,
onto a wall of the transition turns a flat crossing into the bent `ABAB` model without margin.
(2) The interface between moved and unmoved simplices always carries double points (every double
curve leaving `W_k` crosses it), and those are non-free germs. (3) Transitions are not affine near
wall points, and no refinement of the cover changes that. (4) On fully free triangle–triangle
blocks crossing a wall, finite mesh + strict margin + **quantitative transversality to the wall**
do give openness (your remark in U).

**The lead's doubt about the "common protection layer"** (U, end of §2): over a fibre-preserved
open `N` nothing moves, but interface simplices do move and do carry double points, so affected
non-free double points cannot all lie in such an `N`. If this is wrong, say exactly how the
supplier arranges it (which simplices are frozen, where the interface sits, why no double curve
crosses it).

**What we ask for.**
1. **The invariant.** A precise predicate `Inv_k` on the current cell, strong enough to make the
   step go through and weak enough to be produced. Candidate: (a) normality over `Z_k`; (b) stable
   blocks in `ec_m` over `Z_k ∩ P_m` for `m ≥ k`; (c) **quantitative stratified transversality**: on
   the fixed compact overlap blocks, in each later chart `ec_m`, the double curves avoid `|𝒬_m^(1)|`
   and cross the open 2-faces with an angle bound, source fold lines do not meet walls on the double
   set, *and the sheets themselves* are transverse to the strata of `𝒬_m` with a quantitative bound
   (so that a later step's frozen sheets are never in a forced-degenerate position) — state exactly
   which of these are needed, on which sets, with which constants quantified where. Is (c) for
   sheets needed, given that every sheet over `Z_k` was moved generically at an earlier step — and
   what about never-moved parts of `D` lying over `P_m \ Z_k`?
2. **The step theorem**, as one mathematical statement `Inv_k → ∃ cell', Inv_{k+1} ∧ (global
   invariants)`, with the order of all choices (control complex, scales, `R`, `τ`, `K`, the
   perturbation), and a proof sketch organised by strata (free interior / free boundary / interface
   = mixed / untouched), saying for each stratum where openness comes from (which constants of
   `Inv_k`) and where genericity comes from (which finite list of polynomial conditions on which
   parameters, and why each is not identically zero on the constrained parameter space).
3. **The interface specifically.** Old double points on interface simplices: prove they keep
   `Inv` for all admissible `φ` with `τ` small, from the quantitative constants. New double points on
   interface simplices (a slightly moved simplex against a frozen or unmoved sheet): can they be
   excluded by choosing `R` and the collar suitably (e.g. interface simplices so small and so placed
   that their images meet no other sheet except along already existing double curves), or must they
   be made generic — and then relative to which frozen strata?
4. **Base case and end.** `Inv_0` must hold for an arbitrary input `D` (nothing normalised yet, `Z_0 = ∅`):
   check that (c) imposes nothing on never-moved parts that the input cannot satisfy, or say how
   the first steps repair it. At the end `Inv_n` must give normal crossings everywhere.
5. **Is there a cheaper architecture?** E.g. (i) choose the finite atlas so that all charts are
   restrictions of **one** PL embedding of a neighbourhood into `ℝ³`-pieces glued along *affine*
   walls known in advance (the double is a finite simplicial complex: use its simplexwise-affine
   structure, moving vertices only inside open 3-simplices and treating the 2-skeleton of the ambient
   complex as the fixed wall system for ALL steps at once — one wall complex, no later-chart
   bookkeeping); (ii) a two-stage scheme: first make the sheets transverse to the ambient 2-skeleton
   everywhere (a condition on sheets, chart-free), then normalise double curves simplex by simplex
   of the ambient complex, where everything is affine. Would (ii) remove the multi-chart problem
   entirely? What breaks?
6. A **minimal leaf list** for the design you recommend (names + one-line content), marking which of
   the eight frozen leaves survive unchanged.
