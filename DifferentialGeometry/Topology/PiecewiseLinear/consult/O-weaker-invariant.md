# O. Consult — can the induction carry a weaker invariant than the pairing of all of `Z ∩ K`?

*请用中文回答；Lean 标识符与公式保持原样。先给结论（成立 / 不成立 / 需改动），再给证明思路或反例；
总长约 1500 字。这是对 consult L 的追问；不要重复 L 的内容。*

**Where.** Repository https://github.com/liao9yuan/differential-geometry-dev, branch
`moise-integration`, directory `DifferentialGeometry/Topology/PiecewiseLinear/`:
`Skeleton/GeneralPositionInDouble.lean` (the chart-by-chart normalization; eight leaves, seven frozen),
`consult/L-pairing-seed.md`, `consult/L-answer-digest.md`, and
`consult/J-generalposition-skeleton-review-digest.md` (second to fifth sections).

**Context.** Your answer L: the seed `exists_pairingStableSubdivision_in_adaptedChart` is
`NEEDS_PROOF`; it is provable under a quantitative transversality margin; you recommend changing the
induction invariant to *stable normality* in all later charts, with a common target subdivision `𝒬`
of the chart overlaps and new finite transversality conditions. Before redesigning, the lead asks
whether a **smaller** change suffices. The following is the lead's own analysis — **unverified;
please attack it**.

**Observation 1 (what the induction really needs).** The endpoint only needs, after the last step,
PL normal double crossings at all double points. A step therefore does not have to *conjugate* the
new map to the old one over `Z ∩ K` (the full-preimage pairing `χ, ψ`); it has to make the new map
**normal** over `Z ∪ closure W`. Over the part of `Z ∩ K` where all simplices involved are *free*
(no frozen vertex), a generic vertex choice on the final subdivision `R` (the guard, extended by the
usual edge–edge, vertex–triangle conditions) makes every crossing a transverse crossing of affine
triangles — normal and stable — whether or not the double curves are the old ones (a bent old
crossing with both fold edges through the double curve may turn into three transverse double arcs;
that is harmless for general position).

**Observation 2 (where stability cannot be avoided).** The frozen outer ring `Ac` necessarily
contains double points (a double curve through `W_k` leaves through the ring), and the *mixed*
simplices (some frozen, some free vertices) at the inner edge of the ring may lie over `Z`. A frozen
double point cannot be re-genericised, and if its local picture is not stable (e.g. the two link
circles on a small sphere meet at a vertex of one of them; or two source edges are frozen onto a
common target segment with alternating wings, the `ABAB` model), arbitrarily small moves of the free
neighbours can destroy normality (`ABAB → AABB`, or a node where two double arcs cross). With `τ`
chosen after `R` and small against the mesh, the directions of the free wings change little, so an
old configuration that is *stable in the current chart's affine structure* persists.

**Observation 3 (where the frozen and mixed simplices live).** The cover `W_j`, `closure W_j ⊆ V_j`,
`V_j ⊆ ⋃ W_i` is fixed **before** the induction. At step `k` the images of the frozen ring and of
the mixed simplices lie in the fixed target zone `V_k \ closure W_k` (by `hsep`/`hAfree` they miss
`closure W_k`), and everything is measured in the fixed chart `ec_k`.

**Proposed weaker invariant.** After step `k`: (a) the map has PL normal double crossings over
`Z_{k+1} = ⋃_{j ≤ k} closure W_j`; (b) for every *later* index `m > k`, over
`Z_{k+1} ∩ closure (V_m \ closure W_m)` the crossings are **stable in the chart `ec_m`** in the
sense of your margin condition `(*)` (graph form with `Lip_v a · Lip_u b ≤ 1 − η`, only two sheets
in the block, boundary traces included). No pairing over `Z ∩ K`; no requirement in charts other
than `ec_m` on its own transition zone; over the free part of `K` the step re-genericises.
Step `k` then: keeps the frozen ring; by (b) for `m = k` the old crossings met by frozen or mixed
simplices are stable under all vertex moves `< τ` (τ after `R`); the free part is made generic;
and the new crossings it creates must again satisfy (b) for all `m > k` — finitely many open
conditions per later chart on the fixed zones `V_m \ closure W_m`.

**Questions.**
1. Is Observation 1 correct — may a step replace the old double curves over the free part of
   `Z ∩ K` by new transverse ones, or does something downstream (the buffered boundary homotopy,
   fibre control `≤ 2`, `StarInj T`, properness, the boundary models on `BdM`) actually need the
   conjugacy? In particular: can re-genericising near a *boundary* double arc of `Z` (ending on
   `BdM`) break the boundary model?
2. Is the weaker invariant (a)+(b) enough to prove the step? Where exactly does the argument need
   stability **outside** the zones `V_m \ closure W_m` — e.g. a free simplex of another sheet passing
   through an old crossing that lies over `Z ∩ closure W_k`-free part but close to a mixed simplex;
   or third-sheet entry; or crossings between a free and a frozen triangle whose intersection
   segment ends on a frozen edge?
3. Requirement (b) for the **new** crossings: a crossing generic in `ec_k`'s affine structure is
   only piecewise affine in `ec_m`. Does (b) still force your common subdivision `𝒬` and the
   wall-transversality conditions `Σ(g) ∩ |𝒬^(1)| = ∅`, `Σ(g) ⋔ relint F`, now only on the fixed
   zones — or is there a cheaper formulation (e.g. choose the finite atlas so that the transition
   maps are affine on the pairwise overlaps of the zones; or state (b) intrinsically as "the two
   link circles at every double point cross at interior points of link edges with respect to the
   subdivision making `ec_m ∘ D` facewise affine")?
4. If (a)+(b) fails, give the smallest counterexample configuration and say whether your §3
   invariant (stability over all of `Z`, all later charts) is then really the minimum.

**What we will do with the answer.** If (a)+(b) works, only the crossing leaf and the seed leaf of
the skeleton change (the pairing certificate disappears; the seed becomes your §2 with `φ_* = ec ∘ D`
on the frozen/mixed part plus a generic choice on the free part). If not, we implement your §3.
