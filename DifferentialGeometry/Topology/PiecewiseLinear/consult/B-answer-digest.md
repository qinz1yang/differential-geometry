# B — answer digest (external consultant, 2026-09-20; reviewed branch head `b5086b0e2`)

Digest of the answer to `B-touching-seam.md`, keeping every statement and formula that work
will be built on. The checkable claims were verified against the tree by the lead the same day
(marked ✓). Notation: `W = |K| ⊂ M = double(|K|)`, `H = ∂W = BdM`, `A` the selected boundary
branch, `Q = [-1,1]²`, `I = [0,1]`, `X = ({x=0} ∪ {y=0}) ∩ Q`.

## Verdict

Route **(a), the relative product tube**, implemented by a *marked* version of the existing
arc-cell induction; keep `crossSeamResolve` and all its transport theorems. Do not develop a
general uniqueness theorem for regular neighbourhoods. `CrossSeamTube` and `ResolvedCellNormal`
are **not** aimed at the wrong target; their producer simply does not yet supply the PL and
boundary-relative data. Ranking: (a) > (d) simplicial [an implementation of (a), not an
alternative] > (b) bicollar > (c) general position.

## Corrections to our own formulations

1. **The tube is a neighbourhood of `A` relative to `W`, not a regular neighbourhood of the arc
   in the double.** Target: a PL embedding `Φ : Q × I → W`, `N = Φ(Q × I)`, with
   `Φ({0} × I) = A`, `N ∩ D(Δ) = Φ(X × I)`, `N ∩ H = Φ(Q × {0,1})`. The core's end-points lie
   on `∂N`. The separate **open isolating set** `U ⊂ M`, `N ⊂ U`, `Double(D) ∩ U = A`, may
   extend into both halves — the closed-cylinder / open-`U` split in the tree is right.
2. **The hypothesis on `B` is a neighbourhood condition, not dimension two.** Moise p. 184:
   `B'` "forms a neighborhood of |L| in B" ✓. With
   `Int_H B = {p ∈ H | some H-neighbourhood of p lies in B}`, carry the invariant
   `D(Δ) ⊂ W` and `D(∂Δ) ⊂ Int_H B`, and have the producer output
   `Φ(Q × {0,1}) ⊂ Int_H B` (stronger than `⊂ B`: it preserves the buffer for the next step).
   Dimension two is insufficient; so is "a surface with boundary" when the end-point lies on
   its boundary. (`B = range D.boundary` refutes the *consumer's* `hendDisks`, not literally
   the conclusion of `IsCrossSeamTubeProducer`, which does not assert it.)
3. **`PLPieceIn.exists_bicollar` needs `IsCombinatorialManifold 2` (boundaryless)** ✓
   (`BicollarManifold.lean:95`), so it does not apply to the bent disk. Route (b) would need a
   relative collar of a properly embedded disk compatible with `H`, one-sidedness continued
   along the arc, isolation of the negative collar from all other sheets, and a bump that
   vanishes near the artificial attaching edges but **not** at the true seam end-points.
4. **End-point link ≠ interior link.** Interior vertex of `A`: `(S², susp{1,2,3,4})`. End-point
   on `H`, working in `W`: `(D², T₄)`, a four-spoke tree with centre in `Int D²` and leaves on
   `∂D²`; the original disk contributes half-sheets ending on `H`.
5. **Consecutive closed vertex stars do not meet in a single disk** (the intersection can have
   3-dimensional parts). Use trimmed vertex blocks and transverse splitting disks / dual blocks
   (Moise §32, p. 223, for the unmarked decomposition), as `ArcCellNormalizationInduction.lean`
   already does; what is missing there is the four pages and the end-point boundary marking.
6. **(c) is false as a shortcut** ✓: in a transverse plane `y = |x|` and `y = -|x|` touch; move
   the second to `y = -|x| + ε` and they cross at `x = ±ε/2`. Swept along `I`, with a cutoff
   near the lateral wall, an arbitrarily small perturbation preserving local injectivity and
   the fibre bound replaces **one touching branch by two crossing branches**. Smallness and
   genericity do not control the branch count.
7. One ambient homeomorphism applied to both sheets cannot separate a double point; the
   modification must distinguish the two source sheets (as the tagged model does).
8. Do not quantify over arbitrary `G` with the same image and double points (`G = D` has the
   crossing pairing, not the bent one) — keep the actual cut-and-paste witness. (Already done:
   `IsCrossRegluedCell`.)

## The lemma package

**Lemma A — boundary-marked local four-page blocks.** After a finite adapted triangulation near
`A` respecting `D(Δ)`, `A`, `H` and the source-sheet information:
*Interior block extension.* A small block around an interior point of a normal double branch,
with two marked transverse cross-disks, is PL equivalent to
`(Q × I; X × I, {0} × I, Q × {0,1})`, and the equivalence can **extend a prescribed PL
identification on the incoming cross-disk** respecting the four pages and their cyclic order.
*End-point block extension.* The same at an end-point in `H`, one cross-disk being the block's
intersection with `H`, the block lying in `W`. The prescribed identification includes the
marked spokes. Proof: straighten the marked graph in the link, extend over the complementary
disk regions (2-D PL Schoenflies + extension over a disk), cone. A theorem about the pair
(ball, core arc) does not supply this.

**Lemma B — finite marked-block productization over an interval.** Blocks `C₀,…,C_r` in a
chain, consecutive ones meeting in the designated cross-disk, non-consecutive ones disjoint,
each of the form of Lemma A ⇒ the union is PL `Q × I`, pages ↦ `X × I`, core ↦ `{0} × I`. The
induction extends the identification on the outgoing interface; **the far-end framing is
chosen by continuation, never prescribed** (independent labelings at both ends may be
incompatible). Over an interval there is no monodromy.

**Lemma C — PL boundary-relative tube production.** Hypotheses: normality, the boundary branch,
`D(Δ) ⊂ W`, `D(∂Δ) ⊂ Int_H B`. Output: the existing `CrossSeamTubeData` plus: `Φ` a PL
embedding on `Q × I`; `N ⊂ W`; `N ∩ H = Φ(Q × {0,1})`; `Φ(Q × {0,1}) ⊂ Int_H B`. The isolating
`U` comes from compactness and disjointness of the finitely many branches; saturation of the
local two-sheet neighbourhoods excludes unrelated parts of the source.

**Lemma D — a PL reading of the actual cross reglue.** For the cross reglue `G` (with its
cut-and-paste witness), `P = G⁻¹(N) ∩ Δ'`, `F = closure_{Δ'}(Δ' \ P)`: a decomposition
`P = P₊ ⊔ P₋` into two disjoint compact PL disks and PL homeomorphisms
`κ± : P± → bentSheet±` assembling into the tagged `coord`, with
(4) `G = Φ ∘ crossSeamInclude ∘ coord` on `P`;
(5) `x ∈ P ∩ ∂Δ' ⇔ t(coord x) ∈ {0,1}`;
(6) `x ∈ P ∩ F ⇒ coord x` lies on the lateral attaching wall.
`P±` and `F` are polyhedra. A merely set-theoretic bijection `coord` is insufficient (it can
hide a discontinuous reassignment of sheet labels).

**Constructing `cell` instead of assuming it.**
(7) `R x = Φ (crossSeamResolve (coord x))` for `x ∈ P`, `R x = G x` for `x ∉ P`.
PL by finite gluing over the closed polyhedral cover `{P₊, P₋, F}`: on `P±` a composite of PL
maps, on `F` it is `G`, and on `P ∩ F` the two agree by (6) and lateral stationarity of the
model. So `R` is a `SingularTwoCell` on the same source disk. Then the existing transport gives
`Double(R) = Double(D) \ A`, the branch equivalence, normality and strict descent. Image
control: (8) `R(Δ') ⊂ G(Δ') ∪ N ⊂ D(Δ) ∪ N ⊂ W` (do not ask `R(Δ') ⊂ D(Δ)`). The boundary cover
becomes derived: `Ω₁ = e⁻¹(P)`, `Ω₂ = closure(S¹ \ Ω₁)`; the PL reading gives `hcocont`, (6)
gives `hlateral`.

Suggested bundles (schematic): `PLBoundaryTube (W B) T` with a `PLPieceIn` for
`T.chart '' spliceCylinder` whose complex space is `spliceCylinder` and whose map is `T.chart`,
`side : T.chart '' spliceCylinder ⊆ W`, `boundary_eq : … ∩ BdM = T.chart '' spliceEndDisks`,
`end_buffer : T.chart '' spliceEndDisks ⊆ relInterior BdM B`; and `PLCrossSeamReading T G` with
`coord`, `bijOn_coord`, `reglued_eq`, the two polyhedral source pieces with their PL
homeomorphisms, polyhedrality of `F`, `overlap_lateral`, `boundary_iff_end`. **No field may
assert that the resolved cell exists.** Keep the old conditional theorems; add adapters.

## Boundary and side

*Properness is a cheap consequence of normality* ✓:
`NormalSingularCellData.preimage_boundary_eq_frontier : D.domain ∩ D ⁻¹' BdM = frontier D.domain`.
If `D x ∈ H`, by `image_inter_boundary` there is a boundary point `z` with `D z = D x`; if
`x ≠ z` this is a boundary double point, and `exists_boundary_crossing_chart` +
`fiber_subset_frontier_of_boundary_crossing` (`LoopTheorem/BoundaryCrossing.lean:233, 222`) put
`x` on the frontier. Then connectedness of the source interior puts the image in one copy of
`Int|K|`. For the terminal existence statement reflection of the double suffices, but for
controlled surgery carry the side: `N ⊂ W` and (8). Keep `NormalSingularCellData` unchanged;
carry the side in the producer / induction context.

## Extremes

Coincident end-points of `A`: excluded (embedded arc). The two lifted crosscuts sharing a
source end-point: excluded (the restriction over an interval is a split 2-sheeted cover; Moise
says "disjoint", pp. 185–186) — keep disjointness in the witness. Case 4: the same geometric
resolution after relabelling the four pages; only the word bookkeeping differs
(`L₁ = συ`, `L₂ = στ⁻¹υφ⁻¹`, p. 187). A small proper neighbourhood of an embedded PL arc is a
ball, hence orientable; this says nothing about global knottedness and does not justify fixing
both end framings independently.

## Closed branches (Case 1)

The block construction gives a mapping torus of some PL automorphism `h : (Q, X) → (Q, X)`
whose ray permutation is dihedral. **Literal conjugacy to `Prod.swap` is FALSE** ✓: for an odd
increasing non-identity PL homeomorphism `ψ` of `[-1,1]` fixing the end-points,
`h(x,y) = (ψ y, ψ x)` has the ray permutation of swap but `h² = (ψ², ψ²) ≠ id`, so it is not
conjugate to an involution. The right statements:

```lean
theorem crossDiskAut_isotopic_of_same_rayPermutation (h k : PLCrossDiskAut)
    (hp : h.rayPermutation = k.rayPermutation) : Nonempty (PLPairIsotopy h k)
theorem mappingTorus_pairEquiv_of_pairIsotopy (H : PLPairIsotopy h k) :
    Nonempty (PLMappingTorusPairEquiv h k)   -- carrying core, cross and the source reading
```

(straighten on the cross and on the boundary arcs, then the relative PL Alexander trick in each
complementary sector). The ray permutation comes from the source: the connected two-fold
preimage says the monodromy exchanges the two sheets, which still allows a quarter turn; the
preimage circle `J` has an **annular** neighbourhood in the source disk (Moise pp. 184–185), so
`(ray permutation)² = id`, which excludes quarter turns and leaves the two diagonal
reflections. Chain: connected sheet cover + two-sided source circle ⇒ swap-type ray
permutation ⇒ PL pair isotopy to swap ⇒ PL equivalence with the swap mapping torus ⇒
`ClosedSeamResolution` applies. The Case 1 tube is the **twisted** disk bundle, not a solid
torus; a quarter turn exchanges the two smoothings, which is why the annulus argument is needed.

## References

Moise pp. 184–187 (Lemma 2, Cases 1–4), p. 223 (dual cells, splitting disks). M. M. Cohen,
*A general theory of relative regular neighborhoods*, Trans. AMS 136 (1969) 189–229 — the
consultant did **not** find a theorem there (or in Hudson, Rourke–Sanderson) matching the
marked four-page tube with its source reading; do not cite one as if it did.

**Next geometric target:** the boundary-marked four-page block extension lemma, then its
finite-chain induction.
