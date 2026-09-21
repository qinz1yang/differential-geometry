# E. The closed branches of Lemma 2: can orientability delete Case 1, and how to push off in Case 2

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only. Lean paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
Context: your answers B, B2, D (`consult/*-answer-digest.md`). The scoping this prompt rests on
is the section "车道 C — 闭支" at the end of `LANES_CODEX_20260920.md`.

As in prompt D: **try to refute our claims before confirming them.**

## 0. What the book says and what the tree has

Moise p. 185, in full. *Case 1*: `Γ` is the image of a single polygon `J ⊂ Δ`, `D|J` exactly
two-to-one; take a regular neighbourhood of `Γ`, a cylindrical diagram with identification
`(x, y, 0) ∼ (y, x, 1)`, replace the two rectangles by the traces of `x − y = ±1`, whose union
is an annulus `A'`, and redefine `D|A`. *Case 2*: `Γ` is the image of two disjoint polygons
`J₁, J₂`; take `J₁` inmost; `Γ` bounds a 2-cell `Δ₁ ⊂ |D|`; map the interior of `J₂`
homeomorphically onto `Δ₁`, "and the resulting image can be forced off a neighborhood of `Δ₁`
in `|D|`". Nothing more.

The tree has the selection step, with the dichotomy
(`LoopTheorem/InnermostCleanDisk.lean:221`):

```lean
theorem exists_innermost_cleanDisk_of_exists_not_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch, ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch, ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧ IsPLBall 2 Q ∧
        Q ⊆ interior D.domain ∧ frontier Q = J ∧
        doublePointPreimage D D.domain ∩ Q = J ∧
        D '' interior Q ∩ doublePointSet D D.domain = ∅ ∧
        D '' Q ∩ doublePointSet D D.domain = D '' J ∧
        (hD.branchPreimage c = J ∨
          ∃ T, IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧ InjOn D Q)
```

and model-level files for Case 1 (`CylinderSplice.lean`, `ClosedSeamResolution.lean`,
`ClosedBranchOrientability.lean`). Nothing connects a real closed branch to a descending
surgery. Your answer B says Case 1 needs the twisted tube: marked interior blocks chained round
the circle, a PL pair isotopy of the monodromy to the swap (conjugacy being false), a mapping
torus equivalence. That is the most expensive item left on the whole Lemma 2 side.

## 1. Can orientability delete Case 1?

**Observation.** The consumer already assumes orientability (`MoiseChain.lean:36`):

```lean
def Moise252 : Prop :=
  ∀ {E : Type} … (K : Geometry.SimplicialComplex ℝ E) (_ : Finite K.faces),
    IsCombinatorialManifoldWithBoundary 3 K → IsOrientable 3 K → …
```

while the statements the surgery serves do not: `LemmaTwoBufferedStatement`
(`LoopTheorem/LemmaTwoBuffered.lean:60`) quantifies over all `NormalSystem`s `S`, `T` and a
`DoubleCoverReduction S T`, and `DescentStepStatement` (`LoopTheorem/LemmaTwoSpine.lean:124`)
over every `NormalSystem S`, working in `double 3 S.manifoldComplex`. The tower's cover
producer even branches on orientability (`LoopTheorem/CoverReduction.lean:126`,
`by_cases hor : S.IsOrientableManifold`: the orientation cover if not, another double cover if
the boundary component is not a sphere).

**Claim.** In an orientable 3-manifold Case 1 cannot occur. Smooth-style argument: orient `Δ`,
`M`, and `J`; `J → Γ` is the connected double cover, so both preimages `a, b` of a point of `Γ`
induce the same direction `t` on `Γ`. Let `n_a`, `n_b` be the oriented normals of the two sheets.
`σ(a, b) := sign det (t, n_a, n_b)` is nonzero by transversality, locally constant, and
`σ(b, a) = −σ(a, b)`. Going once round `Γ` carries the ordered pair `(a, b)` to `(b, a)`, so
`σ(a, b) = σ(b, a)`: contradiction. The tree's present exclusion,
`IsCylindricalDiagram.not_closedBranchCase1` (`ClosedBranchOrientability.lean:289`), reaches
the same conclusion but only *after* a cylindrical diagram round `Γ` exists — i.e. after the
tube we want to avoid building.

**Q1.1** Is the claim right, including for a source circle `J` that is two-sided in `Δ`
automatically (it lies in a disk)? Is there a genuine Case 1 example in a nonorientable `M`
(so that the hypothesis is necessary and not merely convenient)? We have in mind the solid
Klein bottle with monodromy the reflection `(x, y) ↦ (y, x)` of the normal disk.

**Q1.2** What is the cheapest rigorous **PL** form of the sign argument, given what exists?
The tree has: combinatorial orientability `IsOrientable 3 K` (coherent orientation of the
3-simplices); at each double point a PL chart carrying the two sheets to the coordinate planes
(`HasPLTwoSidedCrossingAt.exists_openPartialHomeomorph_slab_interior_isImage`,
`BoundaryCrossingChart.lean:303`); local injectivity of `D`. There is no tangent bundle and no
degree theory for PL charts beyond what `ClosedBranchOrientability.lean` proves for circle maps
with increasing lifts. We would like an argument that needs finitely many overlapping crossing
charts round `Γ` and a sign attached to each chart, **not** a product structure on a
neighbourhood of `Γ`. Candidates we see: (a) the sign "is the chart orientation preserving
w.r.t. the orientation of `M`, the orientations of the two source sheets and the direction of
`J`", shown constant on overlaps; (b) a homological version — the local intersection number of
the two sheets along `Γ`, or the first Stiefel–Whitney class of the normal bundle of `Γ`
evaluated via the link of an edge of `Γ` in a triangulation in which `|D|` is a subcomplex;
(c) reduce to the existing circle statement by reading the four rays on the boundary circles of
the links of the vertices of `Γ`, where the link of a vertex of `Γ` is a PL 2-sphere meeting
`|D|` in two circles crossing twice. Which would you formalise, and what exactly must be proved
about overlaps?

**Q1.3** The cost on the other side. To use the exclusion, orientability has to reach the
cell on which the surgery is done. Which of the following are needed, and are any false in the
combinatorial setting? (i) a subcomplex that is a combinatorial 3-manifold with boundary inside
an orientable one is orientable (regular neighbourhoods in the tower); (ii) a double cover of an
orientable combinatorial manifold is orientable; (iii) the double `double 3 K` of an orientable
`K` along its boundary is orientable; (iv) with `K` orientable at the top, **every** level of the
Stallings tower is orientable, so the non-orientable branch of `CoverReduction` is never taken.
Is it then better to (A) add `S.IsOrientableManifold` (and its preservation) to
`LemmaTwoBufferedStatement`, `GeneralPositionInDoubleBufferedStatement`, `DescentStepStatement`
and re-run the induction, or (B) keep those statements general and prove Case 1 only in the
form "`M` orientable ⇒ contradiction", leaving the non-orientable Case 1 as an explicit open
obligation that the orientable consumer never calls? We lean to (A) if (i)–(iv) are routine.
Does anything downstream of `Moise252` in Moise's route (30.4, 30.5 tame, §34–35) ever need the
loop theorem in a non-orientable 3-manifold?

## 2. Case 2, nested sub-case (2a): no tube, no push — is that right?

Let `E₂` be the disk of `Δ` bounded by `T`. Since `Q` is clean, `T ⊄ Q`, so either
`Q ⊆ interior E₂` (2a) or `Q ∩ E₂ = ∅` (2b).

**Claim 2a.** Define `G = D` off `interior E₂` and `G = D ∘ k` on `E₂`, `k : E₂ → Q` a PL
homeomorphism extending the identification `T → J`. Then: `G` is continuous and PL; locally
injective (at `T` it is the bent sheet `Y_out ∪ X_in`, and the crossing model says those two
half-sheets meet only along `Γ`; note `J` *and a collar of it outside `Q`* lie in `E₂` and are
overwritten, so the half-sheet `X_out` no longer exists); fibres ≤ 2; the double point set of
`G` is a union of **whole** old branches not containing `c` (each preimage component of another
branch is connected, misses `J ∪ T`, is not inside the clean `Q`, hence lies entirely in the
overwritten annulus `E₂ \ Q` or entirely outside `E₂`; a branch with exactly one preimage
component in the annulus simply disappears; `D '' interior Q` carries no double points, so
nothing new appears); `G = D` near `∂Δ`, so the three descent invariants (side, boundary buffer,
avoidance of the normal subgroup) are inherited verbatim; the remaining crossings are still
normal crossings because `G = D` near their preimages.

**Q2.1** Confirm or refute, in particular the normality of `G` **at `T`**: `G` is locally
injective there but its image has a corner along `Γ`. Our `NormalSingularCellData` asks local
injectivity, fibres ≤ 2, a PL crossing model at each *double* point, properness at `BdM`, and a
triangulated singular set; it asks nothing at non-singular points. Is a bent sheet acceptable
for every later use (general position is not re-run), or does some later step silently assume
more regularity at non-singular points?

## 3. Case 2, disjoint sub-case (2b): the push-off

Here overwriting `E₂` by `D ∘ k` makes the whole disk `Δ₁ = D(Q)` a double set, so a push is
unavoidable. Our plan, replacing Moise's one sentence:

Triangulate `M` with `|D|` a subcomplex and let `N` be a regular neighbourhood ball of the
embedded clean disk `Δ₁`. Round `Γ = ∂Δ₁` the four half-sheets occur in the cyclic order
`X_in = Δ₁`, `Y_out`, `X_out`, `Y_in`, so `∂N ∩ |D|` consists of three disjoint circles
`c_{Y_out}`, `c_{X_out}`, `c_{Y_in}`, parallel on the sphere `∂N`, with `c_{Y_out}` and
`c_{Y_in}` adjacent to the two caps of `∂N` parallel to `Δ₁`. Let `Δ'` be the disk of `∂N`
bounded by `c_{Y_out}` and containing neither of the other circles: `Δ' ∩ |D| = ∂Δ'`. Let
`T' = D⁻¹(c_{Y_out})` near `T`, a circle parallel to `T` outside `E₂`, bounding `E₂' ⊃ E₂`;
define `G = D` off `E₂'` and `G : E₂' → Δ'` a PL homeomorphism extending `D|T'`. The annulus
of `Y` between `Γ` and `c_{Y_out}`, and all of `Y_in`, are discarded.

**Q3.1** Is this right? In particular: (i) that `∂N ∩ |D|` is exactly three circles needs `N`
small and `|D| ∩ N = ` (a neighbourhood of `Δ₁` in `X`) `∪` (a collar of `Γ` in `Y`), which uses
cleanness of `Q` and the fibre bound — anything else? (ii) `D⁻¹(N)` near `T` is an annulus
round `T` whose outer boundary is `T'` — does this need more than the crossing model and
compactness? (iii) local injectivity of `G` at `T'` needs `Y` transverse to `∂N`; is that
automatic for a derived neighbourhood, or must it be arranged? (iv) the other preimage
components inside `E₂'`: as in 2a, whole branches disappear; but a branch with one preimage
component in the thin annulus `E₂' \ E₂` — can that happen for `N` small? (v) the side and
buffer invariants hold since everything happens in `interior Δ` and inside `N ⊂` the side `C`
— but `N ⊂ C` needs `Δ₁ ⊂ interior_M`-side control: `D(Q)` may touch `BdM`? (`Q ⊆ interior Δ`
and properness `D⁻¹(BdM) = ∂Δ` give `Δ₁ ∩ BdM = ∅`; then `N` small suffices — agreed?)

**Q3.2** Is there a formulation of 2b that avoids regular-neighbourhood theory altogether —
for instance a one-sided collar of the embedded disk `Δ₁` built from the crossing charts along
`Γ` and a bicollar of `interior Δ₁` — and if so which is cheaper to formalise given the tree
(`BicollarEmbedding.lean`, `SpanningDiskNeighborhood.lean`, `SpanningDiskBallNeighborhood.lean`,
`SpanningDiskPrism.lean` on the branch: relative ball neighbourhoods and prisms of *spanning
disks of a closed surface*; here the "surface" `Y` is only an immersed sheet)? Could those
spanning-disk results be applied to the embedded surface `Y ∩ N₀` for a small neighbourhood
`N₀` of `Γ`?

**Q3.3** A cheaper alternative we could not rule out: in 2b, is there always a *different*
choice of branch or of roles that lands in 2a or in a boundary case, so that 2b never has to be
performed (e.g. by choosing `c` differently, or by an induction on the number of preimage
circles outside `Q`)? We think not — two disjoint clean disks on disjoint circles is a perfectly
good configuration (two spheres meeting in one circle, cut open) — but would like it confirmed.

## 4. Fixtures

**Q4** Please give one explicit positive-complexity normal singular cell for each of 2a and 2b
(in the style of the two models of your answer D), with the nested/disjoint condition visible,
on which the whole hypothesis tuple of the corresponding assembly holds simultaneously; and, if
Case 1 survives Q1, one in a non-orientable `M`.
