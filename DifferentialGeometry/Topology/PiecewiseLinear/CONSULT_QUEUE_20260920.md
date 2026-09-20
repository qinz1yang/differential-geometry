# Consultation queue — 2026-09-20

Paste-ready prompts for GPT Pro / Fable / Astra. Each one is self-contained: it
names the repository, the branch and the commit, so the consultant reads the right
tree. Ordered by how much they unblock.

Repository **https://github.com/qinz1yang/differential-geometry-dev**,
branch **`codex/moise-integration`**, commit **`b5ad49d39`**.
Other branches (`main`, `Moise`, `candidate`, other `codex/*`) diverge and their
line numbers do not match; every prompt below says so.

| # | Question | Unblocks | Status |
| --- | --- | --- | --- |
| 1 | Relative product tube along a branch arc | Lemma 2, the last geometric brick of the boundary case | ready |
| 2 | Injectivity in the relative compact PL approximation | Moise 35.2, and 35.1/34.1 behind it | ready |
| 3 | Where closed-branch Case 1 actually occurs in the tower | Lemma 2, closed case | drafting |
| 4 | Boundary room and the free-homotopy lift | Lemma 2, the selection step | drafting |

Entries 3 and 4 depend on lane reports still in flight; they will be filled in
below as those land, and this line is what to check on waking.

## The status these prompts rest on

Read this first; it is what makes the two prompts the right two. Every arrow below
is a **proved** Lean theorem on this branch, verified by focused compile, with
transitive axioms exactly `propext, Classical.choice, Quot.sound`. Every node in
**bold** is an open `Prop` with no producer.

```
  LemmaTwoStatement                      Moise352Stages n
        │ moise252_of_lemmaTwo                 │ moise352_of_stages
        │ EmbeddedDiskTower.lean:173           │ LocallyFiniteApproximation.lean:479
        ▼                                      ▼
     Moise252                               Moise352 n
        │ moise304_of_moise252                 │ plApproximationManifold_three_of_moise352
        │ SphericalShellCompression.lean:88    │ Endgame.lean:9   (only at n = 3)
        ▼                                      ▼
     Moise304                           PLApproximationManifold 3
        │ moise305_tame_of_moise304
        │ TameNestedCells.lean:34
        ▼
   Moise305Tame
```

So at this moment the two assembled chains have **exactly two open roots**:
**`LemmaTwoStatement`** and **`Moise352Stages 3`**. Prompt 1 attacks the last
geometric brick of the first; prompt 2 attacks the core of the second. Nothing else
on either chain is missing.

Two status corrections worth recording, both verified against current source rather
than against the notes:

* `ROUTE_AUDIT_20260919.md` lists confirmed statement defects in `Moise252`,
  `Moise331` and `Moise351`. **All three are now repaired in the source.**
  `Moise252` (`MoiseChain.lean:36`) carries the non-nullhomotopy of the new boundary
  inclusion into the specified boundary component at lines 50–54, which is the book's
  third conclusion. `Moise331` (`:136`) now existentially chooses `T, L'` with
  `(derivedNeighborhood T L').space ⊆ U`, fixing the quantifier order, and adds the
  no-valence-one-vertex condition. `Moise351` (`:191`) now requires
  `IsLocallyFinitePolyhedralGraph` input and concludes
  `IsLocallyFiniteRegularNeighborhoodOf`. The audit table is stale, not wrong at the
  time it was written. That matters because `moise252_of_lemmaTwo` proves the
  *repaired* `Moise252`, so Lemma 2 buys more than the notes suggest.
* `Moise331`, `Moise341` and `Moise351` are all still open, but **none of them is
  currently wired into the `Moise352Stages` reduction**. The reduction as built goes
  through `plManifoldMapApproximation` (proved, `MoiseChain.lean:243`) and
  `CompactEmbeddingApproximation`, and what it is missing is injectivity — see
  prompt 2. Whether `Moise341` is the right thing to consume is precisely question
  2.Q2.

One thing that neither `lake build` nor `#print axioms` can check, and that is not
yet done: **non-vacuity anchors.** A vacuous `Prop` — one whose hypotheses nothing
satisfies — passes both. `LemmaTwoStatement` quantifies over
`NormalSystem.DoubleCoverReduction`, and `NormalSystem` (`SingularCell.lean:524`) is
a twenty-odd-field structure; nobody has yet exhibited one. Until that is done, a
proof of `LemmaTwoStatement` would be worth less than it looks. The tree does this
correctly elsewhere — `ArcChainNeighborhood.lean:73`
`exists_isLocallyFiniteRegularNeighborhoodOf_nonempty_arc` is a worked witness — so
the pattern to copy exists. This is queued as work, not as a consultation.

---

## 1. The relative product tube along a branch arc

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/qinz1yang/differential-geometry-dev**,
branch **`codex/moise-integration`**, commit **`b5ad49d39`**.

```
git clone https://github.com/qinz1yang/differential-geometry-dev
cd differential-geometry-dev && git checkout b5ad49d39
```

Do not read `main`, `Moise`, `candidate` or another `codex/*` branch; they diverge
and line numbers will not match. Paths below are from the repository root.

### State

Moise's Lemma 2 runs an induction on the branch complexity of the singular set of a
normal singular two-cell `D` in a combinatorial 3-manifold. For a *boundary* branch
`c` there are two candidate surgeries. The second one, the cross reglue
(`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CutAndPaste.lean:1223`,
`exists_cross_reglued_cell_of_boundaryBranch`), does not delete the branch on its
own: it concludes `hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain`,
because the reglued map still sends both new seams to the centre of the transverse
cross.

The repair is now proved **in the model**, in
`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CrossSeamResolution.lean`
(854 lines, 110 declarations, axioms exactly `propext, Classical.choice,
Quot.sound`). Replacing the two bent transverse arcs `[e₁,0] ∪ [0,-e₂]` and
`[-e₁,0] ∪ [0,e₂]` by the two disjoint chords of the cross-section square,
fiberwise along `Icc 0 1`, is the restriction of a single affine map of the plane,

```
crossSeamChordPos p = ((p.1 + p.2 + 1)/2, (p.1 + p.2 - 1)/2)
```

and gives `doublePointSet crossSeamResolve bentSource = ∅` exactly, is the identity
on the four lateral attaching intervals, and does not move the base coordinate.

So the model step is done. What is missing is the statement that lets the model be
applied: a neighbourhood of the branch arc in the ambient 3-manifold with a product
structure *relative to the four sheets of `D` that meet along the branch*.

### What the tree already has

- `DifferentialGeometry/Topology/PiecewiseLinear/RegularNeighborhood.lean` —
  `regularNeighborhoodIn K A`, `regularNeighborhood K A :=
  regularNeighborhoodIn (secondDerived K) A`, with
  `regularNeighborhood_mem_nhdsWithin K A hx : (regularNeighborhood K A).space ∈
  𝓝[K.space] x` for `x ∈ A`.
- `DifferentialGeometry/Topology/PiecewiseLinear/ArcChainNeighborhood.lean:57` —
  `IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_arcComplexIn`:
  for a simplicial arc in a finite combinatorial 3-manifold with injective vertices
  and all arc faces interior, the derived neighbourhood of the arc is a PL **ball**
  neighbourhood.
- `DifferentialGeometry/Topology/PiecewiseLinear/CylinderSplice.lean` — the model:
  `spliceSquare`, the transverse chords `spliceArcPos`/`spliceArcNeg`, the cylinder
  `spliceSquare ×ˢ Icc 0 1`, and (`:466`, `:483`) the fact that the two sheets' rays
  meet the square's boundary in the two interleaved opposite pairs.

So *a ball neighbourhood of the arc exists*. What is not available is the product
structure carrying the four local sheets of `D` to the four model half sheets.

### The question

**Q1.** State precisely the theorem that supplies this. Informally: for a normal
singular two-cell `D` in a combinatorial 3-manifold `K` and a branch arc `c` of its
singular set, there is an open `U ⊇ branchCarrier c` and a PL homeomorphism
`Φ : spliceSquare ×ˢ Icc 0 1 → U` carrying the core `{0} ×ˢ Icc 0 1` onto
`branchCarrier c` and the four model half sheets onto the four local sheets of `D`
along the whole arc. What are the exact hypotheses — how much of "normal" is
needed, does the arc have to be interior, is finiteness needed, does the branch have
to be a single arc rather than a circle?

**Q2.** Is this a consequence of a *relative* regular neighbourhood theorem for the
pair (3-manifold, 2-complex), and if so which form — Rourke–Sanderson, Hudson,
Zeeman? Please give the precise citation and the precise statement, and say what
has to be checked to apply it here. If instead Moise proves it directly, give the
book page (Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47) and the
statement number.

**Q3.** Is the product structure *along the whole arc* actually needed, or does
Moise only ever use a local product at each point plus a compactness/uniqueness
argument? If the latter, what is the weaker statement that suffices, since it would
be much cheaper to prove.

**Q4.** Is there a hypothesis under which this is **false** — a normal singular
two-cell with a branch whose neighbourhood is not a product of that kind? Knowing
the counterexample would tell us which hypothesis of `NormalSingularCellData` is
load-bearing. If the four sheets can be locally knotted or the branch can be wild,
say so plainly.

### Constraints on the answer

- Exact mathematical statements, not strategy prose; Lean-ish is fine.
- Cite Moise by printed page where you rely on him, and say what you could not verify.
- Do not weaken any existing statement; anything more general must keep the old ones
  as corollaries.
- If a piece already built is aimed at the wrong target, say so plainly — that is the
  most useful possible answer.

---

## 2. Injectivity in the relative compact PL approximation

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/qinz1yang/differential-geometry-dev**,
branch **`codex/moise-integration`**, commit **`b5ad49d39`**. Same warning: do not
read another branch.

### State

Moise 35.2 — PL approximation of a topological embedding of one PL manifold in
another — has been reduced twice.

1. `DifferentialGeometry/Topology/PiecewiseLinear/LocallyFiniteApproximation.lean:479`
   proves `moise352_of_stages : Moise352Stages n → Moise352 n`. All the non-compact
   content (limit of the stages, keeping injectivity, keeping the PL local inverse,
   converting stagewise constant errors into a prescribed continuous positive error)
   is done there. The remaining obligation `Moise352Stages` is at `:461` and asks,
   on each compact stage `T.coreSpace i` and for each constant tolerance `ε i`, for a
   PL embedding approximating `h` and **agreeing with the previous stage's map on the
   previous stage**.
2. `DifferentialGeometry/Topology/PiecewiseLinear/CompactEmbeddingApproximation.lean`
   reduces the compact statement to **injectivity**: the local-inverse clause of
   `IsPLHomeomorphInto` is discharged on a compact set.

And the PL-map half, *with the agreement clause*, is already proved:
`DifferentialGeometry/Topology/PiecewiseLinear/MoiseChain.lean:234`
`PLManifoldMapApproximation`, proved at `:243` from `exists_isPLOn_dist_lt_eqOn`:

```
IsPolyhedron P → IsPolyhedron Q → Q ⊆ P → ContinuousOn f P → IsPLOn n 3 f Q → 0 < ε →
  ∃ g, IsPLOn n 3 g P ∧ EqOn g f Q ∧ ∀ x ∈ P, dist (g x) (f x) < ε
```

So the gap is exactly this: **the approximating PL map can be chosen injective on
the stage, relatively to the previous stage.**

The tree also carries `Moise341` (`MoiseChain.lean:99`), the PL-ball case in
`EuclideanSpace ℝ (Fin 3)` with a constant ε and hypotheses `ContinuousOn h C`,
`InjOn h C`; it is an open obligation here. `Moise351` (`:191`) is the locally
finite *polyhedral graph* case and is a different statement. `Moise331` (`:136`) is
the regular-neighbourhood-of-a-graph statement, also open; an earlier audit found
and the tree has since repaired the quantifier-order defect, so `Moise331` now
existentially chooses the neighbourhood inside the prescribed open `U`.

### The questions

**Q1.** Write the injectivity statement precisely, in the relative form
`Moise352Stages` needs: a topological embedding `h` of a compact PL manifold pair,
a PL map `g` already ε-close to `h` and already agreeing with a PL embedding on a
subpolyhedron `Q`, and the conclusion that `g` can be modified off `Q` to be a PL
embedding still ε-close. State the exact hypotheses on the pair and on `Q`.

**Q2.** Does `Moise341` imply it? `Moise352Stages` is stated for arbitrary `n` and
an arbitrary charted PL target `M₂`, while `Moise341` is fixed at dimension 3 with
target `EuclideanSpace ℝ (Fin 3)` and domain a PL ball. If the implication needs
`n = 3`, say where. If it needs more than the ball case, say exactly what.

**Q3.** Moise's route to 34.1 goes through 33.1 and is long. Is there a shorter
modern route to the *relative* compact statement in dimension 3 — Bing's side
approximation theorem, Hudson's PL approximation, or the Hauptvermutung machinery
this tree has already built? Give the precise statement you would import and its
citation, and say what its own prerequisites are, so we can judge whether it is a
shortcut or a detour.

**Q4.** Is the relative form genuinely harder than the absolute one, or is there a
standard trick (approximate absolutely on a slightly larger stage, then interpolate
in a collar) that reduces it? If the collar trick works, what exactly does it need
about the previous stage's boundary?

**Q5.** Honest assessment: how far is 35.2 from being closeable, in the sense of
how many independent theorems of this size are between us and it? We currently
believe it is five chapters deep (35.2 → 35.1 → 34.1 → 33.1 → …) and would like that
checked rather than confirmed.

### Constraints on the answer

Same as prompt 1: exact statements, printed-page citations, no weakening of existing
statements, and a plain statement if something already built is aimed wrong.

---

## 3. Where closed-branch Case 1 actually occurs in the tower

*Drafting — waiting on the lane that is instantiating the exclusion on the splice
model.* The previous consultation established the key precision: the orientability
in `CylindricalMonodromy.lean:78` is that of the **diagram's own target complex**
(the triangulated tube with induced orientation), not of the ambient manifold, so
there is no contradiction with `Moise252` requiring `IsOrientable 3 K`. The residual
question is whether Case 1 — a closed branch whose preimage is a single circle
doubly covering it, forcing the reflection model `(x,y,0) ~ (y,x,1)` — actually
arises at some stage of the Stallings tower, and if so what the induction does with
it. This will be written up once the exclusion is instantiated concretely.

## 4. Boundary room and the free-homotopy lift

*Drafting — waiting on the lane assembling the selection step.* The two boundary
candidates now both descend (see prompt 1), so the selection logic is "both descend,
pick the one the word elimination allows". What is not yet pinned down is the
boundary room hypothesis that `CutAndPaste` needs and the free-homotopy lift that
carries the boundary class up the tower. The prompt will state whichever of those
the lane could not discharge, verbatim.
