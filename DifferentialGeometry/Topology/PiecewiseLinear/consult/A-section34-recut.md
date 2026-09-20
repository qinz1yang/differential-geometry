# A. Re-cutting the §34 transition: obligations strictly smaller than Moise 35.2

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only; every other branch diverges and line numbers will not match. Lean paths
below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. The book is Moise,
*Geometric Topology in Dimensions 2 and 3*, GTM 47; pages are printed pages.



### State

The target is Moise, *Geometric Topology in Dimensions 2 and 3* (GTM 47), Theorem 35.2
(printed p. 251): PL approximation of a topological embedding of a polyhedral 3-manifold
with boundary `K ⊆ M₁` into a PL 3-manifold `M₂`. In Lean (`Transition361.lean:251`):

```lean
def Moise352 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ (φ : M₁ → ℝ), ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x
```

Proved, with axioms exactly `propext, Classical.choice, Quot.sound`:

```
Moise352InwardPush 3 ∧ Moise351 ∧ Moise352SkeletonExtension 3
    → Moise352 3                         (SkeletonReduction.lean:236)
    → PLApproximationManifold 3          (Endgame.lean)
```

**What we found today, and the reason for this prompt.**
`Moise352SkeletonExtension n` (`SkeletonReduction.lean:208`) has the *same binder prefix
and the same conclusion* as `Moise352 n`, with two hypotheses inserted before the
conclusion: the inward push at every tolerance `ψ`, and Theorem 35.1 on every open
`U ⊆ K` for every locally finite polyhedral graph `G ⊆ U`. So
`Moise352 n → Moise352SkeletonExtension n` holds by weakening, and the "reduction" is modus
ponens: **the open obligation is all of 35.2 given 35.1 and the push, i.e. the whole of
the §34 argument, undecomposed.** It is true (at `n = 3`), it is faithful to the logical
shape of printed p. 251, and it records no progress.

The other two inputs:

* `Moise352InwardPush 3` (`SkeletonReduction.lean:158`) is proved for compact `K`
  (`ControlledInwardPush.lean:554`). We tried to refute the non-compact statement at the
  quantifier extremes and could not; it localises (exhaustion by compact stages, per-stage
  collar heights tapering to zero on the seams), needs no new vocabulary, and is in
  progress (~1–1.4k lines). **Not a question for you.**
* `Moise351` (`MoiseChain.lean:191`), Theorem 35.1, is open with no producer. It asks for
  `ContinuousOn φ U ∧ ∀ x ∈ U, 0 < φ x` where the book asks only strong positivity, so it is
  a slightly weaker deliverable than the book's; its only consumer feeds it continuous `ψ`.

Mismatches between the tree and the book that you should know about:

1. `Moise341` (`MoiseChain.lean:99`) is stated `EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ
   (Fin 3)` with a constant `ε` and source `IsPLBall 3 C`. Printed p. 249 applies 34.1 as
   `f_v : C''_v → M₂` with `M₂` an arbitrary PL 3-manifold. The Lean statement has no
   producer and no consumer.
2. §34 is written for a **finite** complex in **ℝ³** (Lemma 5(7) uses "the unbounded
   component of ℝ³ − …"; Lemma 8's termination uses finiteness). The Lean obligation is
   locally finite, in an arbitrary — possibly non-orientable — PL 3-manifold.
3. "One simplex at a time" (p. 251) is *not* an induction over skeleta. Pp. 244–246 perform a
   single seven-stage extension over a fixed decomposition — `Bd D_σ ∩ Bd D_e`, `Bd D_e`,
   `Bd C_v ∩ Bd D_σ`, `X(σ³,v)`, `C_v`, `D_σ`, `C(σ³)` — after Lemmas 1–11 and Operations
   1–2 have fixed the combinatorics globally. There is no inductive hypothesis, no tower and
   no agreement clause. Two earlier formulations of ours that *did* introduce a tower with an
   agreement clause (`Moise352Stages`, `Moise352StageStep`) were both **false**, for
   quantifier reasons, so please do not reintroduce one without checking it at the extremes
   (tolerance huge; tolerance sequence fixed before the family).
4. `n` is unconstrained in `Moise352*`, and `Moise352 n` is false for `n ≥ 5`
   (homeomorphic, not PL-homeomorphic closed PL manifolds). Only `n = 3` is instantiated.

Tree inventory against the book's dependency chain (status: PROVED / CONDITIONAL on … /
STATED ONLY = a `def … : Prop` with no producer / ABSENT):

| Book | Tree | Status |
| --- | --- | --- |
| 25.1 / 25.2 | `MoiseChain.lean:31,36` | STATED / CONDITIONAL (Lemma 2 of the Loop theorem chain, separate effort) |
| 26.4 extended Loop theorem | `MoiseChain.lean:57` | STATED ONLY |
| 30.4 shell ⇒ separating PL sphere | `MoiseChain.lean:86` | CONDITIONAL on 25.2 |
| 30.5 nested 3-cells | `MoiseChain.lean:92`; tame form `TameNestedCells.lean:34` | wild: STATED ONLY; tame: CONDITIONAL on 30.4 |
| 30.6 / 30.7 toroidal shell, nested solid tori | `MoiseChain.lean:118,128` | STATED ONLY |
| 30.8 spine generates π₁ of a solid torus | `MoiseChain.lean:257` | STATED ONLY |
| 27.3 / 28.8 polygon in an annulus | — (annulus infrastructure exists) | ABSENT |
| 32.1–32.4 pseudo-cells, tubes | — | ABSENT |
| 33.1 | `MoiseChain.lean:136` | STATED ONLY, faithful |
| 34.1 | `MoiseChain.lean:99` | STATED ONLY, wrong form (mismatch 1) |
| 35.1 | `MoiseChain.lean:191` | STATED ONLY |
| §34 transition | `SkeletonReduction.lean:208` | ≡ 35.2 |

Proved infrastructure that exists: dual cells and splitting disks (`DualCells.lean`, incl.
`IsCombinatorialManifold.isPLBall_dualCell`), derived and regular neighbourhoods, general
position (`GeneralPosition.lean`, ~5.7k lines), annuli, `IsTopologicalSolidTorus`, a 2-D PL
Schoenflies theorem, PL map approximation with an agreement clause
(`exists_isPLOn_dist_lt_eqOn`, `ManifoldApproximation.lean:347`, dimension-free),
locally finite piece towers with a gluing lemma (`LocallyFinitePieceTower.lean:148`).

### The questions

**Q1. The re-cut.** Replace `Moise352SkeletonExtension 3` by a DAG of obligations, each
*strictly weaker than 35.2* and each statable in the vocabulary above, such that a proved
reduction to `Moise352 3` remains. Please give exact statements (Lean-ish is ideal), not
strategy prose. In particular: (i) the precise form of each of Lemmas 1–13 and Operations
1–2 of §34 that the seven-stage extension consumes, as transported to §35's setting;
(ii) the seven stages themselves as seven extension lemmas with their exact input and
output clauses; (iii) which statement carries the tolerance, and how it is chosen — *before*
or *after* the subdivision, the regular neighbourhood and the map from 35.1. This is the
step we have twice formulated falsely.

**Q2. ℝ³ versus a manifold target, finite versus locally finite.** Where §34 uses ℝ³
(unbounded component, Lemma 5(7)) or finiteness (Lemma 8), what replaces it on printed
pp. 248–251? State exactly the "two reductions" of the first paragraph of the proof of 35.2
and say whether the argument can be run *without* them by localising to small stars whose
images lie in single charts of `M₂`. If chart-localisation works, give the precise
smallness condition and where it is chosen.

**Q3. The right 34.1.** State 34.1 in the form p. 249 uses (`M₂` a PL 3-manifold, pointwise
or constant tolerance?) and say whether it follows from the ℝ³ form by a chart argument, or
whether the ℝ³ form is genuinely weaker.

**Q4. The minimal prerequisite set.** Which of 26.4, 30.5 (does the *tame* form suffice
everywhere it is used in §§33–35?), 30.6, 30.7, 30.8, 28.8, 32.1–32.4 are genuinely on the
path to 35.2 at `n = 3`, with the page where each is consumed?

**Q5. A shorter route?** Is there a published route to the conclusion of `Moise352 3`, or
directly to `PLApproximationManifold 3` (every homeomorphism of PL 3-manifolds is
approximable by PL homeomorphisms), that is *shorter given this tree* — Bing's side
approximation (1957/1959), Hamilton's torus-trick proof (1976), Shalen (1984), or other?
For each candidate give the precise statement to import, its own prerequisites, and whether
those prerequisites are closer to what the tree has than §§32–34 are. We want this judged,
not merely listed: a route that needs the Loop theorem anyway is not a shortcut.

**Q6. Honest size.** How many independent theorems of the size of 33.1 stand between the
tree and 35.2 on the best route? We currently believe: 26.4, 32.x, 33.1, 34.1, 35.1 and the
§34-style transition — six chapter-scale items — and would like that checked rather than
confirmed.

### Constraints on the answer

Exact mathematical statements; cite Moise by printed page and say what you could not verify;
do not weaken an existing statement (several are consumed verbatim by proved reductions);
if something already built is aimed at the wrong target, say so plainly. **"This statement
of yours is false, here is the counterexample" is the most valuable answer you can give:**
seven statements on these chains have turned out false, each for a quantifier or
construction-reading reason.
