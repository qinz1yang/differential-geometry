# D. Vacuity audit: four hypotheses we believe are unsatisfiable, and what should replace them

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only. Lean paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
Some of the statements below live in working files that are **not** on the branch (we rejected
them); they are quoted here in full, so nothing in this prompt depends on a file you cannot see.

**What "vacuous" means here.** A theorem `H → C` whose hypothesis `H` can never hold is true,
compiles, passes every linter and the axiom audit, and proves nothing: nobody can ever supply `H`.
On one evening we found four of these in a Lean 4 formalisation of Moise's *Geometric Topology in
Dimensions 2 and 3* (Lemma 2 of the Loop theorem, and §34–35). Two had already been accepted into
the branch. **We are the ones asserting the vacuity, and we want it checked by someone who is not
us**: please try to *refute* each claim before you confirm it, and where you confirm it, give the
statement that should stand in its place.

Conventions: `Path x y` is Mathlib's continuous `[0,1] → X` from `x` to `y`; `γ.trans δ` runs
`γ` on `[0,1/2]` and `δ` on `[1/2,1]`; `pathToCircle` turns a loop into a map of the circle; a
`BoundaryWordWitness G ρ w` says that the boundary circle of the singular 2-cell `G : Δ → M`
factors as `ρ ∘ loop` through an embedding `ρ : X → M` with `loop` freely homotopic to the word `w`
(`LoopTheorem/BoundaryWordWitness.lean:84`).

---

## Part 1. The boundary words of the two cut-and-paste candidates

### 1.0 The geometry, as we understand it (please check this first)

`D : Δ → M` is a normal singular 2-cell, `Δ ⊂ ℝ²` a PL disk. A *boundary branch* of its double
point set has preimage two disjoint PL arcs `A, C ⊂ Δ`, each a chord of `Δ`, with a PL
homeomorphism `g : A → C`, `D ∘ g = D` on `A`. The chords cut `Δ` into `Δ₁ ∪ Δ₂ ∪ Δ₃` with
`Δ₁ ∩ Δ₂ = A`, `Δ₂ ∩ Δ₃ = C`, `Δ₁ ∩ Δ₃ = ∅`. Write `p, q` for the end points of `A` and `u, v`
for those of `C`; going once round `∂Δ` we meet **four distinct points** `p, q, u, v` and four
arcs

```
σ₀ : p → q   (= Δ₁ ∩ ∂Δ)      τ₀ : q → u   (⊂ Δ₂)
υ₀ : u → v   (= Δ₃ ∩ ∂Δ)      φ₀ : v → p   (⊂ Δ₂)
```

each an *injective* path of the source circle `∂Δ`
(`BoundaryWordFourArcs.lean:547`, `exists_boundary_four_arc_word_of_cut`). The boundary of `D`
lies in a surface piece which is the image of an embedding `ρ : X → M`, and there is a continuous
`f : ∂Δ → X` with `ρ ∘ f = D|∂Δ`. The *letters* are the pushed-forward paths
`σ = f ∘ σ₀`, `τ = f ∘ τ₀`, `υ = f ∘ υ₀`, `φ = f ∘ φ₀` of `X`. Put `a = f p`, `b = f q`.
Two cases, according to how `g` matches the end points:

* **reversing**: `g p = u`, `g q = v`, so `f u = a`, `f v = b`;
  `σ, υ : a → b` and `τ, φ : b → a`.
* **preserving**: `g p = v`, `g q = u`, so `f u = b`, `f v = a`;
  `σ : a → b`, `τ : b → b`, `υ : b → a`, `φ : a → a` — **two of the letters are loops of `X`,
  although no source arc is a loop of `∂Δ`.**

The word of `D` itself is `w = σ τ υ φ`. The two candidates of Moise's Cases 3 and 4 (pp. 185–187):

* the **direct** candidate `G_d = Δ₁ ∪_g Δ₃` (discard `Δ₂`);
* the **cross** candidate `G_c`: keep all three pieces but exchange `Δ₁` and `Δ₃`, i.e. attach
  `Δ₁` to `Δ₂` along `C` (through `g`) and `Δ₃` to `Δ₂` along `A` (through `g⁻¹`)
  (`LoopTheorem/CutAndPaste.lean:1315`, `exists_cross_reglued_cell_of_cut`).

We computed their boundary words by walking round the reglued disks:

| | direct | cross (as walked) | cross (normalised) |
|---|---|---|---|
| reversing | `σ υ⁻¹` | `τ σ φ υ` — all four source arcs **forwards** | `σ φ υ τ` |
| preserving | `σ υ` | `τ σ⁻¹ φ υ⁻¹` — `σ₀`, `υ₀` **backwards** | inverse, rotated: `σ τ⁻¹ υ φ⁻¹` |

Sanity check we did: with `d` the direct word, `d = 1` gives `c ∼ w` (reversing:
`c = d·(υφ)·d⁻¹·(στ)`) and `c ∼ w⁻¹` (preserving), which is the algebra the descent needs.

**Q1.0** Are the table and the two case descriptions right? In particular the directions in the
cross rows.

### 1.1 Claim: `hlong` is unsatisfiable (this is on the branch)

`LoopTheorem/BoundaryWordWitnessOfCell.lean:210` (and its twin at `:230`; the `_of_endpoints`
forms and `exists_pair_of_fourArcMatch_*` in `LoopTheorem/BoundaryCandidatesOfCut.lean:146–254`):

```lean
theorem exists_of_fourArcMatch_reversing [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b} {τ φ : Path b a}
    (hlong : Function.Injective ⇑(τ.trans (σ.trans φ))) (hυ : Function.Injective ⇑υ)
    {α : Path (ρ b) (ρ a)} {ω : Path (ρ a) (ρ b)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑(τ.trans (σ.trans φ)))
    (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))
```

Our argument: `τ.trans (σ.trans φ)` is at `b` at parameter `0` and again at `3/4` (the junction
of `σ` and `φ`), and at `a` at `1/2` and `1`. So `hlong` is false for every choice of letters,
with or without `a = b`. In the preserving twin the hypothesis is
`Function.Injective ⇑(φ.symm.trans (σ.trans τ.symm))`, whose first letter is already a loop.
The proof goes through `Path.Homotopic.of_injective_of_range_eq` (two paths with the same end
points and the same range, one of them injective, are homotopic — true inside an arc), applied
to the three-letter concatenation as if its range were an arc.

**Q1.1** Confirm or refute. We also claim that it **cannot** be repaired by asking only that
`τ`, `σ`, `φ` be injective separately, for two reasons: (i) the range of `τσφ` is then a theta
graph (three arcs from `a` to `b`), and a path from `b` to `a` with that range is not determined
up to homotopy — `τσφ` and `φστ` have the same range and end points; (ii) in the preserving case
range equality does not even fix the direction of a loop letter. Is that right?

### 1.2 Claim: the letters need not be injective in `X` at all

The direct-candidate theorems on the branch assume `Function.Injective ⇑σ` and
`Function.Injective ⇑υ` for the letters **in `X`** (`BoundaryCandidatesOfCut.lean:91–138`,
`exists_of_twoArcMatch_of_endpoints`). This is satisfiable, but we claim it cannot be discharged
in general: `D` may have a second boundary branch whose two preimage chords both lie in `Δ₁`;
its four end points lie on `σ₀`, two of them with the same `D`-image, so `σ = f ∘ σ₀` is not
injective. Moise does not choose an innermost branch, so this configuration is not excluded.

**Q1.2** Confirm or refute; if Moise's argument does exclude it, where?

### 1.3 The repair we ordered, and the first attempt at it (also vacuous)

Repair: compare **in the source circle**, arc by arc. On each boundary arc of a candidate the
cell equals `D ∘ Fᵢ` with `Fᵢ` a PL homeomorphism of that arc onto one of `σ₀, τ₀, υ₀, φ₀`
(for the cross candidate the branch has `G = D ∘ Fᵢ` on three source pieces,
`LoopTheorem/CrossRegluedSource.lean`). So the recorded boundary path, read in `∂Δ`, is an
injective path with the range of `σ₀` (say) and the same end points — homotopic to `σ₀`, or
to `σ₀⁻¹` if the end points are exchanged, *inside the arc*, where injectivity is true. Push
the homotopy to `X` with `f`, concatenate, rotate. No injectivity in `X` is assumed. The long
arc of the cross candidate has to be cut at the two seam points into three sub-paths first.

The lane's first attempt (working file, quoted):

```lean
theorem exists_of_sourceCrossMatch_preserving
    {Q : Type w} [TopologicalSpace Q] [T2Space Q] (f : Q → X) (hf : Continuous f)
    {p q : Q} (φ₀ : Path p p) (σ₀ : Path p q) (τ₀ : Path q q) (υ₀ : Path q p)
    (hφ₀ : Function.Injective ⇑φ₀) (hσ₀ : Function.Injective ⇑σ₀)
    (hτ₀ : Function.Injective ⇑τ₀) (hυ₀ : Function.Injective ⇑υ₀)
    {φ₁ : Path p p} {σ₁ : Path p q} {τ₁ : Path q q} {υ₁ : Path q p}
    (hφ₁ : Set.range ⇑φ₁ = Set.range ⇑φ₀) … (hυ₁ : Set.range ⇑υ₁ = Set.range ⇑υ₀)
    {a b : X} {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a} …
    (hφ : ∀ t, φ t = f (φ₀ t)) … (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans (τ.trans (υ.trans φ)))))
```

Our claims: (i) `hφ₀`, `hτ₀` ask a loop (`γ 0 = γ 1`) to be injective — impossible; (ii) the
types are at the wrong level: by 1.0 the *source* arcs join four distinct points and never are
loops, the letters become loops only after `f`; (iii) the concluded word `σ τ υ φ` is the word
of `D`, not the preserving cross word `σ τ⁻¹ υ φ⁻¹`. The reversing twin
(`σ₀ : p → q`, `τ₀ : q → u`, `υ₀ : u → v`, `φ₀ : v → p`, all injective, recorded boundary
`(τ σ φ) υ`) we accepted.

**Q1.3** Is the source-side repair sound, and is there a cleaner formulation? We have in mind
one single-arc lemma in two directions — `P₀ : Path p q` injective in a Hausdorff `Q`,
`P₁ : Path p q` (resp. `Path q p`) with the same range ⇒ `f ∘ P₁ ≃ f ∘ P₀` (resp.
`≃ (f ∘ P₀)⁻¹`) — and the four words assembled from it by concatenation and cyclic rotation.
Is there a hidden difficulty in the global orientation of the boundary parametrisation `e`
(the gluing does not pin it; we carry the dichotomy `param = e ∨ param = e ∘ (θ ↦ −θ)`)?

---

## Part 2. The §34 assembly (35.2 side)

Background: you answered prompts A and A2 (`consult/A-answer-digest.md`,
`consult/A2-answer-digest.md`): a DAG P0–P8 of obligations each strictly smaller than 35.2,
then seven PL extension stages E1–E7 (plus the inserted 2b), the error estimate coming from the
carrier inclusions (C0), (C1). A lane then wrote `Section34Contracts → Moise352Open 3` (working
files, quoted). We rejected it for two independent reasons.

### 2.1 Claim: the stage contract is uninhabited

```lean
structure Section34StageContract (D : Section34Input) (η : M₁ → ℝ) (S : Section34SourceData D η) where
  initial : ∀ ε : ℕ → ℝ, (∀ i, 0 < ε i) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f (S.tower.coreSpace 0) ∧
      ∀ x ∈ S.tower.coreSpace 0, dist (f x) (D.h x) < ε 0
  extend : ∀ (ε : ℕ → ℝ), (∀ i, 0 < ε i) → ∀ i (g : M₁ → M₂),
    IsPLHomeomorphInto 3 g (S.tower.coreSpace i) →
    (∀ x ∈ S.tower.coreSpace i, dist (g x) (D.h x) < ε i) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f (S.tower.coreSpace (i + 1)) ∧
      EqOn f g (S.tower.coreSpace i) ∧
      ∀ x ∈ S.tower.coreSpace (i + 1), dist (f x) (D.h x) < ε (i + 1)
```

`coreSpace i ⊆ coreSpace (i+1)` are compact and exhaust the open source `U`; `D.h : U → M₂` is a
topological embedding. P8 concludes `Nonempty (Section34StageContract D η S)`, and the endpoint
feeds it to `LocallyFinitePieceTower.exists_isPLHomeomorphInto_dist_lt_of_stages`
(`LocallyFiniteApproximation.lean:394`, on the branch).

Our argument: let `f₀` come from `initial` with `ε ≡ 1`. If `h` is not PL on `coreSpace 0`
there is `x₀` there with `d₀ = dist (f₀ x₀) (h x₀) > 0`. Apply `extend` with `ε 0 = 1`,
`ε 1 = d₀`, `i = 0`, `g = f₀`: the produced `f` has `f x₀ = f₀ x₀` and
`dist (f x₀) (h x₀) < d₀`. Contradiction. So the contract is inhabited only if `h` is already
PL on the first stage. Independently, for large `ε` the clause says that *every* PL embedding of
a stage extends over the next — false (a knotted solid torus in a ball). The branch already
records the same two defects for `Moise352Stages` / `Moise352StageStep`
(`CONSULT_QUEUE_20260920.md:163–221`), and records that the repaired `η`-before-`g` clause
does not assemble because the tolerances are forced to increase along the tower.

**Q2.1** Confirm or refute.

### 2.2 Claim: the P0 source data is uninhabited for small `η`

```lean
structure Section34SourceData (D : Section34Input) (η : M₁ → ℝ) where
  tower : LocallyFinitePieceTower 3 M₁ D.U
  …
  carrier : ℕ → Set M₂
  carrierLocalFinite : LocallyFinite carrier
  carrierCovers : D.h '' D.U ⊆ ⋃ i, carrier i
  carrierCore : ∀ i, D.h '' tower.coreSpace i ⊆ carrier i
  carrierSmall : ∀ i x, x ∈ tower.coreSpace i → ∀ y, y ∈ carrier i → dist y (D.h x) < η x
  …
```

and P0 is `∀ η` continuous positive on `U`, `Nonempty (Section34SourceData D η)`. The carriers
are indexed by the **stage** `i`, and the stages increase. So for `x, x'` in one stage `k`,
`h x' ∈ carrier k` and `dist (h x') (h x) < η x`. With `η ≡ dist (h x) (h x') / 2` this is
false. Hence P0 fails as soon as some stage has two points. In your answer the carriers `H_α`
are indexed by the simplices `α` of a locally finite triangulation
(`h(|St α|) ⊂ Int H_α`, `diam H_α < η` on `|St α|`), which is a different and satisfiable thing.

**Q2.2** Confirm or refute.

### 2.3 What should the assembly be?

Our reading of your A2 answer: §34 is *not* a tower of approximating maps. P0–P8 produce a
locally finite family of **pieces** in the target with the source incidences; E1–E7 are seven
PL extensions each performed **once, over the whole locally finite family**; the result is a PL
embedding `f : U → M₂` (not required to equal the 35.1 map on `N`); and
`dist (f x) (h x) < φ x` follows from (C1) `h(C_v) ∪ V_v ⊂ H_v`, `h(Q_t) ∪ R_t ⊂ H_t` and the
smallness of the carriers alone. No sequence `ε`, no exhaustion, no agreement clause between
stages of a tower.

**Q2.3a** Is that reading right? If so, please state the assembly theorem
`P0 ∧ … ∧ P8 → Moise352Open 3` so that every `P_i` is inhabited in the intended situation, and
say for each `P_i` what its *output* is (pieces and incidence relations, never stage maps). In
particular give the control clause of P0 in a form we can write down: carriers indexed by what,
small relative to what (`sup`/`inf` of `η` over which set), locally finite in which space.

**Q2.3b** The final map is PL on each compact piece and the family is locally finite in `U`; the
target family is locally finite in `h(U)` but not in `M₂`. Is "PL homeomorphism of `U` onto an
open subset of `M₂`" immediate from injectivity + local finiteness + invariance of domain, or is
there a closedness/properness point we should isolate as its own lemma? (The tree has
`Moise352Open` at `OpenSourceReduction.lean:297` and a uniform ball-family extension lemma.)

**Q2.3c** Where, if anywhere, does a compact exhaustion legitimately enter — only in the
labelled normalization P5 ("visit every label infinitely often"), which is a finite-change
construction of pieces and not of maps?

---

## Part 3. How do we stop doing this?

All four vacuities passed the focused compile, thirteen environment linters and the axiom audit;
they were found only by reading the statement and evaluating a hypothesis at a junction point or
at an extreme tolerance. Our rules now: for each injectivity hypothesis evaluate at `0`, `1` and
every concatenation point; no injectivity on a `Path x x`; for each tolerance hypothesis try a
very large value, a very small value and two adjacent stages; for each hypothesis name the
*proved* producer that supplies it; every predicate ships with an inhabitant theorem.

**Q3.1** What would you add? Is there a cheap mechanical discipline (e.g. a companion
`example : ∃ …, hyps` per conditional theorem, or a `¬`-probe per bundled structure) that would
have caught these, short of proving the producers?

**Q3.2** Please audit the following statements on the branch for the same defect — hypotheses
that cannot hold simultaneously, or that pin an approximating object to the thing approximated,
or that index a smallness condition by an increasing family. For each, either name a concrete
inhabitant of the hypotheses or say which clause you doubt.

* `LoopTheorem/LemmaTwoBuffered.lean:167` `GeneralPositionInDoubleBufferedStatement`, `:60`
  `LemmaTwoBufferedStatement`; `LoopTheorem/LemmaTwoSpine.lean:124` `DescentStepStatement`.
* `LoopTheorem/NormalCell.lean:78` `NormalSingularCellData` (nothing inhabits it yet);
  `LoopTheorem/CutAndPaste.lean:1255` `IsBoundaryBranchCut`.
* `LoopTheorem/CrossRegluedCellPredicate.lean:95` `IsCrossRegluedCell`;
  `LoopTheorem/BoundarySurgeryCellPredicate.lean:96` `IsBoundarySurgeryCell` and the two
  boundary-case assemblies in that file (thirty-six hypotheses each).
* `LoopTheorem/CrossSeamTube.lean:541` `CrossSeamTubeData`, `:928` `IsCrossSeamTubeProducer`;
  `LoopTheorem/CrossSeamResolvedCell.lean:143` `PLSeamTubeChart`, `:189` `PLCrossSeamReading`
  (the last has a non-degenerate inhabitant in `LoopTheorem/CrossSeamReadingWitness.lean`; the
  tube does not).
* `OpenSourceReduction.lean:297` `Moise352Open`; `MoiseChain.lean:191` `Moise351`.

**Q3.3** If you find the *claims of this prompt* wrong anywhere, say so first and plainly — a
wrong refutation costs us as much as a wrong theorem.
