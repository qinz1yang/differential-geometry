# OPUS_FILL_LOG_C3B2 (leaf `CapWindowContinuation`: endpoint re-derivation and slab derivative)

## 2026-09-26 entry 1 (start, 05:40 PDT)

Read: AGENTS.md, logs C3B, L4E, L10, DESIGN_C3B.md, the leaf, `CapWindowContinuationAssembly.lean`,
`DerivativeBoundExtension.lean`, L6e. Plan: one new file
`Surgery/Topology/CapWindowContinuationLeaf.lean`:
1. `RetainedCoreHistory.exists_capWindowPoint_bounds` = the per-point theorem with the bridge at
   `t` itself (L6e, `μ = 0`), no room hypothesis, current bound `DerivativeBoundBefore … t`.
2. per-slab `CanonicalBoundsOn` from `DerivativeBoundBefore (2Ctime) (2qcan) (t₀ + η)`.
3. leaf for `t₀ > a` via L10 (`capWindowContinuation_of_slab_interior`), and the full leaf from an
   explicit slice hypothesis (`t₀ = a`, L10 `_of_slice`).
Compile method: scratch modules in `scratchpad/c3b2` (L6e, L10 have no oleans; L4e scratch olean
from `scratchpad/l4e`, source identical by `diff`).

## 2026-09-26 entry 2 (delivered, 06:05 PDT; failures first)

### NOT proved: the leaf at `t₀ = a` (slab start). One statement remains.

`CapWindowContinuation P₀ g₀` is proved conditionally on ONE explicit hypothesis, the slab-start
slice lemma. It is stated verbatim as the `hslice` binder of
`capWindowContinuation_of_slab_start_bounds`. Proposed name: `exists_slice_bounds_at_slab_start`.

```lean
theorem exists_slice_bounds_at_slab_start (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ Cs : ℝ≥0, ∀ Ctime : ℝ≥0, Cs ≤ Ctime →
      ∃ (Rs qs : ℝ) (ms : ℕ), 0 < qs ∧ ∀ qcan : ℝ, qs ≤ qcan →
      ∃ (δs ρs εs : ℝ), 0 < δs ∧ 0 < ρs ∧ 0 < εs ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εs → Rs ≤ p₀.modelRadius → ms ≤ p₀.modelOrder →
        δbound ≤ δs → ρbound ≤ ρs →
      ∀ H : RetainedCoreHistory P₀, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
        p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
        Gk.flow.base.metric (H.time k) = H.initialMetric k →
        H.EventSlabsDerivative Ctime qcan k →
        (∀ y : (H.stage k).Carrier, ContinuousWithinAt (fun z : ℝ × (H.stage k).Carrier =>
          derivWithin (fun v => Gk.flow.scalar v z.2) (Ici z.1) z.1)
            (Ici (H.time k) ×ˢ univ) (H.time k, y)) ∧
        ∀ y : (H.stage k).Carrier, qcan < Gk.flow.scalar (H.time k) y →
          |derivWithin (fun v => Gk.flow.scalar v y) (Ici (H.time k)) (H.time k)| ≤
            Ctime * Gk.flow.scalar (H.time k) y ^ 2
```

The two conjuncts are exactly `hreg` and `hstart` of L10's
`exists_derivativeBoundBefore_extend_of_slice` at `t₀ = a`, with `(C, q) = (Ctime, qcan)`.
Only the derivative slice is needed. The bridge consumes only `DerivativeBoundBefore`, and the
leaf's gradient clause comes pointwise from the per-point theorem, so the gradient `_of_slice`
is not used.

How each quantifier is consumed by the leaf:
- `Cs` sits before `Ctime`: the leaf takes `Ctime₀ ≥ Cs`.
- `Rs, qs, ms` sit after `Ctime` and before `qcan`: they go into `Rcap, q₀, mcap`.
- `δs, ρs, εs` sit after `qcan`: they go into `δmax, ρmax, εcap`.

Expected proof, per DESIGN_C3B L10b:
- regularity: from `Gk.smoothUpTo`, i.e. the right time-derivative of `R` is jointly continuous
  up to `a`.
- `k = 0`: the slice bound is vacuous once `qs > sup R(g₀)`. This uses `InitialIdentification`.
- retained region: the left limit of the previous slab's bound, from `EventSlabsDerivative`,
  together with smooth convergence to the terminal metric.
- fresh caps and collar: `∂ₜR = ΔR + 2|Ric|²` of the near-standard initial metric, and
  `R ≥ c·scale`. This gives `Cs` absolute, with `εs, Rs, ms` fixed by the cap accuracy.

### Proved (file `Surgery/Topology/CapWindowContinuationLeaf.lean`, 365 lines, new, unregistered)

1. `RetainedCoreHistory.exists_capWindowPoint_bounds`. This is the per-point theorem with
   `μ = 0`. It has the same quantifier order as `…_of_room`, with `μ` and the room hypothesis
   removed. The current-slab hypothesis is now `t < s` and
   `Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) t`. The bridge is called at `t` itself.
   L6e (`exists_uniform_orientedWitness_of_standard_close_endpoint`) is used at `(Θ, Dcap + 1)`.
   The window flow `S` lives on `closed 0 T`, and `T ≤ θcap ≤ Θ`. The ½-lower comparison is at
   `Θ`. The proof reuses the assembly's lemmas unchanged (`capWindow_flow_metric_eq` at
   `T ∈ Icc 0 T`, `orientedWitness_of_capWindow_flow` with `t ≤ t` by `le_rfl`, the jets lemma
   with `T ≤ T`). It is the old proof minus the margin bookkeeping. It elaborates within the
   default budget, with no warning.
2. `RetainedCoreHistory.exists_capWindow_canonicalBoundsOn`. This is the per-slab form, uniform
   in `k`: `Gk.DerivativeBoundBefore (2Ctime) (2qcan) (t₀ + η)` implies
   `Gk.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η (CapWindowPoint … k …)`.
3. `capWindowContinuation_of_slab_interior`. This is the leaf's exact statement with both
   `t₀ ∈ Ico …` replaced by `t₀ ∈ Ioo …` (event and terminal branch). Constants:
   `C1₀ = C2₀ = C₀`, `Ctime₀ = Cgrad₀ = max Ctime₀' 1`, `q₀ = 1`. `η` comes from L10's
   `exists_derivativeBoundBefore_extend` per slab. The initial metric is
   `(H.isContinuationSlab_event hH.2.2.1 j).2` in the event branch and `hG.2` in the terminal
   branch. The identification is `hH.1` and `Λδ ≤ ½` is `hH.2.2.2.2`.
4. `capWindowContinuation_of_slab_start_bounds (P₀ g₀) (hslice : <statement above>) :
   CapWindowContinuation P₀ g₀`. It covers both branches and all `t₀ ∈ Ico` through L10
   `_of_slice`. Constants: `Ctime₀ = Cgrad₀ = max (max Ctime₀' 1) Cs`, `Rcap = max Rcap' Rs`,
   `q₀ = max 1 qs`, `mcap = max`, and `δ/ρ/εcap = min`.
   Both 3 and 4 are corollaries of 2.

Compile (scratch module pattern, dir `scratchpad/c3b2`, `build.sh`, `mk.sh`). There are no oleans
for L6e and L10, so both were copied as `C3b2Scratch.L6e` (import `L4eScratch.Perturbation`, whose
source is identical to L4e by `diff`, reusing `scratchpad/l4e/out`) and `C3b2Scratch.L10`
(verbatim). Each was compiled with `-o` in about 40 s with no output. The leaf copy
`C3b2Scratch.Leaf` differs only in its two import lines (checked with `diff`, 4 changed lines). It
was compiled against the committed/ACC5 oleans (Assembly 05:25) with
`LEAN_NUM_THREADS=2`, `-DmaxSynthPendingDepth=3` and `-Dweak.linter.mathlibStandardSet=true`, in
55 s with **no output**. `#print axioms` for all four public theorems gives propext,
Classical.choice, Quot.sound. `#lint` (14 linters) found 0 errors in 5 declarations. Lines are
≤ 100 except imports. There are no comments, sorry or option overrides. All names are
grep-unique. No `lake build`, no git writes, nothing else edited.
