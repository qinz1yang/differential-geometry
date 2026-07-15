# Plan: Classical (sequential) Arzelà–Ascoli wrapper — Lemma 3.14

**Audience:** implementer (codex) taking this over.
**Status:** not started. No such lemma exists in the project; Mathlib has the
pieces but not this exact packaging.

---

## 0. Goal (the statement we want)

> **Lemma 3.14.** Let `X` be a σ-compact, locally compact Hausdorff space.
> If `{fₖ}ₖ∈ℕ` is an equicontinuous, pointwise-bounded sequence of continuous
> functions `fₖ : X → ℝ`, then there is a subsequence converging uniformly on
> compact sets to a continuous `f∞ : X → ℝ`.

Target Lean signature (names indicative; tune to project conventions):

```lean
theorem arzelaAscoli_subseq_tendstoUniformlyOnCompacts
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X]
    (f : ℕ → C(X, ℝ))
    (hequi : Equicontinuous (fun k => (f k : X → ℝ)))
    (hbdd  : ∀ x : X, BddAbove (Set.range fun k => |f k x|)) :
    ∃ (φ : ℕ → ℕ) (g : C(X, ℝ)),
      StrictMono φ ∧
      ∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun n => f (φ n)) g atTop K := by
  sorry
```

Notes on the statement:
- We phrase inputs/outputs with bundled `C(X, ℝ)` so that the compact-open
  topology and metrizability instances fire automatically. If the HCG callers
  hold raw `X → ℝ` with continuity proofs, add a thin adapter that bundles them.
- `hbdd` is "pointwise bounded". Equivalent forms (`BddAbove (range fun k => f k x)`
  + `BddBelow …`, or `∃ C, ∀ k, |f k x| ≤ C x`) are all fine; pick whatever the
  caller produces and convert.
- Output uses `TendstoUniformlyOn … K` for each compact `K`. The bundled-limit
  form (`Tendsto (f ∘ φ) atTop (𝓝 g)` in `C(X,ℝ)`) is *equivalent* and may be
  easier to produce first, then unfold (see Step 4).

---

## 1. Why this is not already available

- **Project / DGreference:** the string "Arzela-Ascoli" appears only in comments
  in `RicciFlower/HCGCompactness/{SolutionCompactness,HamiltonCompactness,
  MetricCompactness}.lean`. There is no theorem.
- **Mathlib `Topology/UniformSpace/Ascoli.lean`:** general theorem, stated as
  *set compactness* in uniform/inducing language — not sequential.
- **Mathlib `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`:** the classical
  metric form (`arzela_ascoli`, `arzela_ascoli₂`) but for **bounded** continuous
  functions `α →ᵇ β`, and again as `IsCompact (closure A)`, not subsequence
  extraction. Our `fₖ` are not globally bounded, so this is the wrong door.

The missing content is purely the **set-compactness → sequential-subsequence**
wrapper, which is free once we know the function space is **metrizable**.

---

## 2. The three load-bearing Mathlib facts

1. **Metrizability of the function space.**
   `Mathlib/Topology/Metrizable/ContinuousMap.lean`:
   ```
   instance [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
       [MetrizableSpace Y] : MetrizableSpace C(X, Y)
   ```
   With `Y = ℝ` (a `MetrizableSpace`), and `X` σ-compact + (weakly) locally
   compact, `C(X, ℝ)` is metrizable ⟹ `FirstCountableTopology` ⟹ sequential
   compactness is usable. (`LocallyCompactSpace → WeaklyLocallyCompactSpace`.)

2. **Compact-open = uniform-on-compacts.**
   `Mathlib/Topology/UniformSpace/CompactConvergence.lean`: convergence in the
   compact-open topology on `C(X, ℝ)` is exactly uniform convergence on each
   compact set. Key lemma to finish Step 4:
   `ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn` (verify exact
   name; alternatives: `ContinuousMap.tendstoLocallyUniformly_iff` /
   `tendsto_iff_tendstoUniformlyOn`).

3. **Arzelà–Ascoli (set compactness form) + sequential extraction.**
   - `ArzelaAscoli.isCompact_of_equicontinuous`
     (`Topology/UniformSpace/Ascoli.lean`):
     ```
     (S : Set C(X, α)) (hS1 : IsCompact (ContinuousMap.toFun '' S))
       (hS2 : Equicontinuous ((↑) : S → X → α)) : IsCompact S
     ```
     gives `IsCompact S` in the **compact-open** topology.
   - `IsCompact.tendsto_subseq` (`Topology/Sequences.lean`):
     ```
     (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
       ∃ a ∈ s, ∃ φ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
     ```
     needs `FirstCountableTopology` on the ambient space — supplied by Fact 1.

---

## 3. Proof outline (step by step)

Let `S₀ : Set C(X, ℝ) := Set.range f` (the sequence as a set).

### Step A — Equicontinuity of the set `S₀`
From `hequi : Equicontinuous (fun k => (f k : X → ℝ))` derive
`Equicontinuous ((↑) : S₀ → X → ℝ)`.
- `Equicontinuous` of the family indexed by `ℕ` transfers to the subtype
  `S₀ = range f` because every element of `S₀` is some `f k`.
- Look for `Equicontinuous.comp` / restriction lemmas, or prove directly:
  the subtype map factors through `f` up to choice of preimage index.
- If friction arises, instead take `S := closure S₀` and use
  `Equicontinuous.closure'` (as `arzela_ascoli` does, line ~119 of
  `Bounded/ArzelaAscoli.lean`) to keep equicontinuity under closure.

### Step B — Pointwise compactness `IsCompact (toFun '' S)`
This is the main assembly task. `toFun '' S ⊆ (X → ℝ)` with the **product
(pointwise) topology**. We need it compact.
- Pointwise bounded (`hbdd`) ⟹ for each `x`, the orbit `{f k x}` lies in a
  compact interval `Icc (-Mₓ) Mₓ`.
- The pointwise closure of `toFun '' S₀` sits inside `Set.pi univ (fun x => Icc …)`,
  which is compact by **Tychonoff** (`isCompact_univ_pi` + `isCompact_Icc`).
- Take `S := closure S₀` in the compact-open topology. Then:
  - `toFun '' S` is closed in the product topology (continuity of `toFun`,
    plus `S` closed), and
  - contained in the compact box ⟹ compact (`IsCompact.of_isClosed_subset`).
- **Caveat to resolve:** `ArzelaAscoli.isCompact_of_equicontinuous` wants
  `IsCompact (toFun '' S)` for the *same* `S` we conclude `IsCompact S` about.
  Using `S = closure S₀` is the clean choice: equicontinuity survives (Step A
  fallback), pointwise image is closed, box-bounded ⟹ compact. Double-check the
  interaction `toFun '' (closure S₀)` vs `closure (toFun '' S₀)` — they need not
  be equal, but we only need `toFun '' (closure S₀)` ⊆ box ∧ closed, both of
  which hold directly.

### Step C — `IsCompact S` and membership
- Apply `ArzelaAscoli.isCompact_of_equicontinuous S (Step B) (Step A)` ⟹
  `IsCompact S` in compact-open topology.
- `f k ∈ S` for all `k` (since `S₀ ⊆ S = closure S₀`).

### Step D — Extract subsequence
- `C(X, ℝ)` is `FirstCountableTopology` (Fact 1).
- `IsCompact.tendsto_subseq (IsCompact S) (fun k => f k ∈ S)` ⟹
  `∃ g ∈ S, ∃ φ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 g)` in `C(X, ℝ)`.
- `g : C(X, ℝ)` is automatically continuous (it's a bundled map) — this is the
  `f∞` continuity conclusion, for free.

### Step E — Translate `𝓝 g` convergence to uniform-on-compacts
- Convert `Tendsto (f ∘ φ) atTop (𝓝 g)` in compact-open topology to
  `∀ K compact, TendstoUniformlyOn (f ∘ φ) g atTop K` via Fact 2
  (`tendsto_iff_forall_compact_tendstoUniformlyOn` or its sibling).
- Package the existentials to match the target signature.

---

## 4. Deliverables / file placement

- **New file:** `RicciFlower/HCGCompactness/ArzelaAscoli.lean`.
  - Imports: `Mathlib.Topology.UniformSpace.Ascoli`,
    `Mathlib.Topology.Metrizable.ContinuousMap`,
    `Mathlib.Topology.UniformSpace.CompactConvergence`,
    `Mathlib.Topology.Sequences`.
  - Namespace: `RicciFlower.HCGCompactness`.
  - Export the theorem in both forms if useful:
    1. bundled-limit form (`Tendsto (f∘φ) atTop (𝓝 g)`), and
    2. uniform-on-compacts form (the Lemma 3.14 statement).
- **Wire into callers:** update the comment sites in
  `SolutionCompactness.lean` / `HamiltonCompactness.lean` /
  `MetricCompactness.lean` to consume this lemma where they currently say
  "by Arzelà–Ascoli". (Do not change their math content in this task — just
  make the dependency real where it's a 1-line plug; otherwise leave a precise
  TODO referencing this theorem.)

---

## 5. Risks / things to verify while implementing

1. **Exact Mathlib lemma names drift.** Confirm:
   - `ArzelaAscoli.isCompact_of_equicontinuous` signature (verified present,
     `Ascoli.lean:496`).
   - the compact-convergence translation lemma name (Step E) — grep
     `CompactConvergence.lean` for `tendsto_iff` / `tendstoUniformlyOn`.
   - `IsCompact.tendsto_subseq` (verified, `Sequences.lean:268`).
2. **`WeaklyLocallyCompactSpace` instance.** `LocallyCompactSpace X` should give
   it; if the instance isn't found automatically, add
   `haveI : WeaklyLocallyCompactSpace X := inferInstance` or the explicit
   downgrade lemma.
3. **Equicontinuity-on-subtype transfer (Step A).** The
   family→subtype/closure conversion is the most fiddly part. The
   `arzela_ascoli` proof in `Bounded/ArzelaAscoli.lean` (uses
   `Equicontinuous.closure'`) is the reference pattern.
4. **Pointwise-compact box (Step B).** Make sure to use `closure S₀` so the
   image is closed; verify `toFun` continuity into the product topology
   (`continuous_apply` / `ContinuousMap.continuous_coe`).
5. **Pointwise-bounded hypothesis shape.** Caller may give two-sided bounds or a
   single `|·|` bound; provide a small normalizing lemma so the public statement
   matches what HCG actually produces.
6. **Universe / `T2Space`.** `IsCompact.tendsto_subseq` and the Ascoli image
   compactness are fine for ℝ-valued; `T2Space X` is only needed where stated.
   Keep `[T2Space X]` in the signature to match Lemma 3.14 even if not strictly
   used everywhere.

---

## 6. Suggested order of work

1. Stand up the file + signature with `sorry`; get it to compile against imports
   (`./scripts/lake-locked build +RicciFlower.HCGCompactness.ArzelaAscoli`).
2. Step D+E first against a *hypothesised* `IsCompact S` (admit B,C) to lock the
   output-side plumbing and the compact-convergence lemma name.
3. Then Step B (the box/Tychonoff compactness) — the real analytic content.
4. Then Step A (equicontinuity transfer), close `IsCompact S` via Ascoli.
5. Remove `sorry`, full targeted build, then wire one caller as a smoke test.

Verification command (per project policy, do **not** call `lake build` directly):
```
./scripts/lake-locked build +RicciFlower.HCGCompactness.ArzelaAscoli
```
