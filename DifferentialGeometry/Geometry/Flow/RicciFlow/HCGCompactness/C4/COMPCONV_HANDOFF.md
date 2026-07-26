# COMPOSITION-CONVERGENCE (Faà-di-Bruno) SESSION — kickoff prompt

**Paste everything below the line into the new session. Self-contained.**

---

Work in `E:\testdifferential-geometry` (Lean 4 / Mathlib, branch `short-time-existence`).
All Lake ops go through `scripts/lake-locked.ps1` (`claim` before editing, `check`/`build` to
verify, `release` after; never call `lake` directly; `status` before assuming a file is free —
other sessions are active). Read `CLAUDE.md` first. NEVER push (the human pushes). Record
findings in same-name `.md` notes. Report = the math conclusion + where you're stuck, in prose;
no theorem-list dumps; be honest about the % of the whole MSM135 Ch4 project (it is ~20%).

## The one lemma to build (the goal)

A **`C^∞` composition-convergence** lemma for the project's "C^∞-on-compacts" map-convergence
engine: composition is continuous in `MapCInfConvOnCompacts`. This is the single missing
analysis lemma that upgrades MSM135 Ch4 `lbl399` from `C⁰` to `C^∞` AND unblocks `lbl404`
(it is THE current frontier of the Theorem-3.9 B-track). It is pure real analysis — no
manifolds, no geometry.

**Reusable engine form** (prove this; put it in a NEW file `MapConvergenceComp.lean` in the
PARENT `…/HCGCompactness/` next to `MapConvergence.lean`, importing `MapConvergence` +
`Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno`):
```
-- E, F, G finite-dim real normed spaces
theorem mapCInf_comp {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (B : ℕ → E → F) (Binf : E → F) (A : ℕ → F → G) (Ainf : F → G)
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBsm : ContDiffOn ℝ ⊤ Binf U) (hAsm : ContDiffOn ℝ ⊤ Ainf V)
    (hmap : Set.MapsTo Binf U V)            -- limit lands in V
    (hmapk : ∀ K ⊆ U, IsCompact K → ∃ K' ⊆ V, IsCompact K' ∧ ∀ᶠ k in atTop, Set.MapsTo (B k) K K') :
    MapCInfConvOnCompacts U (fun k => A k ∘ B k) (Ainf ∘ Binf)
```
(Adjust the moving-domain hypothesis `hmapk` to whatever the proof actually needs — the point
is to corral the moving evaluation point `B k x` into a fixed compact `K' ⊆ V`, exactly as the
`C⁰` core already does; see below.)

**Two-parameter consumer** (then upgrade the existing `C⁰` lemma): in
`…/C4/StepBApproxIso.lean` there is `comp_tendsto_id_on` (the `C⁰` core). Produce its `C^∞`
analog `comp_cInf_id_on`: from `B_k → B_∞`, `A_ℓ → A_∞` (both `MapCInfConvOnCompacts`) and the
limit identity `A_∞ ∘ B_∞ = id`, conclude `A_ℓ ∘ B_k → id` in `MapCInfConvOnCompacts U` as
`k, ℓ → ∞` **independently** (the book's `lbl399`). The `k, ℓ` independence is handled exactly
as in `comp_tendsto_id_on` (thresholds `max NA NB`, both `≥ N`).

## Exact definitions (from `MapConvergence.lean`)

```
mapDerivNorm r Φk Φinf x        := ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖
MapCPConvOn K p Φ Φinf          := ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ r≤p, ∀ x∈K, mapDerivNorm r (Φ k) Φinf x ≤ ε
MapCInfConvOnCompacts U Φ Φinf  := ∀ compact K ⊆ U, ∀ p, MapCPConvOn K p Φ Φinf
```
So `C^∞`-on-compacts = for every compact `K ⊆ U` and every finite order `p`, all Euclidean
iterated derivatives up to `p` of `Φ k − Φ∞` are uniformly `≤ ε` on `K` for `k` large.

## What already exists (reuse, do not rebuild)

- `MapConvergence.lean` (parent): the engine above + order/subset/subseq API and the bridges
  `tendstoUniformlyOn_of_cPConv`, `tendsto_of_cInf`, `mapCPConvOn_of_tendstoUniformly`. Also
  `MapConvergenceDeriv.lean` (derivative-level helpers) — check it before adding derivative API.
- `StepBApproxIso.lean:comp_tendsto_id_on` — the `C⁰` core to extend. Its statement:
  `(hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf) … (hid : ∀ x∈U,
  Binf x∈V → Ainf (Binf x) = x) (K compact ⊆ U) (hKV : ∀ x∈K, Binf x∈V) : ∀ ε>0, ∃ N, ∀ k≥N,
  ∀ l≥N, ∀ x∈K, dist (A l (B k x)) x < ε`. Its proof shows the corral technique: `Binf '' K` is
  compact in `V`; `Metric.cthickening δ₀ (Binf '' K) ⊆ V`; `B k x` lands in that cthickening for
  `k` large (uniform `C⁰` convergence of `B`); then uniform continuity of `Ainf` + uniform
  convergence of `A` on that fixed compact. **Replicate this corral, then run Faà-di-Bruno at
  each order.**
- Mathlib `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` — the **static** iterated-derivative-
  of-composition formula (`iteratedFDeriv ℝ n (g ∘ f)` as a sum over ordered partitions of
  `(iteratedFDeriv ℝ · g) ∘ f` composed with the `iteratedFDeriv ℝ · f`). There is **no
  convergence version** — that is exactly what you are adding.

## Mathematical route

For fixed compact `K ⊆ U` and order `r`: by Faà-di-Bruno, `∇ʳ(A_k ∘ B_k) x` is a universal
finite polynomial `P_r` in the factors `(∇^{≤r}A_k)(B_k x)` and `(∇^{≤r}B_k)(x)`. Same for
`∇ʳ(A_∞ ∘ B_∞)`. So `∇ʳ(A_k∘B_k) − ∇ʳ(A_∞∘B_∞)` is `P_r` evaluated at the `k`-factors minus
`P_r` at the `∞`-factors. Each factor converges uniformly on the corralled compacts:
- `(∇^{≤r}B_k)(x) → (∇^{≤r}B_∞)(x)` uniformly on `K` (from `hB`, order `≤ r`);
- `(∇^{j}A_k)(B_k x) → (∇^{j}A_∞)(B_∞ x)` uniformly on `K`: split as
  `(∇^j A_k − ∇^j A_∞)(B_k x)` (uniform conv of `A` on the fixed compact `K' ⊇ {B_k x}`) plus
  `(∇^j A_∞)(B_k x) − (∇^j A_∞)(B_∞ x)` (uniform continuity of the continuous `∇^j A_∞` on `K'`,
  since `B_k x → B_∞ x` uniformly). `∇^j A_∞` continuous because `Ainf` is `C^∞` on the open `V`.
`P_r` is a fixed continuous (multilinear-product/sum) map, so it preserves the uniform
convergence on `K` (bound each monomial via `‖·‖` sub-multiplicativity + uniform bounds of the
factors on the compacts). This gives `mapDerivNorm r (A_k∘B_k) (A_∞∘B_∞) → 0` uniformly on `K`,
i.e. `MapCPConvOn K r`, for every `r` — i.e. `MapCInfConvOnCompacts`.

The bookkeeping (indexing Faà-di-Bruno's ordered partitions, the per-monomial bound) is the
real work; everything else is the corral already done at `C⁰`.

## Tasks

1. Verify feasibility against Mathlib's `FaaDiBruno` API (what exactly `iteratedFDeriv_comp`
   gives, the partition indexing). State whether the static formula is usable as-is.
2. Build `mapCInf_comp` in a new `…/HCGCompactness/MapConvergenceComp.lean` (PARENT dir —
   shared engine layer; claim it and coordinate, the Ch3 session may build the parent).
3. Upgrade `StepBApproxIso.comp_tendsto_id_on` to `comp_cInf_id_on` (`C^∞`, two-parameter →
   `id`), consuming `mapCInf_comp`. Update `StepBApproxIso.md`. This closes `lbl399` at `C^∞`.
4. Targeted-build green, `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
5. If a genuine wall appears (e.g. Mathlib's Faà-di-Bruno indexing is intractable to push
   convergence through), STOP and report the smallest missing sub-lemma — do NOT invent a
   broad convergence framework or add axioms.

## Constraints / off-limits

- State convergence `U`-relative on `MapCInfConvOnCompacts U` (the project's convergence-spine
  ruling); the maps live on bounded Euclidean balls, not `Set.univ`.
- Off-limits (other sessions own them): the Ch3 P-track (`RicBound*`, `MetricPreconv*`,
  `PointedConvergence`, `AllTimes*`) and the `C4/` Step-B geometry already done
  (`StepBInputs`/`StepBLocalMetrics`/`StepBTransition` are settled — only `StepBApproxIso` is
  yours to edit here). `MapConvergence.lean` is shared with Ch3 — add a NEW sibling file rather
  than editing it; `status`/`claim` carefully.
- This lemma is the B-track frontier; it does NOT need Step A, Hopf–Rinow, or the center-of-mass
  (Step C). It is self-contained pure analysis. After it lands, the next B-track step is the
  center-of-mass averaging (Step C / `lbl434`) that turns these `→ id` local maps into the
  averaged `lbl397` approximate isometry.
