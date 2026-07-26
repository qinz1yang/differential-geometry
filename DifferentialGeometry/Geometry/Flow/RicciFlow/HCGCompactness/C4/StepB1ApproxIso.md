# StepB1ApproxIso.lean — MSM135 Ch4 Step B1 (`lbl397`), assembly notes

## Current state — 2026-07-09: false endpoint removed, honest conditional assembly green

The former `stepB1_approxIso (P) r ε p` was mathematically false: properness of the members does
not produce the C-track comparison maps.  It has been removed.  The replacement API is:

- `StepB1RawInput P`: the eventual raw comparison maps, local diffeomorphism/injectivity,
  basepoint identity, and two-sided `PreApproxIsoDataOn`;
- `stepB1_of_raw P B`: the checked conditional assembly through `stepB1_glue`.

**Live update (2026-07-18).**  Downstream
`MetricCompactBase.exists_b1_raw` now has a complete proof body and closes all
five raw fields; its canonical framed dependency chain is currently being
revalidated, so it is source-complete but not yet framed-green.  The separately
named textbook Step B1 theorem remains unstated/unproved (0%), as do the
unconditional compactness endpoints.  The older accounting below is a
historical snapshot.

Focused verification passes, and this file now has no `sorry`.  Honest accounting remains:
conditional assembly 100%; producer of `StepB1RawInput` from the conditional compactness inputs
0%; textbook B1 theorem 0%.  Step D consumes this boundary explicitly through `directed_of_b1`.

## 2026-07-09 import-boundary audit

The raw-input/assembly layer no longer imports `StepCProducers` or `StepCSmoothness`.  Neither
module supplies a declaration consumed by the checked assembly.  Removing them exposed the one
real low-level dependency: `ProperMetricOn` and `ProperMetricOn.top_eq`, both declared in
`GoodCoveringOrdered`, which is now imported directly.  Focused verification passed with this
narrower boundary.  This is dependency hygiene only, so the progress accounting above is
unchanged.  The final unused `ApproxIsometryCompHigher` import was also removed and the file
again passed focused verification.

## Removed endpoint (historical shape; do not restore)

The former `stepB1_approxIso` claimed that for `r>0, ε∈(0,1), p`, ∃ `k₀` s.t. ∀ `k,ℓ≥k₀` the center-of-mass comparison
map `F_{kℓ;r}` (`lbl400`) is a ball-onto-image `PartialDiffeomorph` on `B(O_k,r)`, `Phi O_k = O_ℓ`,
and an `(ε,p)`-approximate isometry there (`BookApproxIsoPartialData`). Feeds Step D
`exists_directedApproxSystem` verbatim (STEPD_PLAN §0/D1).  This P-only endpoint was false and has
been deleted; the correct public boundary is `StepB1RawInput` plus `stepB1_of_raw`.

## Historical state — 2026-07-05 (superseded): glue proved, producer hidden in one `sorry`
Full `lake build` green (3915 jobs). `#print axioms`:
- `stepB1_glue = [propext, Classical.choice, Quot.sound]` (sorry-free)
- `PreApproxIsoDataOn.congr = [propext, Classical.choice, Quot.sound]` (sorry-free)
- `stepB1_approxIso` — ONE `sorry` = the C-track producer bundle (see below).

### What is PROVED (`stepB1_glue`, the book-faithful assembly)
Given the raw ball-onto-image map `F` on an open `U ⊇ closedBall(O_k,r)` with
- `hloc : IsLocalDiffeomorphOn I I ∞ F U` (`lbl403` nonsingularity),
- `hinj : InjOn F U` (`lbl403` injectivity),
- `hbase : F O_k = O_ℓ` (`lbl400` χ-cutoff basepoint),
- forward `PreApproxIsoDataOn (closedBall) ε p F g h` and reverse
  `PreApproxIsoDataOn (F''closedBall) ε p (invFunOn F U) h g` (`lbl402` + bounds),
it PRODUCES `∃ Phi, closedBall ⊆ Phi.source ∧ Phi O_k = O_ℓ ∧ Nonempty BookApproxIsoPartialData`:
1. `exists_diffeo_of_injOn hloc hU hinj` (Comparison/ExpBallDiffeo, REUSED) realizes `F` as a
   `PartialDiffeomorph Φ` with `source = U`, `target = F''U`, `EqOn Φ F U`.
2. `source_sub` = `hsrc ▸ hKU`; basepoint `= (hEq hOkU).trans hbase`.
3. `BookApproxIsoPartialData` forward/reverse via `PreApproxIsoDataOn.congr` (the transport lemma):
   forward `hfwd.congr hev_fwd` where `hev_fwd x = eventuallyEq_of_mem (hU.mem_nhds (hKU x)) hEq`;
   reverse needs `Φ.symm =ᶠ invFunOn F U` on `Φ.target` (proved from `Φ.toPartialEquiv.left_inv` +
   `hinj.leftInvOn_invFunOn`) and `Φ''cb = F''cb` (`Set.EqOn.image_eq`), rewriting the set with `rw`.

### `PreApproxIsoDataOn.congr` (reusable, also for Step-D composition)
`PreApproxIsoDataOn K ε p F g h` + `(∀ x∈K, F' =ᶠ[𝓝 x] F)` → `PreApproxIsoDataOn K ε p F' g h`.
Same tensor field; `smoothOn` via `ContMDiffOn.congr (·.self_of_nhds)`; `pullback_apply` via
`rw [self_of_nhds, EventuallyEq.mfderiv_eq]`. Must be a `noncomputable def` (structure is `Type`,
not `Prop` — a `theorem` errors "not a proposition").

## Historical `sorry` goal — now the explicit `StepB1RawInput` producer frontier
```
∃ k₀, ∀ k ℓ ≥ k₀, ∃ R (r<R) F,
  IsLocalDiffeomorphOn I I ∞ F (ball O_k R) ∧ InjOn F (ball O_k R) ∧ F O_k = O_ℓ ∧
  Nonempty (PreApproxIsoDataOn (closedBall O_k r) ε p F g_k g_ℓ) ∧
  Nonempty (PreApproxIsoDataOn (F''closedBall O_k r) ε p (invFunOn F (ball O_k R)) g_ℓ g_k)
```
This is the actual `lbl400/402/403` content: `stepCJoin` (`lbl400`, C3, green but takes ~2 dozen
honest inputs itself: NetLimitData, PackingBound, ExpInverseDerivBoundInput, POU, overlaps, …)
gives the averaged map; `lbl403` (Neumann invertibility of `dF≈id` + `C⁰`-closeness injectivity)
makes it a ball-onto-image local diffeo; `lbl402` + `comp_cov_le`/`comp_cov_accum` (F5/F6) + the
**quantitative `|∇^{p+1}cm| ≤ C̃` bounds** give the forward/reverse approx-iso data.  The arbitrary-
order bound is still not stated.  This producer content is now exposed by `StepB1RawInput`; it is no
longer hidden behind a `sorry` or a false P-only theorem in this file.

## Lessons / gotchas (cost time)
- **Topology diamond (REAL, not just generic):** `ProperMetricOn.top_eq` (metric topology = manifold
  topology) is only PROPOSITIONAL, not defeq. So `Metric.isOpen_ball` gives openness in the metric
  topology, but `exists_diffeo_of_injOn`/charts need the manifold topology. FIX: make `stepB1_glue`
  take the open set `U` abstractly with `hU : IsOpen U`; the caller supplies `hU` for `ball O_k R`
  via `rwa [ProperMetricOn.top_eq (X.obj k) (P k)] at (Metric.isOpen_ball …)`. `top_eq ▸ isOpen_ball`
  FAILS — `▸` can't target the implicit `TopologicalSpace` instance arg; use `have hb := isOpen_ball;
  rwa [top_eq] at hb`.
- `PreApproxIsoDataOn` is `Type`-valued ⇒ cannot chain with `∧` in the producer bundle
  ("has type Type … expected Prop"). Wrap each in `Nonempty (…)`, then `obtain … ⟨hfwd⟩ ⟨hrev⟩`.
- `Function.invFunOn F s` needs `[Nonempty (source)]` — add `haveI : Nonempty (X.obj k).M` in BOTH
  the bundle's `letI` block (for the type to elaborate) and the proof body.
- `Set.image_subset` was renamed → use `Set.image_mono (h : s⊆t) : f''s ⊆ f''t`.
- `(Φ.symm : N→M) (Φ x) = x`: `Φ.toPartialEquiv.left_inv hx` (defeq through the coercions; no
  dedicated `PartialDiffeomorph.left_inv`).

## UPDATE 2026-07-07 — the 2026-07-06 blockage below is LARGELY DISSOLVED; see `StepB1Producers.md`
The goal-rounds of 2026-07-07 closed (b) `lbl403` completely (manifold forward IFT incl. `n = ∞`,
`Geometry/Coordinates/LocalDiffeoIFT.lean` + the `hlocOn_of_chartNeumann_infty` /
`hlocHinj_of_chartNeumann` producers), built the `lbl404` ABSTRACT layer 100% (`averagedCInf_id` —
the convergence route needs no Faà-di-Bruno difference bounds; the "MISSING brick" doc line was
stale, `MapCInfConvOnCompacts.comp` is delivered), the diagonal-identity chain
(`centerOfMass_diag`/`chartCm_diag`/`diagEventuallyEqId`), and the (d)-basepoint cm-core
(`centerOfMass_delta`).  Remaining producer-bundle work = INSTANTIATION inputs only (POU weights,
per-slot target convergence, `Φ_cm` `ContDiffOn ∞` + `CenterInput` family) — `StepB1Producers.md`
has the current frontier map.  The section below is kept as history.

## Producer-bundle attack (2026-07-06) — task is BLOCKED BELOW FALLBACK; premise "engines ready" is false
Attempted to dismantle the `stepB1_approxIso` producer-bundle `sorry` per the (a)–(d) decomposition.
Survey finding: NONE of (a)–(d) is a ready-to-connect engine.  Details + the exact frontiers live in
the new `StepB1Producers.lean` docstring.  Summary:
- **(b) `hloc`**: Mathlib has NO forward `invertible mfderiv ⟹ IsLocalDiffeomorphAt` (only the reverse
  `mfderivToContinuousLinearEquiv`; `expMap_isLocalDiffeomorphAt_zero` builds a bespoke
  `PartialDiffeomorph`).  MINIMAL BRIDGE = chart-level `ContDiffAt` + invertible `fderiv` ⟹ manifold
  `IsLocalDiffeomorphOn` (via `ContDiffAt.toPartialHomeomorph` + chart transfer). ~100–150 lines, real.
- **(b) `hinj`**: REDUCIBLE and DONE — `StepB1Producers.injOn_of_dist_le` +`stepB1_hlocHinj` (green,
  sorry-free): `InjOn` from the `C¹`-closeness displacement bound `dist x y ≤ K·dist (F x) (F y)`.
- **(a)** averaged `C^p→id`: genuine multi-lemma analysis (Faà-di-Bruno of the threaded
  `cmChartDerivLe`-shaped bound × the summand `comp_cInf_id_on` smallness); NOT transcription.
- **(c)** blocked on (a).  **(d)** basepoint: MISSING POU producer (`φ_k^α(O_k)=δ_{α0}`,
  `F^0_{kℓ}(O_k)=O_ℓ` not in `StepCAveragePOU`, which is off-limits to edit).
- **Fixed-signature obstruction (resolved by deleting the false endpoint):**
  `stepB1_approxIso (P) r ε p` could not supply `stepCJoin`'s ~2 dozen honest inputs from `X + P`.
  The current API threads the honest raw bundle explicitly instead.
- DELIVERED: `StepB1Producers.lean` (2 green lemmas + the precise producer interface/frontier map).
  At this historical snapshot the old endpoint still contained one `sorry`; it has since been deleted.
- Verification: `StepB1Producers.lean` passed the focused `lake env lean` check (43.5s, sorry-free);
  a concurrent session then broke+evicted the shared upstream `PointedConvergence.olean`
  (its `:1847` errors), blocking a fresh full build — external, not this file.

## Where B1 sits in the whole project (honest, 2026-07-09)

The conditional B1 assembly (`stepB1_glue` / `stepB1_of_raw`) is **100% checked**.  The producer of
`StepB1RawInput` and the textbook B1 theorem are each **0%**.  The whole HCG project is conservatively
about **45% machinery**, while its endpoint theorems remain **0%**; none of those percentages may be
inferred from this file's local no-`sorry` status.
