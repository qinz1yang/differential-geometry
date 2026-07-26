# FlowLimitUpgrade.lean — P4 assembly skeleton (MSM135 Thm 3.10 upgrade)

Historical plan pointer (superseded):
`C:\Users\liao9\.claude\plans\fluffy-coalescing-leaf.md`.  Current producer
state is tracked in the repo by `P4_CONV_PLAN.md` and `ConvFieldEndgame.md`.

## 2026-07-24: retain squared Ricci-norm convergence

`FlowLimitData` now records `ricciNorm : RicNormPullback maps` next to the
existing scalar-curvature convergence field, and `flowLimit_upgrade` passes it
through the canonical `SmoothCGHConverges.ofRestrictPullback` constructor.
This record is only the data-retention boundary: the concrete ConvOut/endgame
producer must prove the field rather than receive an endpoint wrapper or a
synonymous assumption.

The data-plumbing subtask is 100% checked.  Unconditional Theorem 3.10 remains
0%; its dedicated P4 consumer machinery and the whole-HCG machinery estimates
remain those recorded in `PROJECT_MAP.md`.

Verification: focused verification and the exact exported-module refresh
passed.

## 2026-07-09: concrete upgrade boundary

`FlowUpgradeData X mc` is now the canonical producer package above
`FlowLimitData`. It exposes the further strictly monotone subsequence and the
actual limit-flow data over `mc.compSubseq`; `FlowUpgradeData.toConclusion` is
the only assembly step. This package cannot be populated by supplying the
desired `CompactnessConclusion`.

`FlowLimitData` now also records `hL0 : L.atTime 0 = mc.limit`. This is the
pointed-limit invariant that makes the package an upgrade of the specific
Theorem 3.9 conclusion `mc`, rather than unrelated smooth-limit data sharing
only its subsequence. The endgame producer supplies it from its two comparison
equalities; removing that equality input would weaken the canonical API.

Focused verification passed for this module and the downstream
`ConvFieldEndgame` and `SolutionCompactness` consumers; the exported-module
refresh also passed.

The module no longer imports `SolutionCompactness`, so the low-level P4
assembly is independent of the theorem-facing API.  The former exact-conclusion
adapter was removed; `solutionComp_of_mc` and the conditional wrappers consume
`FlowUpgradeData` directly.

Focused verification and the targeted module refresh passed. Refactor item 5
at this boundary: 100%. The conditional Theorem 3.10 consumer assembly from an
honest Theorem 3.9 conclusion and concrete upgrade data is 100% checked. Unconditional
Theorem 3.10: 0%; this refactor does not prove Theorem 3.9 or discharge the
remaining P4 producer hypotheses. The project-wide endpoint remains 0%; the
current project map's separate Chapter 4 machinery estimate remains about 59%,
while whole-HCG machinery remains about 45%.

> **Superseded as current instructions (2026-07-09).**  Everything below this
> notice is retained as an implementation log.  In particular, the old
> “Remaining”, “RESUME HERE”, and 3.10⇐3.9 wiring instructions must not be used
> as the live handoff; use the canonical `FlowUpgradeData` boundary above plus
> `P4_CONV_PLAN.md` / `ConvFieldEndgame.md`.

## Historical: landed + verified (2026-06-17, axiom-clean, build green 3789 jobs)

- `FlowLimitData X mc` — bundles the P4 frontier ingredients given the time-zero
  conclusion `mc : MetricCompactnessConclusion (X.atZero)`: `L` (Brick A, limit
  flow), `hL0` (its time-zero pointed-limit identification), `maps` (Brick B),
  `scalar` (Brick E), `hσsrc`/`hσtgt`/`refMetric`
  (Brick C inputs), `conv` (Brick D, the window norm-bridge output).
- `flowLimit_upgrade` — PROVES the upgrade arrow: assembles `FlowLimitData`
  through the already-built `SmoothCGHConverges.ofRestrictPullback` →
  `CompactnessConclusion X`. **Brick F's core (correctly feeding the keystone
  constructor) is DONE.**
- Historical adapter `smoothFlowLimitInput_of_flowLimitData` — removed on
  2026-07-09 with the exact-conclusion compatibility API.

So the P4 assembly is verified; the previously-opaque `upgrade` is now a proved
theorem modulo the explicit honest frontier fields.

## The `FlowLimitData` builder (2026-06-21, axiom-clean, build green 3789 jobs)

`cghMaps_of_hL0 X mc L hL0 : PointedCGHMaps X L mc.subseq` — the **Brick-A →
Brick-B handoff** and the last missing producer of the `maps` field. Given the
limit flow `L` with `hL0 : L.atTime 0 = mc.limit` (Brick A's output contract),
the time-zero comparison maps `mc.maps` transport along `hL0.symm` to
`PointedRiemannianCGMaps (X.atZero) (L.atTime 0) mc.subseq`, which
`pointedCGHMaps_of_atZero` (Brick B) carries to the spacetime maps. The `▸`
transport is over the `L`-index of `PointedRiemannianCGMaps`; it introduces **no
axiom** (`#print axioms cghMaps_of_hL0 = [propext, Classical.choice,
Quot.sound]`, no `sorryAx`).

**Design decision (item #3 of the work list).** No verbose re-typed
`flowLimitData_of_…` wrapper was added. With `cghMaps_of_hL0` in hand,
`FlowLimitData`'s **own anonymous constructor IS the builder** — the structure-
instance syntax infers the frontier field types from the supplied `maps`:

```lean
flowLimit_upgrade X mc
  { L := L
    hL0 := hL0
    maps := cghMaps_of_hL0 X mc L hL0   -- Brick A+B, the only non-frontier field
    scalar := …      -- Brick E (honest frontier input)
    hσsrc := …; hσtgt := …; refMetric := …   -- Brick C inputs
    conv := … }      -- Brick D (honest frontier input, consumes hShi)
  : CompactnessConclusion X
```

A positional 5-argument builder would only restate the verbose field types and
duplicate `cghMaps_of_hL0 X mc L hL0` five times (CLAUDE.md: shortest correct
implementation, no redundant adapters). The honest frontier fields stay as
`FlowLimitData` fields (item #4), so the structure itself is the intended input
interface; `cghMaps_of_hL0` is the producer that makes it constructible.

## Historical field-discharge checklist (superseded as a current task)

- **Brick A** (`L`): the limit Ricci flow on `mc.limit.M` with metric `gInf`
  (Lemma 3.11 output) + `IsSolutionOn` (limit-is-a-solution — HARD). Build `L`
  so that `L.atTime 0 = mc.limit` (then Brick B's `rmaps := hL0 ▸ mc.maps`).
- **Brick B** (`maps`): ✅ DONE — `pointedCGHMaps_of_atZero` (2026-06-21, build
  green). **The feared manifold-type-identification wall does NOT exist**:
  `PointedFlowData.atTime` preserves `M`/topology/charted/basepoint
  *definitionally* (Basic.lean:72, only `metric` changes), so the time-0
  `PointedRiemannianCGMaps` over `L.atTime 0` transport field-for-field to
  `PointedCGHMaps X L subseq` by defeq — a 4-field copy, no casts. Consume it
  with `rmaps := hL0 ▸ mc.maps` where `hL0 : L.atTime 0 = mc.limit` (Brick A).
- **Brick C** (`hσsrc`/`hσtgt`/`refMetric`): σ-compactness of the open
  source/target + a reference metric. Mechanical.
- **Brick D** (`conv`): apply `winGInfOfSol` to the pulled-back flows `Φ_k* g_k`,
  bridge the source-domain `derivNormSupOn` to Lemma 3.11's `metricDerivNormSupOn`
  on `M_∞`. The keystone bridge; consumes `hShi` (honest input).
- **Brick E** (`scalar`): `ScalarPullbackTendsto` from `C^∞` metric convergence.

## Historical resume point (superseded 2026-07-09 — do not resume here)

The transport layer is COMPLETE (all sorry-free, build-verified): P1.1 `convexComb`
(`Geometry/Metric/ConvexCombination.lean`), P1.2 `bumpExtendOpen` (`Geometry/Metric/
BumpExtend.lean`, repaired 2026-06-29 — see note below), P1.3 `MovingShiPullback.lean`,
P1.4 `SolutionPullback.lean` (`solutionOn_pullback`/`isSolutionOn_pullback`, all 9 fields)
+ `WindowDataPullback.lean` (green 3899): all 5 `Sol*Data` sub-records + capstone
`solWindowData_pullback` + endpoint `winGInfOfPullback` — the pullback layer works along a
GLOBAL `Φ : M ≃ₘ N`, which fits `sourceTargetDiff : SourceDomain ≃ₘ TargetDomain`.
Restriction-invariance (`MetricDerivNormRestrict.lean`) also done.

Remaining = the assembly phase: **`P4_CONV_PLAN.md`** (this folder), Bricks 1–7:
(1) `solutionOn_restrictOpen`/`isSolutionOn_restrictOpen` — the ONE missing transport link
(curvature ingredients banked: `Curvature/OpenSubtypeNaturality`, `RestrictOpenRm04`,
`PullbackNaturalityLocal/Cross`); (2) per-k pulled-back flow on `SourceDomain` (thin
composition); (3) `windowGInfAll` — one subsequence + one global gInf, all compacts
(diagonal; independent, parallelizable); (4) bump-extended sequence + raw `windowGInf`
hypotheses (bulkiest); (5) conv field + `gInf 0 = mc.limit.metric` + mc re-index along φ;
(6) the `L` term + PDE `∂ₜg∞ = −2Ric(g∞)` (second frontier) + scalar + σ-compact;
(7) endgame wiring through `flowLimit_upgrade` (done).

P1.2 repair lesson (2026-06-29): a grep "0 sorry" on an untracked file from a dead pid is NOT
a green signal — always `lake build` before trusting it (error-recovery sorries are invisible
to grep). Fixes were: `open scoped Classical` for the `dite (x∈U)`; removed a wrong
`omit [FiniteDimensional ℝ E]`; closed a rw-motive-cast `X=X` via
`DFunLike.congr_fun (DFunLike.congr_fun (dif_pos hx) v) w`.

## Historical 3.10 ⇐ 3.9 wiring plan (superseded as the current route)

The upgrade IS the book's "compactness for solutions from compactness for metrics"
(§lbl352). **BBS/Shi is a CITED input, not a proof obligation** — see
[[bbs-off-critical-path-310-from-39]]. Theorem 3.9 (lbl334) ASSUMES `|∇ᵖRm|≤Cₚ ∀p`;
the `|Rm|≤C₀ ⟹ |∇ᵖRm|≤Cₚ` bridge is cited (Shi, Thm lbl1118/1120). So `hShi`
(`MovingShiBoundOn`) and Theorem 3.9 (`metricCompactness`) enter as honest CITED inputs.

Book steps and their Lean status:
1. Theorem 3.9 at t=0 → maps Φ_k with Φ_k^*g_k(0)→g_∞ : **input** (`mc`).
2. Apply Lemma 3.11 + AA (lbl351) to Φ_k^*g_k(t) on M_∞ : `winGInfOfSol` — **DONE**.
   Output `WindowGInfOut`: `∃φ gInf, ∀ε ∃k0 ∀k≥k0 ∀t, metricDerivNormSupOn K p (gSeq(φk)t)(gInf t) gRef < ε`.
3. Assemble into solution convergence : `flowLimit_upgrade` — **DONE**.
4. "limit is a solution" : `ricci_continuous_in_metric_time` — **DONE** (one-sentence Ricci-continuity).

**HISTORICAL FRONTIER (SUPERSEDED) — the old norm-bridge diagnosis:**
`winGInfOfSol` gives the covariant norm for TOTAL metrics on M_∞; the `conv` field needs
it on the per-k SourceDomain SUBTYPE (Φ_k is a `PartialDiffeomorph`, so Φ_k^*g_k only
lives on the source `U_k`). Bridge = **restriction-invariance of `metricDerivNormSupOn`**:
the covariant metric-derivative norm is local ⇒ unchanged by `restrictOpen` to an open
submanifold. Building block: `covDerivAlong_restrict_eq_leviCivita`
(`Comparison/Variation/CovariantChainRule.lean:187`). NOT built at the norm level. This is
the only genuine missing lemma; the rest (`SolWindowData` for Φ_k^*g_k from the cited Shi
bounds, threading `hσsrc`/`hσtgt`/`refMetric`) is pullback bookkeeping.

Historical work list (superseded): (a) `metricDerivNorm`/`metricDerivNormSupOn` restriction-invariance
lemma; (b) `SolWindowData` builder for the pulled-back flows (cited `hShi` → `H0`/`Hcov`/`Hlip`);
(c) `conv` producer = `winGInfOfData` ∘ (b) bridged by (a); (d) wire through `flowLimit_upgrade`.

### Historical progress + conv-field frontier (2026-06-21; superseded)

- **(a) DONE, verified.** `metricDerivNorm_restrictOpen` (pointwise, via "Koszul is local":
  `OpenSubtypeNaturality.lean` bracket/Koszul/connection restriction) + **`metricDerivNormSupOn_restrictOpen`**
  (sup level, `MetricDerivNormRestrict.lean`). Both axiom-clean, targeted build green.

- **(c) is the genuine multi-session frontier (stuck, 3 routes).** The blocker: `derivNormSupOn`
  (PointedConvergence.lean:1424) = `metricDerivNormSupOn (sourceCompactSet Φ k K) p (pullbackMetric t)
  (limitMetric t)(referenceMetric t)`, where `ofRestrictPullback` fixes `limitMetric = restrictOpen(L.metric)`
  (✓ a restrictOpen) and `pullbackMetric = Diffeomorph.pullbackMetric (restrictOpen g_k)(sourceTargetDiff)`
  — a **pullback, NOT a restrictOpen**. So (a) bridges the limit/reference metrics but **not** the pullback
  metric. The covariant norm comparison of the *varying-manifold* pullbacks `Φ_k^* g_k` to the *fixed-limit*
  `gInf` requires bringing the pullbacks onto a common fixed manifold for the Arzelà–Ascoli. Three routes,
  all multi-session, no project shortcut:
  1. **sup-corollary direct** — FALSE: `pullbackMetric` is a `Diffeomorph.pullbackMetric`, the restriction
     tools don't touch it.
  2. **bump-extension to L.M** — define total `gSeq k = χ_k·(Φ_k^*g_k) + (1−χ_k)·gRef` via a compact
     exhaustion `C_k ⊆ source_k` (have `source_exhausts.subset`) + smooth bumps; then `restrictOpen(gSeq k)=
     pullbackMetric` on `C_k`, apply `winGInfOfData` + (a). **No metric-extension/convex-combination
     `SmoothRiemannianMetric` constructor exists** — the bundle-smoothness of `gSeq k` is the new work.
  3. **restrict-to-fixed-source + patch** — for each `K`, take `m` with `K ⊆ source_m`; for `k ≥ m`,
     `restrictOpen(pullbackMetric_k, source_m)` is total on `source_m`; run `winGInfOfSol` on `M := source_m`,
     bridge by (a), then patch the per-`m` limits into one `L.metric` (uniqueness of C^∞ limits). Needs
     `SolWindowData` on `source_m` for the restricted pullbacks + the L-consistency/patching.
  Route 3 avoids bump-smoothness (cleanest; the `k<m` truncation is handled by setting those terms to
  `restrictOpen(L.metric)`), but every route bottoms out at the SAME step: **assembling the single limit
  metric `g_∞ = L.metric` on all of `M_∞` from the per-source-domain Arzelà–Ascoli limits** (`winGInfOfSol`
  produces a limit *per domain*; identifying them as one global `g_∞` needs a global extension or a
  patching/uniqueness argument). That is exactly the book's **Step D** metric assembly ("these metrics form
  a Riemannian metric `g_∞` on `M_∞` via the coordinate charts", chapter4.tex:89–91 — glossed as "not hard
  to see"). So the 3.10⇐3.9 wire bottoms out NOT on BBS and NOT on new analysis (Lemma 3.11 + AA are done),
  but on the **`g_∞` assembly** — a genuine multi-session construction. STUCK here after 3 routes; recommend
  a dedicated session on Route 3 (restrict-to-`source_m` + winGInfOfSol-per-domain + patch via C^∞-limit
  uniqueness), reusing the now-complete `metricDerivNorm(SupOn)_restrictOpen`.

## Design notes

- `FlowLimitData` is parameterized by `mc` because `maps`/`conv`/`refMetric` all
  reference the limit manifold + subseq from `mc`. The fields use the
  `letI : … := L.topology / sourceDomTop maps k` instance pattern mirroring
  `SourceDomainMetricData.ofRestrictPullback`.
- Per the approved plan (scope = "frontiers as inputs"), `hShi` and the Thm-3.9
  conclusion stay honest inputs (`mc` is the Thm-3.9 conclusion; `hShi` enters
  Brick D's `winGInfOfSol` application).
- Superseded design choice: the exact-conclusion compatibility structure and
  its bridge were removed on 2026-07-09.  Canonical consumers now take
  `FlowUpgradeData` directly.
