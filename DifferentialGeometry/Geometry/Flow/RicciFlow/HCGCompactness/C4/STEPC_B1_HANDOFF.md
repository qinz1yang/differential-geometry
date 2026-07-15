# [SUPERSEDED 2026-07-01 → use `B1_JOIN_HANDOFF.md`] STEP C → B1 kickoff prompt

> Task (A) (StrictDistInput + centerOfMass wrapper), the averaging analytic layer, and the
> lbl411 gradient all landed (see `StepCCenterOfMass.md` updates). Do not paste this prompt.

**Paste everything below the line into the new session. Self-contained.**

---

Work in `E:\testdifferential-geometry` (Lean 4 / Mathlib, branch `short-time-existence`).
All Lake ops go through `scripts/lake-locked.ps1` (`claim` before editing, `check`/`build`,
`release` after; never call `lake` directly; `status` before assuming a file is free — several
sessions are active). Read `CLAUDE.md` first. NEVER push. Record findings in same-name `.md`
notes. Report = math conclusion + where stuck, in prose; honest about the % of the whole project
(~20%; a single lemma is a small fraction). **Read `…/C4/StepCCenterOfMass.md` end-to-end first**
— it is the live status of this exact task (what is proved, what the open frontiers are).

## Where things stand (do NOT redo)

- **lbl399 is DONE at `C∞`**: `StepBApproxIso.comp_cInf_id_on` (two-parameter `A_ℓ∘B_k → id` in
  `C∞` on compacts), on the new engine `…/HCGCompactness/MapConvergenceComp.lean`. Use it for C4.
- **Hopf–Rinow / properness DONE**: `Comparison/HopfRinowProper.lean`
  (`expImgClosedBall_compact`, `properSpace_riemMetric`, `riemMetricSpace`) — closed.
- **C1 (center of mass) is most of the way**: `Comparison/CenterOfMass.lean` (0 sorry) proves
  EXISTENCE outright and UNIQUENESS *conditionally* on a strict-convexity input
  (`exists_unique_curve_dist_le`, `exists_unique_jensen_dist_le`), plus the gradient algebra
  (`grad_centerEnergy`, `sum_grad_eq_zero`, `sum_expInv_of_flat`) and the `cm → q*` stability
  bound. Two honest frontiers remain (below).

## The two open Step C frontiers

1. **lbl411 one-summand gradient** `grad(½ d(·,pt)²) = -exp_·⁻¹ pt`. **A PARALLEL SESSION OWNS
   THIS** (the variation layer: `FirstVariation.lean`, `SecondVariationMinimiser.lean`,
   `ExpVariationSmooth.lean`, `diagExp`). It is reduced to a `diagonal_exp_local_diffeomorphism`
   (moving-base `exp⁻¹` section). **DO NOT duplicate it** — coordinate; treat its covector output
   `(mfderiv (halfSqDist pt) q).toLinearMap = metricFlatEquiv g q (-(normalChartAt g q pt))` as the
   interface `CenterOfMass.grad_halfSqDist_of_flat` already consumes.
2. **lbl413/lbl416 strict-convexity (Hessian of `d²`)** — THIS IS YOURS, and it is the immediately
   unblocked piece. The book CITES the Hessian comparison (lbl413) as an external theorem, so it
   is a LEGITIMATE honest-input field (`CLAUDE.md`: honest inputs only where the book cites an
   external theorem — lbl413 qualifies). `ConvexBalls.lean` currently only takes a NON-strict
   `ConvexOn` along-curve input. You must add the **strict** version.

## Tasks (in order)

**(A) Close C1 uniqueness unconditionally** — provide the lbl413/lbl416 honest input and wire it.
- Add a small honest-input predicate/structure (in `C4/StepCInputs.lean` or extend
  `StepAInputs.lean`) for the lbl413 Hessian-comparison conclusion in the exact shape
  `CenterOfMass.exists_unique_curve_dist_le` consumes: each `½ d(·,qᵢ)²` is
  `StrictConvexOn ℝ unitInterval` along the Hopf–Rinow joining curves on the `2r` ball
  (equivalently a positive Hessian lower bound). Name it per the book (e.g.
  `HessianComparisonInput` / `StrictConvexDistSqInput`); docstring it as the lbl413 honest input.
- Feed it to the conditional C1 theorems to get an UNCONDITIONAL `∃!`-minimizer, then **define the
  `cm` function** `centerOfMass (μ) (q) : M := Classical.choose (the unique minimizer)` with its
  defining lemmas (`cm ∈ B(p,2r)`, `IsMinOn`, the gradient equation `Σ μᵢ exp_cm⁻¹ qᵢ = 0` via
  `sum_expInv_of_flat` + the lbl411 interface, and the `cm → q*` continuity from the stability bound).

**(B) C3 — the averaging map (lbl434)** in `…/C4/StepCAveraging.lean`.
- Build the partition of unity `{φ_k^α}` subordinate to the Step-A good cover (book L1561–1620;
  reuse `GoodCovering*.lean` / the Step-A cover data — `ψ^α∘(H_k^α)⁻¹` normalized, with the
  basepoint-preserving `χ_k` cutoff for `α≠0`). Then define the averaged map
  `F_{kℓ;r}(x) := cm_{(φ_k^α(x))} {F_{kℓ}^α(x)}` and prove it is well-defined and continuous on
  `B(O_k,r)` (uses the `cm → q*` continuity + the partition-of-unity smoothness).

**(C) C2 — smooth dependence of `cm` (lbl430)**: IFT on `Σ μᵢ exp_q⁻¹ qᵢ = 0`, needing the lbl411
gradient (parallel session) AND the lbl413 nondegenerate Hessian (your (A) input). Gate this on the
lbl411 covector identity landing; state the IFT cleanly and wire it when ready.

**(D) C4 — average of (`→id`) maps `→ id` (lbl436)**: feed `StepBApproxIso.comp_cInf_id_on`
(lbl399-`C∞`, DONE) through the averaging — the local maps `F_{kℓ,β}^α → id`, and the center of mass
of points all `→ x` is `→ x` (`cm → q*`). This is mostly assembly once C3 exists.

**(E) lbl397 = B1 (the payoff)** in `…/C4/StepB1ApproxIso.lean`: `F_{kℓ;r}` is an
`(ε,p)`-approximate isometry on `B(O_k,r)` for `k,ℓ` large. Assembles C2 (smoothness/`C^p` control)
+ C3 (the map) + C4 (`→id`) + lbl399-`C∞`. This is the join of the B and C tracks and a genuine
Theorem-3.9 critical-path endpoint.

## Constraints / coordination

- Off-limits (other sessions): the variation/`lbl411`-gradient layer (`FirstVariation`,
  `SecondVariationMinimiser`, `ExpVariationSmooth`, `HalfSqDistGrad*`, `diagExp`) — coordinate via
  the `grad_halfSqDist_of_flat` interface, do not edit those files. The Ch3 P-track
  (`RicBound*`/`MetricPreconv*`/`PointedConvergence`/`AllTimes*`) and the settled Step-B geometry
  (`StepBInputs`/`StepBLocalMetrics`/`StepBTransition`) and lbl399 brick (`StepBApproxIso`,
  `MapConvergenceComp`). `Comparison/` is shared — extend `CenterOfMass.lean` (yours) and add NEW
  files; `status`/`claim` before editing.
- Honest-input discipline: the ONLY new honest input is lbl413 (Hessian comparison), book-cited.
  Everything else you PROVE. No `sorry`/admissions beyond that documented field; `#print axioms`
  must be `[propext, Classical.choice, Quot.sound]`.
- There is a stale file lock on `Metric/Sphere/RoundShape.lean` (dead pid) — ignore it unless you
  touch that file, then `release -Force` it after confirming the pid is dead (`status`).
- Stop-and-report condition: if (A)'s strict-convexity wiring needs a function-convexity API that
  `GeodesicConvexity`/`ConvexBalls` can't compose, or C3's partition of unity needs missing Step-A
  cover data, report the smallest missing lemma rather than inventing convexity or cover machinery.
