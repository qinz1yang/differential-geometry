# STEP C (center of mass / nonlinear averages) SESSION — kickoff prompt

**Paste everything below the line into the new session. Self-contained.**

---

Work in `E:\testdifferential-geometry` (Lean 4 / Mathlib, branch `short-time-existence`).
All Lake ops go through `scripts/lake-locked.ps1` (`claim` before editing, `check`/`build` to
verify, `release` after; never call `lake` directly; `status` before assuming a file is free —
other sessions are active). Read `CLAUDE.md` first. NEVER push (the human pushes). Record
findings in same-name `.md` notes. Report = the math conclusion + where you're stuck, in prose;
no theorem-list dumps; be honest about the % of the whole MSM135 Ch4 project (it is ~20%, and a
verified helper is a small fraction of it). **Read `…/C4/StepCCenterOfMass.md` first — it is the
verified feasibility plan for this exact task** (infra map, C1 proof route, honest-input boundary).

## Goal

Build MSM135 Chapter 4 §6 **Step C** (book L2092–end): the center-of-mass averaging. Endpoints:
- **C1 = lbl429** (Existence of center of mass): for `q₁,…,qₖ ∈ B(p,r)` with `r < min{inj/3, π/(6√K)}`,
  weights `μᵢ ≥ 0`, `Σμᵢ > 0`, the energy `φ(q) = ½ Σᵢ μᵢ d²(q,qᵢ)` has a UNIQUE minimizer
  `cm{q₁,…,qₖ} ∈ B(p,2r)`; plus `cm → q*` as `qᵢ → q*` uniformly in the weights.
- gradient: `grad φ(q) = -Σᵢ μᵢ exp_q⁻¹ qᵢ`; minimizer ⟺ `Σᵢ μᵢ exp_q⁻¹ qᵢ = 0`.
- **C2 = lbl430**: smoothness / derivatives of `cm` in weights and points (IFT on `grad φ = 0`).
- **C3 = lbl434**: averaging maps — partition of unity `φ_k^α` over the Step-A cover + `cm`.
- **C4 = lbl436**: average of (`→ id`) local maps `→ id`.

**Start with C1.** It is the foundation and is fully feasible now (below). C2–C3 follow; C4 is
gated on the lbl399-`C∞` composition-convergence brick (a separate parallel session, `COMPCONV_HANDOFF.md`).

## Feasibility — VERIFIED. The geometry C1 needs is already built, sorry-free.

Do NOT re-derive these; reuse them.
- **Properness / closed-ball compactness** (existence of the minimizer): `Comparison/HopfRinowProper.lean`
  — `expImgClosedBall_compact`, `properSpace_riemMetric`, `riemMetricSpace`, `riemMetric_dist_eq`,
  `riemMetric_realizes`. Rests on the unconditional `MinimizingGeodesic.hopf_rinow_expMapIntrinsic_surjective_minimizing`
  (0 sorry). [This same chain already discharged `GoodCoveringOrdered.exists_proper_realization`.]
- **Geodesic convexity of small balls** (`lbl417`): `Comparison/ConvexBalls.lean:isConvexWith_smallNormalBall`,
  built on the `lbl416` along-curve `d²`-convexity input. `Comparison/GeodesicConvexity.lean`:
  `IsGeodesicallyConvexWith`, `smallNormalBall`, `joinedIn`, `inter`.
- **Distance / continuity**: `riemannianEDist`, `riemannianEDist_ne_top` (finite on connected M),
  `Comparison/RiemannianDistContinuity.lean:continuous_riemannianEDist`, `riemMetric_dist_eq` (real form).
- **exp / exp⁻¹ / Gauss**: `Comparison/NormalCoordinates.lean` (`normalChartAt` = exp⁻¹, `expMapDiffeo`),
  `Exponential/GaussLemma.lean`. **`lbl411`** (`grad(½d²(·,x)) = -exp_·⁻¹ x`) is NOT yet a named lemma
  — add it (provable from the done minimizing geodesics + Gauss lemma); needed for the gradient
  characterization and the IFT in C2.

Mirror the instance/variable context of `HopfRinowProper.lean` (the `RiemannianBundle` /
`IsContinuousRiemannianBundle` / `SigmaCompactSpace` / `ConnectedSpace` / `T3Space` setup) — it is
the exact context where the properness + distance API is stated.

## Honest-input boundary for Step C (small)

ONLY the **strict convexity / Hessian positivity of the `d²` function** (`lbl416`, from the
`lbl413` Hessian comparison): needed for uniqueness of the minimizer (C1) and the IFT (C2). Take
it the SAME way `isConvexWith_smallNormalBall` does — as the along-joining-curve convexity
hypothesis — do NOT invent a new convexity predicate. Everything else (existence, gradient
characterization, the averaging construction) you PROVE.

## C1 proof route

1. **Energy**: define `φ q := ½ * ∑ i, μ i * (d q (qᵢ))^2` with `d` the `riemMetricSpace` distance
   (or `(riemannianEDist q qᵢ).toReal`). Prove `Continuous φ` (sum of continuous `d²`, via
   `continuous_riemannianEDist` + `riemMetric_dist_eq`).
2. **Existence**: show `φ q > φ p` for `q ∉ B(p,2r)` (book L2679: any such `q` is `≥ 2r` from `p`
   hence the weighted sum exceeds `φ p`), so a global minimizer lies in the compact
   `closedBall p (2r)` (`expImgClosedBall_compact`/`properSpace_riemMetric`); extract via
   `IsCompact.exists_isMinOn`.
3. **Uniqueness**: `φ` strictly convex on `B(p,2r)` — each `½d²(·,qᵢ)` strictly convex there
   (`lbl416` honest input, since `B(p,2r) ⊆ B(qᵢ,3r) ⊆ B(qᵢ, π/(2√K))`), `μᵢ ≥ 0`, `Σμᵢ > 0`.
   Use the convexity API in `GeodesicConvexity`/`ConvexBalls`. Strictly-convex ⟹ ≤ one minimizer.
4. **`cm ∈ B(p,2r)`**, **gradient characterization** (via the new `lbl411` lemma), and the
   **`cm → q*`** continuity (apply existence/uniqueness on shrinking balls `B(q*,r*)`).

## File placement

The center-of-mass theory is general Riemannian geometry → put C1/C2 (and `lbl411`) in a new
`Geometry/Comparison/CenterOfMass.lean` (next to `ConvexBalls`/`HopfRinowProper`, reusable). Put
the HCG-specific averaging (C3 partition-of-unity over the Step-A cover, C4) in `…/C4/StepC*.lean`.

## Tasks

1. Read `StepCCenterOfMass.md`; verify the C1 route against the book (`chapter4.tex` L2640–2720
   for lbl429/430, L2123 for lbl411). State which sub-steps reduce to existing API.
2. Add the `lbl411` gradient lemma, then build C1 (`exists_unique_centerOfMass`) taking the
   `lbl416` convexity as the honest-input hypothesis. Then C2 (smoothness via IFT), C3 (averaging).
3. Targeted-build green, `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]` + the
   one `lbl416`/`lbl413` honest-input field — no `sorry`/admissions beyond that documented input).
4. C4 (`average of →id maps → id`) is **deferred** until the lbl399-`C∞` composition-convergence
   brick lands (parallel session). Build C1–C3 now; leave C4 with a one-line pointer.
5. If a genuine wall appears (e.g. the convexity API doesn't compose to function-strict-convexity,
   or the IFT setup needs missing manifold API), STOP and report the smallest missing lemma — do
   NOT add axioms or fabricate the convexity beyond the documented `lbl416` input.

## Constraints / off-limits

- Off-limits (other sessions own them): the Ch3 P-track (`RicBound*`, `MetricPreconv*`,
  `PointedConvergence`, `AllTimes*`); the settled C4 Step-B geometry (`StepBInputs`,
  `StepBLocalMetrics`, `StepBTransition`); and the lbl399-`C∞` brick (`StepBApproxIso` +
  new `MapConvergenceComp.lean`, owned by the COMPCONV session). `Comparison/` is shared with
  Ch3 — add NEW files (`CenterOfMass.lean`) rather than editing existing ones; `status`/`claim`.
- The Step-A Hopf–Rinow input (`exists_proper_realization`) is DONE — do not rebuild it.
- After C1–C3 land, the payoff is `lbl397` (B1): the averaged map `F_{kℓ;r}` is an approximate
  isometry — that assembly needs BOTH this Step C averaging AND the lbl399-`C∞` brick, and is the
  join point of the two parallel B/C tracks.
