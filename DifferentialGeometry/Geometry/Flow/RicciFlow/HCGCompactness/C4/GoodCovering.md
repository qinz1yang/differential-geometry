# GoodCovering.lean — MSM135 Chapter 4 §2 Step A (good coverings by balls)

Target: `metricCompactness` (Thm 3.9), Step A of `CHAPTER4_PLAN.md` (A1–A14).
Book source: `RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter4.tex`
L781–1369 (§"Construction of good coverings by balls").

## Math-feasibility audit (2026-06-08, before coding)

**A1 — λ[r] (eq `lbl386`, L885–895): FEASIBLE, no blocker.**
λ[r] = (a/D)·min(ι₀,1)ⁿ·e^{−Cr}, with a,C,ι₀ from `InjRadiusDecayInput` (A0 honest
input), D>0 a free constant chosen so λ[0]≤1. Pure real-analysis: positive,
antitone (C≥0), and λ_D[r] ≤ μ[r] ≤ inj(x) for D≥1 (μ = the decay bound = the
radius in `InjRadiusDecayInput.decay`). The ≤inj corollary is the geometric point:
λ-balls sit inside the injectivity radius (embedded/convex later).

**A2 — net of ball centers (L897–955): the *faithful* book construction is partly
blocked.** The book builds the net greedily, ordered by distance from O, taking
`r^α = d(Sᵅ,O)` as the *attained* minimum over the closed set `Sᵅ`. That minimizer
needs **properness** (closed bounded ⟹ compact), which routes through
`Geometry/Comparison/HopfRinow.lean` — currently **4 sorries** (minimizing-geodesic
existence; the false single-chart `expMap` continuity/surjectivity sorries have been
deleted, superseded by the cross-chart `expMapIntrinsic` route in
`Exponential/MinimizingGeodesic.lean`). Also
`InjRadiusDecayInput.dist` is a *bare* `M→M→ℝ` with **no metric axioms**.

Consequences / decisions:
- The pairwise-disjointness of `B(xᵅ,λ[rᵅ])` only needs `xᵅ ∈ Sᵅ` (membership),
  NOT the minimizer. So a **maximal λ-separated packing via Zorn** gives the
  disjoint family with no properness — this is the feasible A2 core.
- The book's *ordered* net (monotone `r^α`, `A(r)=max{α:r^α≤r}`) is what the later
  count bound A3/`lbl387` and A5/`lbl389` use. The attained-minimizer/ordering is
  the genuine remaining frontier — tie to properness (Hopf–Rinow) or carry as an
  honest input. Do NOT fake it.
- Distance model: keep using the supplied `dist`; metric axioms (triangle/symm)
  needed for "maximal ⟹ 2λ-cover" are supplied where used, not assumed globally.
  (Architectural: the supplied-`dist`-vs-Riemannian-distance reconciliation is the
  same honest-input question flagged for `metricCompactness`; defer the global
  wiring.)

## Plan (this file)

- [A1] `InjRadiusDecayInput.mu` / `.lambda`; `mu_pos`, `mu_antitone`, `lambda_pos`,
  `lambda_antitone`, `lambda_le_mu`, `lambda_le_one_at_zero`, `lambda_le_injRadius`.
- [A2-core] abstract maximal disjoint-packing existence (Zorn) → pairwise-disjoint
  λ-balls. Ordered-net refinement deferred (properness frontier).

## Status

**A1 DONE + VERIFIED + axiom-clean (2026-06-08).** `mu`, `lambda`, `mu_pos`, `mu_antitone`,
`lambda_pos`, `lambda_antitone`, `lambda_le_mu`, `lambda_le_one_at_zero`, `lambda_hasInjRadiusAt`
(λ-ball ⊆ injectivity radius for D≥1) all build; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`. Targeted build `+…GoodCovering` succeeded (StepAInputs + GoodCovering).
Step A inputs relocated to `StepAInputs.lean` (clean) — `GeometricInputs.lean` S6 part left broken
(pre-existing, isolated, flagged).

**A2 ROUTE = Zorn maximal packing on the Riemannian emetric (user-decided 2026-06-08).** Avoids
properness/Hopf–Rinow; deviates from the literal ordered net (mathematically equivalent for the good
cover + A(r) count bound).

**A2 ENGINE DONE + VERIFIED (2026-06-08), generic/Zorn:**
- `exists_maximal_pairwiseDisjoint (f : α → Set β)` — a maximal pairwise-disjoint family exists
  (chain upper bound = `⋃₀ c`; pairwise-disjointness transfers via `IsChain.total`).
- `exists_not_disjoint_of_maximal_pairwiseDisjoint` — maximality ⇒ covering: any outside `z` has
  `f z` meeting some chosen `f x` (abstract `lbl387`).
Both build (focused check EXIT=0, no sorry); depend only on `zorn_subset` + std set lemmas.

**A2 NET DONE + VERIFIED + axiom-clean (2026-06-08).** `InjRadiusDecayInput.lambdaBall` (= `Metric.eball x (λ[d(x,O)])`
in the Riemannian emetric) + `exists_lambdaNet` (a maximal λ-separated net exists ⇒ λ-balls pairwise
disjoint + maximal). Built; `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; no warnings.

**Key fix (the diamond):** with `[InnerProductSpace ℝ E]` in scope, the model fiber inner product on
`TangentSpace I x` does NOT coincide definitionally with the Riemannian one (Mathlib
`normedAddCommGroupTangentSpaceVectorSpace`, Riemannian/Basic.lean:220), so inlining `MetricComplete`'s
emetric `letI` block fails per-fibre synth. RESOLVED by factoring the emetric construction into
`PointedEmetric.lean` (`PointedRiemannianManifold.emetricSpace`), a NEW file in a clean context (NO
`[InnerProductSpace ℝ E]`, only `[NormedSpace ℝ E]`); `GoodCovering` consumes the already-elaborated
`EMetricSpace`. Also: `EMetric.ball`→`Metric.eball`; don't `open scoped ENNReal` (ambiguous `∞`); `open Bundle`.
Radius uses `InjRadiusDecayInput.dist` for `d(x,O)` (matches A1); emetric only for the ball — fine since
existence is radius-agnostic.

**A3 (`lbl387`) GEOMETRIC COVER DONE + VERIFIED (2026-06-08):** `lambdaNet_cover` — for a maximal
λ-separated net `S` and any `z`, `∃ x ∈ S, edist z x < λ[d(z,O)] + λ[d(x,O)]` (in the emetric).
Proof: `z∈S` immediate (`edist_self`+`λ>0`); else covering corollary + `Set.not_disjoint_iff` +
`edist_triangle`/`edist_comm` + `ENNReal.add_lt_add`. Needs `0<D`. Membership→edist is by defeq
(`lambdaBall` = `Metric.eball`, `mem_eball`=`Iff.rfl`). (Zorn route gives the point-dependent sum
`λ_z+λ_x` instead of the book's `2λ[rᵅ]`; still a cover.) No sorry; build clean.

**NET SEPARATION DONE + VERIFIED (2026-06-08):** `lambdaNet_separated` — distinct centers of a
pairwise-disjoint net satisfy `λ[d(x,O)] ≤ edist x y` (emetric), the dual of `lambdaNet_cover`.
Proof: else `y ∈ B(x,λ_x) ∩ B(y,λ_y)` contradicts disjointness. (Lean gotchas: `mem`↔`edist` by defeq
via `lt_of_eq_of_lt` not `rw`; `hS … : (Disjoint on lambdaBall) x y` needs `Set.disjoint_left.mp`, not
`rw [Set.disjoint_left]`, because of `Function.onFun`.)

**dist/edist BRIDGE + COUNT DONE + VERIFIED (2026-06-08).** Resolved the fork by realizing the
documented intent (`dist` = Riemannian distance): `InjRadiusDecayInput.RealizesEdist` (`edist x y =
ofReal(dist k x y)`, `dist≥0`) ⇒ `lambdaNet_dist_separated` (`λ[d(x,O)] ≤ dist x y`). Then **A10
multiplicity** `net_multiplicity` (`lbl383` item 5): centers of the net in `B(O,R)` near `z` number
≤ `Imult`, via uniform `λ[R]`-separation (`λ` antitone) + A0' `VolumeComparisonInput.ballMult` (Fintype
`↥J`, `Fintype.card_coe`). Lean: `le_of_le_of_eq` + `ENNReal.ofReal_le_ofReal_iff` for the bridge.

**ROUTE A — done on the Zorn route, VERIFIED + axiom-clean (2026-06-08):**
A1 (λ) · A2 net (`exists_lambdaNet`) · A3 cover (`lambdaNet_cover`) · separation (`lambdaNet_separated`) ·
**dist=pseudometric bridge** (`RealizesEdist` + `dist_comm`/`dist_triangle`/`distO_sub_le`) ·
**λ-ratio** (`lambda_eq`, `lambda_ratio_le` — the `e^{cC}` mechanism) · dist-level membership
(`mem_lambdaBallC_dist`) · **A10** multiplicity (`net_multiplicity`) · **A8** scaled radii (`lambdaBallC`
= `lbl391` B̃/B̂/B/B̄/B⃗) · **A9-disjointness** (`lambdaBallC_pairwiseDisjoint`) · **A13 nesting**
(`lambdaBallC_subset_of_inter`, item 7) · **A14 metric-core** capstone (`GoodCovering` + `exists_goodCovering`).
`#print axioms` clean throughout (`[propext, Classical.choice, Quot.sound]`).

**OPTION 2 DONE (2026-06-08, user chose "往2走" = add honest inputs):** A3 + A4 completed via the
`PackingBound` honest input (Bishop–Gromov total packing, book-external since Mathlib has no Riemannian
volume): `net_count_le` (A3 `A(r)` ball-number bound), `net_finite_in_ball` (net locally finite), and
`exists_finite_cover` (**A4 `lbl388`** finite cover of `B(O,r)` by net balls). All verified, axiom-clean.

## 2026-07-01, subsequence projections

Added `RealizesEdist.subseq` and `PackingBound.subseq`.

Together with `InjRadiusDecayInput.subseq` and `VolumeComparisonInput.subseq`,
the Step-A distance-realization and packing data now survive ordinary
subsequence refinement.  This is a producer-closure brick for later Step-C
finite-hat/transition pipelines; it does not change the Hopf--Rinow or
ordered-net frontiers recorded below.

Verification passed.

**HONEST CORRECTION:** A7/A11/A12 are NOT reachable by option 2 after all — they need cross-`k` center
MATCHING (the distance-ORDERED net / the comparison maps), i.e. they too need **option 1 (Hopf–Rinow)**,
not just "subsequence machinery". So option 2's clean reach was exactly A3 + A4.

**REMAINING A1–A14 — ALL need option 1 (Hopf–Rinow ordered net) or §5 (also Hopf–Rinow):**
A5/A6 (`r^α↗`), A7 (K'(r)), A9-cover (B(O,r)⊂⋃B̂ by the tuned radii), A11/A12 (cross-`k` stability),
A14-convexity (`lbl417`). Done so far: **A1,A2,A3,A4,A8,A10,A13 fully (7/14)** + A9-disjoint + A14-metric-core;
infra = dist-pseudometric bridge, λ-ratio, `mem_lambdaBallC_dist`, `PackingBound`. To finish Route A:
discharge `HopfRinow.lean` (9 sorries) for the ordered net + §5 convexity. Making the rest honest inputs
would hide book-internal difficulty (forbidden), so they stay visible frontiers.

## Earlier note (pre-relocation)

A1 was first written importing `GeometricInputs`; that module is committed-broken (see BLOCKER below),
so the inputs were relocated to `StepAInputs.lean`.

**BLOCKER (2026-06-08): `GeometricInputs.lean` does not compile (committed-broken, isolated).**
- `GeometricInputs.lean:62` references `RicciFlower.Coordinates.NormalChartData`, which exists
  NOWHERE in the repo (not in `DifferentialGeometry`, not in `RFreference`) — a dangling port
  reference. Downstream `sorry`/stuck-instance errors at 67/98 are consequences.
- The breakage is confined to the **S6 exp⁻¹ machinery** (`NormalChartFor`, `normalTransitionMap`,
  `NormalTransitionDerivBound`, `ExpInverseDerivBoundInput`). The native normal-coordinate API is
  `normalChartAt`/`expMapDiffeo` (`Comparison/NormalCoordinates.lean`); there is no `NormalChartData`.
- `GeometricInputs` is **not imported by the main chain** (`MetricCompactness` imports
  `BoundedGeometry`+`PointedConvergence`), so the project still builds and the sorry-grep read clean.
- The Step A inputs A0/A0' (`PointedSeqDistance`, `InjRadiusDecayInput`, `VolumeComparisonInput`)
  are self-contained and clean — only trapped in this non-compiling module.

**Resolution pending user decision (asked 2026-06-08):** recommended = relocate the 3 clean Step A
input structures into a new building file `StepAInputs.lean`, import that from `GoodCovering`, and
flag the broken S6 part of `GeometricInputs` separately (do NOT redesign S6 now).

## 2026-07-10, bounded-distance injectivity floor

Added `mu_hasInj_of_le`: if a point has supplied basepoint distance at most
`R`, the existing canonical decay scale `mu R` is a positive injectivity-radius
lower bound, uniformly in the sequence index.  This reuses `mu` rather than
introducing a parallel radius definition.  It discharges the injectivity half
of a fixed-radius Step-C scale.  Verification passed.

It does not by itself choose one global `D` for every outer radius; that needs
the moving inverse-exponential branch scale to dominate a fixed multiple of
`mu(distance)` (or a correctly localized/eventual live-slot redesign).
