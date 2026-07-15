# HOPF–RINOW SESSION — kickoff prompt

**Paste everything below the line into the new session. Self-contained.**

---

Work in `E:\testdifferential-geometry` (Lean 4 / Mathlib, branch `short-time-existence`).
All Lake ops go through `scripts/lake-locked.ps1` (`claim` before editing, `check`/`build`
to verify, `release` after; never call `lake` directly; `status` before assuming a file is
free — other sessions are active). Read `CLAUDE.md` first. NEVER push (the human pushes).
Record findings in same-name `.md` notes. Report = the math conclusion + where you're
stuck, in prose; no theorem-list dumps.

## The one theorem to prove (the goal)

`Hopf–Rinow`: a **complete, connected** Riemannian manifold has a **proper** distance
(closed balls compact) realizing the Riemannian metric, with minimizing geodesics between
points. Concretely, discharge this `sorry` (it is the single black box the whole Chapter-4
compactness proof rests on):

`DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringOrdered.exists_proper_realization`

Its statement (in `…/HCGCompactness/C4/GoodCoveringOrdered.lean`): for a
`PointedRiemannianManifold Y` that is `MetricComplete` and connected,
```
∃ ms : MetricSpace Y.M,
  (∀ x y, edist x y [Y.emetricSpace] = ENNReal.ofReal (dist x y [ms]))         -- realizes the emetric
  ∧ (ProperSpace Y.M [ms])                                                     -- closed balls compact
  ∧ (∀ p, ∀ t∈[0, dist p Y.basepoint], ∃ q, dist q Y.basepoint = t)           -- intermediate distance
```
The three conjuncts are: (1) the Riemannian distance is a genuine `MetricSpace` realizing
the stored emetric `Y.emetricSpace`; (2) **properness** (Hopf–Rinow: complete ⇒ closed
balls compact, equivalently `exp` surjective on closed balls); (3) **minimizing geodesic
to the basepoint** realizing every intermediate radius.

## Where the work is, and what already exists

- `Geometry/Comparison/HopfRinow.lean` — the locus. It ALREADY has the geodesic
  ODE/extension machinery (geodesic completeness, endpoint continuation, chart-curve
  regularity: `isGeodesicOn_Ici_of_complete`, `isGeodesicOn_Ioi_of_endpointContinuation`,
  `isGeodesicOn_contMDiffOn_one`, …). It has **4 `sorry`s** in the minimizing-geodesic
  chain — these are the real frontier:
  - `exists_continuous_path_realizing_riemannianEDist` (2 `sorry`s),
  - `minimizing_path_is_smooth_geodesic` (1),
  - `unit_speed_rescale` (1),
  - and `exists_unit_speed_minimizing_geodesic_between_points` (the endpoint these feed).
- `Geometry/Exponential/MinimizingGeodesic.lean` — `riemannianEDist`, finiteness on
  connected manifolds (`riemannianEDist_ne_top`), and the distance API. Read it.
- `Geometry/Exponential/` — `expMap`, `expMapDiffeo`, and **`expMap_contMDiffAt_infty_of_norm_lt`**
  (exp is `C^∞` on a small ball — use it; do NOT re-derive per-order). `injRadius`,
  `normalChartAt` in `Comparison/`.
- The **properness** conjunct is NOT yet built: the standard route is
  `exp_p` defined on all `T_pM` (geodesic completeness, ~have) + surjective onto `M` +
  `closedBall` = continuous image of a compact Euclidean closed ball ⇒ compact ⇒
  `ProperSpace` via `Metric.properSpace_of_compact_closedBall` (or Heine–Borel). Check
  Mathlib for `Metric.proper…`/`isCompact_closedBall` glue before hand-rolling.

## Mathematical route (Hopf–Rinow, the textbook proof)

1. **Minimizing geodesics (the 4 `sorry`s).** A length-minimizing path between two points
   exists (Arzelà–Ascoli on unit-speed paths / the direct method), is a smooth geodesic
   (first-variation / it satisfies the geodesic ODE), and rescales to unit speed. This
   gives `exists_unit_speed_minimizing_geodesic_between_points`. Mathlib has
   `Metric`/intrinsic-length API and possibly `riemannian`-distance results — search before
   building (the project has repeatedly found the "missing" piece already present).
2. **`exp_p` total + surjective** (geodesic completeness): every geodesic extends to all of
   ℝ (the `isGeodesicOn_Ici_of_complete*` lemmas), so `exp_p : T_pM → M` is defined
   everywhere; minimizing geodesics ⇒ surjective.
3. **Proper.** `closedBall p r = exp_p '' (closed Euclidean ball)`, a compact image ⇒ closed
   balls compact ⇒ `ProperSpace`.
4. **Assemble `exists_proper_realization`** in `C4/GoodCoveringOrdered.lean`: the `MetricSpace`
   = the Riemannian-distance metric (realizing `Y.emetricSpace` — conjunct 1 is essentially
   `riemannianEDist` `≠ ⊤` + the emetric=ofReal(dist) bridge); properness from step 3;
   intermediate-distance from the minimizing geodesic to the basepoint (step 1).

## Tasks

1. Verify feasibility against the book (do Steiner/Hopf–Rinow as in any Riemannian-geometry
   text — Morgan–Tian / do Carmo). State which of the 4 `sorry`s reduce to Mathlib API and
   which need real work.
2. Discharge the 4 `HopfRinow.lean` `sorry`s, build the properness conjunct, then
   `exists_proper_realization`. Axiom-clean (`#print axioms` = `[propext, Classical.choice,
   Quot.sound]`).
3. If a genuine analytic wall remains (e.g. minimizing-path existence needs an Arzelà–Ascoli
   on paths not in Mathlib), STOP and report the smallest missing lemma — do NOT add new
   axioms. It is acceptable to leave Hopf–Rinow as the one honest black box if a sub-step is
   a multi-week frontier; say so explicitly with the precise blocker.

Off-limits (other sessions own them): the Ch3 P-track (`RicBound*`, `MetricPreconv*`,
`PointedConvergence`, `AllTimes*`) and the Ch4 `C4/` Step-B work. You touch
`Comparison/HopfRinow.lean`, `Comparison/MinimizingGeodesic`-adjacent files, and the single
`C4/GoodCoveringOrdered.lean:exists_proper_realization` assembly.
