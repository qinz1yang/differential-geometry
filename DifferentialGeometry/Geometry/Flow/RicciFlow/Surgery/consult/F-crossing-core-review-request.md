# Sixth review request (F): the crossing core and the cap-window transport

Target: `liao9yuan/differential-geometry-dev`, branch `codex/pc-target-c-psf` (head of 2026-09-26 evening;
the request names files, not commits). Read `Surgery/Skeleton/DESIGN_CROSSING.md`, `DESIGN_C4.md`,
`DESIGN_C3B.md`, `LEAD_NOTES_20260926.md`, and the logs `Surgery/Skeleton/OPUS_FILL_LOG_B3.md`,
`OPUS_FILL_LOG_B3B.md`, `OPUS_FILL_LOG_B3C.md`, `OPUS_FILL_LOG_B6B.md`, `OPUS_FILL_LOG_B6C.md`,
`OPUS_FILL_LOG_B5.md`, `OPUS_FILL_LOG_SPT.md`, and the Lean files they name under `Surgery/Topology/`
(`SpatialBoundedCurvatureAtDistance.lean`, `BoundedCurvatureAtDistanceLimit.lean`,
`TracedRegionOrCapWindow.lean`, `TracedRegionAncientLimit.lean`, `TracedRegionDepthStep.lean`,
`AncientPointedFlowLimitCurvature.lean`) and `Perelman/CanonicalNeighborhood/SpatialCanonicalWitness*Transport.lean`.

## State

The Crossing leaf (`CrossingContinuation`) and the young-unscathed case of the spatial leaf (C4) share
one open core. Delivered, sorry-free: the room lemma and its terminal version (X2, X2b), traced regions
with independent radius/depth/bound and the common survivor flow (B2), the backward step under the
derivative clause (B4), the traced-region-or-cap-window dichotomy with explicit window constants but
with the along-trace curvature bound `hscal` as a hypothesis (B5), the generic all-radii ancient pointed
limit with compatible exhaustion (B6a) and its history glue (B6b), the limit's `Rm ≥ 0`, slice
completeness and κ-solution packaging (B6c items 1, 2, 5), the single depth step (B7 step), and the
bounded-curvature-at-distance statement below the escape radius from spatial witnesses alone (B3a),
plus the pointed limit at the escape radius (B3b(i), single slab).

Open (each refuted once in a naive form, see the logs):

1. **B3c (cone exclusion) — PROVED on a single slab** (`BoundedCurvatureAtDistance{Necks,Cone}.lean`,
   `BoundedCurvatureAtDistance.lean`: `exists_scalar_bound_at_distance_of_final_slab_window`, with
   witnesses needed only on the final slice, `εcone` absolute, depth only L1's fixed window; route:
   limit ray with necks → punctured cone end in the completion → second blow-up →
   `solution_not_rescaled_cone_limit`). Two earlier failures forced the single-slab form: (a) a purely
   spatial statement is FALSE (thin cone horn end); (b) a window crossing an event is FALSE without
   the records (a fresh cap carries an arbitrary metric). Question: for the Crossing leaf the window
   crosses events; is the right extension "records + `¬CapWindowPoint (Dₙ, θcapₙ)` ⇒ traces exist
   (B5) ⇒ apply the single-slab theorem on the survivor flow", or must the cone exclusion be redone on
   the survivor flow through events?
2. **B6d (bounded curvature of the limit, F9).** The derivative clause is two-sided, so
   `TerminalScalarAncientLimit`'s `∂R ≥ 0` route does not apply; "complete, `Rm ≥ 0`, κ-noncollapsed
   ⇒ bounded curvature" is false as a spatial statement; the tree's time-0 bounds use
   `NormalizedSequence.higher_good` (necks at every point with `R ≥ 2`). Proposed: the approximants'
   age-free spatial witnesses above `qs` give necks at all high-curvature points of every slice in the
   window; adapt the `higher_good` argument to local approximants. Is that the correct route, and does
   it need the accuracy `ε̄cone` fixed before `qcan` (DESIGN_CROSSING F5)?
3. **B6c-κ (κ transfer for local approximants).** `ConvergesOn.parabolicallyKappaNoncollapsedBelowScale`
   needs global flows; the local approximants need a uniform-in-time curvature comparison against
   `G s` rather than `G 0`. Which lemma set closes it (a time-Lipschitz bound of `|Rm|²` on the
   approximants, or a comparison of `G s` with `G 0` uniform on the window)?
4. **B7 (depth induction).** Doubling per backward step does not reach every depth; re-anchoring needs
   the finite-horizon backward bound of the partial limit (the same object as item 2, on `(−T∞, 0]`).
   Is the strong induction on `(A, T)` with B6a's limit at each stage the right structure, or should
   the whole argument be one contradiction sequence with `(Dₙ, θcapₙ)` growing, as DESIGN_CROSSING
   sketches?
5. **C4 case (B) transport (SPT).** Restriction, pushforward and scaling of `SpatialCanonicalWitness`
   are proved; the metric-close transport is proved for the neck and cap alternatives only, and the
   whole-witness transport is blocked by: the gradient clause (`ScalarGradientComparison` is an
   unproved `Prop`), the `rm` bound at `2C` (available lemmas lose a factor 324 or need a complete
   reference), the radius clause with no slack, the universe lift from `standardCapWindow D` (`Type 0`)
   to the stage carrier, and the bridge's reference metric (`StandardCap.metric`) versus the source
   metric. Which of these are real obstacles and which are interface choices (add strict margins to
   the producers; measure the bridge's closeness against the source metric)?
6. **C3b assembly gaps** (`OPUS_FILL_LOG_C3B.md`, `Surgery/Topology/CapWindowContinuationAssembly.lean`):
   the per-point theorem `exists_capWindowPoint_bounds_of_room` proves all three leaf clauses at a
   cap-window point given two extra inputs: (a) room `t + 2ρmax²μ < s` (L6's closeness contradiction
   needs the witness time interior to the window flow; the leaf allows `t₀` arbitrarily close to the
   slab end, so an ENDPOINT form of the perturbation lemma L4 / L6 is needed: is one-sided time
   smoothness at the closed end enough for the comparison jets?), and (b) the current-slab derivative
   clause up to the current time (`Gk.DerivativeBoundBefore (2Ctime) (2qcan) t'`, `t' > t₀`), which the
   leaf supplies only before `t₀`: at `t₀ > a` a continuity argument (L10a); at `t₀ = a` (post-event
   slice) the young fresh caps go through D2, which calls the bridge at `t` — what supplies the
   derivative bound on the post-event slice (the record's standard-cap comparison at time 0?) and
   should the leaf's derivative clauses carry an age condition instead?
7. Anything false or vacuous in the files above, with a configuration.
