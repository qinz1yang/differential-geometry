# Fourth review request (D): the noncollapsing input C2 split into reduced-volume leaves

Target: `liao9yuan/differential-geometry-dev`, branch `codex/pc-target-c-psf` @ 1dfbc801f. Read
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean`
(all definitions and the assembly), `…/Surgery/Topology/CanonicalNeighborhoodInduction.lean`
(`NoncollapsedBefore`, `TerminalNoncollapsedBefore`, `NoncollapsingThroughSurgery`),
`…/Surgery/Topology/HistoryReducedDensity.lean:328` (`regularizedDensity`),
`…/Surgery/Topology/HistoryAction/AbsoluteContinuity.lean:252,266` (`regularizedActionValues`,
`regularizedCost`), `…/Surgery/Topology/HistoryMinimizingDensity.lean:415`,
`…/Surgery/Topology/HistoryAction/MinimumTime.lean:610,957`, `…/Surgery/Skeleton/OPUS_FILL_LOG_C2U.md`
(why the local upper bound could not be proved), and `…/Surgery/Skeleton/FILL_QUEUE.md` entry 22.

## What is on the branch

1. `ObservedHistory.regularMinimizerEndpoints first last hle T B v p`: endpoints `q` at time `T − v²`
   of absolutely continuous stagewise curves from `p` at time `T` that attain `regularizedCost`
   (minimal truncated L-action with scalar floor `B`) and cross every event regularly.
2. `RetainedCoreHistory.reducedVolume k p T v := limsup_{B→∞} ∫_{regularMinimizerEndpoints} regularizedDensity … dvol(stageMetric first (T − v²))`
   with `first := activeStage (T − v²)` (value `0` when `first ≤ k` fails).
3. Leaves: `HistoryReducedVolumeMonotone` (`v₁ ≤ v₂ ⇒ Ṽ(v₂) ≤ Ṽ(v₁)` for every history);
   `HistoryReducedVolumeLocalUpperBound` (`∃ C₀ > 0, ∀ η > 0, ∃ σ ∈ (0,1]`, for every history parabolic
   ball `(t, p, r)`: `Ṽ(σr) ≤ C₀/(σr)³ · vol(B(p,r)) + η`); `HistoryReducedVolumeInitialLowerBound`
   (C2's prefix, `∃ c > 0`, then for `r₀ ≤ r`: `c ≤ Ṽ(√t)`); `SmallScaleNoncollapsingThroughSurgery`
   (balls of radius `< r₀` from noncollapsing at radius `≥ r₀`). Assembly proved: `κ = min(cσ³/(2C₀), κ₂)`.
4. The worker who tried the upper bound reports: every existing mass bound needs one common flow on
   one manifold with a compact barrier; between events a history minimizer may enter a horn that the
   next event discards; no history L-exponential map or Jacobian monotonicity exists; the missing
   bricks are (a) L-exp map + Jacobian monotonicity for history geodesics through regular crossings
   with a Gaussian-tail bound, (b) confinement of `|Z| ≤ R` geodesics in the traced parabolic ball
   (Shi-type gradient bounds through crossings), (c) volume comparison of the traced ball across events.

## Questions (Chinese, ~1500 characters, table of OK / FALSE / FIX, counterexamples clause by clause)

1. Definition of `reducedVolume`: is restricting to endpoints of cost-attaining curves with regular
   crossings the right object for Perelman II 5.2 / KL §79–80 (the L-exponential domain after
   removing the "reachable only through caps" set)? Does the `limsup_{B→∞}` of the truncated action
   equal Perelman's reduced volume for compact-stage histories (scalar floor exists), and is
   `Ṽ` measurable/finite as defined? Any degenerate case (e.g. `regularMinimizerEndpoints` empty,
   `first ≤ k` failing) that makes a leaf vacuous or false?
2. `HistoryReducedVolumeMonotone` as stated (every history, no class hypotheses): TRUE? Perelman's
   monotonicity uses the Jacobian along L-geodesics and the removal of non-minimizing points; with
   surgery, KL §79 restricts to points reached by curves avoiding the surgery regions. Does our
   restriction (regular crossings at event times only; curves may otherwise wander into a horn that
   is later removed — but then the curve's future endpoint would not be in the retained stage) match
   KL's, or must the leaf also require the whole curve to lie in the retained cores (a stronger
   restriction), and does the assembly still close then?
3. `HistoryReducedVolumeLocalUpperBound`: is the statement true with `σ` independent of `r` and of
   the history, or must `σ` depend on the radius bound `ρ` (the worker suggests
   `∀ η ρ, ∃ σ`)? Is Perelman I 7.3's split (`|Z| ≤ R` geodesics stay in the parabolic ball; Gaussian
   tail for `|Z| > R`) valid across regular crossings, and what exactly must the L-exp map through a
   crossing satisfy (continuity of `γ'` across the event through the transition map, Jacobian
   continuity) for the tail bound?
4. `HistoryReducedVolumeInitialLowerBound`: is `r₀ ≤ r` the right restriction (small balls in fresh
   caps have restricted `Ṽ ≈ 0`)? Perelman goes back to time `0`: the point with `l ≤ 3/2` at time `0`
   and the initial geometry give `Ṽ(√t) ≥ c(g₀, B)`; is this uniform over the class with our
   hypotheses (derivative, gradient, canonical clauses; cap windows `hasCanonicalWindow`), and does
   the barrier (curves of cost `≤ 3√τ` cross regularly) suffice, or is a "curves avoid the cap
   windows" clause needed as well?
5. `SmallScaleNoncollapsingThroughSurgery` (radius `< r₀` from radius `≥ r₀`): Perelman handles small
   scales by the canonical-neighbourhood assumption at `R ≥ r⁻²` (necks/caps are κ₀-noncollapsed).
   With our age-restricted witnesses, which points at scale `< r₀` lack a witness, and is the leaf
   still true as stated (it is implied by C2, so truth is not in doubt; the question is provability
   from the leaves' hypotheses)?
6. Anything false, vacuous, or unprovable in `NoncollapsingThroughSurgeryLeaves.lean` that you can
   refute with a configuration.
