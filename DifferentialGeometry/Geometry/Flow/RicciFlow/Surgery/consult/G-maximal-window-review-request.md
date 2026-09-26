# Seventh review request (G): the maximal-window structure, the C4 transport, and the horn-point exclusion

Target: `liao9yuan/differential-geometry-dev`, snapshot branch `codex/pc-consult-g` (head of
`codex/pc-target-c-psf` plus every uncommitted lane file; not built, for review only). Read
`Surgery/Skeleton/DESIGN_MAXWINDOW.md` (whole), `consult/F-crossing-core-review-digest.md`,
`Surgery/Skeleton/OPUS_FILL_LOG_{B3C,B3D,B3E,B3F,B6C,B6CK,B6D,B7,SB13,SPT}.md`, `DESIGN_C4.md`,
and the Lean files they name (`Surgery/Topology/BoundedCurvatureAtDistance*.lean`,
`AncientPointedFlowLimit{Curvature,Noncollapsing,BoundedCurvature}.lean`, `TracedRegionAncientLimitData.lean`,
`TracedRegionDepthInduction.lean`, `Perelman/CanonicalNeighborhood/SpatialCanonicalWitness*Transport.lean`,
`Surgery/Contract/UniformDebitSurgeryStepOfFactory.lean`).

## State since review F

- B3c/B3d: bounded curvature at bounded distance PROVED on the final slab with the window inside it,
  bounded-threshold form, `coneAccuracy` fixed first. B6c-κ PROVED (κ/250). B6d core PROVED (each
  limit slice bounded via necks / cap tubes / compact components, Harnack across times), with the two
  transfers to the limit (spatial witnesses on limit slices; derivative clause on the limit) in progress.
- B7: local induction reaches depth `1/(2·Ctime·Q₀)` only. DESIGN_MAXWINDOW proposes the
  maximal-window structure: one diagonal contradiction sequence, a subsequence-stable maximal depth
  `T*`, the partial limit on `(−T*, 0]`, the time-zero whole-slice bound for the base case, the uniform
  bound near the finite end, extension past `T*`. It identifies B3e (the bound on an ARBITRARY slice
  through the per-point dichotomy, 2.5–5k lines, in progress) as the critical path, and M2–M7.
- S is reduced to one hypothesis (`uniformDebitSurgeryStepStrong_of_long_slabs`: a uniform lower
  bound on attached slab length), to be replaced by B13; B13's analysis says it is the Crossing core
  applied to horn points, plus a topological exclusion of cap-window points for deep horn points and a
  scalar upper bound in the cap window carried to the terminal metric.
- C3b leaf PROVED. Leaves left: S, C2×4, C3c, C4.

## Questions (Chinese, ~2000 characters, verdict table, counterexamples clause by clause)

1. DESIGN_MAXWINDOW as a whole: is the route (sequence with `Dₙ → ∞`, `θcapₙ ↑ 1`, maximal
   subsequence-stable depth, partial limit, time-zero bound, uniform bound near `−T*`, extension) the
   correct formalization of KL §80.4 / Perelman §5.4 for our objects? Are M2 (subsequence stability), M3
   (base case through the time-zero global bound), M4 (bootstrap on the partial limit via Harnack
   distance comparability + far-field bound + the limit's derivative bound) sound? Anything false?
2. B3e as designed (M1): the bound on an arbitrary slice with `¬CapWindowPoint (D, θ)` replacing the
   single-slab window, via traced regions through events and the survivor flow on which the B3c cone
   argument runs. Is the per-point dichotomy the right replacement, and what exactly must the survivor
   flow carry (κ tests at early times, pinching, the witnesses) for the cone exclusion to run on it?
3. B6d's transfers: spatial witnesses on every limit slice from the approximants' witnesses above
   `qsₙ` with bounded ratio `qsₙ/Rₙ`, transported through the `C^p` convergence per point (no
   uniformity in `n` needed), and the derivative clause on the limit from the approximants' clause: any
   trap (points of the limit slice that are limits of approximant points BELOW the threshold; the
   normalized threshold `qsₙ/Rₙ → 0` or only bounded)?
4. B13 / the horn-point exclusion: for a deep horn point `x` of the terminal presentation, the
   dichotomy gives either the traced region (then the local cone argument and the strong-neck threshold
   run on the survivor flow, yielding fine SPATIAL necks at slices `τ → s`) or a cap-window point of
   an earlier record. The B13 analysis says the exclusion of the latter is not an inequality (an earlier
   cut at scale ≈ Q gives cap-window points with `R ≈ Q` at any depth) but topological (the horn's neck
   sphere and the cap-model sphere through `x` bound the same tip side) plus a cap-window scalar
   upper bound in the terminal metric. Is that right, and what is the cleanest formal statement?
5. C4 case (B) transport after review F's corrections: with the cap radius margin real
   (`W.radius > 5000/√R`), what remains genuinely missing for the whole-witness metric-close transport
   is: a local third-order comparison for the gradient clause; the uniform production of ball-sandwich /
   depth / chart-window margins; the `ULift` interface; and the uniform reference conversion on the
   standard family at fixed `Θ < 1`. Confirm the list and the order of attack; is the gradient clause
   needed at all for C4 (the spatial witness's gradient field) or can C4's consumers take it from the
   derivative/gradient CLAUSES of the leaf instead (then the witness field could be dropped from
   `SpatialCanonicalWitness`)?
6. Anything false or vacuous in the files above, with a configuration.
