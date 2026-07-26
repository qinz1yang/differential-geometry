# DistanceBarrier.lean

## 2026-07-23 — Route B-prime analytic endpoint

- The intended public endpoint
  `scaledDist_calabiUpperSupport_of_sol` is now stated with the architecture
  ruling's complete, no-connectedness, no-injectivity-radius signature.
- Its proof remains one visible `sorry`; theorem completion is therefore 0%.
  This is intentional rather than an assumption wrapper: the theorem itself is
  the genuine geometric-analysis frontier.
- The time-direction brick is now checked.  `pathLength_timeDeriv_of_ricciFlow`
  differentiates the length of a fixed regular path using `metricDerivAt`, the
  square-root chain rule, and differentiation under the interval integral.
  `pathLength_deriv_ge` then turns a pointwise quadratic Ricci bound into
  `∂ₜ L ≥ -A L`.  Both declarations are focused-green and sorry-free.
- Exact-current prerequisites now include basepoint-free metric completeness,
  completeness transfer, the componentwise intrinsic-geodesic producer spine,
  point-pair Hopf--Rinow, and compactness of finite closed extended balls.
- Remaining proof-owned ingredients are:
  1. a smooth endpoint variation based at the midpoint of a selected minimizing
     geodesic;
  2. the quantitative fixed-metric Laplacian comparison for the resulting
     Calabi upper support.
- Expected difficulty: substantial new analysis and API assembly.  It should
  be solvable without new HCG hypotheses, but it is not a routine local Lean
  proof.

Accounting: the theorem is 0%; the selected Route B-prime producer machinery
is about 30%; the fixed-path time-variation subtheorem is 100%; the dedicated
P4 consumer machinery remains about 98%;
unconditional `compactnessSol` remains 0%; whole HCG support remains about 60%.

## 2026-07-23 — fixed-metric frontier audit

The Calabi branch-selection route is now precise.  Along a point-pair
Hopf--Rinow minimizer from `O` to `x`, choose a point `q` sufficiently close to
`x`.  Openness of the selected diagonal branch near `(x,x)`, together with
`DiagInvBranch.inv_fst_inf` and `inv_eq_of_exp`, supplies the smooth fixed-first
endpoint family from `q` to nearby endpoints.  Thus no global no-cut-locus
theorem and no pointwise chart selector is needed.

The remaining fixed-metric obstruction is narrower: the repository has no
checked theorem identifying the Laplacian of this selected radial length with
the trace `curveMean` of its transverse Jacobi family.  Existing
`curveMean_le_hyp` gives the Riccati comparison after that identification, and
the new focused-green `hypMeanCurv_le` gives the explicit
`d / r + d * q` scalar bound.  This radial Laplacian/Jacobi-trace identity must
be proved as geometry; it must not be accepted as a new input.

The local support/branch assembly and the scalar model bound are routine
supporting bricks.  They do not change the endpoint accounting:
`scaledDist_calabiUpperSupport_of_sol` remains theorem-level 0%.

## 2026-07-24 — source complete, verification performance blocker

The evolving support proof is now mathematically assembled and contains no
`sorry`, `admit`, or new axiom.  It combines the exact-current fixed-metric
Calabi provenance, closed-slab metric comparison and completeness transfer,
two fixed broken-path length variations, local gradient/Laplacian scaling, and
the final parabolic lower bound.

To avoid one giant dependent proof term, the implementation was factored into
the private data/API boundary

- `ScaledDistSupport`;
- `exists_calabi_coeff`;
- `ricci_quad_of_curv`;
- `CalabiFlowCore` and `calabi_core_of_sol`;
- `CalabiFlowCore.scale`; and
- `scaled_of_quad`.

All of these declarations elaborate without diagnostics.  The remaining
private orchestrator `scaledDist_support` still deterministically times out at
`whnf`: it exceeds the default 200000 heartbeats and also a scoped 500000
heartbeat test.  Three arrangements were tried: the original monolithic
proof, a bundled-support wrapper with fixed-time core/scale helpers, and a
separate completeness/setup boundary.  Making the arguments to
`complete_of_ricBound` and `scaled_of_quad` fully explicit did not remove the
timeout.  The public theorem then fails only because the private orchestrator
constant was not created.

This is an elaboration/kernel-normalization performance blocker, not a
mathematical or missing-API blocker.  The smallest next decision is a
Lean-native opaque/refinement boundary that prevents reduction of the
metric-instance/completeness term, or a justified narrowly scoped resource
setting if no such boundary exists.  The exact repository-specific question,
including the current helper signatures and the three failed layouts, is
recorded in
`HCGCompactness/DISTANCE_BARRIER_PERF_CONSULT.md`.

Honest accounting: `scaledDist_calabiUpperSupport_of_sol` remains theorem-level
0% until focused and exact verification pass; its dedicated source machinery
is about 90--95%.  The solution-generated barrier cutoff and trusted
complete-Shi producer remain theorem-level 0%; whole HCG supporting machinery
remains about 60%, and unconditional `compactnessSol` remains 0%.
