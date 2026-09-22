# Completed κ-solution suite — 20 September 2026

**Accepted for the four theorems below.** Their proofs, original mathematical contracts,
full project build, declaration linters, and transitive axiom closures pass.
The canonical-neighborhood/ancient-extension phase has not been started after this stopping point.
The Poincaré development as a whole still has proof debt; this handoff does not claim otherwise.

## Repository and delivery identity

- Repository: `/Users/bennettchow/Documents/Codex/wt17/ziyang`
- Branch: `codex/pc-work-2026-09-17`
- Upstream: `origin/codex/pc-work-2026-09-17`
- Remote: `https://github.com/qinz1yang/differential-geometry-dev.git`
- Resume checkpoint: `7c2e6848cb8678a932191bc810a64ecd803627ba`
- Final proof commit: **`3b12c1abf575960b58f7adca8f73c54c7ea5049b`**
  (`Prove ancient rank-one persistence and fixed universal-cover splitting`).
- Final repository commit: the documentation commit that first adds this package, immediately
  following the proof commit. Its full hash is stored in Git history; resolve it with the command
  below. A tracked file cannot contain the hash of its own containing commit.
- Delivery state: both commits pushed to the named feature branch; working tree clean.
  No uncommitted mathematical work remains. Existing conditional developments and all retained
  out-of-scope proof gaps remain in the repository.

```sh
cd /Users/bennettchow/Documents/Codex/wt17/ziyang
# Exact final handoff commit, even after later commits modify these documents:
git log --diff-filter=A --format=%H -- docs/handoffs/kappa-solutions-2026-09-20/README.md
# Current checkout, branch, upstream, and working-tree state:
git rev-parse HEAD
git branch --show-current
git rev-parse '@{upstream}'
git status --porcelain=v1
```

At delivery, HEAD equals the handoff commit and upstream, and the last command prints nothing.
The final conversation message also records the literal handoff commit hash.

## Completed theorems

All four names have the namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions`.
Line numbers refer to the final proof commit.

| Theorem | Source | Mathematical conclusion |
|---|---|---|
| `exists_backward_slice_asymptotic_shrinker` | [AsymptoticShrinker.lean:27](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/AsymptoticShrinker.lean#L27) | Backward rescaled slices along any positive escaping time sequence have a complete connected nonflat gradient-shrinker subsequential limit, with actual convergence maps and canonical metric convergence data. |
| `exists_samePole_normalized_asymptotic_shrinker` | [AsymptoticShrinkerNormalization.lean:39](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/AsymptoticShrinkerNormalization.lean#L39) | The same construction for a fixed reduced-length pole, including the reduced-length bound, nonnegative curvature operator, Hamilton-normalized potential, and convergence of reduced volume to the normalized shrinker mass. |
| `klim_terminal_curvature_trichotomy` | [TerminalCurvatureTrichotomy.lean:124](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/TerminalCurvatureTrichotomy.lean#L124) | At the genuine terminal time, a three-dimensional `KLim` is positively curved, flat, or has a `TerminalSurfaceProduct`. |
| `ancient_fixed_universal_cover_product_of_null_plane` | [AncientSplitting.lean:361](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/AncientSplitting.lean#L361) | A nonflat complete connected ancient three-dimensional flow with slab curvature bounds and a null two-plane splits on its universal cover by one fixed product diffeomorphism for every time ≤ 0. The surface flow is complete, connected, simply connected, and has positive scalar curvature. |

Each has exactly the transitive axiom closure **`[propext, Classical.choice, Quot.sound]`**.
There is no `sorryAx` in any of the four.

The two shrinker statements were generalized after the resume checkpoint by removing
`(hdim : 2 ≤ Module.finrank ℝ E)`. Their remaining binders and conclusions are unchanged.
Both original statements compile as corollaries of the current versions. The terminal trichotomy
and ancient splitting declaration texts are unchanged. Do not describe all four signatures as
literally unchanged; old positional callers supplying `hdim` must omit it.

## What closed the ancient splitting proof

The new general theorem
`DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one`
in [AncientRankOne.lean:121](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/AncientRankOne.lean#L121)
propagates curvature-operator rank one from one spacetime point to every point at every time ≤ T.
It assumes an actual complete ancient three-dimensional Ricci flow and bounds on each finite slab.
It needs neither κ-noncollapsing nor a pre-supplied product, simple connectedness, or nonflatness.
It uses a finite-dimensional normed model; proof-only instances are constructed locally.

Backward rank monotonicity and nonflatness first give rank one in the past. On the universal cover,
an initial global surface × line product is pulled back along the whole flow. Complete bounded
forward uniqueness preserves its height reflections. Fixed-point antisymmetry makes the height
harmonic; the scalar maximum principle preserves its unit gradient; Bochner rigidity makes that
gradient parallel. The resulting curvature nullity gives rank at most one forward in time.
Closedness supplies the terminal endpoint, and nonflatness excludes rank zero. The existing
fixed-product theorem then supplies one diffeomorphism for the entire ancient interval.

The headline starts with a null plane at any `t₀ ≤ 0`, including `t₀ = 0`. Endpoint trichotomy,
nonflatness, and the vanishing least eigenvalue give rank one there. No positive-time extension
or Ricci-flow equation at the terminal endpoint is assumed. The surface is not assumed compact;
the original splitting statement has no κ assumption.

## Verification and next action

The root build passed **20,143 jobs**, with **21 retained out-of-scope `sorry` warnings** and no
other diagnostics. All four headline sources, the rank-one source, and the two cylinder sources
also pass fresh elaboration. Nine declarations pass all 13 applicable declaration linters.
See [VERIFICATION.md](VERIFICATION.md) for the exact commands, contract comparison, and axiom table.

There are **21 remaining `sorry`s in 11 files**, none in `KappaSolutions`. Exactly three are
reachable from the current proof of `arbitrary_high_curvature_blowup`:
`bounded_curvature_at_distance`, `terminal_limit_global_bound`, and `ancient_extension`.
See [REMAINING_WORK.md](REMAINING_WORK.md) for the complete inventory, preserved partial work,
and the recommended next theorem.

Read [REFERENCES.md](REFERENCES.md) for toolchain, instructions, books, and attachment provenance.
[CONTINUE.md](CONTINUE.md) is the ready-to-paste prompt for a new conversation.
This delivery stops here; beginning that prompt is a separate continuation of the work.
