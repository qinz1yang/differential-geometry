# `ham3_main` black-box audit and fill plan

## Live correction (2026-07-14, post merge)

The live source now has four theorem-body sorries in
`HamiltonPositiveRicci.lean`, not five:
`ham3_flow_exists_normalized`, `ham3_noncollapse`, `ham3_cgh_limit`, and
`ham3_space_box`.

The frontier-1 Hamilton adapters `ham3_short_isSolution` and
`ham3_short_smooth_solution` are implemented using the merged short-time
theorem and `solutionOn_of_joint`. Their theorem bodies are 100%. The
unconditional short-time theorem is not yet certified axiom-clean on the live
post-merge source: `ShortTime/WeylEigenvalueCountingBound.lean` contains the
pointwise local-Weyl `sorry` explicitly documented as lying on that dependency
closure. Until a fresh axiom probe after the current Spectral rebuild says
otherwise, strict completion of the unconditional theorem is 0%.

The extension consumer
`extends_of_rmBounded` is assembled; its own body is sorry-free. Its live axiom
path previously had three inputs. The moving-Shi input is now discharged by
the checked, axiom-clean `movingShiBoundSol`, so only uniform low-regularity
existence `(N)` and smooth forward uniqueness `(B)` remain upstream of the
extension theorem.

The post-merge API audit in `../SHORTTIME_MERGE_PLAN.md` shows that neither
remaining input is a local adapter. `(N)` needs a quantitative low-regularity
DeTurck theorem uniform under ellipticity and C3 bounds; the current
high-Sobolev engine's explicit time also depends on a high-Sobolev norm of
`Nfun 0`. `(B)` needs the missing harmonic-map heat-flow gauge plus a reverse
strong-solution realization before the existing forcing-space uniqueness
theorem applies.

Strict endpoint accounting: `ham3_flow_exists_normalized`, `(N)`, and `(B)`
are each 0%. The maximal-flow and restart/glue machinery around them does not
count toward those theorem percentages.

There is also no live producer constructing a maximal compatible Ricci-flow
family from the short-time solutions. `MaximalTime.lean` defines
`IsMaximalAtEndpoint` and proves that a finite maximal flow has unbounded
curvature, but every such theorem consumes an already supplied solution and
maximality proof. Therefore `ham3_flow_exists_normalized` still needs a genuine
maximal-interval construction: use forward uniqueness to order and glue local
solutions, take the supremal time, prove maximality, use the positive-scalar
finite-time estimate, and then invoke the curvature-unboundedness theorem.
This is separate from proving `(N)` and `(B)` themselves.

Written 2026-07-05 and live-updated 2026-07-14. The original scope was seven
theorem-shaped `sorry`s behind the assembled Hamilton positive-Ricci endpoint
plus one `MaximalTime.lean` frontier. Three original Hamilton boxes are now
closed: `ham3_short_isSolution`, `limit_to_orig`, and
`spaceForm_const_metric`. Four theorem-shaped `sorry`s remain in
`HamiltonPositiveRicci.lean`; the extension theorem is assembled but still
depends transitively on the two analytic inputs `(N)` and `(B)`.
Companion program document: `../POINCARE_PLAN.md` (the two Perelman boxes are
shared infrastructure with the Poincaré program — fill them once, in the shape
that program needs).

Status legend for "difficulty": **S** = assembly against existing in-tree
machinery; **M** = new theorem layer, no new foundations; **L** = new
foundational layer required.

## Original eight frontiers (six remain open)

| # | Frontier | What it is mathematically | Difficulty | Fill route (summary) |
|---|---|---|---|---|
| 1 | `ham3_short_isSolution` | short-time existence: raw DeTurck data → `IsSolutionOn` bridge | adapter body 100%; unconditional short-time theorem 0% pending local-Weyl dependency discharge | merged theorem + `solutionOn_of_joint`; remove or prove the live pointwise local-Weyl dependency, then rerun the axiom audit |
| 2 | `ham3_flow_exists_normalized` | maximal continuation with finite-time curvature blow-up | L; endpoint 0% | prove `(N)`/`(B)`, construct the maximal compatible solution family, then consume finite-time and curvature-unboundedness theorems |
| 3 | `extends_of_rmBounded` (`MaximalTime.lean`) | bounded `Rm` on `[0,T)` ⟹ extension past `T` | M/L; unconditional endpoint 0% | consumer assembly and moving-Shi producer are checked; only `(N)` uniform low-regularity existence and `(B)` forward uniqueness remain |
| 4 | **`ham3_noncollapse`** | **Perelman no-local-collapsing** at the blow-up scale | **L; endpoint 0%** | actual balls, two-way scale transfer, `ham3_rm_control`, and `ham3_noncollapse_of` are checked; only the original-flow analytic producer remains |
| 5 | `ham3_cgh_limit` | Hamilton–CGH compactness of the rescaled flows | M/L; **endpoint 0%**, whole-HCG machinery ≈45% | = the HCG compactness project (`../HCGCompactness/PROJECT_MAP.md`); keep machinery and endpoint accounting separate |
| 6 | `limit_to_orig` | compact limit globalizes the CGH maps and transfers the constant-curvature metric back | **CLOSED, theorem 100%** | Bonnet--Myers + `PointedConvergenceGlobal` + metric pullback; §3 |
| 7 | `ham3_space_box` | closed 3-manifold with a constant-positive-sectional metric is a spherical space form (Killing–Hopf + quotient) | M/L | space-form lane (active; `spaceform-hardroute-build` memory) |
| 8 | `spaceForm_const_metric` | a spherical space form admits a constant-curvature metric | **CLOSED, theorem 100%** | checked quotient-round-metric construction |

Everything else on the `ham3` chain — pinching §9/§10, point selection, blow-up
window bounds, the limit-side Einstein/constant-curvature argument, #6, and #8 — is
**checked** (see `IMPORTANT_THEOREM_INDEX.md`, "HamiltonPositiveRicci main
chain"). Thus `ham3_main` still depends on four open Hamilton boxes, with the
maximal-flow box additionally depending on `(N)` and `(B)` upstream. Checked
consumers do not reduce an open producer endpoint above 0%.

## §1 Short-time + extension (frontiers 1–3)

Frontier 1's Hamilton adapter is closed; unconditional short-time theorem status
is pending the fresh axiom audit described above. `MaximalTime.lean` has no
source-level sorry in `extends_of_rmBounded`, and
`ExtendShiInputs.movingShi_of_soln` is now backed by the checked, axiom-clean
`movingShiBoundSol`. The unconditional extension route
still depends on the two sorries in `Evolution/ExtendViaUniqueness.lean`:
`ricci_flow_unif_existence` `(N)` and `ricci_flow_forward_unique` `(B)`. See
`../SHORTTIME_MERGE_PLAN.md` and `Evolution/ExtendViaUniqueness.md` for the
post-merge API audit and exact missing producers.

## §2 `ham3_noncollapse` — the Perelman box (the real subject)

### What exactly is assumed

`Ham3Noncollapse P Q hsel κ r₀`: along the blow-up sequence, the genuine
`FlowMetricBall`s in the actual `paraSolution` are `κ`-noncollapsed at scale
`r₀`.  `ham3_rm_control` is checked and supplies `IsRmControlled` on those
balls from `ham3_rm_bound` plus `Ham3Window`; no arbitrary numeric-volume or
`Ham3BallPair` wrapper remains.
So the box is exactly: *closed 3-manifold, Ricci flow on `[0,T)`, `T < ∞`,
curvature control near the singular time ⟹ κ-noncollapsed at comparable scales*
— Perelman's no-local-collapsing theorem, applied along `Q`.

### What is already in-tree (better than expected)

* **Riemannian volume + integration are NOT missing**:
  `Analysis/Integration/Measure/RiemannianMeasure.lean` +
  `riemannianVolumeMeasure` (`Invariance.lean:423`), divergence theorem
  (closed + boundary + Green), integration by parts, L² layer, `VolumeVariation`,
  `JacobiFormula` — the whole `Analysis/Integration` tree is **0-sorry**.
  `Analysis/Integration/Measure/Scaling.lean` now also proves the canonical
  constant-scaling law `dμ_(c g) = sqrt(c)^n dμ_g`, including its setwise form.
  (The HCG honest-input notes say "Mathlib has no Riemannian volume" — true of
  Mathlib, no longer of this project.)
* **The parabolic scale-transfer lane is complete**:
  `Geometry/Metric/DistanceScaling.lean` proves metric-distance and ball-carrier
  scaling; `Perelman/ScaleTransfer.lean` proves two-way carrier, volume,
  curvature-control, kappa, below-scale, and `NoLocalCollapsing` transfer.
  `ham3_radius_event` and `ham3_noncollapse_of` then check the exact downstream
  implication from original-flow `NoLocalCollapsing` to `Ham3Noncollapse`.
* **The W-entropy layer is started**: `Entropy/Defs.lean` has `wFunctional`
  (over a supplied measure), scale/diffeomorphism invariance, first-variation
  interfaces; `Entropy/FirstVariation.lean` + `Entropy/F/` (9 files, incl.
  `Formula510Core`, `Final`) are building the F-functional variation formulas.
  `Entropy/ConjugateHeat.lean` now proves local and interval total-mass
  conservation for any smooth solution of `∂ₜu = -Δu + Ru`; construction of
  such a positive solution for the moving metric remains the A1 frontier.
* Maximum principles: `MaximumPrinciple/ScalarWeak.lean`, `TensorWeak/`.

### Route decision

**Route A — W-entropy (Perelman §4).**  Chain: F/W first variation (in
progress) → W-monotonicity along the flow coupled to the **conjugate heat
equation** → log-Sobolev at small scales ⟹ volume lower bound (ε-regularity
step) → κ along `Q`.  Missing pieces, in order:
1. `A1` conjugate-heat existence: linear scalar parabolic existence/uniqueness
   on a closed manifold, coefficients from a smooth metric family.  **The only
   L-grade item on this route** — and it overlaps the DeTurck/ShortTime linear
   theory and the Weyl/spectral bricks already being built.  (~2–4 months.)
2. `A2` W-monotonicity: the Perelman integrand computation — pure tensor
   calculus + integration by parts, both native strengths of this tree; the
   Entropy lane's 5.10-family formulas are exactly its middle.  (~2–3 months.)
3. `A3` Euclidean log-Sobolev input + comparison (either prove the Gaussian
   log-Sobolev natively or take it as a clearly-cited analytic input at first;
   it is a self-contained ℝⁿ fact).  (~1 month as input, ~2–3 to prove.)
4. `A4` ε-regularity conversion: `W`-lower-bound + curvature bound on the ball
   ⟹ volume ratio lower bound (test-function argument).  (~1–2 months.)

**Route B — L-length / reduced volume (Perelman §7, Morgan–Tian Ch 6–8).**
No parabolic PDE existence needed (its monotonicity is pointwise Jacobian
comparison along L-geodesics), but requires a whole parallel geometry layer:
L-geodesics, L-exponential, L-Jacobi fields, monotonicity of reduced volume
with the measurable cut-locus bookkeeping.  (~8–12 months standalone.)
**This layer is MANDATORY for the Poincaré program anyway** (the surgery-stable
noncollapsing of Morgan–Tian Ch 16 is L-length-based; the W-route does not
survive surgery).

**Recommendation (decide before starting):** fill `ham3_noncollapse` by
**Route A** — it is the shortest path to closing `ham3_main` (its one hard item
A1 is shared with the active short-time lane, and A2 continues an existing
lane), and it does not waste work: W-entropy is independently on the Poincaré
list (M–T uses it nowhere essential, but the F/W layer already exists and A1
is needed by the standard solution and extinction phases regardless).  Build
Route B when the Poincaré program's Phase P2 starts (see `POINCARE_PLAN.md`);
do NOT build it merely for `ham3`.

Total for `ham3_noncollapse` via Route A: **≈ 6–10 months of sessions**, of
which A1 is the pole.  This is the second-longest pole of `ham3_main` (the
longest being #5 = HCG compactness, both in flight conceptually).

## §3 `limit_to_orig` (frontier 6) — CLOSED 2026-07-09

Content: the blow-up CGH limit `(N, g_∞)` of rescalings of a fixed closed `M`
is diffeomorphic to `M`, so the constant-curvature metric transfers.  The implemented route is:
constant positive curvature ⟹ (Bonnet–Myers, in-tree `Comparison/BonnetMyers`)
`N` compact ⟹ in pointed-CGH convergence with compact limit, the comparison
maps are eventually **global** diffeomorphisms `N → M_k = M` (the exhaustion
stabilizes: `K = N` is compact); pull `g_∞` back.  The reusable producers are
`PointedRiemannianManifold.compact_of_ricci` and
`PointedCGHMaps.exists_source_univ` / `target_univ` / `globalDiffeomorph` in
`HCGCompactness/PointedConvergenceGlobal.lean`.  `limit_to_orig` now consumes
the retained CGH maps, source-to-original diffeomorphisms, and slice
completeness, and is checked with no `sorry` (**theorem 100%**).  This closes
only the consumer; `ham3_cgh_limit` remains 0%.

## §4 Space forms (frontier 7 open; frontier 8 closed)

`spaceForm_const_metric` is checked (S³ curvature + quotient route).
`ham3_space_box` (Killing–Hopf direction) is the harder half: constant-curvature
simply-connected complete ⟹ isometric to the round sphere, then deck-transform
quotient bookkeeping.  Keep #7 in that lane; `ham3_main` cannot close without
it, and it is pure global geometry (no flow content), so it parallelizes with
§1–§2.

## Critical path to `ham3_main`

```
short-time lane (§1: #1)         ──┐
extension lane  (§1: #2,#3)      ──┤
W-entropy NLC   (§2: #4, poles A1)─┼──→  ham3_main
HCG compactness (#5; endpoint 0%,
  machinery ~45%)                ──┤
space-form lane (#7)             ──┘
```
Four parallel lanes; the two poles are **#5 (HCG)** and **#4/A1 (parabolic
existence)**.  Honest estimate for `ham3_main` fully sorry-free:
**12–20 months** at current velocity, dominated by those two poles.

## Status log

- 2026-07-05: audit written.  `ham3_main` assembled and checked modulo the 8
  frontiers; `ham3_noncollapse` route decision (A vs B) is OPEN for the user —
  recommendation: Route A.
- 2026-07-09: `ham3_rm_control` landed on genuine `FlowMetricBall`s;
  `ham3_noncollapse` remains 0%.  `PointedConvergenceGlobal` and
  `limit_to_orig` landed and are checked (frontier #6 closed, theorem 100%);
  `spaceForm_const_metric` is checked (frontier #8 closed).  `ham3_cgh_limit`
  remains 0%; whole-HCG machinery is conservatively about 45%, with HCG
  endpoints still 0%.
- 2026-07-09 interface audit: `ham3_noncollapse` and `ham3_cgh_limit` now retain
  the finite maximal-time interval.  `Ham3CompactInput` keeps the raw rescaled
  curvature bound, common window, kappa, and geometric noncollapse, while
  `Ham3SourceRealizes` ties the CGH source metrics and basepoints to the actual
  selected rescalings.  The refactor and public umbrella are checked; both
  producer theorems remain 0%.
- 2026-07-09/10 W-route: `conj_heat_mass_deriv`, `conj_heat_mass_eq`, time
  reversal, `IsHeatPotOn`, `heat_pot_nonneg`, `TimeSobolev.timeOp`, the abstract
  `nonaut_strong_exists`, and the interval-local volume variation
  `first_var_local` are checked supporting bricks.  A1 existence remains 0%;
  dedicated analytic no-local-collapsing machinery is about 25%, while
  `ham3_noncollapse` itself remains 0%.  The next mathematical producer is the
  support-independent fixed-`gT` `H2 -> L2` estimate for the actual
  `Delta_(g_s) - Delta_(gT)` action.  A separate build-performance blocker in
  `nablaRSFun_eval_moving_raw` currently prevents refreshing the focused-checked
  scalar Laplacian bridge; both consult frontiers are recorded in the relevant
  same-name notes.
- 2026-07-09 scale transfer complete: `volume_scaleMetric`,
  `volume_scale_apply`, `edistOf_scale`, and `edistBall_scale` are checked.
  `ScaleTransfer.lean` proves two-way invariance of the real ball predicates and
  transports `NoLocalCollapsing`; `ham3_noncollapse_of` checks the final
  downstream Hamilton adapter.  This sublane is 100%.  The theorem
  `ham3_noncollapse` stays 0% because original-flow analytic no-local-collapsing
  remains unproved.
- 2026-07-14 BBS alternate endpoint route: G3 `exists_endMetric` and G4
  `ricci_tendsto_left` are individually proved; G4 is targeted-exported and
  axiom-clean. The combined `cinftyLimitData_of_allMBounds` source has no local
  `sorry`, but remains theorem 0% because its focused check is blocked before
  elaboration by the missing active-Spectral `GalerkinLimitUniformMass` object.
  This route is not consumed by live `extends_of_rmBounded`, so it contributes
  no percentage to `(N)`, `(B)`, `ham3_flow_exists_normalized`, or any of the
  four open Hamilton endpoints.
