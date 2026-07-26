# ConvexBalls.lean — MSM135 `lbl417` (convex balls), Step A item-3b track

## Context / why

User decision (2026-06-11): un-park the §5 frontier and prove the FULL `lbl383`
item 3 (Step A's only remaining content): (3a) exp-diffeo at ball scale, (3b)
geodesic convexity of the largest balls. This file is the 3b endpoint-assembly
brick: the book's `lbl417` ("Convexity of small enough balls") given the two
analytic inputs that `GeodesicConvexity.lean`'s docstring already names:

1. a two-point minimising selector `join` (Hopf–Rinow-shaped; same black-box
   family as `exists_proper_realization`);
2. the Hessian positivity of `½ d(O,·)²` along the joining geodesics (= the
   book's `lbl416`, which follows from the S3/`lbl413` Hessian comparison — the
   plan-approved honest-input boundary).

## Mathematical route (book `lbl417`, L2386–2410)

For `a, b ∈ B(O,r)` and `γ` the minimal constant-speed geodesic `a → b`,
`f(z) = ½ d(O,z)²` has `(f∘γ)'' > 0` (lbl416), so `f∘γ` attains its max at the
endpoints; hence `d(O,γ(t)) ≤ max{d(O,a), d(O,b)} < r` and the ball is convex.

Formalized shape: with the input stated as `ConvexOn ℝ [0,1]` of
`t ↦ (riemannianEDist I O (join a b t)).toReal²` (the scalar along-curve form of
lbl416 — convexity, not strict, suffices for endpoint-max via
`ConvexOn.le_on_segment`), the conclusion `IsGeodesicallyConvexWith join
(smallNormalBall O r)` is pure 1-D calculus:
`φ(t)² ≤ max(φ(0)², φ(1)²) < r²` ⟹ `φ(t) < r` ⟹ membership. Finiteness of
`riemannianEDist` is free on connected manifolds (`riemannianEDist_ne_top`,
MinimizingGeodesic.lean — so no `≠ ⊤` input needed).

Constant discipline (book): the Step A wiring uses radii `< π/(6√C₀)` (chapter4
L1346), NOT π/(2√K) — the 1/6 gives the slack `3r < π/(2√K)` so the input
region `B(O,3r)` (everywhere the minimal join can reach, by the triangle
inequality) is inside the lbl416 validity radius. That bootstrap lives in the
input-producer brick, not here.

## Bricks (item 3 overall)

- **B1 (this file): lbl417 assembly** — `isConvexWith_smallNormalBall`.
  Inputs: selector fields (continuity/endpoints) + along-curve `ConvexOn`.
  Output: `IsGeodesicallyConvexWith join (smallNormalBall O r)`. SESSION TARGET.
- **B2: item-3a assembly** — exp-diffeo on `ball(0,r)`, `r <` inj, from
  `injOn_expMap_eball_of_lt_injRadius` (have) + a nonsingularity input
  (`mfderiv` of exp invertible on the ball) → `PartialDiffeomorph` at ball scale.
- **B3 (genuine native frontier, multi-session, shared with B0 stages 2/4):**
  the `W=∂_t` covariant commutation → exp-variation-is-Jacobi →
  parallel-frame Grönwall `J(t) ≈ tw` → (i) nonsingularity of `d(exp)` below
  `c/√C₀` (discharges B2's input) and (ii) the `lbl395` metric bounds.
- **B4: lbl416 producer** — from the S3/`lbl413` honest input (approved
  boundary) produce B1's `ConvexOn` input on `B(O,3r)`.
- **B5: wire 3a+3b into Step A** (`GoodCoveringSeq`-level: B⃗-balls convex for
  k large; charts at λ-scale) — the lbl383 item-3 endpoint.

## Status

- B1: DONE + verified sorry-free (this file, 2026-06-11):
  `isConvexWith_smallNormalBall`. Inputs needed: only selector
  continuity/endpoints + along-curve `ConvexOn` (finiteness came free via
  `riemannianEDist_ne_top`; convexity — not strict — suffices via
  `ConvexOn.le_on_segment`).
- B2: DONE + verified sorry-free (`ExpBallDiffeo.lean`, 2026-06-11):
  `exists_diffeo_of_injOn` (generic injective-local-diffeo glue, a Mathlib TODO)
  + `exists_expBall_diffeo` (item 3a with `hloc` nonsingularity input;
  injectivity discharged from `injRadius`).
- **B3 — RESOLVED 2026-06-13, item-3a NOW COMPLETE & UNCONDITIONAL.** The whole
  Jacobi/Grönwall nonsingularity tower was UNNECESSARY for `hloc`: the repo already
  has exp as a `PartialDiffeomorph` via normal coordinates
  (`NormalCoordinates.expMapDiffeo`), whose source contains the ball
  (`ball_subset_normalChartAt_target` + `normalChartAt_target_eq`) and equals exp on
  it (`expMapDiffeo_apply_eq`). New `ExpBallDiffeo.lean:exp_isLocalDiffeomorphOn_ball`
  (~15 lines) discharges `hloc` from this for `r ≤ expMapC2Radius`; new
  `exists_expBall_diffeo_of_lt` is the UNCONDITIONAL item-3a producer (no Jacobi
  input). 6th "search-before-walls" lesson — `mfderiv_expMap_injective_of_norm_lt_radius`
  (GaussLemma, found while scoping the manifold-IFT brick) pointed at expMapDiffeo.
  The B3 Jacobi/Grönwall bricks (keystone `covGronwall_ne_zero`, `ExpNonsingular`,
  the ∞→N refactor) remain valid reusable analysis but are OFF the item-3a path
  (still relevant to Step B's `lbl395` metric bounds).
- B3 (NATIVE FRONTIER, multi-session, B0-shared): CORRECTION 2026-06-11 — the
  old "W=∂ₜ commutation missing" gate is STALE: `commute_ds_dt_curvature` exists
  (de-privatized 2026-06-10) and B0 **stage 2 is fully done**
  (`Exponential/JacobiVariation.lean`: Jacobi eq on `(0,1)`, ICs `J(0)=0`,
  `D_tJ(0)=w`, endpoint `J(1)=d(exp_p)w`). TRUE remaining gate = B0 stage 4 base:
  (a) parallel-frame expansion rule: **CORE DONE 2026-06-11, green** —
  `Connection/ParallelTransport/CovariantDerivativeAlong.lean`: `chartRepAt_sum`,
  `covDerivAlong_sum` (Finset linearity), **`covDerivAlong_expand`**
  (`D_t(Σ yᵢ•Fᵢ) = Σ yᵢ'•Fᵢ` for `D_tFᵢ = 0` at the point; second order = apply
  twice with `y := deriv yᵢ`, no new lemma). REMAINING in (a): coefficient
  extraction `yᵢ := g.inner(J,Fᵢ)` + its differentiability (needs metric
  compatibility along curves — cf. `chartGramAlongCurve_hasDerivAt_zero_of_parallel`)
  + the pointwise ℓ²-norm identity at a g-ON frame (cf. the F4-track
  `exists_gOrthonormalBasis` fiber machinery);
  (b) curvature-norm input `‖R(J,γ')γ'‖_g ≤ C₀‖γ'‖²‖J‖_g`;
  (c) zeroth-order Grönwall: **DONE 2026-06-11, green** —
  `Analysis/ODE/SecondOrderGronwall.lean:gronwall_sub_linear` + `gronwall_ne_zero`;
  (c') **KEYSTONE DONE 2026-06-11, green: `Variation/CovariantGronwall.lean:
  covGronwall_ne_zero`** — covariant ODE bound + parallel full ON frame + ICs +
  smallness ⟹ `J b ≠ 0` (see its same-name `.md`; uses (a)+(c)+InnerExpansion);
  (d) manifold IFT at `v ≠ 0` (mimic `LocalDiffeomorphism.lean`'s at-zero
  construction; also a Mathlib TODO) ⟹ B2's `hloc`.
  (c'') **frame producer DONE 2026-06-11, green: `PerpFrame.lean:
  exists_parallel_frame`** — parallel transport of any `g`-ON seed family along
  any smooth curve stays ON on `[0,L]` (no geodesic/unit-speed needed; arbitrary
  index; supplies covGronwall's `F`/`hpar`/`hON`/`hFdiff` wholesale).
  REMAINING: the radial-Jacobi instantiation of (c') [curvature-norm input (b),
  J/D_tJ regularity plumbing, the t=0 ε-shift (Jacobi eq only on `(0,1)`)]
  and (d).
- B4 (lbl416 producer): not started. DESIGN CHOICE pending: the faithful
  `lbl413` honest-input statement needs scalar-Hessian-of-distance plumbing
  (S1/S2: ∇d², Hess d² as repo objects) that does not exist yet; the
  scalar-along-curve form would essentially restate B1's input (thin-wrapper
  risk). Decide the S1/S2 interface first in a fresh session.
- B5 (Step A wiring): not started; consumes B1–B4 at the `GoodCoveringSeq`
  layer (B⃗-balls convex for k large, charts at λ-scale).

## Verification

B1 + B2 focused checks passed (sorry-free, warning-clean).

## 2026-07-14 selector closure and exact comparison blocker

The two-point selector is no longer a black-box item.  The focused-green
`GeodesicConvexity.minJoin` uses the unconditional intrinsic Hopf--Rinow
minimizing-vector theorem and supplies length, endpoints, and time continuity.
Consequently B4 should not add another selector input or a synonymous join API.

The first missing reusable theorem is now the public, germ-local `lbl412`
identity expressing `hessFun g (halfSqDist pt)` through the covariant derivative
of the selected moving inverse.  After that, the genuine `lbl413` theorem must
give a uniform positive Hessian lower bound on the larger bootstrap cage.  Its
along-`minJoin` corollary supplies both confinement (take target `p`) and strict
convexity (take each active target point).  `SecondVariationMinimiser` only gives
index-form nonnegativity, so it cannot close this strict estimate by itself.

The `lbl417` assembly theorem in this file remains checked, but the actual B4
producer is theorem-level 0%.  Its dedicated machinery is at the foundational
Hessian/variation stage; no new endpoint-radius field or C4 wrapper should hide
that frontier.
