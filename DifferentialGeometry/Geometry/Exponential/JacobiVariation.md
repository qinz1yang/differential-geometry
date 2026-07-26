# JacobiVariation.lean — radial expMap variation is a Jacobi field (B0 stage 2)

Goal: `exists_radial_jacobi_radius` — around every `p` a radius `r > 0` such that
for `‖x‖, ‖w‖ < r` the field `J v = ∂ₛ|₀ expMap g p (v•(x+s•w))` satisfies
`IsJacobiAt g γ J t₀` along `γ v = expMap g p (v•x)` for every `t₀ ∈ (0,1)`.
This is MSM135 Ch.4 / B0 stage 2 (see `HCGCompactness/B0NormalCoordBounds.md` for
the whole-route spec and status).

## Route (decided 2026-06-10)

- The W=∂_t covariant commutation `[∇_s∇_t − ∇_t∇_s](∂_t f) = R(∂_s f, ∂_t f)∂_t f`
  at `s = 0` ALREADY EXISTED: `commute_ds_dt_curvature`
  (`Comparison/Variation/CovariantCommutationCurvature.lean:759`) — it was `private`
  and unused.  De-privatized (visibility-only edit; file + targeted build verified).
  Do NOT re-prove it; its `houterL`/`houterR` hypotheses are the intended inputs.
- It needs a GLOBAL `IsSmoothVariation` (degree-8 `ContMDiff` on ℝ²).  The radial
  variation is globalised by clamping BOTH parameters with
  `exists_smooth_clamp` (`Analysis/Calculus/SmoothClamp.lean`, NEW, verified):
  a `C^∞` bounded clamp that is the IDENTITY on `[a,b] ∋ [0,1]` (bump-integral).
  Degree-8 expMap regularity on a small ball: `Exponential.expMap_contMDiffAtN_of_norm_lt`.
- `houterL` discharge: the inner field `s ↦ ∇_t∂_t F(s,·)|t₀` vanishes identically
  (clamped slices satisfy the geodesic equation at interior parameters —
  `clamped_slice_covDeriv_velocity_zero`, via
  `radial_hasGeodesicEquationAt_of_norm_lt_radius` + rescale +
  `HasGeodesicEquationAt.congr_of_eventuallyEq_at` +
  `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2`).
- `houterR` discharge: pointwise symmetry `commute_ds_dt_intrinsic` (∀v) +
  `variationField_covDeriv_chartRep_differentiableAt` (public, CovariantCommutationCurvature:1187).
- Transfer clamped → clean radial objects by germ congruence:
  `covDerivAlong_congr_curve` (NEW here: curve+section eventual congruence, stated
  E-valued so no dependent-type motive issues), `Filter.EventuallyEq.mfderiv_eq`,
  and `riemannOp_congr_point` (subst-based point transport with E-valued slots).

## Status

- 2026-06-10 (later): **stage 2 FULLY DONE.** Added the second initial condition
  **`exists_radial_jacobi_deriv_radius`** (`D_t J(0) = w`), VERIFIED GREEN, plus the
  reusable **`covDerivAlong_const`** (covariant derivative along a constant curve =
  ordinary derivative). De-privatized `radialCurve_launch_velocity` in
  `GaussLemmaPullback.lean` (visibility-only; olean rebuilt). Route: at `t = 0` the
  transverse curve `s ↦ F s 0` is constant `p` (clamped launch radius `ψ 0 = 0`), so
  `commute_ds_dt_intrinsic` turns `D_t J(0)` into the constant-curve covariant
  derivative of the launch field `s ↦ x + φ(s)·w`, which is the ordinary deriv
  `φ'(0)·w = w`. The two `covDerivAlong_congr_curve` transfers (RHS→clean, LHS→const)
  reuse the same clamped `F` setup as the main theorem (duplicated inline; see
  "future cleanup" below).
- 2026-06-10: **`exists_radial_jacobi_radius` VERIFIED GREEN**, plus the endpoint
  lemmas **`radial_jacobi_zero`** (`J 0 = 0`) and **`radial_jacobi_one`**
  (`J 1 = mfderiv (expMap g p ·) x w`) — file lint-clean, zero warnings.
  SmoothClamp + JacobiField (`IsJacobiAt` pointwise predicate added) green.
  De-privatized `commute_ds_dt_curvature` green; the FULL downstream chain
  (SecondVariation, RegularParameterFirstVariation, GaussLemmaPullback, the whole
  Exponential tree) rebuilt green against it — the visibility change is
  downstream-safe (the private name had no users).
- First-check error patterns worth remembering: `expMap` lives in namespace
  `…Riemannian.Exponential` (NOT bare `…Riemannian`, unlike `expMapC2Radius`) —
  needs the file-level `open`; the `@[simp] covDerivAlong_zero` did not fire
  through `simp` against a β-annotated zero section (`(0 : TangentSpace I ((fun
  s' => F s' t₀) s))`) — `exact covDerivAlong_zero …` with explicit curve closes
  it; two `rw`-chains ended at syntactically reflexive goals that auto-rfl did
  not close — append explicit `rfl`.
- What WORKED first try (the risky parts): the E-valued curve+section congruence
  `covDerivAlong_congr_curve` (subst-helper for mixed-foot
  `continuousLinearMapAt` rewrites; `show`-from-by-rw for the `symmL` CLM
  equality), the `riemannOp_congr_point` subst helper with model-space slots,
  `Filter.EventuallyEq.mfderiv_eq` across propositionally different feet, the
  degree-8 `IsSmoothVariation` from clamps + `expMap_contMDiffAtN_of_norm_lt`
  (cast via `exact_mod_cast`), and the full `commute_ds_dt_curvature`
  application with both houter dischargers.

## Remaining (after stage 2)

- `g_{ij}(x) = ⟨J_i, J_j⟩(1, x)` metric pullback identification: now essentially a
  one-liner from `radial_jacobi_one` (rewrite `mfderiv (expMap g p ·) x eᵢ` to
  `Jᵢ(1)` in both slots of `g.inner (expMap g p x) · ·`); deferred until the
  component/normal-chart API is in play downstream (avoid a content-free wrapper).
- **Stage 4** (the real mass): pull `J` back through a parallel orthonormal frame
  `P_{t,x}` to `Y = P⁻¹J` solving `Y'' + A Y = 0`, `‖A‖ ≤ C₀|x|²`; ICs `Y(0)=0`,
  `Y'(0)=w` are exactly `radial_jacobi_zero` + `exists_radial_jacobi_deriv_radius`;
  differentiate in `x`, Grönwall (`norm_le_gronwall_secondOrder`), conclude
  `|∂^α g_{ij}| ≤ C̃_α`. Stage 3 (parallel frame) is `Comparison/Variation/
  ParallelTransport.lean` (exists, 0-sorry) modulo x-smoothness if stage 4 needs it.
- note: the Jacobi equation is proved on `Ioo 0 1` only (rescale identity lives on
  `Icc 0 1`); the Grönwall stage can start from `[ε, 1]` + continuity, or the
  rescale lemma can be strengthened later.

## Future cleanup

- `exists_radial_jacobi_radius` and `exists_radial_jacobi_deriv_radius` both inline
  the same clamped-variation setup (clamps `ψ`/`φ`, radius `δ/26`, `F`, `hFsmooth`,
  the window agreements `hcentral_eq`/`hJ_eq`). Factor a private
  `exists_radial_clamped_variation` helper returning `F` + those facts and have both
  consume it. Deferred to keep the green proofs untouched while the route settled.
- `covDerivAlong_const` is general enough to live in
  `Connection/ParallelTransport/CovariantDerivativeAlong.lean` (next to
  `covDerivAlong_zero`); kept local for now (surgical, one consumer).

## Lean lessons (this file)

- `expMap` is in namespace `…Riemannian.Exponential`; `expMapC2Radius` in bare
  `…Riemannian` — both opens needed.
- The β-reduced foot problem: `mfderiv_comp`-family conclusions β-reduce
  `(fun s => x + s•w) 0` to `x + 0•w`, which `rw` cannot match against the
  written form, and numerals in CLM-argument slots elaborate at the
  `TangentSpace` synonym type (different `OfNat` path than `(1 : ℝ)`), so `rw`
  by an applied-CLM equation can silently fail to find the pattern.  Robust
  pattern: build the chain with `have`-pinned statements + `Eq.trans` /
  `congrArg (fun L : E →L[ℝ] E => L w)` (defeq-tolerant `exact`s), and
  transport CLM feet with an `E →L[ℝ] E`-ascribed equation proved by
  `rw [hfoot]`.
- `mfderiv_comp_apply` needs `(f := …) (x := …)` named args (higher-order
  unification cannot invert `(f x)`).
- `simp` may refuse (`no progress`) on `(smulRight 1 w) 1 = w` — use the gauss
  pattern `change` + `rw [smulRight_apply, one_apply, one_smul]`.

## NEXT BRICK (2026-06-11, B3 regularity export — blueprint for continuation)

Goal: export, for the CLEAN radial objects (`γ v = expMap p (v•x)`,
`J v = ∂ₛ|₀ expMap p (v•(x+s•w))`), the chartRep-differentiability needed by
`covGronwall_ne_zero` (`Variation/CovariantGronwall.lean`):
`hJdiff`/`hDJdiff` : ∀ t ∈ Icc 0 b (b < 1), DifferentiableAt ℝ (chartRepAt γ J/DJ t) t.

Route (all machinery exists; mimic `exists_radial_jacobi_radius`'s transfer):
1. Rebuild the clamped variation `F s t = expMap p (ψ t • (x + φ s • w))` with
   the same norm budget (δ/26); `hJ_eq`-style: clean J = clamped ∂ₛF on the open
   window `Ioo (-1) 2` ⊇ Icc 0 b (germ argument at each v: `hgerm` +
   `mfderiv_congr_of_eventuallyEq`-style as in the file).
2. Clamped `∂ₛF`'s chartRep-diff at each t: `slice_transverseVelocity_chartRep_…`
   / the `chartCoord_transverseVelocity_contDiffAt` C² lemma
   (CovariantCommutationCurvature.lean) at the slice `s = 0`, any `t`.
3. Transfer by `chartRepAt_eventuallyEq_of_eventuallyEq` (ParallelTransport.lean:939)
   + `Filter.EventuallyEq.differentiableAt_iff`.
4. Same for `DJ = covDerivAlong γ J`: clamped counterpart's diff =
   `variationField_covDeriv_chartRep_differentiableAt` (CovariantCommutationCurvature
   :1193, check it is t-general); equality of fields on the window from `hDJ_ev`
   (in-file pattern) + `covDerivAlong_congr_of_eventuallyEq` (ParallelTransport:948).
5. ALSO export `hODE`-side: `D²J(0) = 0` (the t=0 Jacobi-equation endpoint) —
   needs continuity of `D²J` at `0` (NOT yet available; if hard, leave as the one
   hypothesis and document).

Consumers after this brick: instantiate `covGronwall_ne_zero` with
`exists_parallel_frame` (PerpFrame) seeds from `exists_gOrthonormalBasis`,
ICs `radial_jacobi_zero` + `exists_radial_jacobi_deriv_radius`, hODE from
`exists_radial_jacobi_radius` (Ioo 0 1) + curvature-norm input + the t=0 point,
endpoint `radial_jacobi_one` ⟹ `d(exp)_x` injective below the Grönwall scale.
Then (d) the manifold IFT at `v ≠ 0` ⟹ `IsLocalDiffeomorphOn` ⟹
`exists_expBall_diffeo`'s `hloc` (Step A item 3a complete modulo B4/B5).

### Brick progress (2026-06-11, live)
- Step A DONE: `chartCoord_transverseVelocity_contDiffAt` de-privatized
  (CovariantCommutationCurvature.lean, visibility-only, re-verified green).
- Step B IN PROGRESS: the regularity-export theorem in JacobiVariation.lean.
  Historical claim token `bca77123-4994-4b4b-88ce-d9c5b2bc4953` was released;
  do not treat it as active.

### OBSTRUCTION discovered (2026-06-11, before writing the export theorem)

The instantiation plan hits a smoothness-ORDER mismatch:
- `exists_parallel_transport_on_Icc` / `exists_parallel_frame` demand
  `hγ : ContMDiff 𝓘(ℝ,ℝ) I ∞ γ`;
- the radial curve's smoothness comes from `expMap_contMDiffAtN_of_norm_lt`
  (OffZero.lean:994) — per FINITE order `n` with an `n`-DEPENDENT radius `δ(n)`;
  no `∞`-order statement on a uniform ball exists, and the clamped variation is
  only `IsSmoothVariation` (degree 8).

Resolution options (design choice for the next session):
1. **Weaken the transport producers to finite order** (recommended first check):
  inspect what order `exists_parallel_transport_on_Icc`'s PROOF actually
  consumes (parallel-transport ODE plausibly needs only low order, ≤ 8);
  changing `∞` to that order in the hypothesis is a statement-strengthening
  (more general) edit, then the clamped/clean curves qualify.
2. Prove `expMap` is `ContMDiffAt ∞` on a uniform small ball (true — geodesic
  flow is `C^∞`; the per-`N` radius is a construction artifact) — bigger.
3. Build an order-8 variant of the frame producer.
Status: regularity-export theorem NOT started (obstruction precedes it);
no `sorry` introduced anywhere. Claim on JacobiVariation.lean RELEASED.

### Resolution-1 recon (2026-06-11, order audit of the transport chain)

`hγ : ContMDiff … ∞` is consumed in the chain ONLY as:
- `hγ.continuous` (chart preimages, overlap consistency) — order-free;
- ONE composition `hφ.comp hγ.contMDiffOn` (exists_piece_parallel_section,
  the chart-curve regularity feeding the parallel ODE) — works at ANY order
  the chart composition supports (the ODE needs low order).
⟹ weakening `∞ → (n : ℕ∞)` (with `1 ≤ n`, or fixed `8` matching
`IsSmoothVariation`) across `exists_piece_parallel_section`,
`parallel_transport_unique_of_eq_at_point`,
`exists_global_parallel_transport_on_Ioo`, `exists_parallel_transport_on_Icc`,
`parallel_transport_preserves_inner_product` (check its own hγ uses), and
`PerpFrame.exists_parallel_frame` is a mechanical signature+proof-order edit —
the FIRST brick of the next session. Then the clamped radial curve (degree 8)
qualifies directly, and the regularity-export brick proceeds per the blueprint
above.

### ∞→finite-order refactor DONE (2026-06-11, the obstruction unblock)

Weakened `ContMDiff ∞ γ` → `ContMDiff (N:ℕ∞) γ` with `(hN : 2 ≤ N)` across the
parallel-transport chain (the genuine ODE need is C², `N≥2`):
- `ParallelTransport.lean` (GREEN): `exists_piece_parallel_section`,
  `parallel_transport_unique_of_eq_at_point`,
  `exists_global_parallel_transport_on_Ioo`, `exists_parallel_transport_on_Icc`,
  `parallel_transport_preserves_inner_product` — all take `(N) (hN)` now; the
  internal `extChartAt` smoothness stays `∞` (`.of_le`), `deriv_of_isOpen`/
  `differentiable*` order side-goals discharged with `N ≠ 0` (NOT `1 ≤ N` —
  the API wants `n ≠ 0`).
- `PerpFrame.lean` (pending olean): `exists_parallel_frame` weakened to `(N)(hN)`;
  existing `∞`-callers (`exists_parallel_orthonormal_perp_frame_along_geodesic`,
  `perp_to_velocity_preserved_*`) keep `∞` signatures and `.of_le` at the call
  (cascade bounded — `(N := 2) le_rfl (hγ.of_le (by exact_mod_cast le_top))`).
- `ParallelTransportSmooth.lean` (pending olean): two call sites `.of_le`'d.

⟹ the clamped radial central curve (`ContMDiff 8`) now qualifies for
`exists_parallel_frame`. NEXT: the regularity-export theorem per the blueprint
above, then instantiate `covGronwall_ne_zero`.

### 2026-07-08 chartRep transfer bridge

Added and verified `chartRep_congr_curve`: if two base curves agree near `t`
and their sections agree as model-space tangent vectors near `t`, then their
`chartRepAt` representatives agree near `t`.  `covDerivAlong_congr_curve` now
reuses this bridge.

This is the missing low-level transfer API for Step B's clamped-to-clean
regularity route.  It does not yet export the full clean radial
`hJdiff`/`hDJdiff` theorem.  The next target is the regularity producer:
rebuild the clamped variation from `exists_radial_jacobi_radius`, prove
clamped `J`/`DJ` chartRep differentiability using
`variationField_chartRep_differentiableAt` and
`variationField_covDeriv_chartRep_differentiableAt`, then transfer them with
`chartRep_congr_curve`.

### 2026-07-08 clean radial regularity export

Added and verified `exists_jacobi_diff`.  It rebuilds the same clamped
variation and norm budget as `exists_radial_jacobi_radius`, proves clamped
variation-field and first-covariant-derivative `chartRepAt` differentiability
using the existing variation-field differentiability lemmas, and transfers both
facts to the clean radial objects with `chartRep_congr_curve`.

This closes the clean radial `hJdiff`/`hDJdiff` producer for capped intervals
`[0,b]` with `b ≤ 1`.  It does not close the endpoint `IsJacobiAt ... 0` /
`D^2J(0)=0` producer, which still needs the missing continuity/API bridge at
`0`.  Focused verification passed; the module was also targeted-built after
refreshing a missing `GaussLemmaPullback.olean`.

### 2026-07-08 endpoint route audit after regularity export

The current endpoint target is still the concrete second initial condition
`D_t^2 J(0)=0` (or equivalently `IsJacobiAt ... 0` plus `J(0)=0`).  Three
routes were inspected:

1. Extending the existing interior proof directly to `t0 = 0` fails at the
   geodesic-equation sublemma.  `clamped_slice_covDeriv_velocity_zero` relies on
   `maximalGeodesic_rescale_of_norm_lt_radius`, whose equality is packaged only
   for `t in [0,1]`; this does not give the two-sided `nhds 0` germ needed by
   `covDerivAlong`.
2. The normal-coordinate route found only the first-order producer
   `mfderiv_expMap_at_zero` plus lower chart-flow facts such as the derivative
   of the chart phase vector field at the zero section.  There is no checked
   API yet converting those facts into the covariant acceleration statement for
   `t |-> expMap g p (t • a)` at `0`.
3. The chart-flow rescaling route has a private orbit-projection theorem with
   negative-time intervals, but the public `maximalGeodesic_rescale_at_one_of_small`
   theorem still exposes only the `[0,1]` rescaling shape.  Using it for
   `expMap (t • a)` with negative `t` would require a new sign/negative-scale
   bridge, not a local rewrite in the endpoint Jacobi proof.

Smallest honest next API: prove a radial-center acceleration producer, e.g.
`covDerivAlong g (fun t => expMap g p (t • a)) (curveVelocity ...) 0 = 0` for
small `a`.  Once that exists, the existing `commute_ds_dt_curvature` endpoint
argument should be able to discharge `D_t^2 J(0)=0` without hiding the missing
geometric input.

### 2026-07-08 endpoint Jacobi theorem

Added and verified the endpoint route promised above.

New checked pieces:
- `clamped_slice_covDeriv_velocity_zero_at_zero`: the clamped radial slice has
  zero covariant acceleration at `0`, by germ transfer to
  `Exponential.exp_radial_d2_zero`.
- `exists_jacobi_zero`: radius-packaged endpoint `IsJacobiAt ... 0` for the
  clean radial variation, under the intrinsic completeness / continuous
  Riemannian-bundle hypotheses and the explicit `hEnorm` compatibility.

The proof reuses the interior `exists_radial_jacobi_radius` commutation route:
the only replaced input is `houterL`, now supplied by the endpoint acceleration
producer instead of the one-sided maximal-geodesic rescale theorem.  Focused
verification passed, and the module was targeted-built so downstream imports can
see the new theorem.

Remaining bridge: package `exists_jacobi_zero` in the Volume layer together with
the existing `radialJacobiField` adapter and `d2_zero_of_jac0`.  Two direct
Volume adapter attempts were not kept: adding the wrapper in `RadialGronwall`
and then in `NormalChartMeasure` exposed public theorem-head instance plumbing
around `IsContinuousRiemannianBundle` / `FiberBundle` / `VectorBundle`.  This is
an adapter-context issue, not a mathematical obstruction to the endpoint Jacobi
equation.

### 2026-07-18 canonical launch radius

The four clamped-variation producers now use the explicit common radius
`jacobiVarRadius g p = expMapC2Radius g p / 26`.  The new direct theorems are
`radial_jacobi_of_lt`, `jacobi_diff_of_lt`, `radial_deriv_of_lt`, and
`jacobi_zero_of_lt`; the old `exists_*` declarations remain as compatibility
wrappers with unchanged statements.

This removes the independent opaque `C^8` radius choice from every proof.  The
smooth variation now consumes the named-radius `C^infty` exponential theorem
already built into `expMapC2Radius`, so downstream Rm04 packaging can refer to
one concrete radius rather than taking minima of unrelated choices.  Focused
verification passed.  This is a radius/API advance only: relating the canonical
exponential radius to the sequence-wide CGT decay profile remains a separate
H6 producer obligation.

The focused check and exact module refresh both passed.

### 2026-07-18 natural intrinsic variation

- `intrinsic_jacobi` removes the clamp and launch-radius assumptions for the
  complete intrinsic exponential. It proves the Jacobi equation along the
  entire intrinsic geodesic by applying the existing curvature commutation
  theorem to the globally smooth affine-velocity variation.
- The proof reuses `intrinsicVar_smooth`,
  `intrinsicGeodesic_isGeodesic`, `commute_ds_dt_intrinsic`, and
  `commute_ds_dt_curvature`; no new radius assumption or wrapper was added.
- `intrinsic_jacobi` and `intrinsic_jacobi_one` are focused- and exact-green. The latter
  identifies the time-one variation field with the vector-slot differential of
  `expMapIntrinsic` using `intrinsicFiber_smooth` and the chain rule.
- The coordinated exact module refresh passed (`3799/3799`). No source proof
  frontier remains in this file.

### 2026-07-23 intrinsic initial derivative

Added `intrinsic_jacobi_d0`, the unrestricted endpoint identity
`D_t J_w(0) = w` for the global intrinsic variation.  The proof applies mixed
covariant commutation to
`F(s,t) = intrinsicGeodesic p (x + s • w) t`; at `t = 0` the transverse curve
is constant and the longitudinal velocity is exactly `x + s • w` by
`intrinsicGeodesic_mfderiv_zero`.  The only dependent-fibre wrinkle is handled
with `covDerivAlong_congr_curve`.

Focused verification passed without warnings.  This completes Route B brick
N-c.  The minimizing-implies-no-interior-conjugate theorem remains 0%; its
dedicated N machinery is now roughly 42%, with the abstract index-form
foundation present but the interior uniqueness, corner smoothing, and
abstract-to-geometric collision still open.

### 2026-07-24 component-local intrinsic Jacobi API

Removed the accidental `ConnectedSpace M` assumptions from
`intrinsic_jacobi` and `intrinsic_jacobi_one`.  Their proofs use only the
complete intrinsic-geodesic and smooth-variation APIs; the consumed
`intrinsicVar_smooth`, `intrinsicFiber_smooth`, and `intrinsicExp_smooth`
declarations are already component-local.  The theorem statements and proof
routes are otherwise unchanged.

Focused verification passed without diagnostics, and the coordinated exact
targeted refresh is GREEN (`3799/3799`).  These two theorems remain fully
proved (100%); this is an API-hypothesis cleanup and does not by itself advance
the still-open Route B′ cutoff producer or its endpoint theorem.

### 2026-07-24 component-local radial endpoint API

Removed the stale `ConnectedSpace M` binder from the private endpoint
acceleration lemma, `jacobi_zero_of_lt`, and `exists_jacobi_zero`.  The
independent `intrinsic_jacobi_d0` endpoint was weakened at the same time: its
proof uses the already component-local `intrinsicVar_smooth`.  The radial proof
ends in the component-local `exp_radial_d2_zero`; no connectedness input occurs
in either argument.

Focused verification passed without diagnostics after both cleanups.  The
radial endpoint exports and the final `intrinsic_jacobi_d0`-inclusive artifact
are exact-current (`3801/3801`).
This is an API-hypothesis cleanup: the endpoint Jacobi theorems remain 100%,
while the downstream Calabi support theorem remains unstated (0%).

### 2026-07-24 arbitrary-time intrinsic Jacobi differential

Added `intrinsic_jacobi_at`, identifying the intrinsic initial-velocity
Jacobi field at an arbitrary time `t` with the vector-slot manifold derivative
of `expMapIntrinsic` at `t • x`, applied to `t • w`.  The proof reuses the
checked time-one theorem after scaling the intrinsic geodesic; no raw
exponential radius or connectedness assumption enters the statement.

Focused verification passed without diagnostics.  The new theorem is also
consumed by the focused-green intrinsic whole-tail Bishop comparison in
`Volume/BishopIntrinsic.lean`.  This bridge is complete (100%); the separate
fixed-metric Calabi support theorem remains unstated (0%).
