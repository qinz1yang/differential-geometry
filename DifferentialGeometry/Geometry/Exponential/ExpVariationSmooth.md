# ExpVariationSmooth.lean

## Step C moving-base audit

This file proves smoothness for intrinsic exponential variations of the form
`(s, t) |-> expMapIntrinsic (gamma t) (s • (V0 t).snd)`, assuming a smooth
base curve and a smooth tangent-bundle launch field. This is the right producer
for smooth variations once the launch field is already available.

For the Step C one-summand gradient theorem, the missing object is different:
given a moving basepoint `q` and fixed endpoint `pt`, one needs a local smooth
inverse section `q |-> exp_q^{-1}(pt)`. The useful total-space map for that
future inverse-function-theorem step is now named `diagExp`, with projection
facts `diagExp_apply`, `diagExp_fst`, and `diagExp_snd`.

The existing small-field smoothness theorem also packages through this map as
`diagExp_variation_contMDiffAt_of_smallField`: along a smooth base curve and a
smooth tangent-bundle launch field, the map
`(s,t) |-> diagExp <gamma t, s • V0 t>` is smooth into `M × M` for small
variation parameter. This is useful evidence for the intended diagonal
exponential route, but it remains a curve/field theorem, not a total-space
local diffeomorphism.

The fixed-base inverse-function-theorem pattern in `LocalDiffeomorphism.lean`
does not directly apply to `diagExp`. To reproduce it one first needs a
model-coordinate theorem saying the total-space map
`u |-> (u.proj, expMapIntrinsic u.proj u.snd)` is `ContDiffAt` in tangent-bundle
charts, together with the derivative identification at the zero section
`(delta_p, delta_v) |-> (delta_p, delta_p + delta_v)` up to the chosen product
charts. Only then can the Banach IFT produce the moving-base inverse section.

The endpoint-at-zero fact for `diagExp` is intentionally not placed here: it
would require importing the metric/Hopf-Rinow-side theorem
`expMapIntrinsic_zero` upward into this smoothness file. A downstream file that
already imports the metric-geometric layer can combine `diagExp_snd` with that
theorem when it constructs the local inverse.

Verification passed for the Lean edit.

## 2026-06-24 — total-space charted smoothness LANDED (`diagExp_contMDiffAt_zero`)

The total-space charted-smoothness frontier (target 1) is DONE, verified by a real
`lake build` (3760 jobs, sorry-free, axiom-clean, no warnings):

`diagExp_contMDiffAt_zero (g) (hEnorm) (p) (n : ℕ) (hn : 1 ≤ n) :
ContMDiffAt I.tangent (I.prod I) (n:ℕ∞) (diagExp g hEnorm) ⟨p, 0⟩`.

This is the regularity input the Banach IFT needs for `diagExp` near the zero
section (the prior theorem only gave smoothness after precomposing a launch field).

### Route (mirror of `expMapIntrinsic_variation_contMDiff`, total-space form)

- Base component `u ↦ u.proj`: `contMDiffAt_proj (TangentSpace I)`.
- Endpoint component `u ↦ exp_{u.proj}(u.snd)`: factor near `⟨p,0⟩` as
  `(extChartAt I p).symm ∘ G ∘ R ∘ Ξ` where
  `Ξ = extChartAt I.tangent ⟨p,0⟩` (chart, smooth by `contMDiffAt_extChartAt`),
  `R z = (z.1, t'⁻¹ • z.2)` (the fibre `t'⁻¹`-rescale, a CLM ⇒ `ContinuousLinearMap.contDiff`),
  `G z = (Φ(z,t')).1` (the chart-`p` geodesic-flow projection, `ContDiffOn` from
  `exists_chartExp_jointContDiffOn_nat`).
- Pointwise factorisation = the chart-independence bridge
  `expMapIntrinsic_eq_chartFlow_proj_residual`, holding eventually near `⟨p,0⟩`
  (proj ∈ chart source; `R(Ξ u)` in the phase-ball — both by continuity, value at
  `⟨p,0⟩` is the ball centre), transferred by `ContMDiffAt.congr_of_eventuallyEq`.
- Pair the two components with `ContMDiffAt.prodMk`; `simpa [diagExp]`.

New import: `Geometry.Geodesic.AffineReparam` (for `chartFiberCoord_fiberScale`,
the fibre `t'⁻¹`-linearity that matches `R(Ξ u)` to the bridge's phase point).

### Lean gotchas (cost several iterations)

- `ContDiff.prod` does NOT exist by that dot-name (falls through to `Exists.prod`
  because `ContDiff` unfolds to an `∃`). Build product/linear maps as a
  `ContinuousLinearMap` (`fst.prod (c • snd)`) and use `ContinuousLinearMap.contDiff`.
- `set G := … with hG_def` REWRITES the obtained flow hypotheses (`hG_cd` etc.) into
  `G`/`ctr` form, and `set` transparency makes `ContMDiffAt.comp` over-unfold `G`
  (picks `g = Prod.fst`). Resolution: do NOT annotate the `comp` results' types and
  do NOT `clear_value` (which would break the bridge's `hG_cd` defeq). Let the comps
  infer from arg types (`have hGRΞ := (hG_at.contMDiffAt).comp u₀ hRΞ_cd`), and pin
  the per-point congr goal with `change … = (extChartAt I p).symm (G (R (Ξ u)))`
  (`change`, not `show` — the style linter rejects a goal-changing `show`).
- `mfderiv_comp` takes the point as an EXPLICIT first arg; `ContMDiffAt.comp` too.

### Target 2 (the zero-section derivative): DONE

Landed in `Geometry/Exponential/DiagExpDerivative.lean` (`diagExp_hasFDerivAt_zero`
+ `diagExp_hasFDerivAt_zero_unipotent`), build-verified sorry-free. See
`DiagExpDerivative.md`. Original framing kept below.

NOT done (now done — see above): the derivative identification
`d(diagExp)_{⟨p,0⟩} : (δp, δv) ↦ (δp, δp + δv)` (in the tangent-bundle/product
charts). This is the OTHER Banach-IFT input (invertibility of the derivative). It is
a separate, larger computation: the base part `δp` is the proj derivative, but the
endpoint part `δp + δv` is the JOINT (moving-base) derivative of `exp` at the zero
section. The fixed-base `mfderiv_expMap_at_zero` (= id) is available
(`LocalDiffeomorphism.lean`); the moving-base joint derivative is new content,
obtainable from the same chart factorisation by differentiating
`(extChartAt I p).symm ∘ G ∘ R ∘ Ξ` and computing the geodesic-flow linearisation
`dΦ` at the phase-ball centre (Jacobi-field content). Recommended as a dedicated
follow-up; with both target 1 (done) and target 2, the Banach IFT gives the
moving-base inverse section `q ↦ exp_q⁻¹(pt)`.
