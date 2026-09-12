# SbrGradientContraction.lean

Verified 2026-09-08 in the dev checkout. Native concavity and support produce endpoint angle signs, two-curve distance contraction and distance-to-fixed-point monotonicity, with actual endpoint tangent transport.

Empty focused output: 14.9s. Lint-clean named build: 17.8s.
Fresh external public axiom audit: 12.3s; all 3 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrGradientContraction-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

## Scope, claim, and verification state

Assigned to `soul_distance_field` by the next bounded Ch8 source brief in
`SOUL_PLAN.md`, 2026-09-08. Claim
`4e23262b-a078-4d02-a78b-f4af6d36bf74` was acquired through
`E:/testdifferential-geometry/scripts/lake-locked.ps1` from the dev checkout.
The claim is retained for the parent's verification and integration.

Source-ready only: three public declarations and one private representation
helper. The parent owns the compiler window. This worker ran no Lean, Lake,
REPL, check, build, refresh, or axiom audit, and made no import registration,
shared status/plan edit, earlier-leaf edit, or commit. No compiler feedback
exists for this leaf yet. Static review is not verification.

Static freeze: source Git blob `fa50887a2e2874ea8f479b11538e29b7cd25b302`;
both imports resolve to existing source paths; no forbidden tokens or
trailing whitespace; source parentheses balance. These checks do not
establish Lean elaboration or dependency cleanliness.

Book scope: `master05a.tex:7419-7438`, `cor:sbr-acute-angle`, and
`master05a.tex:7589-7672`, `lem:sbr-two-flow-contraction` and
`lem:sbr-flow-to-fixed-point`. These are conditional comparison results,
not the later existence construction for normalized ascent curves.

## Public API and exact inputs

All declarations are in `DifferentialGeometry.Geometry.Topology` and retain
the actual smooth compatible metric `g`, complete intrinsic geodesics,
native tangent fibers, and `intrinsicRightDerivative` from `SbrDirectional`.

`inner_normalized_support_nonneg_of_le_intrinsic_level` takes `F : M → ℝ`,
a tangent vector `G : TangentSpace I p`, the pointwise support inequality

```lean
∀ v : TangentSpace I p,
  intrinsicRightDerivative g hEnorm F p v ≤ g.inner p G v
```

and a direction `v` such that `F` is concave along its complete native
intrinsic geodesic. If `t > 0` and `F p ≤ F (intrinsicGeodesic ... p v t)`,
then

```lean
0 ≤ g.inner p ((g.inner p G G)⁻¹ • G) v
```

The angle is produced from the positive-time geodesic secant and support.
The result needs neither a minimizing nor a unit direction.

`antitoneOn_dist_of_normalized_gradient_right_derivatives` takes:

- Actual geodesic concavity of `F` for every point and tangent vector.
- A tangent field `G : (p : M) → TangentSpace I p` with the displayed
  directional support inequality at every point.
- Continuous curves `xi`, `zeta` on `Icc a b`.
- For every `t ∈ Ico a b`, their actual right derivatives on `Ici t`,
  with the continuous linear derivative maps explicitly equal to

  ```lean
  (1 : ℝ →L[ℝ] ℝ).smulRight
    ((g.inner (xi t) (G (xi t)) (G (xi t)))⁻¹ • G (xi t))
  ```

  and the corresponding expression for `zeta`.
- `F (xi t) = F (zeta t)` for `t ∈ Ico a b`.

Its conclusion is

```lean
AntitoneOn (fun t => dist (xi t) (zeta t)) (Icc a b)
```

`antitoneOn_dist_fixed_of_normalized_gradient_right_derivative` has the same
function, field, support, and single-curve right-derivative inputs. Instead
of a second ascent curve it takes a fixed `q` with
`F (xi t) ≤ F q` for `t ∈ Ico a b`, and concludes

```lean
AntitoneOn (fun t => dist (xi t) q) (Icc a b)
```

This includes equality of function values, coincident points, and the
terminal time. No separate uniqueness hypothesis is needed to pass through
zero distance.

No Lipschitz constant is used in these bounded comparisons: geodesic
concavity supplies the actual positive secant bound, and the explicit
support supplies the required metric pairing. Thus the results apply in
particular to the intended Lipschitz geodesically concave functions without
carrying an unused Lipschitz assumption. Likewise `G ≠ 0` is unnecessary
here: its squared metric norm and its inverse are nonnegative, with inverse
zero at zero. This is a valid extension of the conditional comparison, not
a claim of normalized trajectory existence at a zero gradient. No
calibration, continuity, or smoothness assumption on `G` is inserted.

## Geometric proof route

The normalized angle lemma first obtains

```text
0 ≤ (F(exp_p(t v)) - F(p)) / t ≤ D_v F(p) ≤ g.inner p G v.
```

The second inequality is the actual
`slope_le_intrinsicRightDerivative`. Multiplication by the nonnegative
inverse squared metric norm then gives the normalized angle. Metric
nonnegativity uses `gInner_self_nonneg`; no cancellation by a potentially
zero norm is performed.

The two-curve proof instantiates
`antitoneOn_dist_of_right_first_variation_nonpos`. At distinct curve points,
that existing comparison produces a native unit minimizing segment from
`soul_unit_minimizing_initial` and ultimately `minExp_of_ne_top`.
The new proof discharges its angle condition for every such segment.
Equal function values give the initial normalized angle. At the terminal
point, `intrGeo_smul_apply` with scalar `-1` and
`intrinsicGeodesic_continuation` prove that the actual intrinsic geodesic
with negative terminal velocity returns to the original point at the same
positive length. Applying the secant/support argument there gives the
second angle with its correct negative sign. Their sum is the required
nonpositive first-variation expression.

The fixed-point proof uses the actual constant curve and
`hasMFDerivWithinAt_const q (Ici t) t`. Its terminal velocity term is zero,
so the initial secant/support argument alone discharges the angle premise.
Both proofs then use the existing Dini comparison across zero-distance
times; they do not assume nonexpansiveness or uniqueness as inputs.

The small private `tangent_cast_model_eq` duplicates only the frozen
distance-comparison leaf's two-line equality-transport bridge. It erases
the terminal endpoint transport in the proof using the existing
`TangentSpace I p = E` representation. The imported public first-variation
condition still contains the actual endpoint transport, and no competing
tangent definition is introduced. The reversal argument directly reuses
native continuation/scaling rather than importing a nonsmooth trajectory
or assuming reversed-geodesic agreement.

## Verification order and remaining scope

Read `SbrDirectional.md`, `SbrDistanceContraction.md`, the actual native
secant, continuation, metric, and manifold-derivative declarations, and the
book proof before implementation. The parent-recorded first compiler API
findings were also read. Static inspection avoided the deprecated
`ContinuousLinearMap.zero_apply` alias in favor of `zero_apply`.

Parent order: verify/refresh `SbrDirectional` and the
`SbrDini → SbrRightFirstVariation → SbrDistanceContraction` chain before this
leaf, then perform its focused check, named refresh, and fresh audit of
the three public declarations. No mathematical gap was found in the
bounded comparison route; elaboration and lint feedback remain pending.

The actual Ch8 application still must provide the constructed generalized
gradient and its directional support, constructed continuous trajectories
with these actual normalized right derivatives, and equal-level
calibration (or the fixed-point level inequality). The endpoint angle
inequality is no longer a separate input of these consumers. This leaf
does not assert gradient existence, trajectory existence, a flow package,
surjectivity, or the Sharafutdinov level-map endpoint.

## Resumed proof repair and trial evidence

Endpoint velocity is transported through the actual endpoint equality by
identity elimination inside its correct tangent fiber. The earlier model-cast
helper is no longer needed and was removed. This avoids temporarily applying
a metric at one point to an untransported vector at another point.
Cold focused diagnostics14.7s; import-only warm environment12.335s; correct
whole body1.995s after a rejected wrong-proof control1.904s. Fresh evidence:
E:/lean-tools/soul-audits-20260907/warm-SbrGradientContraction-r1. Owned REPL and
elaboration lock closed before independent acceptance. The shared guidance's
new failed-request cap is explicitly Chapter23-only; Soul followed the existing
warm-session rules. No global instance or mathematical assumption changed.