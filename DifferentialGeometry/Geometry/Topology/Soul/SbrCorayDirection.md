# SbrCorayDirection.lean

Verified 2026-09-08 in the dev checkout. Actual reversed calibrated corays have exact levels, unit speed and the calibrated intrinsic directional value before the endpoint; affine reversal is proved in the actual tangent model.

Empty focused output: 19.4s. Lint-clean named build: 18.6s.
Fresh external public axiom audit: 17.4s; all 2 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrCorayDirection-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

## Scope, ownership, and verification state

Assigned to `soul_distance_field` by the additional Ch8 source brief at the
end of `SOUL_PLAN.md`, 2026-09-08. Claim
`c200e54f-5dd0-490d-abe9-b596b852d763` was acquired through
`E:/testdifferential-geometry/scripts/lake-locked.ps1` from the dev checkout.
The claim is retained for the parent's verification and integration.

Source-ready only: two public declarations and two private helpers. The
current compiler window belongs to the parent alone. No Lean, Lake, REPL,
focused check, artifact refresh, axiom audit, root registration, shared
status/plan edit, or commit was performed by this worker. No compiler
diagnostics exist for this leaf yet. Earlier delivered leaves remain frozen.

Static freeze: source Git blob `69b14fec7e7a7e1700f4e7cded12257489402646`;
all three import paths exist; no forbidden tokens or trailing whitespace.
These checks do not establish elaboration or dependency cleanliness.

The book argument is `master05a.tex:8199-8257`, particularly
`eq:sbr-prescribed-coray`, `eq:sbr-reversed-coray`,
`eq:sbr-reversed-coray-level`, and `eq:sbr-reversed-coray-calibration` in the
proof of `thm:sbr-surjective-busemann-level-map-local`.

## Exact public results

Both declarations are in `DifferentialGeometry.Geometry.Topology`.

`calibrated_intrinsic_coray_reverse_direction` takes the actual smooth
compatible metric `g`, any scalar function `b : M → ℝ`, an offset `C`,
a point `p`, a unit initial vector `u`, and the calibration

```lean
∀ s : ℝ, 0 ≤ s →
  b (intrinsicGeodesic g hEnorm p u s) = b p + s
```

Writing `gamma := intrinsicGeodesic g hEnorm p u`, its conclusion at each
explicit `t > 0` is

```lean
g.inner (gamma t) (-curveVelocity gamma t) (-curveVelocity gamma t) = 1 ∧
intrinsicRightDerivative g hEnorm (fun q => C - b q) (gamma t)
  (-curveVelocity gamma t) = 1
```

The function `b` is not assumed continuous, concave, or smooth: its exact
calibration along the actual geodesic is sufficient. No isometry assumption
is needed for this bounded directional assertion. The unit speed is an
actual metric statement, and the derivative is the unchanged native
`intrinsicRightDerivative` defined using `derivWithin` on `Ioi 0`.

`exists_busemann_reversed_coray` takes a native isometric ray
`c : ℝ≥0 → M`, a prescribed original point `p`, and a higher level `C`
with `busemann c p ≤ C`. It produces a unit initial vector `u`, retains the
actual intrinsic curve `gamma`, and uses the exact definitions

```lean
T := C - busemann c p
gamma := intrinsicGeodesic g hEnorm p u
delta := fun s => gamma (T - s)
```

Its package gives:

- Global smoothness of this actual reversed intrinsic curve.
- The actual velocity identity
  `curveVelocity delta s = -curveVelocity gamma (T - s)` for every real
  `s`, written in the existing model representation `E` to align fibers.
- The actual prescribed right derivative for every real `s`:
  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I delta (Ici s) s
  ((1 : ℝ →L[ℝ] ℝ).smulRight (curveVelocity delta s))`.
- `busemann c (delta 0) = C` and `delta T = p`.
- `C - busemann c (delta s) = s` for `s ∈ Icc 0 T`.
- `dist (delta s) (delta t) = dist s t` for both parameters in `Icc 0 T`.
- Unit actual velocity and intrinsic directional value one for `C -
  busemann c` at every `s ∈ Ico 0 T`.

The directional calibration is deliberately not asserted at the terminal
time `T`. There the reversed direction would enter negative original coray
times, outside the calibration hypothesis. The actual curve is still
smooth there and the endpoint identity holds. This matches the book's
explicit endpoint qualification. Equality of levels is allowed: `T = 0`
gives the degenerate segment, and the `Ico` assertion is empty.

## Native construction and proof mechanism

The common context is the complete compatible metric on a positive
finite-dimensional smooth boundaryless manifold, with the native
sigma-compactness and continuous Riemannian-bundle instances needed by the
intrinsic exponential and calibrated-coray producers. No curvature,
connectedness, properness, or lower boundedness assumption is introduced.

The private `intrinsicGeodesic_reverse_velocity` proves the exact global
identity

```lean
intrinsicGeodesic g hEnorm (gamma t) (-curveVelocity gamma t) s =
  gamma (t - s)
```

using `intrGeo_smul_apply` at scalar `-1` and
`intrinsicGeodesic_continuation`. These are actual geodesic identities,
not an assumed local agreement. `intrinsicGeodesic_speedSq_eq` then gives
the unit negative velocity.

For `t > 0`, the neighborhood `{s | s < t}` of zero lies in the region
`t - s ≥ 0`. Calibration therefore identifies the scalar composite along
the reversed geodesic with the affine function
`C - b (gamma t) + s` on an open neighborhood of zero. The ordinary
derivative is one, and its restriction to `Ioi 0` computes the existing
intrinsic right derivative. No ambient derivative of `b` appears.

The Busemann endpoint first invokes the verified
`exists_calibrated_intrinsic_ray`; the ray, unit vector, calibration, and
pairwise distance equality are produced by its native minimizing-geodesic
compactness argument. `curveVelocity_affine` from
`Toponogov/PrescribedDistanceSupport` gives the exact reversed velocity.
Smoothness follows from `intrinsicGeodesic_contMDiff` and the actual affine
parameter map. The private right-derivative helper writes the real-domain
continuous linear derivative as `1.smulRight` of its value at `1`; this
follows by linearity, as in the verified `Soul/RadialNormalFlow` argument.

The distance identity uses the produced nonnegative-time isometry at
`T - s` and `T - t`. It is only asserted on the stated segment, where
these original times are nonnegative.

Read `SbrDirectional.md`, `SbrBusemannData.md`, `CalibratedCoray.md`,
`PrescribedDistanceSupport.md`, and the actual continuation, velocity,
derivative, and book declarations before implementation. No competing ray,
tangent, right-derivative, or gradient hierarchy was introduced.

## Verification order and remaining scope

The parent must verify and refresh `SbrDirectional` before checking this
leaf, then perform the named refresh and fresh audit of the two public
declarations. `CalibratedCoray` and `PrescribedDistanceSupport` are already
verified native imports. Static source review has found no remaining
mathematical input for this bounded coray construction; all elaboration and
lint feedback remain pending.

For level-map surjectivity, the actual generalized-gradient support and
sharp unit bound must still identify the produced unit calibrated velocity
with the actual normalized gradient. Uniqueness of the constructed ascent
trajectories must then identify this native reversed segment with the
Sharafutdinov trajectory. Neither a gradient support assumption nor a
trajectory-existence assumption substitutes for the coray construction
here, and no level-map surjectivity endpoint is claimed by this leaf.

## Parent focused check, 2026-09-08

Attempt1 rejected only the affine reversal simplification in hvel (15.1s).
The source now rewrites the actual reparametrized curve and its time value
explicitly before simplifying the velocity scalar. This repair is still
UNVERIFIED: the exclusive window was returned at17:35, with no proof worker
remaining. The claim is retained for attempt2 in the next returned window.