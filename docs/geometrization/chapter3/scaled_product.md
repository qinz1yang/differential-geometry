# Positive distance rescaling and the literal shrinking-factor example

Files:

- `DifferentialGeometry/Geometry/Metric/Scaling/Rescale.lean`
- `DifferentialGeometry/Geometry/Metric/Approximation/ScaledProductCollapse.lean`

## Exact contracts

`MetricSpace.rescale m c hc` constructs a metric on the same carrier as `m`,
with distance `c * m.dist` and the hypothesis `hc : 0 < c`. Its topology is
definitionally the original topology, using mathlib's `ofDistTopology` with
an explicit comparison of metric balls. It introduces no new carrier type.

The identity is a homeomorphism. In the forward direction its Lipschitz
constant is `c`, and in the reverse direction it is `1/c`. Compactness is
preserved with no auxiliary compactness hypothesis. A set is bounded in the
new metric exactly when it is bounded in the old metric. For every bounded
set `s`, including the empty set,

`diam_(c*d)(s) = c * diam_d(s)`.

The boundedness hypothesis is stated explicitly; mathlib's real-valued
diameter is zero for unbounded sets, unlike its extended diameter. No
unbounded-set diameter argument is used here. The scale zero is deliberately
excluded because it usually collapses distinct points and fails to define a
metric on the original carrier.

The existing `PointedBallApprox.rescale` accepts these actual metrics and
the proved `rescale_dist` equations. This supplies its missing metric
producer without a new approximation vocabulary; a direct application of
that existing consumer was checked in Lean.

`MetricSpace.scaledProduct mY mF t ht` constructs the metric on the fixed
carrier `WithLp 2 (Y × F)` whose distance is exactly

`sqrt(distY(y,y')^2 + t^2 * distF(a,a')^2)`.

Here `WithLp 2` is mathlib's established Pythagorean product carrier; the
only modified factor is `F` with distance multiplied by the positive `t`.
The theorem `scaledProduct_dist` proves the displayed formula with both
original metric structures explicit.

`GromovHausdorff.ghDist_scaledProduct_le_half_diam` states that, for nonempty
compact metric spaces `Y,F` and `t>0`, the actual weighted product has
Gromov--Hausdorff distance from `Y` at most `t * diam(F) / 2`. The diameter on
the right is computed in the original metric on `F`. The product metric on
the left is explicitly the constructed `scaledProduct`, rather than an
arbitrary supplied metric satisfying a desired conclusion.

`GromovHausdorff.tendsto_ghDist_scaledProduct` proves convergence to zero for
every sequence of positive scales tending to zero. No monotonicity is
needed. `GC.MetricGeometry.pointedGHConverges_scaledProduct` proves pointed
convergence of these same actual weighted products at `(p,q)` to `(Y,p)`;
this theorem permits any complete base `Y`, with only the factor `F`
required to be compact. Chosen basepoints provide nonemptiness.

The proof uses the actual projection approximation from `ProductCollapse`
and the proved diameter scaling. It does not treat a hypothesis that the
diameters shrink as a proof that a newly specified weighted metric exists.

The illustrative flat three-torus and its smoothness, dimension, and
Riemannian tensor interpretation have not been newly formalized. In
particular, multiplying a metric tensor by `t^2` and proving its associated
length metric is multiplied by `t` is a different adapter. The present
construction concerns distances and is independent of the migrating PC
manifold foundation.

## Sources actually checked

- `master207A.tex`, MC10, lines 1100--1120, and MC16, lines 1743--1760:
  positive distance scaling, Pythagorean weighted product, and the
  correspondence/projection estimate.
- Kleiner--Lott, *Locally collapsed 3-manifolds*, published Astérisque 365
  (2014), Section 2.2, printed pages 19--20 / PDF pages 14--15. These pages
  were reopened for this adapter. The archived PDF's retained identity is
  SHA-256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`.
  The source defines positive multiplication of distance and explicitly
  uses the Pythagorean product convention.
- `reference_checks_revision58.md` records the already checked BBI scaling
  convention at printed page 275 / PDF page 290. Its KL source-convention
  and author-correction checks, supplemented by revision60's correction
  check, are reused for these unchanged claims. No new correction-sheet
  retrieval is claimed.

The exact weighted-product inequality is the blueprint's elementary proof,
implemented here using the earlier proved projection estimate. The local
mathlib source was searched for rescaled metric constructors before adding
this one. Existing `ofDistTopology`, `WithLp 2`, Lipschitz, compactness,
boundedness, diameter, and GH APIs are reused.

## Verification

Both modules built together successfully against Lean 4.35.0-rc3 and
mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e` (2169 jobs), with no
warnings after the final style cleanup. Ten constructor/main-result axiom
checks showed only `propext`, `Classical.choice`, and `Quot.sound`.

Additional compiled applications checked rescaling by one, the empty-set
diameter endpoint, and direct compatibility with
`PointedBallApprox.rescale`. No `sorry`, `axiom`, PC imports, smooth metric
structures, or modifications to existing mathematical modules were needed.
