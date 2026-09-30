# Curvature weakening for comparison angles

Three public theorems prove the curvature-weakening part of ALR01.
The separate rank-two exclusion part still requires the geometric
distance-map openness/dimension argument and is not claimed here.

`Real.convexOn_cosh_sqrt` proves that x -> cosh(sqrt x) is convex on
[0,infinity). The proof sums the convex nonnegative power-series
terms x^j/(2j)!, using Mathlib's actual convergent hyperbolic cosine
series. Zero is included and no differentiability at zero is assumed.

For any kappa>=0 and metric triangle sides a,b,c with a,b>0 and
|a-b|<=c<=a+b, the hyperbolic comparison angle of curvature -kappa
is at most the Euclidean comparison angle. The existing definition
`comparisonAngleNegCurvature kappa` uses the nonnegative magnitude
of the NEGATIVE curvature; the sign convention is unchanged.
Both degenerate triangle extremes, c=0 when a=b, and kappa=0 are
included. No smooth manifold or geometric comparison hypothesis is
used for this model-angle inequality.

Consequently zero-curvature four-point comparison on any subset s
implies curvature -kappa four-point comparison on that SAME subset
for every kappa>=0. No completeness, length structure, locality
extension or comparison-domain enlargement is involved. This gives
the minus-one normalization needed by the paired-chart route when
its zero-curvature input is global, and also preserves bounded
domains when they are the given input.

## Proof and sources

Let v=(a²+b²-c²)/(2ab). Its triangle bounds give v in [-1,1], and
c² is the convex combination of (a-b)² and (a+b)² with weights
(1+v)/2 and (1-v)/2. Convexity yields the cosine-law inequality;
monotonicity of arccos gives the angle inequality. Scaling all
three side lengths by sqrt(kappa) handles general negative curvature.

The full ALR01 proof at blueprint207A lines7056–7096 was reread.
Pinned AKP branch vol1, commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245,
`model.tex` lines74–90 and174–211 supplies the sign/scaling convention,
model-angle monotonicity (`k-decrease`) and both cosine laws. Its statement
has the genuine signed curvature parameter, so decreasing curvature
corresponds to increasing the nonnegative parameter used here. The
direct convexity argument is the blueprint's proof, not an assumed
import of the source's unexpanded calculation. The author errata check
and archived/pinned/published distinctions are preserved from the
preceding source record; no tangent-space theorem is used.

## Verification boundary

All three public declarations and the private cosine-law helper are
covered by the manifest axiom gate; source-copy declaration linters,
degenerate-triangle applications and a same-domain comparison consumer
are checked separately. The preceding mathematical leaves and all
blueprint207 TeX files remain unchanged. No full migrated-root build
or human mathematical approval is claimed. AC46's geometric local
injectivity/openness producer and AC47 classification remain open.
