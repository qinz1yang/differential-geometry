# Exact factors, dimension drop and the same pointed limit

This checkpoint proves AC44 and the covering-input part of AC45, with
same-limit applications and the full-rank Euclidean case of AC48. It adds
28 theorems and one definition in eight mathematical modules. It does not
prove AC45's geometric production of polynomial nets from Alexandrov
curvature and a Hausdorff-dimension bound (AC07/AC04), or AC46/AC47's
one-dimensional recognition and global classification. Blueprint 207 is
unchanged. Source/statement bindings are in `evidence/factor_dimension_sources.json`.

## Actual product and factor geometry (AC44)

An exact splitting here is an onto `IsometryEquiv`
`X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y)`. Both Euclidean space and
its product with Y have their actual Pythagorean metrics. An arbitrary
product of Lean metric spaces would have a different default metric.

The generic slice results allow any first metric factor E and a specified
point u in E. The new definition is an actual isometry from Y onto the
closed subtype `{x : X // (e x).fst = u}`. Completeness and properness pass
from X to Y separately. Triangle equality between two points of this slice
forces the intervening point to stay in the slice. Thus every minimizing
segment stays there; if every pair in X has a constant-speed minimizing
segment on [0,1], the same is true in Y. Coincident endpoints are included.

Global four-point comparison (at any parameter kappa of the existing
comparison definition) pulls back through an isometric embedding. This
supplies nonnegative comparison on the actual factor when X has it. No
local-to-global curvature theorem is assumed inside this restriction.
The slice embedding gives dimH Y <= dimH X. For Euclidean first factor,
a specified point of Y supplies the opposite embedding and k <= dimH X.
The latter point is needed to exclude the empty-product case.

## Exact covering estimate (AC45)

Let k <= n be natural numbers, let e be the onto splitting above, and
assume e(p)=(0,q). Fix delta in (0,1], C>0, and a real radius R. Suppose
that, for every epsilon in (0,1], the closed source ball of radius
S=R+sqrt(k)+1 about p has an internal epsilon-net of cardinality at most
C epsilon^(-n). Then the closed R-ball about q has a finite internal net
F satisfying

    |F| <= 3^n C delta^(-(n-k)),
    for every y in the ball, some z in F has d(y,z) < delta.

This is the blueprint's exact constant; coverage is slightly stronger
(strict), and R need not be positive. Negative-radius balls are empty.
The uniform input constant C is fixed before epsilon. No properness,
completeness, geodesicity or curvature assumption is required for this
metric implication. The full dimension corollary assumes these source
nets for every positive S, with C allowed to depend on S, and gives
Mathlib's actual Hausdorff dimension dimH Y <= n-k.

The proof constructs a delta-separated Euclidean grid in [0,1]^k with
at least delta^(-k) points. Multiplying it by any delta-separated finite
factor set and using an ambient delta/3-net bounds the product cardinality.
The finite packing-to-net theorem is applied with floor(3^n C delta^(-(n-k))),
so no rounding factor is lost. Countable integer-radius exhaustion and
the earlier polynomial-net Hausdorff-dimension theorem finish the proof.
The grid theorem itself allows every delta>0, including delta>1 and k=0.
No general product Hausdorff-dimension equality is imported.

## Zero-dimensional geodesic factor and AC48's full-rank case

A nonconstant metric segment is an antilipschitz image of [0,1], so its
ambient space has Hausdorff dimension at least one. Consequently, a space
with exact minimizing segments between every pair and dimH<1 is
subsingleton. No curvature, completeness or properness is needed here.

For an exact k-splitting with source polynomial covering exponent k,
AC45 makes the geodesic factor zero-dimensional and therefore singleton
(the chosen factor basepoint supplies nonemptiness). Composing the actual
splitting with the singleton-product isometry yields an actual pointed
isometry X to Euclidean k-space, taking p to zero. This holds for k=0 too.
For k=2 this is the plane case of AC48, conditional on the supplied
covering bounds; it does not produce the remaining line/ray/interval/circle
factor models or smooth structures.

## Application to the same limit

For the existing pointed convergence of (X_i,p_i) to (Y,q), assume

    for each R>0 there is C_R>0 such that for each eta in (0,1],
    eventually in i the closed R-ball at p_i has an internal eta-net
    of size <= C_R eta^(-n).

The eventual index may depend on R and eta; C_R may not depend on eta
or i. The new transfer constructs polynomial nets at EVERY center z in
that same Y, using source radius R+d(z,q)+1 and constant C 4^n 2^n.
It recenters the finite image centers internally. No source properness
or completeness is needed. The auxiliary transfer allows real exponents.

Consequently every supplied Euclidean k-splitting of that target, with
a specified factor point and k<=n, has factor dimension <=n-k. A separate
rank lemma proves k<=n from the source bounds. The factor chosen at the
splitting origin need not correspond to q. A real-line version uses
Mathlib's canonical singleton orthonormal basis to identify R with
Euclidean 1-space.

Given properness, global nonnegative comparison, exact segments, and an
actual specified line gamma:R->Y, the previously proved splitting theorem
now gives an aligned onto splitting and a factor with properness,
completeness, geodesics, comparison, and dimension <=n-1 (n>=1). There
is no assumption gamma(0)=q. Alignment means e(gamma(t))=(t,z) for all t.

Finally, actual near-short source curves, eventual source-ball four-point
comparison with kappa_i>=0 tending to zero (curvature parameter -kappa_i),
and the source covering hypothesis produce one target, one basepoint and
one subsequence, followed by the preceding conclusion for every actual
line on that target. It applies the existing extraction theorem and
restricts source eventual estimates along that same subsequence. It does
not replace the target or infer that a line exists. Given a full-rank
pointed splitting, the same target is pointed-isometric to Euclidean space.

## Source check and remaining boundary

Targeted body reading: BBI, AMS 2001, Proposition 1.7.19, printed 23/PDF 38;
KL, Asterisque 365 (2014), section 2.2 printed 20/PDF 15 and Definitions 4.1–4.2,
Sublemma 4.5 printed 28/PDF 23; blueprint 207A AC44–AC45 and AC48, with
revision 71's source comparison. Hashes and exact DAG locators are retained
in the source record. The covering proof is the blueprint's expanded
packing argument. Mathlib supplies independent checked dimension facts.

The retained BBI errata dated July 6, 2024 were reread at PDF 1–2 and 13,
including the printed 22 correction to the Euclidean Hausdorff-measure
argument and splitting corrections. The retained KL correction sheet,
body dated May 15, 2015, lists corrections to 6.5, 14.1(2), 20.2; none lists
the selected product passages. Current remote errata bytes were not
verified. This is targeted source checking, not a full-book audit.

Local-to-global comparison, curvature-to-covering production, actual
lines and compatible higher-rank splittings from collapse, one-dimensional
recognition/classification, and later smooth local models remain separate.
The accepted metric leaves do not use the skeleton's existing admissions.
Verification receipts distinguish scoped Lean checks from the unbuilt
full migrated PC root and from the blueprint's static consistency audit.

## Executed verification

The final combined build checks 62 manifest modules (2840 Lake jobs) and
565 owned constants, including generated/private declarations. It accepts
only propext, Classical.choice and Quot.sound. The eight new modules add
29 authored declarations (28 theorems and one definition), with 41 owned
constants including generated helpers. The supplement checks 19 actual
proof-dependency paths and six compiled review applications. Exact receipts
and source hashes are in `evidence/verification.json` and
`evidence/factor_dimension_verification.json`; those are authoritative.

An inherited AreaUpperBarrier declaration emits its existing admission
warning during the combined build. No audited new declaration depends on
that admission, and existing skeleton admissions are unchanged. No full
migrated PC-root build or human mathematical approval is claimed.

The mandatory blueprint static audit stops at a historical absolute archive
path after the folder move; see `evidence/factor_dimension_blueprint_audit.log`.
This is not a passing document audit. All three blueprint207 TeX hashes and
the old clean PC baseline are unchanged, as recorded in
`evidence/factor_dimension_preservation.json`.
