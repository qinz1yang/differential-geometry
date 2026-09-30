# Complete-buffer residual correction

Three public metric theorems in `Topology/MetricSpace/ResidualCorrection.lean`
prove AC14 and the complete-buffer convergence/openness part of AC23.
They apply to an actual map f:X->Y between arbitrary metric spaces,
with the actual residual e(x)=d(f(x),y). They do not produce geometric
correction moves from a paired packet.

## Exact contract

Fix a center q, radius r, constants mu>0 and 0<=rho<1, and target y.
Assume the closed r-ball at q is complete, f is continuous on that ball,
and e(q)<=mu*r. At every x in that ball with 0<e(x)<=e(q), assume there
is a point z in X such that

    e(z) <= rho*e(x),     mu*d(x,z) <= e(x)-e(z).

Then there is z in the SAME closed ball with f(z)=y and
d(q,z)<=e(q)/mu. The correction witness is not assumed to lie in
the complete ball. No correction is required outside the residual
sublevel, or at a zero residual. Neither X nor Y is required to be
complete as a whole. The non-strict initial inequality allows a
solution on the boundary and includes the zero-radius case.

The proof constructs iterates inside

    S = {x : mu*d(x,q)+e(x) <= e(q)}.

The displacement inequality proves invariance and inclusion in the
complete ball before completeness is used. Zero residuals give stationary
iterates. Residuals decay geometrically, and the same estimates bound
successive distances by (e(q)/mu)*rho^n. The sequence is Cauchy;
continuity on the closed ball identifies its limit with the target.
The invariant yields the sharper e(q)/mu displacement bound, rather
than the looser bound obtained by merely summing the geometric series.

The second theorem assumes these moves for every target in
B(f(q),mu*r) and proves the quantitative inclusion

    B(f(q),mu*r) subset f(B(q,r)).

The third theorem assumes a continuous map and such complete balls
and moves at every center and below EVERY positive requested radius.
It proves `IsOpenMap f`. Repeating the construction inside arbitrary
open source sets is essential; openness of a single image neighborhood
would not prove this conclusion. Constants need not be uniform between
centers or requested radii.

## Checked sources and comparisons

Read BGP1992 English, Remark5.1.1, Definition5.2, Theorem5.4 and its
successive-correction proof5.8, printed17–19/PDF18–20. Its simplifications
assume curvature zero and available geodesics; those are not imported as
geometric producers. Its apparent missing reciprocal in the final
displacement coefficient is avoided by the proved telescoping invariant.
This is a project source observation already retained in revision64,
not an author-issued correction.

Read BBI, AMS2001, Proposition10.8.15 and its complete proof, printed385–386/
PDF400–401. Retained author errata dated July6,2024, PDF13, correct the
printed386 direction inequality and angle index; those geometric steps
are not imported here. The printed proof's use of diam(U) alone does
not justify remaining inside an arbitrary open U. The blueprint's
specified complete ball and buffer, and the explicit invariant above,
provide the containment actually used in this Lean proof. This source
observation is not attributed to the author errata.

Blueprint207A AC14 and AC23, with revisions64–65's source comparisons,
are the project contracts. AC23 needs moves only on the invariant
residual sublevel; the new general theorem preserves that weaker
hypothesis. The stored bounded BGP errata search in revision64 is
reused; it did not confirm a dedicated correction sheet and does not
certify that none exists. Fresh source hashes and exact locators are
in `evidence/residual_correction_sources.json`.

## Remaining boundary and verification

Actual negative-curvature finite differences, almost-radial points,
paired geometric correction moves and the largest-coordinate estimates
must still supply AC23's hypotheses. This result is neither full AC23
nor the curvature/dimension recognition theorem AC46. No PC migration
interface is touched. Scoped builds, all new axiom closures, declaration
linters and concrete correction examples are recorded separately.
Blueprint207 and earlier mathematical leaves are unchanged.
