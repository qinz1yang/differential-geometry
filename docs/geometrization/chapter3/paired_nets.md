# Actual pointed maps from paired nets: MC13, construction step 3

`PointedBallApprox.ofPairedNets` implements the actual-map part of the
countable extraction argument in master207A.tex:1400–1430, in the proof of
`thm:metric-eventual-compactness`. The source-expanded MC13 proof is recorded
in metric_geometry_contracts.csv; the BBI8.1.10 outline (printed274–275,
PDF289–290) does not itself supply these finite-map details.

Given two metric spaces, labelled points x(a), y(a), and a distinguished
label with x(0)=p, y(0)=q, assume:

1. 0<η, 3η<ε<R.
2. Every point of the closed source R-ball is within distance ≤η of an x-label.
3. Every point of the closed target (R−ε)-ball is within distance ≤η of a y-label.
4. Every labelled pair has distance distortion strictly less than η.

Then there is an actual closed-ball pointed approximation with radius R,
error ε, and exact basepoint. Its map chooses a nearby label, selecting label
0 at p. Target coverage follows even when the label chosen at x(a) differs
from a. Labels may coincide; maps need not be continuous. The labels do not
have to lie in the source R-ball. The coverage proof shows that the relevant
source representative does lie there using the matrix radial estimate.

Finiteness of the label type is not needed for this one step. The general
constructor therefore accepts any labelled nets; finite matrix convergence
and diagonal extraction must still produce its inputs. This is a substantive
constructor for MC13, not a proof of the entire extraction theorem.

Source: the displayed quantitative-map proof was read during implementation;
no new curvature, dimensional, completeness, or PC reuse claim is made.
The scoped gate compiles this constructor and audits its transitive axioms.
