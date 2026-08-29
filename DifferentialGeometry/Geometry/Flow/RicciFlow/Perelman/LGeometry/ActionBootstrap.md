# Fixed-chart C1-to-C2 bootstrap

## Result

`lChartVel_c1` starts from the actual nonlinear fixed-chart weak Euler identity
with the native raw `lChartForce`.  A continuous representative `q0` of the
time-`H¹` weak derivative is inserted into `lChartForceRep`; the resulting
force is continuous and agrees almost everywhere with the raw force.

The proof constructs the chart Gram measurability and uniform bound with
`chartGram_time`.  It doubles both the original weak identity and the force,
as required by the normalization in `chartVel_rep_c1`, and transfers the force
integral through the genuine almost-everywhere equality.  No frozen
coefficient or supplied regularity conclusion is used.

The theorem asks only for continuity and almost-everywhere equality of `q0`.
An explicit `derivWithin u.toFun = q0` hypothesis would be redundant: it already
follows from `toFun_c1_of_rep`, so the theorem applies in particular to the
stronger first-stage output carrying that equality.

## Verification and project position

Focused verification and the explicitly named module refresh both passed.  The
source has no `sorry`, `admit`, or axiom declarations, and its sole public name
is within the twenty-character project limit.

This composition module is complete (100%).  The exact next geometric consumer
is to feed `lChart_weak_euler` and the first-stage continuous velocity
representative directly into `lChartVel_c1`, once `ActionWeakEuler` itself has
passed focused and targeted verification.  Its nested-Hom topology issue is
resolved, but the private `lWeakScal_int` and `lWeakCoeff_line` declarations
currently hit elaboration limits and are being split into smaller producers.
Once those checks pass, the composition produces the C2 chart curve needed to
identify the classical Euler--Lagrange ODE.  Dedicated L-geometry machinery is
roughly 86% complete.  The terminal
`exists_lMinimizer` and `redVolume_anti` theorems remain 0% until each is stated
and proved; the broader P2 endpoint remains below 1%, and the whole Poincare
program remains roughly 3--5% complete.
