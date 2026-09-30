# AC13/ALG06: actual intrinsic topology and complete inner balls

Nine public theorems and one definition in three leaves build the actual
finite intrinsic metric on an open ambient ball, identify its topology,
and prove its complete inner balls. The constructor intrinsicBallMetricSpace
uses the previously PROVED all-pairs finiteness theorem; its metric is the
all-path intrinsic distance, with exact edistance and real-distance formulas.
The ambient space only needs the explicit length-curve property for topology
and identification. Ambient completeness is required only for the complete
inner-ball theorem. No local compactness or geodesicity is assumed here.

The generic topology theorem compares two pseudometrics on the same type:
one dominates the other, and their radial distances agree sufficiently
near each point. It proves equality of the generated topologies by ball
neighborhoods. For the actual intrinsic ball metric, the local radius
(L-d(x,o))/8 satisfies the previous4h margin. Thus its generated topology
is exactly the ambient subspace topology. Inclusion is an open embedding
and is distance-nonincreasing from the induced metric to the ambient space.

If X is complete and d(p,o)+r<L, the closed r-ball in the ACTUAL intrinsic
metric is complete in its own generated uniformity. This applies the earlier
embedding/nonexpansive completeness transfer, now to the constructed metric.
It includes zero and negative radii. If h>0 and d(p,o)+4h<L, the image under
inclusion of the intrinsic closed h-ball equals the ambient closed h-ball.
The proof uses local distance equality and proves every ambient point in
that ball belongs to the open domain. With completeness, these give AC13's
common complete balls. The actual induced length property remains separate.

Lean instance audit: supplying a MetricSpace instance on a subtype alone
can leave existing subtype topology or distance parents selected by inference.
The new inclusion, Lipschitz, complete-ball and ball-image statements therefore
name the constructed metric/topology/uniformity and their parent instances
explicitly. Proof applications likewise specify these structures where
needed. They do not accidentally prove claims about the original subtype
metric. Exact constructor distance formulas and explicit-structure review
examples accompany the result.

Sources checked: blueprint207A AC13 full2713-2755 and ALG06 full7536-7580;
previous source readings for the actual path construction and4h equality
are reused unchanged. Mathlib MetricSpace/Pseudo/Defs.lean820-844 was freshly
read for the open-ball topology characterization. Accepted
LipschitzBufferCompleteness.lean and IntrinsicBall.lean bodies are the reused
complete-filter and local-distance engines. Exact source hashes/locators and
retained BBI errata qualifications are recorded separately.

The remaining AC13 induced length proof and ALG06 radial/ambient assembly
are open. Blueprint207 and earlier mathematical leaves remain unchanged.
No PC interface is changed and Chapters3-4 are not claimed complete.
