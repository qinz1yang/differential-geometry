# P1AxiomCheck

This narrow audit file prints the axioms of the P1a project endpoints, the
compact-tail continuation bridges used by the incomplete-manifold route, and
the strict-volume producer chain through sectional curvature.  It cannot
certify the still-missing local compact-closure Bishop--Gromov endpoint.

Focused verification passed after refreshing the two upstream modules whose
new declarations had stale artifacts.  Every printed endpoint and continuation
bridge depends only on `propext`, `Classical.choice`, and `Quot.sound`; no
project axiom or `sorryAx` appears.

That result now applies to all seven accepted project-used endpoints and the
listed continuation/producer bridges.  The expanded audit includes the
pole-Haar, Euclidean model-ball, radial rigidity, sectional-to-Ricci, and final
strict sectional-volume declarations.  The two Euclidean wrappers live in the
dedicated `SegmentBallEuclideanStrict` module so their global inner-product and
measure instances match the checked Euclidean normalization layer.  After its
warning-free focused check and named refresh, the expanded audit passed: all 20
printed declarations depend only on the three standard logical axioms above.
The eighth endpoint, local compact-closure Bishop--Gromov, remains unstated and
therefore remains outside this audit.

The P1b expansion includes the radial-control adapters, both local and global
CGT injectivity producers, the explicit volume-to-injectivity assembly, and the
realized bounded-geometry and Ricci-flow injectivity consumers.  The expanded
audit passed focused verification: all 28 printed declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

This certifies the listed P1b producer and consumer machinery, not the two exact
local-on-balls P1b endpoints.  Those remain zero of two because the incomplete-
ambient compact-closure bridge and the bounded-ball propagation adapter are not
yet stated and proved.
