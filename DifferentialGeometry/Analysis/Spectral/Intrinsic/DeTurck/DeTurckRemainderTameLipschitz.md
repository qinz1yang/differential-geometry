# DeTurckRemainderTameLipschitz

## 2026-07-16 principal coefficient extraction

The duplicate local definition of the complete Ricci--DeTurck top coefficient
was removed.  The oversized legacy assembly now imports the canonical public
definition from `DeTurckTopCoeff.lean`; no new facade was added here.

The Lie C0 field construction has now been extracted to the public
`DeTurckCoefficients/LieCorr0Field.lean` module without a Sobolev-ball or
high-order hypothesis.  The legacy private copy remains here because the
later component proof refers directly to its private construction names.

The remaining low-regularity API gap is narrower but substantial: the exact
component readout identifying that field with the raw order-zero arm and the
top-reanchoring tails.  The final readout depends on roughly sixteen thousand
lines of private normal-form algebra in this file, not only on the nearby
field construction.  A public alias here would violate the agreed module
boundary and would still not provide the no-high-order C3 estimate.  The next
honest extraction must first split that algebra into coefficient-layer modules
below the 3000-line limit.
