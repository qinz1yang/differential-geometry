# NormalPhaseConv

## Role

This file transfers convergence of the normal-coordinate metrics and phase
flows to compact-open smooth convergence of the retained endpoint maps.

## 2026-07-18 framed-radius migration

The smoothness-domain proof now uses positivity of the canonical
`expRadiusGp` profile when extending `phaseRadius_exp` from the quarter ball to
the full framed ball.  Focused verification and the module refresh passed.
No new assumption or convergence theorem was added.

This is consumer machinery only.  The sequence-uniform H6 radius-profile
producer and textbook B1 remain theorem-level 0%.
