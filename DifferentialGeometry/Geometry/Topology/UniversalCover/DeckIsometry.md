# DeckIsometry

## Current state — 2026-07-23

This module supplies the metric part of the universal-cover deck action.

- `hasMFDerivAt_deck`: a deck transformation has identity manifold
  differential in the preferred universal-cover coordinates.
- `deck_inner`: the deck action preserves `liftedMetric` pointwise.

The derivative proof stays in scalar/model coordinates.  It rewrites both
cover charts through `extChartAt_proj_eq` and uses `proj_deckAct`; it does not
assert an equality of whole bundle trivializations.

## Progress accounting

- Deck-action metric producer: complete; focused verification passed.
- `ham3_space_box`: open (0%).
- Dedicated positive Killing--Hopf/quotient machinery: approximately 24%.
