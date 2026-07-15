# NormalCoordinates

## Role

This module packages the canonical exponential partial diffeomorphism and its
inverse normal chart at a base point.

## Current state

- `expMapDiffeo` now selects the existing `exists_exp_pd_chart` witness.  Its
  public type and the definitions depending on it are unchanged.
- `zero_mem_expMapDiffeo_source` and `expMapDiffeo_apply_eq` remain the canonical
  projections from that selected witness.
- `exp_target_sub_chart` exports the retained fact that the selected target lies
  in `(chartAt H p).source`.

Focused verification passed without warnings or local `sorry`s.

## Frontier and accounting

The canonical choice-spec repair is complete.  The immediate consumer is the
selected quantitative diagonal branch: target-in-chart containment should put
the first coordinate of `normalPair` in the fixed tangent trivialization base
set and upgrade `B.dom` containment to `B.readDom`.

This is producer machinery only.  `StepB1RawInput` and textbook B1 remain 0%;
dedicated Step-B/B1 machinery is about 76%, Chapter 4 machinery about 73%, and
whole HCG compactness machinery about 50%.
