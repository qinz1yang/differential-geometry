# CutoffProfile

## Role

`CutoffProfile.lean` supplies the route-neutral one-dimensional profile used by
future geometric cutoff constructions.  It reuses `Real.smoothTransition` and
squares the decreasing transition, so the profile has:

- values in `[0, 1]`;
- an exact inner plateau and outer vanishing region;
- `deriv_nonpos`, the global decreasing-sign needed for a lower parabolic
  bound on an exhaustion function;
- global first- and second-derivative bounds; and
- the absorption estimate `(deriv value s) ^ 2 ≤ C * value s`.

The squared profile is the useful normalization for Bernstein estimates because
it controls the gradient cross term without dividing by a cutoff that may
vanish.

## Verification

The file passes its focused Lean check with no diagnostics.  It contains no
`sorry`, `admit`, or new axiom.

## Honest status

This closes the scalar-profile layer, not the geometric producer of
`ShiCutoffData`.  A solution-generated `ShiCutoffData` theorem remains unstated
and therefore theorem-level 0%.  Its remaining analytic core is a quantitative
smooth parabolic exhaustion, or alternatively a barrier-localized maximum
principle using evolving distance.  Neither follows from the static profile.

Current accounting:

- this scalar profile API: 100%;
- solution-generated `ShiCutoffData`: 0%;
- corrected complete-noncompact Shi theorem: 0%;
- dedicated P4 consumer machinery: about 97%;
- unconditional Theorem 3.10: 0%;
- whole HCG compactness machinery: about 60%, with unconditional endpoints
  still 0%.

## 2026-07-24: extended-real and plateau API

Added the canonical extended-real evaluation `evalue`, its agreement with
`value` at finite inputs, continuity and range lemmas, antitonicity, and exact
inner/outer plateau formulas.  The first and second derivatives are now proved
to vanish on both constant regions.  These are the lower scalar facts needed
by the barrier cutoff; they do not encode any geometric cutoff assumption.

Focused and exact verification are current.  The cutoff-profile theorem layer
and dedicated machinery are 100%.  The solution-generated barrier cutoff is
accounted separately until its own focused and exact checks pass.
