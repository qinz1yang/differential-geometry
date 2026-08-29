# RegIndexAlgebra

## Scope

This module supplies the bilinearity API used to expand a broken-field
regularized L-index form.  It is native to the fixed-manifold Perelman
L-geometry layer and imports only `RegIndex`.

## Public API

- `lRegIndexInt_add` and `lRegIndexInt_smul` prove additivity and homogeneity
  of the pointwise density in the first field.
- `lRegIndexInt_add_r` and `lRegIndexInt_smul_r` give the corresponding
  second-field statements by the existing symmetry theorem.
- `lRegIndex_add` and `lRegIndex_add_r` lift addition to interval forms with
  explicit `IntervalIntegrable` hypotheses for both summand densities.
- `lRegIndex_smul` and `lRegIndex_smul_r` lift constant homogeneity to interval
  forms.  No integrability hypothesis is needed there because the interval
  integral's scalar-linearity theorem is unconditional.
- `lIndexInt_congr`, `lIndex_germ_congr`, and `lIndexInt_int_iff` transport the
  density, its interval integral, and interval integrability across equality of
  curve/field germs.  Endpoints are discarded only through the standard
  almost-everywhere argument.
- `lIndex_adj` gives adjacent-interval additivity under the two honest
  integrability hypotheses.
- `lIndex_sq_add` gives the symmetric quadratic expansion for `Y + c W`.  Its
  `YY`, `YW`, and `WW` densities are all explicitly assumed interval
  integrable; the theorem does not rely on false unconditional additivity of a
  nonintegrable Bochner integral.

The pointwise addition statements require differentiability only for the two
fields being added, exactly where `covDerivAlong_add` needs it.  Constant
homogeneity requires no differentiability hypothesis because
`covDerivAlong_smul` is unconditional.  The right-field statements reuse the
native symmetry API and therefore retain its ambient `SigmaCompactSpace`
assumption.

## Verification

Focused verification passed without warnings or placeholders.

## Project position

The target nonconjugacy theorem `lMinVec_nconj_lt` is now complete; this file
supplies its reusable algebra and germ-transport layer.  `redVolume_anti`
remains unproved (0%).
