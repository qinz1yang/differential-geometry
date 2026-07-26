# Retraction--coretraction parametrix algebra

## Source facts

- `localParametrix E H R = R ∘ H ∘ E` extracts genuine forcing data,
  applies the diagonal local heat solver, and reassembles once.
- `fixedReassemble_dt` and `fixedExtract_dt` prove that fixed extraction and
  reassembly maps commute with the time derivative; no derivative-of-chart or
  derivative-of-cutoff term appears.
- `chartProjection_idem` proves `P² = P` for `P = E ∘ R` from the genuine
  retraction identity `R ∘ E = id`.
- `retractParametrix` proves the exact identity
  `T (R H E) = id + C H E` from the local solver identity, the forcing
  retraction identity, and the localized global-operator identity.
- `retractParam_split` gives the exact decomposition into the spatial
  second-order oscillation arm `B₂` and the first/zero-order
  cutoff-transition arm `B₁₀`.
- `principalError` and `lowerError` are the actual chosen-space operators
  `C₂ ∘ D₂ ∘ H ∘ E` and `C₁₀ ∘ D₁₀ ∘ H ∘ E`; `factoredError` is their sum.
  The corresponding `_norm` and `_le` theorems derive their operator bounds
  from the coefficient and complete heat-jet maps rather than assuming a
  bound on an unnamed `B`.
- `lowerTime` is a positive family-independent horizon, at most one, chosen
  from the fixed lower multiplier and zero-trace jet constants.
  `b10Error_quarter` proves that the concrete lower error is strictly
  quarter-small whenever the complete lower jet has its expected
  `sqrt τ` gain.
- `retractParam_factor` gives the exact identity with both error arms factored
  through their genuine jet carriers.
- `parametrixError_id` fixes the Neumann orientation as
  `B = T Q - id`, hence `TQ = id + B`.

No commutation between the local heat solver and the compatibility projection
is assumed or used.  This is the key correction to the discarded
post-projected-Duhamel route.

## Verification state

Source implementation completed on 2026-07-19.  Lean verification is pending
because the shared named build/export lane currently owns the build lock.  No
Lean process was started for this file, and no `sorry`, `admit`, axiom, opaque
placeholder, or new foundational instance was introduced.

The abstract error-norm frontier has now been removed: the remaining analytic
inputs are concrete coefficient and heat-jet map estimates.  However, the
local frozen heat identity `L ∘ H = id` is not yet an actual theorem.  The
next required producer is the zero-trace frozen Duhamel identity
`(∂t - A : D²) Hf = f`, first for the isotropic kernel and then after the
fixed linear conjugation.  Until that is proved and the W3p carrier is
instantiated, `ricci_flow_unif_existence` remains 0%.
