# FamilyContinuity.lean

## Purpose

`integral_family_cont` is the integration-layer continuity producer for a
moving Riemannian integral on a compact time set.  Its hypotheses are only
entrywise joint continuity of the metric Gram matrices and joint continuity of
the scalar integrand on that set.

## Proof route

The global integral is decomposed by the canonical finite partition of unity.
Each chart term is pulled back to the fixed model Haar measure.  The pulled-back
POU support is compact, so continuity on the compact product supplies one
integrable indicator bound.  Filter-form dominated convergence proves
continuity of each chart term, and the finite sum gives the invariant result.

This avoids a global chart selector, `HasLocallyConstantChartAt`, and any
tensor-valued global trivialization.

## Verification

Focused verification passed.  The file is warning-free and the theorem uses
no additional chart-selection or consumer-side regularity assumptions.
