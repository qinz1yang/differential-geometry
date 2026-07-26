# EmbeddingSubcritical

## 2026-07-16 uniform closed-manifold constant

`sobolev_closed` moves the existential Sobolev constant before the test
function.  Its constant is `max 1 D.toReal`, where `D` is the finite sum of
the already uniform per-chart constants; hence it depends on the fixed metric,
exponent, and canonical atlas partition, not on `u`.  The previous
`sobolev_embedding_subcritical_of_closed` API remains as a direct
specialization.

The theorem is the constant-first Sobolev input needed for a future
log-Sobolev estimate.  It does not prove that estimate or a fixed-metric W
lower bound.  Focused verification passed without warnings or a new `sorry`.

The same pass removed a pre-existing deterministic `whnf` timeout in the
`fderiv` support-restriction helper by supplying the measure, exponent,
function, and set arguments explicitly to the generic indicator lemma.  This
changed only elaboration normal form, not the statement or mathematics.
The uniform Sobolev producer is **100%**; `w_fixed_lower` remains
theorem-level **0%**.
