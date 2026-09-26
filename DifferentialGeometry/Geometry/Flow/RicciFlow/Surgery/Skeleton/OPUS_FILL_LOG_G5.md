# G5 fill log (adapted-frame trace inequality)

- 2026-09-26: new file `Perelman/LGeometry/Jacobian/GramIndexBound.lean` (573 lines, 4 private helpers).
  Abstract layer (index `Q` on a submodule `A` of fields: bilinear+symmetric on `A`, boundary identity
  `Q (J i) x = ½(Nb i (x b) − Na i (x a))`, `0 ≤ Q x x` for `x ∈ A` vanishing at both ends):
  `trace_inv_gram_mul_eq_sum_orthonormal`, `trace_inv_gram_mul_boundary_le_sum_index`
  (tr(G⁻¹N) ≤ 2 Σ Q(W,W)), `half_trace_inv_gram_mul_gramDeriv_le_sum_index`
  (½ tr(G⁻¹(c(N+Nᵀ)+2R)) ≤ 2c Σ Q(W,W) + Σ R(W b, W b)). Minimality is re-derived from (α)–(γ),
  no import of the uncommitted G4 file.
- Single flow: `trace_inv_gram_mul_covDerivAlong_le_sum_lRegularizedIndex` (A = span of J, W;
  bilinearity via span induction on chart-differentiability and integrand integrability),
  `half_trace_inv_lGram_mul_lGramDeriv_le_sum_lRegularizedIndex` (τ-parametrized `lGram`/`lGramDeriv`
  of `J ∘ √`, via `covDerivAlong_comp`), `half_trace_inv_lGram_mul_lGramDeriv_le_lK` (adapted
  `W = (s/√τ)P`, `lRegularizedIndex_trace_linear_cutoff_zero` + `lTraceInt_eq`): bound
  `n/(2τ) − lK/(2τ√τ)`, same RHS as `lExpLog_deriv_le` (Jacobian/Basic.lean:855), whose Hessian
  route is `redLength_lap_le` (ReducedLength/LaplacianBound.lean:69).
- Admissible-class caveat as G4: `hnonneg` is over chart-differentiable fields with integrable
  `I(X,X)`; the tree's `lRegularizedIndex_nonneg` gives only C⁸ fields.
- `lake env lean`: clean. Axioms (all six public): propext, Classical.choice, Quot.sound.
  `#lint` on scratch copy: 0 findings. Not registered in DifferentialGeometry.lean (lead).
