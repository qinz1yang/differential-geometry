# Realized scalar operator notes

## 2026-07-22: drifted product rule

- Added `driftTerm_mul`, the pointwise product rule for the drift term.
- Added `heatDrift_mul`, combining `driftTerm_mul` with the existing
  `laplacianAt_mul_of_scalarRegular` theorem.
- Focused verification passed, and the named module artifact was refreshed so
  downstream maximum-principle files can use the new export.

These are generic localization primitives.  They do not prove a noncompact
maximum principle or construct quantitative Ricci-flow cutoffs.  The corrected
complete-Bernstein theorem remains theorem-level 0%; its dedicated
localization machinery is about 35--40%, while the unconditional HCG
compactness theorem remains theorem-level 0% and the whole HCG support
machinery remains about 60%.

## 2026-07-22: additive drifted operators

- Added `driftTerm_add`, `laplacianAt_add`, and `heatDrift_add` at the generic
  realized-metric-family layer.
- The proofs reuse `gradientFun_add` and `divergence_add`; no Bernstein-specific
  data or compactness assumption enters the statements.
- Focused verification passed, and the named module artifact was refreshed for
  the finite-sum parabolic consumer.

This additive API brick is complete (100%).  It is only calculus
infrastructure: the corrected complete-Bernstein theorem remains theorem-level
0%, its dedicated localization machinery is about 45--50%, and the
unconditional HCG endpoint remains theorem-level 0%.

## 2026-07-23: drifted chain rule

Added `heatDrift_comp`:

`H_X (φ ∘ f) = φ'(f) H_X f + φ''(f) |∇f|²`.

The theorem is a thin family-facing assembly of the canonical
`laplacian_comp` and `gradientFun_comp` rules.  It needs no regularity
hypothesis on the drift field and introduces no parallel composition API below
this layer.

Focused verification passed with no diagnostics.  The theorem is complete
(100%); it supplies route-neutral scalar calculus and does not produce the
geometric cutoff required by `ShiCutoffData`.
