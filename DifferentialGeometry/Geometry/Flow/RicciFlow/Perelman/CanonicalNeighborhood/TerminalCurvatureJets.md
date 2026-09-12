# TerminalCurvatureJets

Verified 2026-09-09: focused106 EMPTY (24.86s), named106 clean (36.23s), fresh
six-public audit106 standard-only (22.59s). Current source SHA256:
f00b2db81443396b17d93893679c6eca64881d54e5e7b2957b69414c4f3a4c16.
Exact five-file acceptance and reproduction receipts:
E:/lean-tools/chapter25-terminal-local-20260909/curvature-jets-completion.json.

The file proves actual terminal left continuity of every nablaKRm04Field, its
evaluation on fixed vectors, and its intrinsic squared norm in the moving
metric. An eventual interior bound therefore holds at the terminal slice with
the same constant. The ancient-flow adapter needs only the existing solution
on ancientTimeInterval; the ancient-kappa adapter allows any interval
presentation with the existing carrier and regular equalities.

Reuse TerminalChartJets for all Gram jets, TerminalRicciJetOperators' finite-jet
composition argument, native iter_comp_conv for every covariant order, and
TerminalRicciHessian.totalNabla0S_chartComponent for the actual tensor identity.
The base curvature component is the native rm04_coord_eq formula; retain its
slot order (idx2,idx0,idx1,l) and the chartModelBasis rather than Module.finBasis.

Three already proved private helpers were exported from TerminalRicciJetOperators
and TerminalRicciHessian without proof changes. Saved-file checks, named refreshes
and fresh audits include those exports. The actual TerminalBackwardExtension
consumer now calls the theorem directly, with no hjet or replacement assumption.

The four other slab interfaces remain separate obligations. This proof assumes
an existing IsSolutionOn; it cannot be used to construct the scalarTime field
of a newly extracted limit. Original Chapter25 proof-slot counts are unchanged.

Iteration findings: keep the constant model frame typed as a tangent-vector
field. An unprotected lambda into E made rw/simp fail at implicit transparency
inside iterCovComp, despite definitional equality with the tangent fiber.
Use congrArg for the dependent Fin.cons tuple before the spatial derivative
step. For the norm, native continuousAt_matrix_inv with Ring.inverse_eq_inv'
avoids ambiguous pointwise-function inverse/smul rewrites. Compute the norm by
the inverse Gram matrix in the fixed chart basis, not an auxiliary fixed norm.
Claims and the shared verification window remain in WORKING_STATUS/script status.
