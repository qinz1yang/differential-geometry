# HamiltonRHS compatibility note

## 2026-07-12 short-time branch alignment

The merged tensor-fiber API no longer lets downstream occurrences of
`Bundle.continuousMultilinearMap.product_fun` infer the base, model fiber, and
tangent bundle solely through opaque tensor subtraction and inner products.
This produced one heterogeneous-subtraction error followed by several stuck
`VectorBundle` metavariables; the apparent missing `pinchEvol_book_of_mixed`
error was only a cascade from those earlier elaboration failures.

The existing mathematical route and public statements were preserved.  The
ten product occurrences now specify the `Real`, base, model-fiber, and tangent
bundle parameters explicitly.  The defining subtraction in
`ricciGradCoupleAt` uses the same explicit `(0,3)` `show` form as the canonical
`normSq0S_smul_sub_product_one_two` theorem, so its existing rewrite proof
continues to match without a new adapter.

Focused verification passed.  No new theorem, assumption, `sorry`, or
mathematical frontier was introduced.  The Hamilton target rebuild and the
remaining direct short-time consumer still require downstream verification.

Honest progress: the declarations and proofs in `HamiltonRHS.lean` remain
complete (100%); this file's branch-compatibility repair is complete (100%);
Hamilton-target integration is approximately 99% pending its downstream
rebuild; short-time branch alignment is approximately 99% pending Hamilton and
the direct consumer checks.  The merge commit remains 0% until those checks,
the final diff review, and merge-state cleanup pass.  This repair does not
change the separate Hamilton positive-Ricci endpoint or HCG compactness theorem
completion percentages.
