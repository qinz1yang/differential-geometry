# Terminal Ricci Hessian

Current verification 2026-09-09: focused101 EMPTY (28.47s), named101 clean
(38.67s), fresh grouped helper audit101 (23.15s), all five publics standard-only.
The scalar binary-operation and finite-sum helpers are exported with unchanged
proofs for TerminalCurvatureJets. Current claims are in script status.
Receipts/hashes: E:/lean-tools/chapter25-terminal-local-20260909/curvature-jets-completion.json.
Reconstruct the actual covariant Hessian from the checked fixed-chart Ricci
jets and Christoffel coefficients. The spatial local-frame identities in
Evolution/Ricci/JointRegularity apply to a metric independently of regular
time; retain their actual frame-domain assumptions when adapting them here.
The terminal flow is not to be marked regular to reuse a joint-time theorem.

Upstream candidate: one spatial chart formula for totalNabla0S of any smooth
covariant tensor. Keep this local under the lane's no-lower-edits rule.

04:46 source checkpoint: the component reconstruction and sequential limit
argument now produce draft continuity of the actual Ricci Hessian in the
fixed tangent fiber, then of its evaluation on arbitrary fixed vectors.
The proof uses the native finite tensor basis, not a changed model tensor.
That source checkpoint was unverified; the final verification above supersedes it.

Native tensor topology matters: explicitly type tensor0SBasis with codomain
Tensor0SSpace, reconstruct continuity by its finite sum, and evaluate through
tensor0SSpaceContinuousLinearEquiv. Inferring an ordinary multilinear-map
basis/continuity expression can silently select the wrong fiber topology.
For the chart-center limit, first dsimp the component's dependent let, then
rewrite the chart left inverse; one combined simp did not rewrite that let.
