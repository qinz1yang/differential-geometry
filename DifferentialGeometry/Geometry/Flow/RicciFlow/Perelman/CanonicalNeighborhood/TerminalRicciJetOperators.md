# Terminal Ricci jet operators

Current verification 2026-09-09: focused101 EMPTY (30.00s), named101 clean
(42.77s), fresh grouped helper audit101 (23.15s), all five publics standard-only.
mapCInfConv_chartJetOperator is now exported with its proof unchanged, and is
consumed by TerminalCurvatureJets for all curvature derivatives. Receipts/hashes:
E:/lean-tools/chapter25-terminal-local-20260909/curvature-jets-completion.json.
Use the existing sequence C-infinity calculus on the full family of terminal
metric jets. Native jet2, jetChristoffel and jetRicci preserve the actual fixed
chart and chartModelBasis. This avoids a new filtered jet-composition calculus.
The sequence criterion now recovers full-family terminal convergence of
actual Ricci jets on compact subsets. TerminalRicciHessian and TerminalRicciRHS
already supply the actual Hessian and evolution reconstruction; the all-order
curvature continuation is now proved in TerminalCurvatureJets.

For MatJet properness, install finite-dimensionality and properness of its
individual continuous-linear-map factors, then use product properness.
Direct product Module inference ran out of the default typeclass budget.

Upstream candidate: stability of jet2 under MapCInfConvOnCompacts. Keep the
implementation in this lane under the no-lower-edits ownership rule.
