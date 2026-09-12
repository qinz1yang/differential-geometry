- `thm:ksol-fixed-kappa-compactness` (stretch goal of the Chapter 23 terminal-boundedness lane), plus
  the limit-noncompactness transfer of `lem:ksol-noncompact-asymptotic-shrinker`. Two public
  theorems: `exists_fixed_kappa_compactness_of_rankOne` and `klim_pointedLimit_noncompact`.
- Mechanism: `exists_preliminary_klim_compactness` already produces the subsequence, the pointed
  maps, `KLim κ L`, `PointedFlowScalarAtBase L 1`, the canonical slice convergence and the all-order
  mixed comparisons; all of those are re-exported verbatim so nothing is lost. The single new
  conjunct is `KLim.isAncientKappaSolution_of_rankOne` applied to `L` with
  `Module.finrank ℝ ThreeSpace = 3`, i.e. the missing `globalScalarBound` field. Noncompactness is
  `pointedLimit_noncompact_of_connected_noncompact_sources` applied to `Phi.atTime (L := L) 0`
  (`PointedFlowSlices.atTime` reinterprets the flow atlas as a Riemannian one at a fixed time);
  `(X.atTime t).obj i` is definitionally `(X.term i).atTime t`, same carrier and same topology, so
  the source hypotheses are stated directly on `X.term i`.
- Dependencies: `KLimThreeBounded` (hence the deferred trichotomy interface), `PreliminaryCompactness`,
  `NoncompactPointedLimit`.
- Pitfall: the rank-one branch `lem:ksol-rank-one-terminal-bounded` can only be stated for the limit
  the theorem produces, so it is an implication INSIDE the conclusion, not a hypothesis;
  `hnoEmbedding` stays an ordinary hypothesis. The file re-enables the three carrier instances of
  `UpstreamTerminalTrichotomy` with `attribute [local instance]` next to
  `PreliminaryCompactness`-style projection instances, so the `TerminalSurfaceProduct` in the
  conclusion is the same record as in the trichotomy. Do not open
  `DifferentialGeometry.Geometry.Riemannian.Topology` here: with `open scoped _root_.Topology` it
  makes `Topology.IsEmbedding` ambiguous, hence the explicit `_root_.Topology.IsEmbedding`.
- Verification: imports unbuilt modules, so checked against the read-only hardlink mirror described
  in `KLimThreeBounded.md`: `lake env bash -c 'LEAN_PATH="<mirror>;$LEAN_PATH" lean <file>'` 20.1s,
  output EMPTY; with the lakefile lean options 21.5s, output EMPTY. The four-file concatenation
  scratch also compiles (21.3s, only the expected `sorry` warning). Axioms:
  `exists_fixed_kappa_compactness_of_rankOne` = `propext, sorryAx, Classical.choice, Quot.sound`
  (both `exists_preliminary_klim_compactness` and `KLim.three_terminal_bddAbove_of_positive` already
  carry `sorryAx` independently of the new interface); `klim_pointedLimit_noncompact` =
  `propext, Classical.choice, Quot.sound`.
- Next step: after the reviewer refreshes the three upstream new modules, run the ordinary focused
  check. Universal precompactness, the derivative estimates and strong-neck detection follow in the
  plan; they are not touched here.
