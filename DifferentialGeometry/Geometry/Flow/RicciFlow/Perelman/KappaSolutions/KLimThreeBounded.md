- `thm:ksol-three-dimensional-KLim-bounded` and `eq:ksol-KLim3-global-bound`, assembled from the
  terminal trichotomy, with the rank-one branch `lem:ksol-rank-one-terminal-bounded` carried as the
  explicit hypothesis `hrankOne` and the book's projective-plane obstruction as `hnoEmbedding`.
  Three public theorems: terminal slice bound, whole-flow `PointedFlowScalarBounded`, and the
  `IsAncientKappaSolution` upgrade.
- Mechanism: case split on `klim_terminal_curvature_trichotomy`. Positive branch is the already
  proved `KLim.three_terminal_bddAbove_of_positive` (same `hnoEmbedding`); flat branch is killed by
  `KLim.not_terminal_flat`; rank-one branch is `hprod.elim hrankOne`. The whole-flow bound is then
  `KLim.scalarBounded_of_terminal_bound` (trace Harnack with `V = 0`, so `R(x,t) ≤ R(x,0)` with the
  SAME constant), and `KLim.toIsAncientKappaSolution` supplies the only field of
  `IsAncientKappaSolution` that `KLim` lacks. Every other field is passed through from `hK`
  unchanged; no extra input is needed for any of them.
- Dependencies: `UpstreamTerminalTrichotomy` (deferred interface, so all three theorems inherit
  `sorryAx`), `KLimTerminalFlat`, `KLimPositiveTerminalBounded`. Does not depend on worker B's
  `RankOneTerminalBounded`.
- Pitfalls: (1) `Nonempty (TerminalSurfaceProduct ...)` cannot be taken apart by an `rcases`
  `⟨P⟩` pattern (the record is `Type (u+1)`); use `Nonempty.elim`. (2) `hrankOne` must quantify over
  the SAME `TerminalSurfaceProduct` instance term as the trichotomy's conclusion, so this file
  re-enables `terminalTrichotomyInhabited`, `terminalTrichotomyLocallyPathConnected`,
  `terminalTrichotomySemilocallySimplyConnected` with `attribute [local instance]` rather than
  declaring its own copies. (3) The binder is `∀ _P : ...` to keep the unused-variable linter quiet
  while staying the plain hypothesis "the rank-one branch holds for this slice".
- Verification: this file imports two unbuilt modules, so it cannot be checked by the plain
  `lake env lean` until the reviewer refreshes the two upstream artifacts. It was checked against a
  read-only hardlink mirror of `.lake/build/lib/lean/DifferentialGeometry` (built in the scratch
  area, project artifacts untouched) with the two new oleans added:
  `lake env bash -c 'LEAN_PATH="<mirror>;$LEAN_PATH" lean <file>'` 18.5s, output EMPTY; same with
  the lakefile lean options 19.5s, output EMPTY. Independently, a scratch file concatenating the
  bodies of all four new files under the already built imports compiles with only the expected
  `sorry` warning (21.3s). Axioms of all three publics:
  `propext, sorryAx, Classical.choice, Quot.sound`.
- Next step: reviewer refreshes `UpstreamTerminalTrichotomy` and `KLimTerminalFlat`, then runs the
  ordinary focused check here. When worker B lands `RankOneTerminalBounded`, discharge `hrankOne`;
  the only remaining obligation is then the deferred trichotomy interface itself.
