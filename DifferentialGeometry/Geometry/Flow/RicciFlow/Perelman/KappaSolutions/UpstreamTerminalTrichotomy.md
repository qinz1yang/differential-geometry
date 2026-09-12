- `thm:ksol-three-dimensional-KLim-bounded` terminal input, with `lem:curvature-one-sided-endpoint`,
  the rank-two exclusion and `lem:ksol-terminal-rank-one-product`: on the time-zero slice of a
  three-dimensional `KLim` flow the curvature operator is positive, identically zero, or rank one
  with the universal cover an isometric `TerminalSurfaceProduct`.
- EXPLICIT INTERFACE, PROOF IS `sorry`. The route needs the native rank/kernel/Ky Fan/splitting API
  of `origin/candidate@49608ce9f` (`RankSpreading`, `KyFanBarrier`, `CurvatureKernel`,
  `KernelRigidity`, `ParallelLineSplitting`), which is not in this checkout; owner instruction
  2026-09-11 leaves that input empty, so the statement is recorded in the style of
  `UpstreamAncientSplitting` / `UpstreamRiemannianProduct`. This is the only `sorry` in the
  Chapter 23 terminal-boundedness assembly; every consumer inherits `sorryAx`.
- Dependencies: `TerminalSurfaceProduct` (shared data record) and `HarnackLimit` (`KLim`) only.
  Hypotheses are exactly `hK` and `hdim`; no noncollapsing constant, global curvature bound,
  surface classification, deck group or earlier-time product is asserted.
- Pitfall: `TerminalSurfaceProduct` really requires only `LocallyPathConnectedSpace`,
  `SemilocallySimplyConnectedSpace` and `Inhabited` on the carrier (checked with `#check`); it needs
  neither `ConnectedSpace` nor `T2Space`/`SigmaCompactSpace`/`I.Boundaryless`, so no `letI` in the
  statement is needed. The three carrier instances are declared here as non-private
  `local instance`s on purpose: consumers must re-enable exactly these constants with
  `attribute [local instance]` so that the product record they quantify over is literally the one
  produced here. `terminalTrichotomyLocallyPathConnected` needs `[I.Boundaryless]` (via
  `I.toHomeomorph`), which is why the variable block carries it.
- Verification: `LEAN_NUM_THREADS=2 lake env lean <file>` 20.1s, output exactly one
  `declaration uses 'sorry'` warning; same with the lakefile lean options 18.9s. Axioms:
  `propext, sorryAx, Classical.choice, Quot.sound`; the three instances are standard-only.
- Next step: when the candidate rank/kernel API lands, replace the `sorry` by the terminal-contact
  strong maximum principle on `[-1,0]` plus the one-sided endpoint transfer; do not merge or copy
  the candidate branch into this checkout to do so.
