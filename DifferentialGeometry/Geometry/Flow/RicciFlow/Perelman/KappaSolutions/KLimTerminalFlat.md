- `thm:ksol-three-dimensional-KLim-bounded`, flat branch of the terminal trichotomy:
  `KLim.not_terminal_flat` shows a three-dimensional `KLim` flow has no time-zero slice with
  identically vanishing `|Rm|²`. Unconditional; standard axioms only.
- Mechanism: take the `notFlat` witness `(t, x)` first, then run the argument at that one point.
  `scalar_abs_le_rm` (`|R| ≤ n²|Rm|`) turns `rmNormSq 0 x = 0` into `F.S.scalar 0 x = 0`, and
  `KLim.rmNormSq_le_of_terminal_scalar_le` (Harnack monotonicity `R(x,t) ≤ R(x,0)` composed with the
  dimension-three comparison `|Rm| ≤ √3 · R`) gives `rmNormSq t x ≤ 3·0² = 0`; with
  `pointedFlow_rmNormSq_nonneg` this contradicts the witness. No whole-slice or spacetime bound is
  needed, and no hypothesis beyond `hK` and `hdim` is used.
- Dependencies: `KLimCurvatureBounds` only (which already pulls `HarnackLimit` and
  `RmNormFromEigenvalues`). Deliberately does NOT import `UpstreamTerminalTrichotomy`: the flat
  branch is independent of the deferred interface, so this file stays `sorry`-free and can be cited
  on its own.
- Pitfall: `scalar_abs_le_rm` is stated with `Module.finrank ℝ (TangentSpace I x)` and with
  `normSq0S g x 4 (metricRm04At g x)`; the bridge to `F.S.scalar` / `F.rmNormSq` is definitional and
  is taken with `change ... at hscalar`, exactly as `CollapsedBallGeometry` does. That `change`
  needs the file's local instances to be `F.topology`/`F.charted`/`F.smooth`/`F.t2` verbatim, and
  the file needs `[InnerProductSpace ℝ E]` because `KLimCurvatureBounds` does.
- Verification: `LEAN_NUM_THREADS=2 lake env lean <file>` 18.6s, output EMPTY; same with the
  lakefile lean options 20.2s, output EMPTY. Axioms of `KLim.not_terminal_flat`:
  `propext, Classical.choice, Quot.sound`.
- Next step: none for this branch. It is consumed by `KLimThreeBounded`.
