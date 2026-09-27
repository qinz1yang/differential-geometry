# W19 log (append-only)

- 2026-09-25: CapWindowPoint gains `Dcap` (after `t`) and conjunct `‖x.val‖ < Dcap + 1`.
  CapWindowContinuation outputs `∃ Rcap q₀ δmax ρmax εcap mcap`, `Dcap + 1 < Rcap`, admissibility
  `Rcap ≤ p₀.modelRadius` (replaces `Dcap ≤ ...`); both classes pass `Dcap`. CrossingContinuation
  class uses its own output `Dcap`. Assembly: C3 Dcap = `max Dd Rw`; crossing admissibility via
  `Dx ≤ Rw` (linarith from `Dx + 1 < Rw`); split uses `Dx θcap`. PoincareEndgame.lean unchanged.
- Read-only compile (LEAN_NUM_THREADS=2 lake env lean): no output. Assembly axioms:
  propext, Classical.choice, Quot.sound (scratch copy outside repo, deleted).
