# G6 fill log

2026-09-26. New file `Perelman/LGeometry/Ray/ParabolicBallRange.lean` (276 lines, unwired).
- Public: `exists_pos_lRegularizedCurve_mem_ball_of_parabolic_rm_bound (R)`: DESIGN_22 §6
  statement (σ ≤ 1, uniform over all `M : Type u` for fixed `I`), plus `[SigmaCompactSpace M]`
  (needed by `shi_curvDerivNorm_on_terminal_ball`). No `hR : 0 ≤ R` (unused).
- σ = min (1/2) (1/(16(√(A Q)+1))), A = exp n², G = n²·C_Shi(n), K = n²,
  Q = exp((1 + 2G/4 + 2K)/2)(4R²+1), n = finrank E; depends only on n and R.
- Route: rescale by `parabolicSolution S T r⁻²` (`Geodesic/Scaling.lean` lRegularizedDomain/Curve
  _parabolic, `Scaling/Parabolic.lean` parabolicRmNormSq, `edistOf_scale`), then unit-scale lemma
  from `mem_lRegularizedDomain_and_edist_lt_of_local_gradient_ricci_bounds` (Range.lean:180) with
  Shi (TerminalBall.lean:373, a = -1/2), `inner_le_exp_mul_inner_of_rmNormSq_le`, QuadraticForm Ricci.
- Needs `T ∈ D.regular`; the common flow of H9 is on `closed a t`, so `T = t` is not regular there
  and G1's continuation needs `CompactSpace` (U is not compact). Open for H9.
- Compile: `Geodesic/Scaling.olean` missing in pc3 build; scratch concatenation (Scaling.lean +
  this file) via `lake env lean`: clean, `#lint` 14 linters passed, axioms propext/choice/Quot.sound.
