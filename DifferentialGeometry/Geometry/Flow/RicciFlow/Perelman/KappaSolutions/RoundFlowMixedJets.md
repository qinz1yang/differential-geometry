# Round flow mixed jets — the spherical case of `thm:ksol-universal-derivative-estimates`

- Discharges the explicit input `RoundMixedJetBound` of `UniversalDerivativeEstimates.lean`
  (`exists_round_mixed_jet_bound`) and closes `eq:ksol-universal-derivative-bound` with no
  roundness hypothesis (`exists_universal_mixed_jet_bound_unconditional`).
- ROUTE TAKEN: route C of the brief (reuse of the existing jet machinery with the curvature
  input factored out). Route A (direct computation of `∇_t^b ∇^a Rm` on `λ(t) g₁`) was not
  used: the parallel-curvature and Levi-Civita-scaling steps would have to be redone at all
  orders, whereas the buffered machinery already produces all orders from one curvature bound.
- Why the existing entry point does not apply: `exists_normalized_klim_mixed_jet_bound` needs
  `KLim kappa` with a constant depending on `kappa`, and the round branch has no `κ₀`-gap
  (`thm:ksol-universal-kappa-gap` excludes exactly the shrinking spherical space forms). The
  `κ`-dependence of that chain is entirely through
  `exists_normalized_klim_local_curvature_constants` → `exists_normalized_klim_spatial_jet_constants`,
  so the two producers are repeated here with the curvature bound as a hypothesis:
  `klim_curvDerivNorm_le_of_rmNormSq_bound` and `exists_mixed_jet_bound_of_rmNormSq_bound`.
  Neither existing file was edited; the proof text was copied and the ball/normalization
  bookkeeping deleted (with a global curvature bound the buffered-ball inclusion is vacuous).
- Side effect worth keeping: `klim_curvDerivNorm_le_of_rmNormSq_bound` is axiom-standard-only,
  while `exists_normalized_klim_spatial_jet_constants` is not. The factored form is therefore a
  strictly cleaner producer for any consumer that already has a curvature bound.
- Round curvature input. `RoundQuotientData.gQuot_constPosSec` gives one constant sectional
  curvature `c > 0`; in a `gQuot`-orthonormal basis of a three-dimensional tangent space the
  double trace is `∑_{i,j} c(δ_jj δ_ii − δ_ij²) = c(9 − 3) = 6c`, so
  `metricScalarAt gQuot ≡ 6c` (`exists_roundQuotient_metricScalarAt_const`). `c` is existential
  and is never normalized; only spatial constancy is used downstream.
- Since `g(t) = 4(T − t) · e^* gQuot`, `metricScalarAt_scaleMetric` and `metricScalar_cross`
  give `R_g(t, ·) ≡ 6c / (4(T − t))`, i.e. spatial constancy at every `t ≤ 0`
  (`sphericalSpaceFormFlow_scalar_eq`). Hence the normalization at any `(x, t)` has
  `R̂(0, ·) ≡ 1` (`sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one`), so
  `KLim.rmNormSq_le_of_terminal_scalar_le` gives `|Rm|² ≤ 3 ≤ 2²` at every past time and every
  point. `K = 2` is the universal curvature input; the constant is `(a, b)`-dependent only.
- Unscaling is the ending of `exists_universal_mixed_jet_bound_of_not_round` verbatim
  (`eq:ksol-mixed-scaling`, `paraTime t Q 0 = t`, `Q^{-(1+a/2+b)}`).
- Small mechanical notes for a future editor: `Fin 3` literal disequalities are not reduced by
  `norm_num` alone in the double-trace sum, so the six `(by decide : ¬(i = j))` facts are passed
  explicitly; `rw [curvatureNormalizedSolution_scalar]` fails on a `universalNormalizedFlow`
  goal because `ht : t ≤ 0` is only defeq to `t ∈ ancientTimeInterval.carrier`, so the scalar
  identity is taken through `congrFun` with an ascribed membership proof instead.
- Verification: `LEAN_NUM_THREADS=2 lake env lean .../RoundFlowMixedJets.lean`, 20.9 s, empty
  output. No `sorry`, no `nolint`, no `maxHeartbeats`/`maxRecDepth`/`skipKernelTC`, no
  `set_option backward.*`, no `show` tactic. No existing file edited; the module is not
  registered in `DifferentialGeometry.lean` and not committed.
- Axiom audit (per-declaration `#print axioms`, run in a temporary copy of this file):
  `klim_curvDerivNorm_le_of_rmNormSq_bound`, `exists_roundQuotient_metricScalarAt_const` and
  `sphericalSpaceFormFlow_scalar_eq` are standard-only (`propext`, `Classical.choice`,
  `Quot.sound`). `exists_mixed_jet_bound_of_rmNormSq_bound`,
  `sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one`, `exists_round_mixed_jet_bound` and
  `exists_universal_mixed_jet_bound_unconditional` are standard plus inherited `sorryAx`.
- Inherited admissions of the round branch, by name (each is a leaf `sorry` in an `Upstream*`
  interface): `exists_mixed_curvature_jet_polynomials` (Chapter 17 regular-time component
  polynomials, via `exists_ancient_mixed_curvature_fields` and
  `mixedCurvatureNorm_curvatureNormalizedSolution`); `complete_forward_flatness`
  (via `ancientKappa_scalar_pos`, `lem:ksol-scalar-positive`);
  `hamilton_ancient_trace_harnack_at_terminal` (via `ancientKappaThree_toKLim`).
  `exists_universal_mixed_jet_bound_unconditional` additionally inherits the non-round branch's
  admissions through `exists_universal_mixed_jet_bound_of_not_round`
  (`ancientKappaThree_universal_kappa_gap`, `exists_normalized_klim_mixed_jet_bound`).
- Remaining obligations: none inside this file. The endpoint becomes unconditional exactly when
  the three named admissions above (plus the `κ₀`-gap chain, for the universal statement) are
  proved. Nothing in the round branch is conditional on a spherical constant any more.
