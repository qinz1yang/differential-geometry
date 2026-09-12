- `eq:ksol-scalar-differential-estimates` (the differential-estimates half of
  `cor:ksol-scalar-scale-comparison`, `master05a.tex` L30540) is PROVED here from the
  universal mixed jet bounds of `thm:ksol-universal-derivative-estimates`. The three
  instances `UniversalMixedJetBound 0 0 C₀`, `UniversalMixedJetBound 1 0 C₁`,
  `UniversalMixedJetBound 2 0 C₂` enter as explicit hypotheses `h00`, `h10`, `h20`;
  nothing here produces them, and there is no `sorry` in this file.
- Public declarations: `scalarDifferentialConstant`,
  `one_le_scalarDifferentialConstant`, `abs_scalarDifferential_le_of_universal`,
  `abs_deriv_scalar_le_of_universal`, `abs_derivWithin_scalar_Iic_le_of_universal`,
  `exists_universal_scalarDifferentialBounds`,
  `ancientKappa_scalar_scale_comparison_of_universal`.
- The universal constant is `η = max 1 (max (9 C₁) (729 C₂ + 162 C₀²))`. The three
  dimensional factors are forced by the tree's estimates: `n² = 9` for the double frame
  trace `dR = tr tr ∇Rm` (`abs_scalarDifferential_le`), `n⁶ = 729` for the triple
  contraction `ΔR = tr tr tr ∇²Rm` (`abs_laplacian_scalar_le_second_curvature`), and
  `2 n⁴ = 162` for `2|Ric|² ≤ 2 n⁴ |Rm|²` (`ricciSq_le_rm04`). The `max 1` is only to
  meet the `1 ≤ η` requirement of `ancientKappa_scalar_scale_comparison_three`; the
  hypotheses do not force `C₀, C₁, C₂ ≥ 0` (a vacuous `UniversalMixedJetBound` would
  allow a negative constant), so `max` and not `+` is the safe assembly.
- Orders used: `(1,0)`, `(2,0)`, `(0,0)`. The book contracts `(1,0)` and `(0,1)`; the
  `(0,1)` route would need a trace identity relating `∇_t Rm` to `∂_t R`, whereas the
  scalar evolution equation `∂_t R = ΔR + 2|Ric|²`
  (`Evolution/Scalar/IntrinsicDerivation.scalar_curvature_evolution`, as
  `ScalarEvolutionEquationOn` at a `RegularTime`) turns the time half into the already
  available spatial orders `(2,0)` and `(0,0)`. This is the same computation as
  `GoodPointDerivatives.lean` L1097-1160.
- Weight conversions (`mixedCurvatureWeight a b = 1 + a/2 + b`, an `rpow` exponent):
  `R ^ mixedCurvatureWeight 0 0 = R` (`Real.rpow_one`),
  `R ^ mixedCurvatureWeight 1 0 = R * √R` (`Real.rpow_add` at `0 < R`, `Real.rpow_one`,
  `Real.sqrt_eq_rpow`), `R ^ mixedCurvatureWeight 2 0 = R ^ 2` (`Real.rpow_natCast`).
  Only the `(1,0)` conversion needs `0 < R`.
- Norm bridges that are definitional (`rfl`, no lemma needed):
  `Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) = mixedCurvatureNorm S k 0 t x`,
  because `mixedCurvatureTensor S k 0 = iteratedMetricTimeDerivWithin … 0` reduces to
  `nablaKRm04Field S t k x` and both norms are `normSq0S (S.base.metric t) x (4+k)`.
  Likewise `ricciSq_le_rm04 (S.base.metric t) (S.base.metric t) x` typechecks directly
  against `normSq0S (S.family.metric t) x 2 (S.ricci t x) ≤ n⁴ *
  nablaKRm04NormSqIntrinsic S 0 t x` (the same defeq used in `GoodPointDerivatives`).
- Terminal time `t = 0`. `ScalarDifferentialBounds` takes `derivWithin … D.carrier t`,
  and `ancientTimeInterval.carrier = Iic 0`, so at `t = 0` this is the left derivative.
  The lower bound `0 ≤ ∂_t R` is `KLim.scalar_derivWithin_nonneg` and already holds on the
  whole carrier (the trace Harnack at vector zero is stated on `D.carrier`), so only the
  upper bound needs the endpoint argument. It is
  `Chapter25.abs_derivWithin_Iic_le_of_interior_bound` on `[-1, 0]`: continuity from
  `IsSolutionOn.scalarCont`, interior differentiability from `IsSolutionOn.scalarTime`
  plus `regular_mem_nhds`, and the uniform interior bound
  `|∂_t R|(s) ≤ (729C₂+162C₀²) R(s,x)² ≤ η R(0,x)²` using `KLim.scalar_le_terminal`
  (`R(s,x) ≤ R(0,x)` for `s ≤ 0`) and `KLim.scalar_nonneg`. The non-differentiable case
  is handled inside that lemma by `derivWithin_zero_of_not_differentiableWithinAt`, so no
  differentiability at the endpoint is assumed.
- Because the interior bound is stated with absolute values
  (`|ΔR + 2|Ric|²| ≤ |ΔR| + 2|Ric|²`), the Harnack sign is never used in the upper half;
  `abs_deriv_scalar_le_of_universal` is a genuine two-sided bound.
- Axiom audit (fresh, on a scratch copy of the saved source, 7 `#print axioms`, 23 s):
  `scalarDifferentialConstant` and `one_le_scalarDifferentialConstant` are standard-only
  (`propext`, `Classical.choice`, `Quot.sound`). The other five additionally carry
  `sorryAx`, inherited from exactly two delegated upstream obligations:
  * `ancientKappa_scalar_pos` (`ScalarPositive.lean`), whose admitted root is
    `complete_forward_flatness` of `UpstreamForwardFlatness.lean` (complete
    bounded-curvature forward flatness);
  * `ancientKappaThree_toKLim` (`StandardHarnackLimit.lean`), whose admitted root is
    `hamilton_ancient_trace_harnack_at_terminal` of `UpstreamTerminalHarnack.lean`
    (terminal left-derivative form of the ancient trace Harnack inequality).
  A transitive `sorryAx`-root trace (a `Lean.Environment` walk over
  `ConstantInfo.thmInfo.value`, ~74500 constants visited, 70 s) confirms that
  `complete_forward_flatness` and `hamilton_ancient_trace_harnack_at_terminal` are the ONLY
  admitted roots: `abs_scalarDifferential_le_of_universal` and
  `abs_deriv_scalar_le_of_universal` reach only `complete_forward_flatness`;
  `abs_derivWithin_scalar_Iic_le_of_universal` and the two main theorems reach both.
  Every other ingredient is standard-only: `abs_scalarDifferential_le`,
  `abs_laplacian_scalar_le_second_curvature`, `ricciSq_le_rm04`,
  `scalar_curvature_evolution`, `abs_derivWithin_Iic_le_of_interior_bound`,
  `KLim.scalar_derivWithin_nonneg`, `KLim.scalar_le_terminal`, `KLim.scalar_nonneg`,
  `ancientKappa_scalar_scale_comparison`.
- Verification: `LEAN_NUM_THREADS=2 lake env lean
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/UniversalScalarDifferentialBounds.lean`,
  23 s, exit 0, empty output (no errors, no warnings). Not registered in
  `DifferentialGeometry.lean`, not committed, no named artifact refresh performed, so a
  downstream consumer needs one exclusive-window refresh of this module first.
- Remaining obligation for an unconditional `cor:ksol-scalar-scale-comparison`: the three
  `UniversalMixedJetBound` instances. `exists_universal_mixed_jet_bound`
  (`UniversalDerivativeEstimates.lean`) supplies them from `RoundMixedJetBound a b C` at
  the same orders, i.e. from the spherical branch only.
