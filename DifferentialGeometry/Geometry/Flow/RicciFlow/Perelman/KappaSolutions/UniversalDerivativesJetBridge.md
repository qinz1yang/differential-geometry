- Purpose: identify the Chapter 25 jet representation `Chapter25.MixedCurvatureJet` with the
  lane's `mixedCurvatureTensor` / `mixedCurvatureNorm` on the ancient carrier, and read off
  the content of the sorried Chapter 25 slot
  `Chapter25.Upstream.kappa_universal_derivatives` from `UniversalMixedJetBound`.
  `Chapter25Theorems.lean` is NOT edited; its `sorry` stays where it is. What is proved here
  is a separate theorem with the same conclusion, usable to discharge that slot later.
- Public declarations: `ricciEndAt_metricRicciAt_eq_ricciSharp`,
  `exists_slotEquiv_mixedCurvatureJet_value`, `mixedCurvatureJet_norm_eq`,
  `ancientKappa_mixedCurvatureTensor_differentiableWithinAt`,
  `ancientKappa_universal_derivatives_jet`,
  `exists_kappa_universal_derivatives_of_round`.
- Import cycle check: `Chapter25Theorems` transitively imports 22 `KappaSolutions` modules
  (`HarnackLimit`, `PointedNoncollapse`, `RescaledPointedSequence`, … ) but NOT
  `UniversalDerivativeEstimates`, `BufferedMixedCurvature`, `MixedCurvatureTerminal`,
  `MetricTimeDerivative` or `StandardHarnackLimit`. So a `KappaSolutions` file may import
  `CanonicalNeighborhood.Chapter25Theorems` together with `UniversalDerivativeEstimates`;
  no relocation to `CanonicalNeighborhood/` was needed.
- Slot-order bridge `a + 4` vs `4 + a`. `curvEquiv` and `curv_apply_iterCov` are `private`
  in `Compactness/Bounds/CurvatureTowerBridge.lean`, and the public
  `curvCovDeriv_normSq_eq` / `curvNormSq_eq` give only the NORM identity, which is not
  enough for the induction on the time order. The definition and the proof of
  `curv_apply_iterCov` are therefore reproduced here verbatim as private helpers (they use
  only public API: `curvCovDeriv_succ`, `curvStep_eq_covStep`, `covStep_domDomCongr`,
  `frontExtendEquiv`). If those two are ever made public upstream, the local copies should
  be deleted and the imports switched.
- Why any bijection would not do: the base case fixes `e` to be the one matching
  `curvCovDeriv g a` with `iterCov g 4 (metricRm04 g) a`; but once fixed, the SAME `e`
  propagates through every time order, because both the fixed-fiber time derivative and the
  Ricci slot insertion commute with an arbitrary slot bijection. Hence the existential
  statement `exists_slotEquiv_mixedCurvatureJet_value` quantifies `e` before `b`.
- Ricci slot action: `ricciEndAt g (metricRicciAt g x) w = ricciSharp g x w`. Proof by
  nondegeneracy (`SmoothRiemannianMetric.eq_of_inner_eq_gen`) from
  `ricciEnd_inner` (`g.inner x (ricciEndAt g Ric X) Y = Ric (vec2 X Y)`),
  `metricRicciAt_apply_eq_ricciTensor` and `inner_ricciSharp`. Requires
  `[T2Space M] [BoundarylessManifold I M]` (from `RicciIdentity.lean` and
  `MetricLeviCivitaReconcile.lean`), not dimension three.
- Derivative sets. Chapter 25 differentiates within `D.carrier ∩ Iic t`; the lane
  differentiates within `D.carrier`. On `ancientTimeInterval` and for `t ≤ 0` these are
  `Iic t` and `Iic 0`, and `Iic 0 ∩ Iic t = Iic t`. No case split on `t = 0` is needed:
  from `HasDerivWithinAt f c (Iic 0) t` and `Iic t ⊆ Iic 0` one gets
  `HasDerivWithinAt f c (Iic t) t` by `.mono`, and both `Iic 0` and `Iic t` are
  unique-diff at `t` (`uniqueDiffOn_Iic`). The evaluation step
  `derivWithin (fun s => A s v) J t = (derivWithin A J t) v` is
  `tensor0SEvalCLM v |>.hasFDerivAt.comp_hasDerivWithinAt`, exactly as inside
  `metricTimeDerivWithin_apply`.
- Slot reindexing of the Ricci sum: `Function.update_comp_equiv` gives
  `update v (e i) u ∘ e = update (v ∘ e) i u`, and `Fintype.sum_equiv e` transports the sum
  over `Fin (a+4)` to the sum over `Fin (4+a)`.
- Norm step: `J.value a b t x = (mixedCurvatureTensor S a b t x).domDomCongr e` by
  `ContinuousMultilinearMap.ext`, then `normSq0S_domDomCongr` with the orthonormal basis of
  `exists_gOrthonormalBasis` and `metricInverseInBasis_of_orthonormal` — the same two lines
  as in `curvCovDeriv_normSq_eq`.
- Differentiability input. `exists_slotEquiv_mixedCurvatureJet_value` takes it as an
  explicit hypothesis at the single point `x`, for all orders `q` and all `t ≤ 0`. On a
  normalized ancient `κ`-solution it is discharged by
  `ancientKappa_mixedCurvatureTensor_differentiableWithinAt`, which is the first conjunct of
  `exists_normalized_klim_mixed_jet_bound … kappa 0 le_rfl p q` at the basepoint
  (`riemannianEDistOf_self` makes the radius-`0` ball condition trivial) after
  `ancientKappaThree_toKLim`. The `κ`-dependent constant produced there is discarded; the
  actual bound is the universal one.
- Axiom audit (fresh, on a scratch copy of the saved source, 6 `#print axioms`, 26 s):
  `ricciEndAt_metricRicciAt_eq_ricciSharp`, `exists_slotEquiv_mixedCurvatureJet_value` and
  `mixedCurvatureJet_norm_eq` are standard-only (`propext`, `Classical.choice`,
  `Quot.sound`) — the REPRESENTATION BRIDGE ITSELF IS UNCONDITIONAL.
  `ancientKappa_mixedCurvatureTensor_differentiableWithinAt`,
  `ancientKappa_universal_derivatives_jet` and
  `exists_kappa_universal_derivatives_of_round` additionally carry `sorryAx`, entirely from
  the differentiability producer. A transitive `sorryAx`-root trace (a `Lean.Environment`
  walk over `ConstantInfo.thmInfo.value`, 86098 constants visited, 61 s) lists exactly 19
  admitted roots for both, all in this namespace:
  `exists_local_ancient_flow_compactness`, `volumeMeasurePreserving_pullbackMetric`,
  `hamilton_ancient_trace_harnack_at_terminal`,
  `ricciFlow_additive_distance_bound_of_ricci_upper`,
  `exists_backward_slice_asymptotic_shrinker`,
  `complete_noncompact_three_shrinker_universal_cover_fibres`,
  `universalCover_image_ball_liftedMetric`, `universalCover_volume_image_le`,
  `volumeMeasurePreserving_pullbackMetricCross`,
  `riemannianVolumeMeasure_product_real_of_inner_eq`,
  `ancient_fixed_universal_cover_product_of_null_plane`,
  `metricRm04At_product_real_of_inner_eq`,
  `complete_surface_shrinker_compact_constant_scalar`, `complete_forward_flatness`,
  `compact_ricciFlow_volumeVariation_on_regular`, `existsUnique_meanZero_smooth_poisson`,
  `complete_surface_constant_scalar_round_cover`, `scalar_slice_zero_of_nonnegative_slab`,
  `exists_mixed_curvature_jet_polynomials`. These are the recorded admission frontier of
  `BufferedMixedCurvature` ("the spatial-jet chain's 18 inputs plus the Chapter 17
  regular-time polynomial input"), inherited unchanged; this file adds none.
- Verification: `LEAN_NUM_THREADS=2 lake env lean
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/UniversalDerivativesJetBridge.lean`,
  25 s, exit 0, empty output (no errors, no warnings). Not registered in
  `DifferentialGeometry.lean`, not committed, no named artifact refresh performed.
- Host note: on this checkout `lake env lean` intermittently fails at import time with
  `failed to read file '….olean'` (varying modules, including 19 MB ones) even with no
  other `lean.exe` running. Re-running the identical command succeeds. Treat such a failure
  as inconclusive, not as a verification result.
- Remaining obligations for discharging `Chapter25.Upstream.kappa_universal_derivatives`
  itself: (i) the spherical branch `RoundMixedJetBound a b C₁` of
  `thm:ksol-universal-derivative-estimates`, the single explicit input of
  `exists_kappa_universal_derivatives_of_round`, which already has the slot's exact
  `∃ C, 0 < C ∧ …` shape; (ii) the 19 inherited admitted roots above must be closed for the
  result to be unconditional; (iii) `Chapter25Theorems.lean` must then be edited to replace
  its `sorry`, which this task is not authorized to do.
