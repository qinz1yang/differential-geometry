# JacobianBounds

## 2026-07-07 V1c determinant-bound algebra

Status: `JacobianBounds.lean` starts the V1c layer without pretending that the
Jacobi/Gronwall comparison theorem is already available.

Completed:

- Added `sqrt_det_le_of_entry_bound`: an entrywise matrix bound plus
  nonnegative determinant gives an upper bound for `sqrt(det A)` via
  `Matrix.det_le`.
- Added `normalDensity_le_of_radial_entry_bound`: the same upper determinant
  bound specialized to `radialJacobiGram`, using the V1b identity
  `normalDensity_radial`.
- Added `normalChart_volume_le_of_radial_entry_bound`: the corresponding
  volume-integral upper bound for measurable sets inside the normal-chart
  source and Jacobi radius.
- Added the endpoint-length bridge `radialEntry_le_of_length_bound`: a uniform
  bound on the square-root Riemannian lengths of endpoint radial Jacobi fields
  gives the entrywise Gram bound `B * B` by pointwise Cauchy-Schwarz.
- Added `normalDensity_le_of_radial_length_bound`: a direct density consumer of
  that length bridge.
- Added `density_le_gronwall`: a pointwise upper-density bridge that consumes
  `radialJacobi_fin_le` directly, removing the intermediate manual `hJ`
  endpoint-length hypothesis while keeping the analytic and scalar Gronwall
  inputs explicit.
- Added `density_le_gronwall_of_init_bound`: the same pointwise upper-density
  bridge, but using a uniform initial-speed bound `A` and one scalar model
  comparison instead of per-basis scalar Gronwall hypotheses.
- Added `density_le_gronwall_of_deriv_eq`: the V1c-facing pointwise
  upper-density bridge that consumes fixed-basis derivative equalities
  `D_tJ_k(0)=e_k` and a uniform `g_p`-length bound on the model basis instead
  of the abstract `hinit`.
- Added `density_le_gronwall_of_radius_deriv`: the pointwise upper-density
  bridge that consumes the small-radius radial-Jacobi derivative theorem
  directly, keeping `‖chartModelBasis E k‖ < r` explicit.
- Added `density_le_gronwall_of_scaled_radius`: the pointwise upper-density
  bridge that consumes the scaled-basis endpoint producer.  It replaces raw
  basis smallness by the explicit side condition `‖a • chartModelBasis E k‖ < r`
  and a scaled model comparison.
- Added `normalChart_volume_le_of_radial_length_bound` and
  `normalChart_volume_le_const_mul_of_radial_length_bound`: direct volume
  consumers from endpoint-length bounds, including the constant times
  model-Haar measure form needed by V1d.
- Added `sqrt_pow_le_sqrt_det`: a pure matrix bridge from a uniform eigenvalue
  lower bound for a positive semidefinite real matrix to a lower bound for
  `sqrt(det)`.
- Added `radialJacobiGram_posDef` and `normalDensity_ge_of_eigen_bound`: the
  V1c lower-density algebraic consumer.  It turns future singular-value or
  Gronwall lower control of the radial-Jacobi Gram eigenvalues into a pointwise
  lower bound for `normalChartDensity`.
- Added `ball_src_of_radius`, `density_ge_det`, and `density_ge_det_ball`: the
  model-ball lower-density bridge from a determinant lower bound for
  `radialJacobiGram` to a lower bound for `normalChartDensity`, with the
  normal-coordinate source and `C²`-radius side conditions discharged from
  `R ≤ expMapC2Radius`.
- Added `eigenvalues_ge_of_rayleigh`,
  `sqrt_pow_le_sqrt_det_of_rayleigh`,
  `normalDensity_ge_of_rayleigh_bound`, and `density_ge_rayleigh_ball`.  These
  turn a unit-vector Rayleigh lower bound for the radial-Jacobi Gram matrix
  into the existing eigenvalue/determinant/density lower-bound consumers.
- Added `radialJacobiGram_quadratic`,
  `normalDensity_ge_of_combo_bound`, and `density_ge_combo_ball`.  These turn a
  lower bound for every unit linear combination of endpoint radial Jacobi
  fields into the Rayleigh lower-bound route.
- Added `normalDensity_ge_of_dir_bound` and `density_ge_dir_ball`.  These
  consume a lower bound for the single endpoint radial Jacobi field generated
  by each unit coefficient direction `sum_i v_i e_i`, using
  `radialJacobi_one_sum` to match the combo route.
- Added `exists_dens_le_rm04` and `exists_dens_ge_rm04`.  These consume the
  endpoint-closed Rm04 producer wrappers from `RadialGronwall.lean` and feed
  them into the existing upper endpoint-length and lower unit-direction density
  consumers.
- Added `exists_dens_two_rm04`.  It synchronizes the upper and lower
  endpoint-closed Rm04 density wrappers by taking the minimum available radius
  and returning both pointwise density inequalities under one shared hypothesis
  package.
- Added `exists_dens_le_rm04_at`, `exists_dens_ge_rm04_at`, and
  `exists_dens_two_rm04_at`.  These are the localized-regularity variants of
  the endpoint-closed Rm04 density wrappers; they consume the `_at` packaged
  endpoints from `RadialGronwall.lean` and replace the global radial-curve
  `ContMDiff` input by pointwise `ContMDiffAt` on `Icc 0 b`.  The old theorem
  names remain as compatibility wrappers.

Route:

- This is the reusable algebraic bridge from future radial-Jacobi entry
  estimates to the upper normal-density bound.
- The length-bound bridge is intentionally one-sided: it converts endpoint
  Jacobi length estimates into an upper Gram-entry estimate, but it does not
  supply the missing lower determinant/singular-value control.
- The Gronwall bridge is still conditional: it consumes the verified
  radial-Jacobi endpoint producer but does not produce radial regularity,
  parallel frames, ODE bounds, or the scalar initial-speed bound.
- The uniform-initial-speed bridge narrows the scalar frontier to `hinit` and
  `hmodel`; it still does not prove that fixed `chartModelBasis` vectors satisfy
  those bounds.
- The derivative-equality bridge narrows `hinit` further to the honest
  fixed-basis initial condition `D_tJ_k(0)=e_k` plus a separate center metric
  basis-length bound.  It does not prove the small-radius side condition needed
  to get that equality from `exists_radialJacobi_deriv_radius`.
- The radius bridge removes the manually assembled derivative-equality family,
  but it does not solve the scale problem: consumers still need fixed-basis
  smallness or a future scaling/linearity bridge.
- The scaled-radius bridge is the upper-density scale route.  It does not solve
  the lower determinant/singular-value side, and it still requires analytic
  hypotheses for the scaled Jacobi fields plus an explicit positive scale.
- The constant-measure wrapper only removes a trivial integral over a constant;
  it does not prove any model-ball containment or Haar ball scaling.
- The lower determinant bridge is stated against eigenvalue lower bounds, not
  entrywise bounds.  This keeps the real missing input honest: the lower half of
  V1c must still come from Gronwall/singular-value control.
- The model-ball determinant bridge is intentionally weaker than the eigenvalue
  bridge: it does not prove determinant control, but it gives future
  singular-value/Riccati producers a direct V1d-facing density hypothesis.

2026-07-08 follow-up 8an: localized the Rm04 density packages after the
`RadialGronwall` `_at` endpoint propagation.  Verification passed for
`JacobianBounds.lean`; a targeted refresh of `Volume.JacobianBounds` also
passed so downstream `BallVolume` can import the new declarations.  This is
still a density-package interface change, not the final V1c two-sided
determinant theorem: theorem completion remains 0%, while its dedicated
density/Gronwall machinery is about 93.5% complete.  Next target is the
`BallVolume.IsRm04VolHyp` package field and volume wrapper consumption.
- The Rayleigh bridge narrows the lower route to the natural producer statement
  `a ≤ vᵀ(radialJacobiGram)v` on unit coefficient vectors.  It still does not
  prove that Rayleigh lower bound from Jacobi-field lower estimates.
- The combo bridge identifies `vᵀ(radialJacobiGram)v` with the Riemannian
  norm-square of `∑ i, v_i J_i(1)`.  It still does not prove the lower norm
  bound for that Jacobi-field combination.
- The direction bridge is the lower-route consumer closest to the expected
  analytic producer: prove a lower bound for `J_{sum_i v_i e_i}(1)` for every
  unit coefficient vector `v`, and the density lower bound follows.  It still
  does not prove that analytic endpoint lower estimate.
- The endpoint-closed Rm04 density wrappers remove the repeated radial
  `chartRepAt`, ODE, and small-radius derivative hypotheses from the direct
  density consumers.  They still do not provide parallel-frame data, scalar
  model estimates, launch/Rm04 coefficient bounds, or a single named two-sided
  capped Jacobian theorem.
- The two-sided density wrapper is only a radius-synchronization and
  hypothesis-sharing package.  It does not prove the geometric input package
  or the eventual volume comparison theorem.

Current blocker / next frontier:

- V1c's target theorem is still not started as a two-sided capped-scale
  Jacobian theorem.  The next target is to move the shared two-sided pointwise
  density package toward the existing `BallVolume.lean` two-sided local volume
  wrappers, while keeping the missing geometric inputs explicit: parallel-frame
  data, scalar model bounds, launch/Rm04 coefficient bounds, and radius/scale
  choices.

Progress estimates:

- `sqrt_det_le_of_entry_bound`: 100% complete.
- `sqrt_pow_le_sqrt_det`: 100% complete.
- `radialEntry_le_of_length_bound`: 100% complete.
- `density_le_gronwall`: 100% complete as a conditional pointwise upper
  density bridge; it is not the analytic hypothesis package.
- `density_le_gronwall_of_init_bound`: 100% complete as a conditional pointwise
  upper density bridge from a uniform initial-speed bound; it is not the
  initial-speed producer.
- `density_le_gronwall_of_deriv_eq`: 100% complete as a conditional pointwise
  upper density bridge from fixed-basis derivative equalities; it is not the
  derivative-equality/radius producer.
- `density_le_gronwall_of_radius_deriv`: 100% complete as a conditional
  pointwise upper density bridge from a small-radius derivative theorem; it is
  not the fixed-basis smallness or scaling producer.
- `density_le_gronwall_of_scaled_radius`: 100% complete as a conditional
  pointwise upper density bridge from scaled-basis smallness; it is not the
  analytic scaled-basis package or lower determinant producer.
- `radialJacobiGram_posDef`: 100% complete.
- `normalDensity_ge_of_eigen_bound`: 100% complete as an algebraic lower
  consumer; it is not the Gronwall/eigenvalue producer.
- `density_ge_det_ball`: 100% complete as a determinant-to-density model-ball
  consumer; it is not the determinant producer.
- `normalDensity_ge_of_rayleigh_bound` / `density_ge_rayleigh_ball`: 100%
  complete as Rayleigh-to-density lower consumers; they are not the
  Rayleigh/singular-value producer.
- `radialJacobiGram_quadratic` / `normalDensity_ge_of_combo_bound` /
  `density_ge_combo_ball`: 100% complete as combo-norm-to-density lower
  consumers; they are not the Jacobi-field lower norm producer.
- `normalDensity_ge_of_dir_bound` / `density_ge_dir_ball`: 100% complete as
  direction-endpoint-lower-bound-to-density consumers; they are not the
  Jacobi-field lower norm producer.
- `exists_dens_le_rm04` / `exists_dens_ge_rm04`: 100% complete as
  endpoint-closed Rm04 pointwise density wrappers; they are not the parallel
  frame, scalar model, coefficient-bound, or two-sided capped theorem package.
- `exists_dens_two_rm04`: 100% complete as a shared-radius, two-sided
  pointwise density wrapper; it is not the final capped-scale Jacobian theorem
  and does not provide the missing geometric inputs.
- V1c determinant-bound algebraic bridge: about 91% complete, including the
  upper entry/length/Gronwall/uniform-initial-speed consumers, the lower
  eigenvalue-to-density consumer, the determinant-to-density model-ball bridge,
  the scaled-radius upper-density route, and the Rayleigh-to-density lower
  bridge plus its Jacobi-combination quadratic-form and direction-endpoint
  adapters, now with direct endpoint-closed Rm04 density wrappers and a
  shared-radius two-sided pointwise density wrapper.
- V1c two-sided determinant theorem: 0% complete; no capped-scale theorem is
  stated yet.
- Stage V1: about 75% complete after the V1d shell work, the V1c lower
  Rayleigh/combo/direction density bridge, and endpoint-closed Rm04 density
  wrappers.
- Whole volume-comparison lane: about 50% complete; V0, V1a, endpoint V1b,
  V1c algebraic upper/lower consumers, and V1d conditional integration shells
  are in place, but Gronwall comparison, explicit capped constants, and the
  final two-sided theorem remain.

Verification: focused verification and targeted module verification passed for
`JacobianBounds.lean` before this derivative-equality bridge; focused
verification and targeted module verification passed again after adding
`density_le_gronwall_of_deriv_eq`; downstream target verification passed for
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.  Focused
verification passed after adding `density_le_gronwall_of_radius_deriv`.
Focused and targeted verification passed after adding
`density_le_gronwall_of_scaled_radius`; downstream target verification passed
for `DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.  Focused and
targeted verification passed after adding the Rayleigh lower bridge; downstream
target verification also passed through
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.  Focused
and targeted verification passed after adding the combo lower bridge; downstream
target verification also passed through
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.  Focused and
targeted verification passed after adding the direction lower bridge;
downstream target verification again passed through
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.  Focused and
targeted verification passed after adding `exists_dens_le_rm04` and
`exists_dens_ge_rm04`, following a successful targeted refresh of
`DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall`.  Focused and
targeted verification passed after adding `exists_dens_two_rm04`.  No `sorry`
or `axiom` occurs in this file.

2026-07-08 follow-up 8as: added `exists_dens_pair_rm04_at`, a split-constant
pointwise Rm04 density wrapper.  It reuses the existing lower and upper Rm04
density producers but keeps the lower endpoint constant `Blo` and upper
endpoint constant `Bhi` separate, avoiding the artificial same-`B`
compatibility that blocked the higher volume route.

Verification passed for focused `JacobianBounds.lean` with no global Lake lock,
and targeted module verification passed because `BallVolume.lean` consumes the
new exported declaration.  Current honest estimates: V1c determinant-bound
algebraic bridge ~94%; V1d local volume shell/package machinery ~98.2%; V1c
two-sided determinant theorem 0%; final V1d two-sided ball-volume theorem 0%;
Stage V1 ~83.8%; whole volume-comparison lane ~63%.  Next target: consume this
split-constant wrapper in the volume layer and avoid reintroducing a
same-constant package unless a real compatibility lemma is proved.
