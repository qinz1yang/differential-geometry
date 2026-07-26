# Conjugate heat

## State — 2026-07-10

The first conjugate-heat producer is checked:

- `conj_heat_mass_deriv` proves that a smooth solution of
  `∂ₜu = -Δu + Ru` has zero derivative of its total mass against the
  moving Ricci-flow volume measure.
- `conj_heat_mass_eq` upgrades the local derivative formula to conservation of
  total mass on a closed time interval.
- `reverseFamily`, `reverseHeat`, `conj_heat_forward`, and
  `conj_heat_backward` give the checked two-way time-reversal bridge with the
  correct reaction sign.
- `IsConjHeatOn` specializes the interval-local `IsHeatPotOn` predicate to the
  forward problem for the reversed metric, and `heat_pot_to_conj` recovers the
  original backward equation at reflected regular times.
- `Geometry/Operator/LaplacianBridge.lean` contains the checked
  source bridge from the realized scalar equation to divergence-form
  `Delta_g` for the canonical Levi-Civita connection.  Its former upstream
  `nablaRSFun_eval_moving_raw` performance wall is closed, and its targeted
  build now passes.
- `conj_heat_mass_one` propagates unit terminal mass to every earlier time.

The proof is geometric rather than a predicate wrapper.  Ricci-flow volume
variation changes the derivative into `∫(∂ₜu - Ru) dμ`; the conjugate heat
equation leaves `-∫Δu dμ`, and the closed-manifold Green identity makes this
zero.

## Historical frontier — 2026-07-10

`MaximumPrinciple/HeatPotential.lean` now proves `heat_pot_nonneg`: every
classical heat-potential solution with potential bounded above and nonnegative
initial data stays nonnegative on the full closed interval.  This is a genuine
conditional positivity theorem; it does not assume a positivity wrapper.

The next genuine producer is existence of a smooth solution of the backward
conjugate heat equation for a time-dependent Ricci-flow metric, with prescribed
terminal density.  `IsHeatPotOn` records the interval-local classical solution
interface, and `nonaut_strong_exists` supplies the abstract two-scale strong
solution theorem.  The genuine frozen-scale inputs are now checked:
`lapDiffA20_short` realizes `Delta_(g(T-s)) - Delta_(gT)`, and
`conjA1_short` realizes multiplication by `-R(T-s)`.
`ConjStrong.conj_strong_exists` now completes their specialized spectral
strong-solution assembly.  The remaining analytic gap is to upgrade that
time-Sobolev solution to a jointly smooth classical field satisfying
`IsHeatPotOn`; the exact proposed producer is `heatpot_of_maxreg`.

Normalization and nonnegativity are now checked conditionally on a classical
solution; existence remains separate.  Later entropy
steps are coupling to the `W` first-variation formula and square completion.
The separate parabolic-rescaling bridge is now complete:
`Analysis/Integration/Measure/Scaling.lean`, `Metric/DistanceScaling.lean`, and
`Perelman/ScaleTransfer.lean` transport the genuine ball, volume, curvature,
and kappa predicates.  `ham3_noncollapse_of` also checks the downstream
original-flow-to-Hamilton adapter.  Thus the remaining frontier is entirely
upstream of scale transfer: produce original-flow `NoLocalCollapsing` by the
analytic W-route.

## Historical accounting — 2026-07-10

- time-reversal, classical-solution interface, and mass normalization: 100%.
- conjugate-heat existence theorem: not proved (0%); its dedicated analytic
  machinery is about 70%.
- Perelman no-local-collapsing theorem and `ham3_noncollapse`: not proved (0%).
  Existing W/F variation plus the conjugate-heat bricks amount to roughly 32%
  of the dedicated analytic producer machinery.
- Hamilton-side rescaled-ball/curvature realization remains about 40%; this is
  separate from the unproved Perelman theorem.
- The dedicated geometric scale-transfer sublane is complete (100%).
- Whole HCG compactness machinery remains about 45%, with its endpoint theorems
  still 0%; this entropy brick does not change that percentage.

The conjugate-heat source passed focused verification.  The upstream derivation
performance blocker and the Laplacian-bridge object-file blocker are now
resolved; the new A2 and A1 producer stacks both pass focused and targeted
verification.

## 2026-07-17 reverse-time offset bridge

`heat_pot_add` translates an `IsHeatPotOn` solution from reverse time `q` to
`q + a`, while moving the reverse-family anchor from `T` to `T + a`.  This is
the exact algebraic bridge needed to start Perelman's W comparison at a
strictly positive scale `a`: the original metric time remains
`T - q = (T + a) - (q + a)`.  The proof is a genuine pullback of joint
smoothness, endpoint continuity, slice smoothness, and the heat equation; it
does not assert equality of whole tensor or Hom objects.

The offset mismatch is therefore closed.  The remaining obstruction is not a
time-translation issue: `gallim_pos` supplies a classical solution only on some
short interval starting at zero, while `w_rev_antitone` compares only closed
subintervals contained in the open regular set.  To compare the prescribed
initial cutoff with positive reverse times one still needs a proved right-hand
continuity theorem for W at the initial heat slice (from the retained
all-Sobolev Galerkin continuity), followed by a finite-horizon continuation or
uniform local-existence argument.  `IsHeatPotOn.jointCont` alone is
mathematically insufficient because W reads spatial derivatives.

The offset theorem and its dedicated machinery are 100%.  A finite-horizon W
lower theorem remains unstated and hence 0%; its existing conjugate-heat and W
variation machinery is about 90%.  `NoLocalCollapsing` and
`ham3_noncollapse` remain theorem-level 0%.  Focused verification passed.
