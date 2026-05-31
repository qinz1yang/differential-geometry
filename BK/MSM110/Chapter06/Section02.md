# MSM110 Chapter 6.2

## 2026-05-13 Uhlenbeck trick scaffold

The Section 6.2 companion now imports
`RicciFlower.RicciFlow.Evolution.Uhlenbeck` and exposes thin book-label wrappers
for:

- `eq:e_a_evolution_equation`
- `lem:evolving_frame_calculation`
- the orthonormal-frame corollary after that lemma
- `eq:ode_for_bundle_isomorphism`
- the Uhlenbeck bundle-isometry claim
- `eq:uhlenbeck_pullback_of_riemann`
- `lem:uhlenbeck_curvature_evolution_one`
- `eq:rm_minus_evolution_minus_uhlenbeck_trick`

The companion is label-facing only.  The intentional `sorry` frontiers live in
the RicciFlower Uhlenbeck module.

Verification: focused file check passed after building the new RicciFlower
Uhlenbeck module.  A later targeted BK module build is currently blocked by an
unrelated current dependency failure in `RicciFlower/Curvature/Components.lean`,
where the proof near lines 1220 and 1227 leaves coordinate-input equality
goals unsolved.

## 2026-05-26 Gram Value-Constancy Interface

Updated the orthonormal-frame corollary wrapper after the RicciFlower
Uhlenbeck interface split derivative-zero data from actual Gram value
constancy.

`cor_evolving_frame_orthonormal` now consumes
`MovingFrameGramValueConstantOn`, which is the mathematically correct input for
preserving initial orthonormality.  The lower ODE/FTC producer that turns
derivative-zero data into value constancy remains in the RicciFlower module, not
in this BK label wrapper.

Focused verification passed.

## 2026-05-26 Pulled Curvature Quadratic Split

Updated the `lem_uhlenbeck_curvature_evolution_one` wrapper after the
RicciFlower theorem split the raw quadratic term into `Borig` and `Bpull`.
The wrapper now consumes `UhlenbeckPullbackBComponents iota Borig Bpull`,
which is the honest bridge between the pre-Uhlenbeck Riemann evolution and the
pulled curvature equation.

Focused verification passed after refreshing the RicciFlower Uhlenbeck module.
