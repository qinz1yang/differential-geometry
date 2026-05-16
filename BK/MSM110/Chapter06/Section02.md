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
