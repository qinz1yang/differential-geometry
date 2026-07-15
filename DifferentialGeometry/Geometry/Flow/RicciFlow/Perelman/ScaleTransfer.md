# Perelman scale transfer

## State — 2026-07-09

`ScaleTransfer.lean` is checked without `sorry`.  It now proves the complete
parabolic scale-transfer chain for the canonical geometric predicates:

- `paraFlowTime` identifies a rescaled time with its original-flow time;
- `paraBall` and `backBall` multiply/divide the radius by `sqrt R`;
- their time-slice carriers agree, and their volume measures differ by
  `ENNReal.ofReal (sqrt R) ^ finrank Real E`;
- `IsRmControlled` and `IsKappaNoncollapsed` transfer both ways;
- `para_noncollapse` transports `KappaNoncollapsedBelowScale S kappa rho` to
  the rescaled flow at scale `sqrt R * rho`;
- `para_no_local` transports the full `NoLocalCollapsing` predicate.

The proof uses the genuine time map, distance-defined ball carriers,
Riemannian volume measure, and canonical curvature norm.  It adds no numeric
volume wrapper and no new frontier assumption.

`HamiltonPositiveRicci.lean` now supplies the checked consumer
`ham3_noncollapse_of`: a canonical `NoLocalCollapsing P.S rho` producer plus
the already checked rescaled curvature control imply the fixed-radius
`Ham3Noncollapse` conclusion.  `ham3_radius_event` proves the required eventual
scale inclusion from `R_i t_i -> infinity` and the finite maximal time.

## Remaining frontier and progress

The scale-transfer sublane and the downstream
`NoLocalCollapsing -> Ham3Noncollapse` adapter are 100%.  The remaining blocker
is upstream and analytic: construct `NoLocalCollapsing` for the original smooth
closed Ricci flow.  The chosen W-route still lacks moving-metric positive
conjugate-heat existence, W-monotonicity, log-Sobolev input, and the cutoff
volume-ratio argument.

Accordingly, the theorem `ham3_noncollapse` itself remains 0%; its dedicated
analytic machinery is about 10%.  The whole HCG machinery estimate remains
about 45%, with HCG endpoint theorems at 0%.
