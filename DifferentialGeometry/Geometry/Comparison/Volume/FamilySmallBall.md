# FamilySmallBall

`FamilySmallBall.lean` isolates the metric-family version of the compact-uniform
small-ball volume lower bound needed by Perelman's initial-time argument.

`family_vol_low` is the geometry producer used by the initial-time route.  It
removes RicciFlow and Perelman-specific vocabulary from the theorem: for a
smooth realized metric family on `[0, omega)`, it asks for one short time and
one normalized volume constant that work for every centre and every radius with
`r^2 <= t`.

Verification status: `family_vol_low` is proved without `sorry`, axioms, or new
consumer assumptions.  Its focused check is warning-free.  The proof uses a
finite cover by fixed initial exponential parametrizations, takes finite minima
of the local time/radius/density constants, embeds a shifted model ball into the
moving Riemannian ball using `param_edist_le`, and applies `param_vol_ge` plus
model-Haar ball scaling.

Historical API audit: `Exponential/Smoothness/OffZero.lean` contains chart-level
joint smoothness for the chart-coordinate exponential flow, and
`Comparison/InjectivityRadius.lean` already states the compact-uniform
injectivity-radius theorem conditional on lower semicontinuity of
`p ↦ injRadius g p`.  That detour was not needed: fixed parametrizations and
compactness give the required uniform constants directly.

## 2026-07-23 direct fixed-parametrization route

Further live audit did not find a direct route from existing fixed-centre
small-ball theorems to the all-centre statement.  `SmallBall.exists_edist_vol`
chooses the density radius, inner-product comparison constant, and normalized
volume constant after the centre `p`; it does not expose an open spatial patch
around `p` whose constants remain valid for nearby centres.  The conditional
injectivity-radius file gives the right compactness shape only after
`LowerSemicontinuous (fun p => injRadius g p)`, and the current exponential
smoothness API has not yet bridged chart-level joint exponential regularity to
that lower-semicontinuity or to a compact-uniform normal-coordinate radius.

Internal route review rejected both the full injectivity-radius
lower-semicontinuity detour and the idea of transferring a fixed-centre
small-ball estimate to nearby centres.  The latter loses uniformity because a
fixed spatial patch cannot make the centre displacement `O(r)` for every
`r -> 0`.

The selected route freezes one actual parametrization `Ψ` at each anchor and
proves scalar control on a compact model ball:

1. `diffeo_edist_le` supplies local pairwise Riemannian-distance control for
   any fixed smooth partial diffeomorphism, together with source membership.
2. The producer `exists_param_ctrl` gives a positive lower bound
   for the pullback volume density and a uniform upper bound for the speed of
   straight model-space segments, simultaneously for all sufficiently small
   times.
3. Those two scalar bounds put the image of a shifted model ball inside the
   moving metric ball and bound its volume below by a fixed multiple of
   `r ^ finrank`.
4. Compactness of `M` extracts finitely many anchor patches; finite minima of
   their time, radius, and density constants close `family_vol_low`.

This route needs neither `HasLocallyConstantChartAt` nor a globally selected
frame, and it adds no consumer assumption.

Progress accounting after this proof:

- `family_vol_low` theorem: 100%; its dedicated direct-route machinery: 100%.
- The refreshed `early_vol_low`, `early_ball_low`, and `no_local_open` consumer
  chain is source-complete: the original-flow all-carrier
  `NoLocalCollapsing` theorem and its dedicated assembly are 100%.
- The broader entropy/noncollapsing source machinery is about 99%. It is not
  axiom-clean because the positive-time branch still inherits the separate
  Weyl diagonal-kernel counting `sorry`.
- Hamilton's `ham3_noncollapse` is a separate downstream theorem; its direct
  source wiring and axiom status are recorded in `HamiltonPositiveRicci.md`.

## 2026-07-23 downstream axiom closure

The separate scalar Weyl frontier mentioned above is now closed for the
rank-zero entropy consumers. The complete downstream `EarlyBall` artifact
refresh passed, and `no_local_open` has no `sorryAx` in its axiom set.
Consequently the original-flow `NoLocalCollapsing` producer and its dedicated
small-ball/entropy assembly are both 100%; the stronger arbitrary-valence Weyl
theorem remains a separate short-time realization frontier.
