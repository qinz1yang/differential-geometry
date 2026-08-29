# Nonlinear time actions

## Scope and status

Dedicated Perelman L-geometry machinery is about 79--83% complete, while its
reduced-volume capstone remains 0%.  This generic nonlinear time-action brick
is complete for the statements below (100%); applying it to the geometric
L-action is outside this file and remains 0% here.

`timeNlinPot_line` differentiates the genuine curve-dependent density
`V t (u t)` along affine time-`H¹` variations.  Its hypotheses are pointwise
gradient realization and joint continuity of the density and gradient; the
dominated-integral estimate is proved from compactness rather than assumed as
an action derivative.

`timeNlin_euler` obtains the integral `L¹` force pairing from an actual
fixed-endpoint local minimizer.  The force is `G t (u t)`, is proved integrable,
and is in the exact form consumed by `mom_primitive_l1`.

## Curve-dependent quadratic coefficient

`coeffQuad_line` proves the pointwise affine-line derivative of
`inner (B(x) p) p` from an actual Fréchet derivative `DB` and self-adjointness.
`coeffForce` is the Riesz representative of its spatial derivative.

`timeCoeff_line` differentiates the corresponding curve-dependent quadratic
action for time-`H¹` curves.  It does not freeze `B` and does not assume the
action derivative: the formula is obtained from `coeffQuad_line` and the
parametric integral theorem.  Its explicit measurability and common integrable
domination hypotheses are the honest remaining consumer obligations.  For a
geometric metric coefficient these require coefficient bounds and first
spatial-derivative growth strong enough to control the quadratic `L²` velocity
term in `L¹`; this file does not claim those geometry-specific estimates.

Thus the generic coefficient line differentiation theorem is complete (100%),
while a geometric producer of its domination hypotheses is not started here
(0%).  The fixed-coefficient `timeNlin_euler` must not be described as closing
the curve-dependent kinetic coefficient case.

Focused verification and the targeted module refresh passed without warnings
or placeholders.
