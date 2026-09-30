# AC58: actual arc-length prefixes and opposite calibration

Five public theorems in three leaves close the finite-metric AC58 contract.
The general parametrization theorem starts with an actual continuous curve
c:[0,1]->X of finite eVariationOn. It constructs a continuous monotone parameter
phi from zero to the actual total variation ell, and a 1-Lipschitz curve
q:[0,ell]->X with the original endpoints and c(t)=q(phi(t)). Every subinterval
[s,t] has EXACT eVariationOn equal to t-s. Pauses in the original curve and
zero total length are allowed; no strict monotonicity of phi is assumed.

The construction uses signed variation, its continuity for continuous curves,
the intermediate value theorem, and constancy on equal-variation fibers. It
chooses actual original curve points, never points in a completion. Exact
subpath lengths follow from variation under monotone composition. Thus neither
completeness, local compactness, minimizing source segments nor curvature is used.

For an actual curve from p to a with length <d(p,a)+eta, eta>0, the second leaf
restricts the constructed parametrization to [0,d(p,a)]. The resulting prefix
stays in the image of the supplied curve, starts at p, is 1-Lipschitz and has
remaining distance <d(p,a)+eta-t. It proves the radial bounds t-eta<=d(p,q(t))<=t
and same-branch bounds t-s-eta<=d(q(s),q(t))<=t-s. The full original path is
not asserted to remain in the open endpoint-radius ball.

For the original arbitrarily-short-curves characterization of a length metric,
actual opposite endpoints at equal positive distance L produce TWO actual
prefixes on [0,L]. With E=2L-d(aPlus,aMinus), they obey the blueprint's exact
cross-branch estimate t+u-E-2eta<=d(qPlus(t),qMinus(u))<=t+u and BOTH signed
distance-coordinate calibration bounds:

    t-eta <= L-d(qPlus(t),aPlus) <= t,
    -t <= L-d(qMinus(t),aPlus) <= -t+E+eta.

Every initial prefix up to T lies in the closed T-ball, including its boundary.
The scalar opposite-prefix estimate is also public under its exact radial/tail
inputs. E is the actual absolute excess, not an assumed relative-error packet.
No source properness or completeness is added. The source-length producer is
expressed using continuous unit-interval curves and their actual metric variation.

Checked sources: blueprint207A full AC58 5033-5085 and AC59-60 5089-5205;
BBI AMS2001 Proposition2.5.9, printed46/PDF61, including the nondecreasing
continuous length parameter, equal-variation fibers, nonexpansion and exact
subpath lengths. The retained July6,2024 errata PDF1-3 were reread, retaining
the finite-metric qualification for Sections2.4-2.5. No correction to2.5.9
itself is listed there. The adjacent2.5.14 diagonal/uniform proof and its
constants are not imported here. Pinned Mathlib VariationOnFromTo34-171,
351-362 and BoundedVariation500-550,986-1023 supply the actual signed variation,
composition and continuity proofs. No fresh remote errata clearance is claimed.

AC58 is now produced from original finite length-space inputs. AC59 extraction
of whole lines in the same prescribed target, finite-family synchronization,
and the connection to the checked AC60 coordinate squeeze remain next. This
milestone does not silently replace an almost-minimizing prefix by a source
geodesic or claim multi-axis splitting. Earlier mathematical leaves, blueprint207
and migration interfaces are unchanged.
