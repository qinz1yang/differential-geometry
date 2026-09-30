# Interval restrictions and cradle iteration

Five public theorems in three leaves prove actual interval-parametrized
forward/backward restrictions of a supplied isometry, compatibility of
those restrictions with the canonical germ angle, and a state-space cradle
iteration theorem.

The restricted maps are the explicit functions on [0,b-h] and [0,h-a]
obtained from the SAME interval extension at h+t and h-t. They are isometries,
including zero-length restricted intervals. At positive restricted length,
using the interval extension of this new map has exactly the same canonical
germ angle as the original shifted/reversed extension, for any other curve.
The compatibility theorem does not need curvature or geodesicity because
it follows from exact equality on a positive initial interval.

The iteration theorem uses any type of actual states Q and their numerical
arms a,b and angle alpha. States with model side below D must satisfy the
sorted cradle window. Each such state must admit a successor with the
specified actual min/max arm recurrence, nonincreasing model side, and
short model-angle domination. All states satisfy D<=a+b and alpha in[0,pi].
The theorem proves D<=S at EVERY state. Its proof constructs a sequence in
the subtype of putative failing states using choice, derives nonincrease,
and applies the accepted quantitative infinite-recurrence theorem. No
pre-existing sequence, convergence witness or terminal-state assumption is
required. If a state would be a successful stopping case, it cannot enter
that failing-state subtype.

The state functions and transition hypotheses are explicit assumptions.
This is the iteration engine, not the missing geometric instantiation:
constructing/sorting the actual specified hinges and discharging every
zero-arm, endpoint and small-hinge stopping case remain to be assembled.
Full ALG02 and final globalization are not claimed.

Source-checked frozen blueprint207A ALG02 full body7339-7415, especially
stopping/infinite iteration7389-7415, and pinned AKP vol1
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 defs-CBB.tex951-1090 are reused
unchanged from the preceding milestones. The blueprint's ell/36 quantitative
recurrence replaces an informal source late-arm assertion, as already
recorded in the accepted cradle_sequence contract. Metric restriction
formulas and canonical eventual-equality arguments reuse the accepted
source-checked SegmentExtension and CanonicalGermAngle leaves. Previously
checked source/errata distinctions remain unchanged.

Blueprint207, earlier mathematical leaves and PC migration interfaces are
unchanged. Endpoint-free recognition, intrinsic adaptation and uniform
curvature-to-covering production remain open.
