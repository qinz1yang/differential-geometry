# Distance coordinates, Lipschitz constants and the open-image rank bound

One definition and eight public theorems in two leaves bind AC15 and the
upper-Lipschitz/rank part of AC23 to Mathlib's actual norms and Hausdorff
dimension. They do not assume injectivity or claim that openness has yet
been produced from a pointwise paired packet.

`Metric.distanceCoordinates p a x` is the vector of the actual ambient
distances d(x,a_i), in Mathlib's `PiLp p`. For every p>=1, its Lipschitz
constant is card(iota)^((1/p).toReal). The p=1 and p=2 theorems give exactly
card(iota) and sqrt(card(iota)), respectively. Empty index types are
included. The p=infinity specialization uses Mathlib's usual convention;
no change to the ambient or target metric is hidden in these maps.

For a Lipschitz map on a subset s into any finite-dimensional real normed
space E, a nonempty interior of its actual image gives

    finrank(Real,E) <= dimH(s).

The ball-image version combines this with dimH(s)<=n and concludes the
ordinary natural-number inequality finrank(Real,E)<=n. Applying it to
the SAME distance-coordinate map gives card(iota)<=n. The proof uses
actual Hausdorff image monotonicity and the dimension of a nonempty
open set in E. It makes no inference from mere injectivity, and requires
a positive-radius ball in the ball-image version.

## Sources checked and library binding

Read blueprint207A AC15's full statement/proof, lines2808–2832, and AC23's
upper-norm and rank conclusions, lines3160–3223. Reopened BGP1992 English
Section6.2 and Lemma6.4 with its full proof, printed20–21/PDF21–22; this
is the Lipschitz open-image rank step, not a proof of the paper's entire
burst-index/rough-dimension equivalence. Existing BGP errata qualifications
from revision64 are reused unchanged.

Inspected the pinned Mathlib c55e6e786f49471c72fbddbec5415808896aec1e
source bodies for `PiLp.lipschitzWith_toLp`, its antilipschitz/one-sided
inverse dependencies, `LipschitzOnWith.dimH_image_le`, and
`Real.dimH_of_nonempty_interior` / `Real.dimH_of_mem_nhds`, including the
finite-dimensional equivalence and positive Euclidean-ball calculation.
The underlying max-norm coordinate map is proved 1-Lipschitz by the actual
metric distance inequality before applying the PiLp norm equivalence.
The target dimension is transported by the canonical WithLp linear
equivalence and Mathlib's finite-function-space finrank theorem.
Exact source hashes and locators are in the evidence receipt.

## Remaining scope

AC21 now supplies geometric moves on a common comparison domain. Its
finite packet consumer, complete-buffer local openness and localization
from pointwise strict angle inequalities remain to be assembled for
full AC23. Rank-exclusion injectivity and later rough-dimension transport
remain separate. Blueprint207 and earlier mathematical leaves are unchanged.
