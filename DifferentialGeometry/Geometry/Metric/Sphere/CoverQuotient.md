# CoverQuotient

## Role

`roundQuotientUC` turns a global metric isometry from the round sphere onto
the universal cover of a standard-model manifold into `RoundQuotientData`.
It is deliberately a transparent `noncomputable def`, rather than an opaque
theorem returning data, so its output carrier `.Q` reduces definitionally to
the input manifold.

## Route

The fundamental group acts on the universal cover by deck
diffeomorphisms.  Conjugating that action by the supplied global
diffeomorphism gives an action on the round sphere.  Metric preservation is
proved without differentiating the inverse: the identity

`d ∘ φ a = (fun z => a • z) ∘ d`

is differentiated on both sides and combined with `deck_inner` and the two
instances of the supplied metric-isometry equation.  `orth_rep_of_iso` then
realizes the action by ambient orthogonal transformations.

Compactness of the round sphere transfers across `d`, so
`finite_pi1_of_uc` gives a finite fundamental group.  The quotient map is
the universal-cover projection composed with `d`; its orbit fibers use
`proj_eq_iff_smul`, and its local sections come from `SectionWitness.ofLocal`
using `proj_localDiffeo` and `hloc_comp`.  No consumer-side convergence,
chart-selector, or additional quotient assumptions were introduced.

## Verification and progress

Focused verification passed without warnings, and the exact module build
passed.  The file contains no `sorry` or `admit`.

This universal-cover-to-round-quotient producer is complete (100%), as is
the dedicated deck-action/quotient assembly it packages.  The theorem
`ham3_space_box` itself remains unstated/unproved here and is therefore 0%;
its dedicated global spherical-space-form machinery is approximately 90%.
The wider Hamilton positive-Ricci infrastructure remains approximately 80%,
and the whole HCG compactness infrastructure approximately 60%.
