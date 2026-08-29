# Curve chart cover

## Scope

`exists_chart_split` is the weak-assumption curve-localization producer used by
the Perelman direct method. A curve continuous on `Icc a b` has a monotone
sequence of break points that starts at `a`, is eventually equal to `b`, and
whose consecutive closed pieces each map into one preferred chart source.
Only `ChartedSpace H M` is required.

`exists_cpt_split` strengthens the same subdivision on a locally compact
regular target. Each closed piece maps into the interior of a compact set
contained in its preferred chart source. Mathlib's compact-between theorem
produces this compact buffer directly from the compact curve-segment image and
the open chart source; no global compactness or Hausdorff assumption is needed.

`mapsTo_eventually` is the generic stability producer used after extracting a
uniformly convergent subsequence. If the limiting map sends a compact set into
an open set, every sufficiently late approximant does too. The necessary
uniform entourage is produced internally from the compact limiting image by
the Lebesgue-number lemma.

The eventual equality supplies a genuinely finite effective subdivision. The
statement avoids the existing heavy parallel-transport theorem, which assumes
global continuity and carries unrelated finite-dimensional smooth-manifold
context.

## Verification and next boundary

Focused verification passes without warnings or placeholders. The first proof
is a direct specialization of Mathlib's compact-interval open-cover
subdivision. The buffered refinement reuses it and applies compact-set
shrinking inside each open chart source.

The next analytic boundary is restriction and translation of `timeH1` data to
the finitely many subintervals, followed by finite diagonal extraction. This
file deliberately introduces no manifold-valued Sobolev object.
