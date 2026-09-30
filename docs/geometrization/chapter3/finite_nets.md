# Witnessed nets, packing bounds, and proper finite prefixes

This leaf completes the explicit finite-cardinality part of MC02 and the
proper-source finite-prefix corollary of MC13. It uses the actual metric and
finite sets of points, not abstract covering numbers.

`Metric.card_le_card_of_separated_net` says that a finite rho-separated set
has cardinality at most that of a witnessed epsilon-net when rho > 2 epsilon.
The proof sends each point to a chosen nearby center and proves injectivity.
`Metric.exists_finset_net_card_le_of_packing` proves the converse with its
cardinality retained: if every finite rho-separated subset of a specified set
has at most N points, there is a net inside that set with at most N points
and all covering distances strictly less than rho. It selects a largest
eligible cardinality among 0,...,N; another uncovered point would contradict
maximality. Empty sets and N=0 require no special nonemptiness premise.

`Metric.exists_finset_net_of_isCompact` produces finite centers inside a
compact set and witnessed non-strict error bounds at every positive scale.
`Metric.uniform_finite_nets_of_eventual_of_proper` takes actual properness of
every source space and the quantified eventual net bound
forall R>0, epsilon>0, exists N,I, forall n>=I. It supplies an all-index bound
by adding the cardinalities of individually chosen nets for n<I. Both the
net centers and the covered points stay in the specified closed ball.
There is no assertion that local curvature bounds make the omitted prefixes
proper. The main pointed precompactness theorem does not require this
finite-prefix adapter or proper sources.

All four results work for pseudometric spaces. Their cardinality statements
are about actual finite sets; they do not count coincident labels twice.

Source comparison: blueprint207A, MC02 in the finite-nets section and MC13's
eventual-net/finite-prefix discussion; the corresponding complete entries in
metric_geometry_contracts.csv were reread. Unchanged source checks are reused
from reference_checks_revision58.md and reference_checks_revision61.md:
BBI Definition 1.6.1, printed13/PDF28; Exercise1.6.4 and Theorem1.6.5,
printed14/PDF29; the project's own MC13 finite-prefix argument. The archived
BBI2001 SHA256 is
4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971.
No new errata or full-book reading is claimed. The pinned Mathlib finite
compact ball-cover and finite-cardinality APIs are applied directly.

The scoped leaf build passed on Lean4.35.0-rc3. The combined manifest gate
records the source hash and checks every declaration's axiom closure.
