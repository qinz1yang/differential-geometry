# ScalarNonautSpan

## Goal

Produce prescribed-length scalar nonautonomous estimates on a compact regular
time interval.  These estimates are the analytic input for a finite interior
Galerkin propagation argument; they do not change the scalar Galerkin consumer
assumptions.

## 2026-07-18 metric and flux span

`metricDiff_span` and `scalarFlux_span` were added in a new Garding module so
the compact-span lane does not edit the stale-claimed `ScalarFluxJetBound.lean`
or `ScalarNonautUniform.lean` files.

The metric theorem uses `HCGCompactness.metric_c1_span` with tolerance `1/4`.
For one radius on `Icc a b ⊆ D.regular`, every admissible frozen time and
backward interval has the existing quarter-small metric perturbation and a
common fixed-background metric-difference jet envelope.  Compactness of the
prescribed interval supplies the all-order envelope through `joint_jet_bdd`.
The flux theorem then applies the existing `scalarFlux_jet_grid`; no tensor
algebra was duplicated.

The upstream object refresh completed.  The first full elaboration then found
two private-API visibility failures: `metricDiff_joint` and `grid_mono` are
private to `ScalarFluxJetBound.lean`.  The small finite-product monotonicity
argument was closed inline.  The substantive joint-smoothness bridge was not
copied: its exact `ContMDiffOn` obligation is now the file's single explicit
`sorry`, pending canonical exposure of the already-proved private theorem.

## Exact next frontier

The next mathematical producer is a prescribed-length version of the
principal and connection pairing estimates, followed by `cc_a2_span`.
This is not obtainable by restricting `cc_comm_unif` or `cc_conn_unif`: their
existential lifetimes are selected independently at each frozen time.

Before the later pairing replay, the reusable generic jet-envelope proofs live
as private declarations (`appRS_jet_bdd`, `fixed_jet_bdd`,
`fluxDiv_jet_bdd`, and `traceCast_jet_bdd`) in the stale-claimed
`ScalarNonautUniform.lean`.  The preferred refactor is to expose the smallest
generic helpers at the Garding layer and reuse them from both the local-slab
and compact-span theorems.  Duplicating them in this file would create a second
implementation, while force-releasing the existing claim would violate shared
workspace ownership.

A normal claim attempt confirmed the blocker.  The conflicting token is
`a05069d7-e9e4-45fc-a965-f4abe11355eb`; its recorded process is no longer
running, but ownership is unknown, so it was not force-released.  Two other
routes were rejected: finite-subcovering the independently selected lifetimes
does not transport estimates between the terminal-metric spectral spaces, and
copying the private helpers locally would leave two canonical implementations.
The earlier joint-smoothness bridge is likewise blocked behind the stale claim
`4bc8c3d3-d009-4dce-bc77-21043f23e1d4` on
`ScalarFluxJetBound.lean`; its recorded process is also no longer running, but
it was not force-released.

### Prepared consult prompt (do not send automatically)

Use the GitHub repository `liao9yuan/differential-geometry`, branch
`short-time-existence`, as the reference tree.  We have a verified compact-slab
varying-background `metric_c1_span` and have implemented target-length
`metricDiff_span` and `scalarFlux_span`.  To replay `cc_comm_unif`,
`lapCoeff_slab`, `cc_conn_unif`, `cc_lap_unif`, and `cc_a2_unif` at a prescribed
length, the current proof needs the generic declarations `appRS_jet_bdd`,
`fixed_jet_bdd`, `fluxDiv_jet_bdd`, and `traceCast_jet_bdd`, but all four are
private in `DifferentialGeometry/Analysis/Spectral/Intrinsic/Garding/ScalarNonautUniform.lean`.
Recommend the smallest canonical API extraction and exact theorem normal forms
that let both the old existential-slab and new compact-span proofs reuse one
implementation.  Do not add consumer assumptions, do not use
`HasLocallyConstantChartAt`, do not compare whole spectral spaces at different
terminal metrics, and keep every new theorem name at most 20 characters.

Focused verification now succeeds with exactly one `declaration uses sorry`
warning and no Lean errors.  Honest status: `metricDiff_span` and
`scalarFlux_span` remain theorem-level 0% because that one producer obligation
still has `sorry`; their dedicated proof machinery is about 95%.
`cc_a2_span`, the target-length critical tame estimate, `gal_span`, and all
downstream noncollapsing propagation theorems are not yet stated and remain
theorem-level 0%.

## 2026-07-19 prescribed A2 source

The stale-claim blocker above is superseded.  After confirming that both old
claim processes were dead, the claims were released and the smallest canonical
API was exposed: `metricDiff_joint`, `fluxDiv_jet_bdd`, and
`finite_lap_unif`.  No copies or consumer assumptions were introduced.

The explicit `sorry` in `metricDiff_span` is discharged by the public
`metricDiff_joint`.  The module now contains `metricDiff_span`,
`scalarFlux_span`, `cc_comm_span`, `cc_conn_span`, `cc_lap_span`, and
`cc_a2_span`, all without local `sorry`.  The common radius is chosen before
the terminal time and before the terminal-metric spectral type.  The final A2
constant is independent of spectral support and Galerkin cutoff.

Both edited producer modules pass focused verification.  Final focused
verification of this module is pending their sequential exported-object
refresh.  Until that check passes, these new span theorems remain theorem-level
0% with approximately 99% dedicated source and machinery.  The next theorem is
`scalar_crit_span`, followed by the target-length Galerkin assembly.

## 2026-07-23 post-merge check

The span module now imports the cometric double-trace field API directly, opens
the needed parabolic/intrinsic namespaces, and proves the finite spectral
support sum extension using `hv.toFinset`.  Focused verification and the module
artifact refresh both passed.
