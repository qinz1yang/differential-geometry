# Uniform scalar nonautonomous pairings

## 2026-07-14 one-slab source closure

The source now contains the complete intended one-slab chain:

- `cc_comm_unif` gives a support-independent principal commutator constant at
  each order;
- `cc_conn_unif` derives time-uniform `connTraceCoeff` jets from the same
  `metricDiff_slab` metric envelope and gives the first-order pairing bound;
- `cc_lap_unif` intersects the commutator, connection, and quarter-smallness
  slabs, preserves `T - s ∈ D.regular`, and has the fixed top coefficient
  `1 / 3`;
- `cc_a2_unif` converts this to the finite scalar Galerkin normal form with top
  coefficient `5 / 3` and quantifier order
  `tau`, regular-time arm, `n`, `Cmid`, time, mode set, spectral vector.

The constants are independent of spectral support, its cardinality, and the
Galerkin cutoff.  The proof uses `appRS_jet_bdd` and `fixed_jet_bdd` as the two
small coefficient-envelope combinators, the public connection-difference
product-grid estimate, balanced pairing, the scalar Dirichlet gap, and the
existing finite spectral pairing identity.  It adds no consumer assumptions
and does not use `HasLocallyConstantChartAt`.

Focused verification now passes.  The stale source failures were not analytic:
the file needed direct access to `CometricDoubleTraceField`, the
`TensorHeatEquation` and `DeTurck` namespaces had to be opened explicitly, and
three local `let` definitions had to be normalized with `simp only` before
rewriting.  No theorem statement or hypothesis changed.

Honest accounting: `cc_a2_unif` and its dedicated machinery are 100% verified.
The downstream `scalar_crit_tame` theorem is source-written but remains 0%
complete pending its own verification; its dedicated machinery is about 99%.
Perelman no-local-collapsing and `ham3_noncollapse` remain theorem-level 0%,
with about 44% dedicated analytic machinery.  Whole HCG machinery is about
54%, with its endpoint theorems at 0%.

## 2026-07-15 all-scale coefficient slab

`lapCoeff_slab` is now a separate verified producer.  On one common backward
slab it returns nonnegative all-order pointwise covariant-jet envelopes for
both `scalarTraceCoeff` and `connTraceCoeff`, together with the reflected
regular-time arm.  Its time interval is chosen before the jet order and before
the input tensor, so later Sobolev constants remain independent of spectral
support.

The producer is extracted from the existing `metricDiff_slab` route rather
than added as a wrapper assumption.  The private trace construction now
retains the already-proved `scalarTraceCoeff` envelope as well as the
`traceCast` envelope.  `cc_conn_unif` consumes `lapCoeff_slab`, removing the
duplicated coefficient construction while preserving its public statement.
Focused verification passes without `sorry`.

Honest accounting: `lapCoeff_slab` is theorem-level **100%**, and its dedicated
coefficient machinery is **100%**.  The downstream `lapDiff_hs_unif` smooth-core
A2 theorem is separately verified at **100%**; it is not a completed operator.
The `H^(m+2) ->L H^m` A2 operator and its time-continuous path remain unstated
(**0%** each), with approximately **88%** and **60%** dedicated machinery,
respectively.  Perelman no-local-collapsing and `ham3_noncollapse` remain
endpoint-level **0%**.

## 2026-07-19 minimal shared API

Only two existing generic producers were made public for the compact-span
replay: `fluxDiv_jet_bdd` and `finite_lap_unif`.  Their proofs, hypotheses, and
normal forms are unchanged.  The lower helpers `appRS_jet_bdd`,
`fixed_jet_bdd`, and `traceCast_jet_bdd` remain private; the new span proof uses
the already-public joint coefficient API and therefore does not need to widen
that surface.

Focused verification passes without warnings or `sorry`.  The public
producers and their dedicated machinery are theorem-level 100%; downstream
compact-span verification awaits the sequential exported-object refresh.
