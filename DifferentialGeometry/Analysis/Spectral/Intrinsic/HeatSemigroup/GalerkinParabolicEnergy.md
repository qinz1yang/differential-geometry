# Galerkin parabolic energy

## 2026-07-13 rank-generic consumer

The spectral energy, ODE derivative identity, and uniform per-scale energy
consumer are now rank-generic in the tensor valences.  Existing DeTurck uses
continue to infer `(0,2)`, while the scalar non-autonomous lane can instantiate
the same API at `(0,0)` without a parallel energy hierarchy.

The edited module passes focused verification and its named module refresh
passes.  A direct focused verification of the existing DeTurck consumer did
not reach elaboration of these calls because its dependency chain still has
missing stale object files; refreshing one missing dependency exposed another,
and the named consumer refresh exceeded the verification time window before a
subsequent missing dependency was reported.  No DeTurck source was changed.

This refactor does not close the scalar regularity frontier.  The load-bearing
consumer hypothesis remains the per-order closure inequality in
`galerkin_energy_uniform_bound_perScale`, with a top-energy coefficient
strictly below `2`.  The current scalar `H² → H⁰` operator bound and
`conj_weak_ae` only provide the base-scale equation; they do not prove that
per-order inequality.  A direct finite-core scalar dissipation theorem would
be sufficient and is weaker than a full operator-norm `scalar_crit_tame`, but
its high-order coefficient and commutator estimate is still genuine missing
analytic content.

