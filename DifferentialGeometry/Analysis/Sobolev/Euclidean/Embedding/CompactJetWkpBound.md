# CompactJetWkpBound

## Proved source boundary

`wkp_bdd_of_jet` is the general quantitative bridge from uniformly bounded
compactly supported Frechet jets to a uniform `W^{k,p}` bound on an ambient
open set.

Its hypotheses are:

- one open set `Omega`;
- one compact set `K` with `K subset Omega`;
- a family of globally smooth scalar functions, all with topological support
  in `K`;
- one pointwise bound for all iterated Frechet derivatives through order `k`.

Its conclusions are simultaneous `MemWkp k p` membership and one common
finite `wkpNorm` upper bound.  The witness is the finite sum over orders and
coordinate multi-indices of

`volume K ^ (1 / p.toReal) * ENNReal.ofReal C`.

The proof uses only the canonical Euclidean APIs:

- `MemWkp_of_smooth_compactSupport_pub`;
- `iterWeakPartial_smooth_ae_eq_iterClassicalPartial`;
- `norm_iterClassicalPartial_le_iteratedFDeriv`;
- `eLpNorm_restrict_eq_of_support_subset`;
- `eLpNorm_le_of_ae_bound`.

## Verification state

The theorem now passes its focused Lean check with no local warnings.  The
only source repairs needed were the repository's current finite-sum binder
syntax (`∑ j ∈ ...`) and using `hC` explicitly when proving that the
`ENNReal.ofReal C` factor is finite.

No `sorry`, `admit`, axiom, opaque declaration, instance, notation, or
heartbeat setting was added.

Estimated status: this local producer 100%; `ricci_flow_unif_existence` 0%
until its exact theorem is proved and verified.

## Downstream use

`MetricWkpData.lean` should instantiate this theorem with the fixed compact
Euclidean image of each active POU support.  The remaining geometric work is
to bound the derivatives of the POU-weighted metric-difference component by
the intrinsic order-at-most-three metric bounds, then sum over the finite
active chart/component set.
