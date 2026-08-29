# GeodesicSpeedBound

## Endpoint Cauchy and compact-limit API

`curve_cauchy_speed` extracts the existing bounded-speed estimate as a Cauchy-filter
producer without assuming ambient completeness. The original complete-space endpoint
is now a wrapper around this producer.

`curve_lim_of_compact` applies compact-set completeness in the pseudo-emetric topology
to the same Cauchy filter. Eventual membership of the curve tail in the compact set
ensures that the filter is bounded by the corresponding principal filter.

Focused verification and the named module refresh passed.
