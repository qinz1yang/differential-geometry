# LogSobolev

## 2026-07-16 closed three-manifold estimate

`logSobolev_closed` is checked without warnings or a local `sorry`.  For a
fixed closed three-manifold it chooses one constant before `tau` and `v`, and
controls every positive normalized smooth amplitude uniformly for
`tau ∈ Set.Ioc 0 tauMax`.  The dimension equation `finrank ℝ E = 3` constructs
the required local `NeZero` instance inside the proof, so the public theorem
does not carry a redundant consumer assumption.  No positivity assumption on
`tauMax` is needed: when the interval is empty the conclusion is vacuous.

The log-Sobolev producer is **100%**.  It supplies the entropy input to
`w_fixed_lower`; it is not the intrinsic cutoff or no-local-collapsing theorem.
