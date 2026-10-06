import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RecentProtection_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowConstants_CX2

set_option autoImplicit false

namespace GC.LongTime.Ch12

/-!
# W2 / G3b components (CX2)

Source contract: commit 423084828353abab336bcbd50d70a86fc0386ed1,
`build-logs/ch12/DELIVERIES.md`, CH12-O4 FROZEN (G3b), and
`docs/geometrization/chapter13/design-wbd-merged-20261004.md`, sections 4.1–4.4.

Proved here and in the imported CX2 modules:

* `slice_isTracedRegion_iff_CX2`: the actual observation prefix and its tower
  history have equivalent traced regions, including incoming-terminal bounds.
* `enlarged_rm_bound_of_slice_seed_CX2`: G3a transported to the exact histories
  used by G2. `enlarged_rm_bound_along_seed_trace_CX2` identifies the independently
  chosen G2 centres with one compatible seed trace.
* `smooth_path_first_exit_CX2` and its scaled version: the moving curvature
  buffer prevents first exit on a smooth compact-stage interval. The proof
  uses the bound only inside that buffer.
* `exists_recent_path_lift_CX2`: after uniform choices of T and Λ, the actual
  records lift a whole low-curvature outgoing path to the incoming terminal
  metric, preserving its anchor, length, and curvature bound. The argument
  excludes the retained-image frontier by continuity of scalar curvature
  from the dense retained interior; it needs no cap-interior scalar assumption.
* `exists_window_constants_CX2`: the strict W2 time budget and the length
  factor less than two, uniformly in the observation time and radius.

Remaining assembly (not asserted as a theorem): extend the smooth path
estimate to an incoming slab whose top endpoint is its terminal limit,
then induct backwards over the finite surgery indices, preserving one
cumulative exponential length estimate across all slabs. For every final
x in B_t(p,2r), this must produce a BackwardPointTrace to t-τ*r² and prove
both clauses of isRmBoundedBy (K/r²). Quantifying over x then yields the
isTracedRegion required by `macroWholeBall_O2_of_W2_S8`.

In particular, this module does not prove hW2 from G1 and G2. G1 and G2 are
still the frozen upstream suppliers; no weaker seed statement is substituted
for either supplier, and the remaining assembly is not hidden in a named
proposition or supplied as an additional hypothesis to a claimed W2 theorem.
-/

end GC.LongTime.Ch12
