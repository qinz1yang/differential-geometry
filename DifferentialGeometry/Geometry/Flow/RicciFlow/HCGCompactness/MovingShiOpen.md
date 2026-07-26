# MovingShiOpen

## Current verification state

The public interface remains unchanged.  `movingShi_of_bound`,
`movingShi_complete`, and `CurvBoundInput.movingShi_open` are focused-green and
the exact target is current (`9634/9634`), with no local `sorry` or warning.
The local assembly repairs installed the stored carrier instances explicitly,
used the complete left-anchor metric for the tangent norm, and removed an
accidental compactness requirement from the chart-local tower-norm regularity
chain.

This remains an assembly result, not yet a trusted end-to-end complete-Shi
theorem.  The arbitrary-dimensional direct tower is now exact-current as
`towerHeatSol_raw` / `towerHeatSol_any`, and the unsupported sorry-backed
`exists_rmTowerSol` has been removed.  The remaining lower analytic gap is the
concrete solution-produced `ShiCutoffData`: this module still calls the legacy
sorry-backed `BernsteinTower.estimate_complete`.  The corrected fixed-order
generic consumer `BernsteinTower.estimate_cutoff_at` is exact-current, with
`estimate_of_cutoff` retained as its all-order compatibility wrapper, but
neither can be used here until that cutoff producer is proved.

- `shiOpenConst` is an explicit constants-first envelope depending only on the
  model dimension, the common squared-curvature bound, the buffered time slab,
  and the requested finite order.  It contains no flow or sequence-member
  argument.
- `movingShi_complete` is fully assembled from the constants-first core.
- `CurvBoundInput.movingShi_open` is fully assembled on the canonical windows.
  It uses
  `alpha = openWindowLeft a 0 (n + 1)`,
  `beta = openWindowLeft a 0 n`, and
  `psi = openWindowRight b 0 n`.
  The curvature package first chooses one `C` on `[alpha, psi]`; the theorem
  then chooses `shiOpenConst ... C alpha beta psi N` before introducing the
  sequence member `k`.  Thus there is no invalid uniformization of memberwise
  existential constants.

The public sequence conclusion necessarily displays the stored topology,
charted-space, manifold, sigma-compactness, and `T2Space` instances for each
varying carrier.  These are the canonical fields of `PointedFlowData`, not new
geometric hypotheses.

## 2026-07-23 fixed-order cutoff adapter

The finite truncation has been factored once as the private
`exists_trunc_tower`.  The legacy `complete_of_heat` path and the new
`complete_of_cutoff` path share that constructor rather than duplicating the
tower proof.  The cutoff path retains the genuine tower through `m + 1`, bounds
the reaction constants through that same level, and transports only the Kato
prefix through `m` to `BernsteinTower.estimate_cutoff_at`.  It does not consume
metric equivalence or a Ricci lower bound.

After one local multiplication-order repair and the coordinated
`BernsteinComplete` refresh, the complete file is focused GREEN with zero
diagnostics and exact GREEN (`9634/9634`).  The conditional cutoff adapter is
therefore checked; it is not yet the public route because the solution cutoff
producer does not exist.

## Analytic assembly

`movingShi_of_bound` now combines:

1. exact-current `towerHeatSol_any`, with the explicit constructor-tree cost
   `rmTowerCost`;
2. the legacy `BernsteinTower.estimate_complete`; the trusted replacement is
   exact-current `estimate_cutoff_at` through the checked private
   `complete_of_cutoff`, plus the still-unproved solution-produced
   `ShiCutoffData`;
3. the arbitrary-dimensional Ricci trace bound;
4. one-sided metric equivalence from the complete left anchor under the
   curvature bound; and
5. finite truncation through order `N` with the explicit common constant.

The strict start needed by `towerHeatSol_any` forces the canonical midpoint
`t0 = (alpha + beta) / 2`.  Consequently the uniform denominator in
`shiOpenConst` is `((beta - alpha) / 2) ^ k`, not
`(beta - alpha) ^ k`.  The complete anchor remains the given metric at
`alpha`; a private one-sided Ricci-flow comparison transports it to the
shifted Bernstein slab.  No completeness-at-every-time, compactness,
injectivity-radius, or endpoint-radius hypothesis was added.

The public proof currently uses `complete_of_heat`, the compatibility consumer
around legacy `BernsteinTower.estimate_complete`.  The same private truncation
constructor now also feeds the checked `complete_of_cutoff`; once concrete
cutoff data are available the public call can switch without changing the
Bernstein algebra or adding a second public API.  Thus the exact-green
HCG-facing assembly does not yet make the complete-Shi route trusted end to
end.

## 2026-07-24 point-centered barrier adapter

Added the private fixed-order `complete_of_barrier`.  It uses the same
`exists_trunc_tower` constructor as the smooth-cutoff adapter, retains the
tower through `m + 1`, transports Kato control through `m`, and consumes the
quantifier-correct point-centered family

```text
∀ O, Nonempty (ShiBarrierCutoffData G T O).
```

After rewriting the truncated time horizon, it calls the exact-current
`BernsteinTower.estimate_barrier_at`.  Focused verification of the complete
file is GREEN, and the coordinated exact refresh is GREEN (`9634/9634`).
This adapter adds no new public assumption and does not yet replace the public
legacy call: that switch remains blocked on the actual solution-generated
barrier-cutoff family.

The single-flow and sequence/open-window theorems contain no further `sorry`.
In particular, the sequence theorem must never be reproved by calling
`movingShi_complete` separately for each member and then trying to extract a
uniform constant.

## Honest accounting

- `movingShi_of_bound`: source proof and verification 100%; trusted theorem
  completion remains 0% because it consumes the one remaining legacy lower
  `sorry` in `estimate_complete`.
- `movingShi_complete` and `CurvBoundInput.movingShi_open`: wrapper proofs and
  verification 100%; trusted complete-Shi route remains 0% for the same lower
  reasons.
- dedicated HCG-facing complete-Shi assembly machinery: 100%.
- arbitrary-dimensional curvature-tower producer and dedicated machinery:
  100% checked.
- generic fixed-order cutoff/barrier Bernstein consumers and their HCG
  conditional adapters: 100% checked; the concrete solution-produced
  `ShiBarrierCutoffData` theorem remains 0%.
- unconditional `compactnessSol`: theorem 0%.
- whole-HCG support machinery: about 60%.
