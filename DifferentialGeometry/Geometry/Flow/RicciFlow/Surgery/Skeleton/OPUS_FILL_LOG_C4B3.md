# OPUS_FILL_LOG_C4B3 (DESIGN_C4B brick M5, case (B) per-point theorem)

## 2026-09-26 entry 1 (start)

Read: pc3 AGENTS.md (no header, no module docstring), DESIGN_C4B.md §0–§3, review H11 digest,
OPUS_FILL_LOG_C4B1.md, OPUS_FILL_LOG_C4B2.md, template `exists_capWindowPoint_bounds`
(`Surgery/Topology/CapWindowContinuationLeaf.lean:29`), bridge
`exists_standard_comparison_of_cap_window_trace`, `capWindow_flow_metric_eq`.

Compile method: own scratch `scratchpad/c4b3` (script `lc.sh`, copied from C4B2's with the
prefix `C4B3`); the five uncommitted C4B2 modules are compiled as `C4B3.<Base>` scratch modules;
C4B1's three files are committed and have shared oleans, imported by their real names.

Plan (constants): `Cs := Cw` (M4★). After `(Ctime, Cgrad, Dw, θcap)`: `Θ := max θcap (1/2)`,
`eta` (scalar/metric lower comparison at `Θ`), `c₀` (standard scalar lower bound),
`L := 2·Cw/√(c₀/2) + 1` (bounds `2·radius` since `R_S(z,T) ≥ c₀/2`), `Λ` (M1b window form at
`Θ`), M4★ at `(Θ, r := Dw + 1 + Λ(L+1) + 1)` gives `(D, N, e)`, bridge at `(Θ, Ctime)` and
`(D, e, eta, N)` gives `(Rcap, mcap, εcap, δmax)`; `ρmax` as in C3b.

## 2026-09-26 entry 2 (successor worker; predecessor killed)

Constant plan revised (simpler, same order): the carry-ball bound uses `Q.val.one_le_scalar`
(`R_Q ≥ 1` on `[0,Θ]`) and the lower comparison `R_S ≥ R_Q/2`, so `√R_S ≥ 1/2` and
`2·W.radius ≤ 4·Cw < L := 4·Cw + 1`; no `c₀`. Order: `Cs := Cw` (M4★); after
`(Ctime, Cgrad, Dw, θcap)`: `Θ := max θcap (1/2)`, `eta` (lower comparison at `Θ`), `Λ` (M1b
window form at `Θ`), `L`, M4★ at `(Θ, r := Dw + 1 + Λ(L+1))` gives the ONE `(D, N, e)`, bridge at
`(Θ, Ctime)` and `(D, e, eta, N)` gives `(Rcap, mcap, εcap, δmax)`; `ρmax` as in C3b. The bridge
is called with `qcan` itself (M5's `DerivativeBoundBefore Ctime qcan t`), `qcan ≤ Cb·q` from
`birth_scale_bounds`' `2qcan ≤ Cb·q`.

File: `Surgery/Topology/CapWindowSpatialCanonicalWitness.lean` (new). Scratch deps recompiled
(the predecessor's run had died with rc=127 on the second module).

## M5 (done, compiles clean)

- `Surgery/Topology/CapWindowSpatialCanonicalWitness.lean` (191 lines),
  `RetainedCoreHistory.exists_capWindowPoint_spatialCanonicalWitness`, statement byte-identical to
  DESIGN_C4B §2 M5 (diffed). No deviation, no added hypothesis.
- Proof: bridge `exists_standard_comparison_of_cap_window_trace` at `(Θ, Ctime)` with `(D, e, eta, N)`
  from M4★ at `(Θ, Dw + 1 + Λ(L+1))`; `capWindow_flow_metric_eq`; `subst` of `(Ξ z).val.val = y`;
  the gradient hypothesis (constant `Cgrad ≤ max Cw Cgrad`) pulled back by G to `S T` at `z`;
  M4★ with `C2 := max Cw Cgrad` gives `W` on `S T`, rewritten to the local pull; carry ball
  `L = 4Cw + 1` (`R_S ≥ R_Q/2 ≥ 1/2` from the lower comparison and `one_le_scalar`, so
  `2·radius ≤ 4Cw`), compact by M1b (window form, `(1/2)Q ≤ S T` from the same comparison,
  room `‖z‖ + Λ(L+1) < D + 1`); M3 `pushforwardOfInjectiveULift` along `val∘val∘Ξ`
  (injectivity `injective_backwardSurvivorIncomingDomain_val_val`); then
  `SpatialCanonicalWitness.scaleMetric q⁻¹` and `scaleMetric q⁻¹ (scaleMetric q g) = g` by
  `ext_inner`. Constants `(1, max Cw Cgrad)` unchanged by the carry, so no `enlargeConstants`.
- Compiled as scratch module `C4B3.CapWindowSpatialCanonicalWitness` against scratch builds of the
  five C4B2 modules (all rc=0, zero output), lakefile options, zero output.
- Axioms: `[propext, Classical.choice, Quot.sound]` (probe outside the tree, removed).
- Wiring: imports `C4B2`'s `StandardWindowSpatialCanonical` / `StandardWindowBallPlacement`
  (uncommitted) and the committed M3 / G / bridge / assembly modules; register after those.
