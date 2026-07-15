# GaussLemmaPullback.lean — notes

## 2026-06-13 (session 5): `expMapC2Radius` anchored to the ∞ smoothness producer

Context: Step B (`HCGCompactness/StepBLocalMetrics.md`, HARD-STOP #1) needed the forward-`expMap`
∞-smoothness available on a **geometrically named** radius that Step-A can bound below. The two
chart-flow producers in `Smoothness/OffZero.lean` are independent `Classical.choose` existentials
(`expMap_contMDiffAt2_of_norm_lt` for C², `expMap_contMDiffAt_infty_of_norm_lt` for ∞), so their
radii cannot be compared — the named-radius ∞ smoothness must be sourced from the ∞ producer
directly. This file owns `expMapC2Radius`, so the fix lives here.

Change (Option X — minimal, all opaque consumers safe):
- `expMapC2Radius` component **1** now uses `Exponential.expMap_contMDiffAt_infty_of_norm_lt`
  (was `…_contMDiffAt2_…`). `expMapC2Radius_pos`'s first branch updated to match. Every consumer of
  `expMapC2Radius` uses it opaquely (positivity + `min_le_*`), so the value shift is harmless; the
  `ρ ≤ expMapC2Radius` discipline elsewhere is an upper-bound hypothesis on `ρ`, unaffected.
- NEW `expMap_contMDiffAt_infty_of_norm_lt_radius (hw : ‖w‖ < expMapC2Radius g p) : ContMDiffAt ∞ … w`
  := `(choose_spec …).2 w (lt_of_lt_of_le hw (min_le_left _ _))`.
- `expMap_contMDiffAt2_of_norm_lt_radius` keeps its `ContMDiffAt 2` statement (it has C² consumers in
  JacobiVariation / MinimizingGeodesic) but is now derived `∞ → 2`.
  - **Gotcha:** the ContMDiff smoothness order is `WithTop ℕ∞`, where `∞ ≠ ⊤` (`ω = ⊤`). Plain
    `le_top` does NOT prove `(2 : WithTop ℕ∞) ≤ ∞`. Working idiom:
    `.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))` (cf.
    `Curvature/Riemann/Basic/Field.lean:145`). `exact_mod_cast (le_top : (2:ℕ∞) ≤ ⊤)` fails to bridge
    the WithTop numeral.
- NEW `mem_expMapDiffeo_source_of_norm_lt_radius (hx : ‖x‖ < expMapC2Radius g p) :
  x ∈ (expMapDiffeo g p).source` — extracted from the inline derivation in
  `mem_expDomain_of_norm_lt_radius` (which now reuses it). Gives `ball 0 expMapC2Radius ⊆ source` for
  free (component 4), so downstream the named ball needs no `∩ source`.

All focused checks GREEN; the new endpoints are axiom-clean (`propext, Classical.choice, Quot.sound`).
Downstream consumption (named-radius metric producers) lives in `HCGCompactness/StepBInputs.lean`.

## 2026-07-09: public radial-chain bridge

Promoted the formerly private radial chain-rule calculation to the public theorem
`mfderiv_exp_radial`.  It identifies the velocity of `t ↦ exp_p(t • a)` with the differential
of `exp_p` at `t • a` applied to `a`, under the existing `expMapC2Radius` smallness condition.
This is the reusable exponential-layer API needed by Step B; no HCG-specific data enters its
statement.  Focused verification and the targeted module refresh passed.

## 2026-07-13: optimal coercivity witness

`gpCoerciveConst` keeps its public name and existing positivity/coercivity API,
but its opaque witness is now selected as the minimum of `g_p(v,v)` on the
compact unit sphere.  The new comparison theorem `le_gpCoerciveConst` proves
that every global quadratic coercivity coefficient is below this selected
constant; the candidate coefficient need not be positive.

This is the canonical lower-layer repair needed by the HCG Gate 6 radius
producer.  Focused verification and the targeted module refresh passed.  No
HCG endpoint assumption or parallel coercivity constant was introduced.
