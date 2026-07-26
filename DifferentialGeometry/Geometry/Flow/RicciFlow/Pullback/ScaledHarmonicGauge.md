# Density-scaled harmonic gauge

## Proved source facts

- `transportScalar r Φ` is the smooth target scalar `r ∘ Φ⁻¹`.
- `ricci_pullback_drift` is the arbitrary-drift version of the reverse
  Ricci-flow pullback identity.
- `fixed_pullback_drift` gives the simultaneous evolution of a fixed metric
  pulled back by the same gauge.
- `scaled_hmf_target` identifies a source-scaled tension field with the
  transported-scalar multiple of the target DeTurck field.
- `scaled_inv_vel` exposes the inverse-gauge equation
  `∂ₜΨ⁻¹ = DΨ⁻¹ ((r ∘ Ψ⁻¹) W)`; this is the derivative-balanced alternative
  to evolving the pulled-back background as an independent tensor.
- `scaled_hmf_inverse` gives the exact inverse-pullback PDE
  `∂ₜG = -2 Ric(G) + ℒ_((r ∘ Ψ⁻¹) • W(G,q)) G`.
- `scaled_bg_inverse` gives, for `H = Ψ⁻¹* q`,
  `∂ₜH = ℒ_((r ∘ Ψ⁻¹) • W(G,q)) H`.

These declarations are source-written but have not yet been checked because a
shared named Lake build is still active.  They must not be counted as proved
until the focused check passes.

## Design ruling

For the fixed-reference-measure weak equation, the natural source scale is
`r_g = dμ_g / dμ_q`.  After inverse pullback the drift coefficient is
`r_g ∘ Ψ⁻¹`.  Naturality gives

`r_g ∘ Ψ⁻¹ = dμ_(Ψ⁻¹* g) / dμ_(Ψ⁻¹* q)`,

not `dμ_(Ψ⁻¹* g) / dμ_q` in general.  However, after adjoining the pulled-back
background `H = Ψ⁻¹* q`, this is exactly the intrinsic pair coefficient
`dμ_G / dμ_H`.  Thus the faithful common system is the closed pair

`G_t = -2 Ric(G) + ℒ_(a W(G,q)) G`,

`H_t = ℒ_(a W(G,q)) H`,

with `a = dμ_G/dμ_H`, rather than a metric-only equation for `G`.

At the coordinate principal level the `H` equation contains

`a H_kj G^bc ∂_i Γ(G)^k_bc + a H_ik G^bc ∂_j Γ(G)^k_bc`.

Thus it contains second derivatives of `G` but no second derivatives of `H`.
An equal-order `H^s` energy for `H` asks for `G` in `H^(s+2)`, one spatial
derivative beyond the time-integrated gain of the standard `G` parabolic
energy.  Lowering `H` by one order fixes that half, but not the whole coupled
estimate: linearizing the `G` equation differentiates
`a = (det G / det H)^(1/2)` inside `ℒ_(aW)G`, producing the term
`d(δH) · W(G,q)`.  Thus an `H^s` energy for `G` asks for `δH` in `H^s`, while
the `H` equation can be bounded from the parabolic dissipation only with
`δH` in `H^(s-1)`.  The requirements conflict by exactly one derivative.

The pair is closed algebraically but the direct Sobolev energy has a
one-derivative gap.  The `(G, Ψ⁻¹)` formulation removes the `∂²G` term from the
gauge equation (`∂ₜΨ⁻¹ = DΨ⁻¹ · aW(G,q)`), but because `a` then depends on
`DΨ⁻¹` the differentiated `G` equation still needs a weighted/cancellation
argument; it is not yet a closed unweighted energy proof.

The ordinary moving-measure weak form has the mass term
`(ρ(t)-1) ∂ₜu` after freezing the measure.  The current rough path carrier
controls `u` and its spatial gradient but no time derivative or source norm,
so that term cannot presently be inserted into its Duhamel map without an
additional estimate; integrating it by parts in time would require control of
`∂ₜρ`, which is absent at the joint-`C⁰` initial edge.

## Endpoint accounting

- `ricci_flow_forward_unique`: **0%** (exact theorem not proved).
- Scaled-gauge geometric identity: **source-written, 0% verified** pending the
  focused check.
- Smallest next mathematical lemma after verification: formulate the local
  chart-density identity `r_g ∘ Ψ⁻¹ = dμ_G/dμ_H`, then determine whether a
  parabolic--transport difference energy closes for `(G,H)`.
