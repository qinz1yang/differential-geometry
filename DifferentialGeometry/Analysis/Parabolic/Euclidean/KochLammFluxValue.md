# KochLammFluxValue

## Intended facts under focused verification

- `klHeat1 t w f x` is the sum of `heatEarly1 t w f x` and the full terminal
  potential `klFluxFull1 (sqrt t) w f x`, using the same direction `w`;
- the `KLSource1.local_l2` arm makes the complete early half-slab integrand
  Bochner integrable, while the canonical terminal shell theorem gives
  integrability on the late half-slab;
- `klHeat1_eq_heatPot` splits the product-measure integral at `t/2` and proves
  strict equality with the original Duhamel definition `heatPot1 t w f x`;
- `klHeat1_norm` combines the early `A₂` estimate and terminal `Aₚ` estimate
  at every positive `t ≤ T`, with explicit linear dependence on `norm w`.

This closes the value-level `KLSource1 → L∞` analytic chain only.  Gradient
and Carleson control of the full heat map, the fixed-point theorem, and the
exact theorem `ricci_flow_forward_unique` remain unproved; the endpoint is
still **0%**.
