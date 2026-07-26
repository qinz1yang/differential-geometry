# HeatResolvent

## Durable result

This module is complete and focused verification passes without local
warnings.  It proves the five intended declarations:

- `baseHeat_fourier`: the normalized time-one Gaussian has Fourier symbol
  `exp (-4 * pi^2 * norm xi^2)`;
- `heatKernel_fourier`: positive-time parabolic scaling gives the symbol
  `exp (-4 * pi^2 * t * norm xi^2)`;
- `dampHeat`: the causal heat kernel with exponential damping;
- `dampHeat_int`: positive damping makes that spacetime kernel integrable;
- `dampHeat_fourier`: its exact spacetime Fourier transform is
  `1 / (delta + 4 * pi^2 * norm xi^2 + 2 * pi * i * tau)`.

The spacetime carrier is `WithLp 2 (Real x V)`.  The proof transfers volume
to the ordinary product by the existing measure-preserving `WithLp`
equivalence, applies time-first Fubini, uses `heatKernel_fourier` on the
spatial slices, and closes the causal time integral with the existing complex
exponential integral on `Ioi 0`.

No converse Plancherel theorem, convolution framework, Young inequality, CZ
layer, new class, instance, or notation was introduced.  The only failed
attempts were local elaboration shapes (coercions, real scalar multiplication,
and moving constants through Bochner integrals); they did not expose a
mathematical or API-design obstruction.

## Project status

- This producer module: 100%.
- The actual causal heat-Hessian `L2` realization sublane: still incomplete;
  this resolvent is one input, and the damped Hessian identification plus the
  limit as damping tends to zero remain.
- `ricci_flow_unif_existence`: exact theorem 0% (still unproved).
- `ricci_flow_forward_unique`: exact theorem 0% (still unproved).
- Consequently `extends_of_rmBounded` still depends on both analytic
  frontiers, and the full Hamilton positive-Ricci endpoint remains 0%.

The smallest next use of this file is to identify the damped causal spatial
Hessian with the bounded Fourier multiplier, then pass to zero damping in
`L2`.  That work belongs in the next realization module, not here.
