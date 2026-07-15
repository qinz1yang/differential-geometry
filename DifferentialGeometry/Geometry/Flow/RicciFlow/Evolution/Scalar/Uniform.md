# Scalar uniformity

## Goal

Turn the carrier-local joint continuity field `IsSolutionOn.scalarCont` into
the uniform-in-space time modulus needed by the conjugate-heat potential
operator.  No metric, chart, or global-frame structure is added to `M`.

## Route

At each spatial point, regularity of the center time upgrades carrier-local
continuity to ordinary continuity on a product neighborhood.  Compactness of
the manifold extracts a finite spatial subcover, and the associated finite
intersection of time neighborhoods gives the uniform statement
`scalar_unif`.

## Verification status

Focused verification and the targeted module build both pass without local
diagnostics or `sorry`.  The first heavy helper statement timed out while it
mentioned the full `IsSolutionOn` object; abstracting that helper to a real
function continuous on `K × univ` removed the `whnf` cost without raising
heartbeats or changing consumer assumptions.

## Progress accounting

- `scalar_unif`: complete (100%).
- Geometric `A1 : H¹(gT) →L H⁰(gT)`: theorem not yet assembled (0%);
  its dedicated scalar-uniformity producer is complete.
- Moving conjugate-heat existence theorem: not proved (0%).
- Perelman no-local-collapsing theorem: not proved (0%).
