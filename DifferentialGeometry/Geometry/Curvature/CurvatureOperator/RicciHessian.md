# Ricci--Hessian contraction

## 2026-07-16 checkpoint

`ricHess_eq_inner` is proved and focused verification passes.  It identifies
the trace of the canonical raised-Ricci map composed with
`v ↦ ∇_v (grad f)` with `inner02 Ric (hessianSec f)`.  The proof is
basis-independent at the public interface.  Internally it chooses a
metric-orthonormal basis, applies the existing inverse-metric trace and
`inner02` coordinate formulas, and uses `hessSec_inner_cov` plus Ricci
symmetry.  It never asserts equality of whole tensor or Hom-bundle models and
does not use supplied components or a Bianchi hypothesis.

The first attempted normal form used `ricEndoRaisedFib`.  That carrier was
rejected here because its defining module exports substantially stronger
ambient assumptions (`CompactSpace`, boundarylessness, nonzero dimension, and
related instances) than this scalar algebraic identity needs.  The checked
proof instead constructs the endomorphism directly from `metricRicciAt`,
`tensor0S_curry`, and `cotangentSharpLinear_gen`.  The remaining
`SigmaCompactSpace` and `T2Space` assumptions come from the canonical
`metricRicciAt` producer; finite dimensionality supplies `CompleteSpace E`
locally rather than adding it to the theorem interface.

Progress is deliberately separated:

- `ricHess_eq_inner`: theorem **100%**; its dedicated adapter machinery
  **100%**.
- `ricDriftDiv`: theorem **0%**; its dedicated geometric machinery is roughly
  **35%** (the Ricci--Hessian contraction is ready, but the exact divergence
  and derivative assembly is not).
- `weighted_hess_split`: theorem **0%**; its dedicated machinery is roughly
  **25%**, because it still depends on the preceding weighted-divergence
  identity and square-completion assembly.
- W monotonicity and Perelman no-local-collapsing: theorem **0%** each.  This
  helper is only a small producer inside that route; the canonical broader
  entropy/noncollapse machinery estimate remains about **59%**.
- The whole HCG program remains about **60%** at the machinery level, while its
  endpoint theorems remain **0%**.

No new `sorry`, axiom, consumer-side black box, or synonym hypothesis was
introduced.
