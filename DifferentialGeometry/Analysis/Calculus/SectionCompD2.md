# SectionCompD2

## Durable result

`sectionCompD2` isolates the exact second-order chain rule for a section
composition `p ↦ F (p, v p)`.  Its only term containing the top derivative
`D²v` is

`partialFDeriv₂ F p (v p) (D²v[a,b])`.

The remaining term is `D²F[(a,Dv a),(b,Dv b)]`, so it depends only on the
first jet of `v`.  For a local addition this identifies the full-state
vertical derivative that cancels after applying its inverse; no coarse or
small highest-order coefficient is introduced.

`sectionD2_cancel` records that cancellation as an exact theorem: on the
invertible vertical-derivative locus, subtract the first-jet remainder and
apply the inverse to recover `D²v` itself.  The geometric HMF chart formula
therefore does not need to re-prove the Banach-calculus algebra.

## Verification state

- Source implementation: 100%.
- Focused Lean verification and the named exported-module build: GREEN, with
  no local warning and no placeholder.
- Endpoint impact: both `ricci_flow_unif_existence` and
  `ricci_flow_forward_unique` remain theorem-level 0% until their exact public
  declarations are proved and checked.

## Next consumer

Specialize `F` to `connAddTarget q α`.  On a neighborhood where
`partialFDeriv₂ F z.1 z.2` is invertible, apply its inverse to the chart
tension formula.  The resulting lower term depends only on `(v,Dv)` and is
the input for the state-dependent constant, linear, and quadratic estimates.
