# ConnAddHessian

## Exact fixed-chart result

This file specializes the generic `sectionCompD2` and `sectionD2_cancel`
theorems to `localAddTarget g p`; it does not repeat their chain-rule algebra.

- `connAddD2Rem g p v z a b` is
  `D²(localAddTarget)_(z,v z)[(a,Dv a),(b,Dv b)]`.  Relative to the section
  variable `v`, it depends only on the first jet `(v z,Dv z)`.
- `connAddD2_split` proves that the Hessian of
  `x ↦ localAddTarget g p (x,v x)` is exactly
  `J(z,v z)(D²v[a,b]) + connAddD2Rem`, where `J` is `partialFDeriv₂`.
- `connAddD2_cancel` proves that, when `J(z,v z)` is invertible, subtracting
  the remainder and applying `J⁻¹` returns `D²v[a,b]` exactly.
- `exists_connAddD2` combines this identity with `exists_connAdd_tube`: one
  fixed-basepoint compact coordinate tube has continuous inverse vertical
  derivative, and every `C²` section state in that tube satisfies the exact
  cancellation.

There is no small or coarse coefficient multiplying `D²v` after cancellation.
No new class, instance, notation, axiom, opaque declaration, or placeholder is
introduced.

## Geometric boundary

These are fixed Euclidean-chart identities only.  They do not identify the
Hessian with harmonic-map tension, a pullback covariant Hessian, or any Ricci
flow PDE.  The next geometric layer must add the source and target Christoffel
terms in the same fixed chart and prove that the resulting trace is the actual
map tension.  Its lower part will contain constant, linear, and quadratic
first-jet arms.

As in `ConnAddVertInv.md`, the coordinate-tube radius is fixed-basepoint rather
than uniform over the manifold.  A global HMF Nemytskii estimate still needs a
finite fixed-atlas jointly regular coefficient package and overlap
compatibility.

## Verification

Focused checking is green with no local warning, and the named targeted export
build is green at **3802/3802**.  The fixed-chart Hessian split and cancellation
package is therefore 100% source-written and 100% Lean-verified.

The exact theorem `ricci_flow_forward_unique` remains theorem-level **0%**;
this is supporting full-state gauge calculus, not the harmonic-map heat-flow
existence theorem or the final gauge comparison.
