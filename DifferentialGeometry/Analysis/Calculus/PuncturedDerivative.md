# PuncturedDerivative

## Purpose

This file supplies the generic real-parameter removable-puncture lemma needed
when a curve equation is known on both sides of a finite subdivision node.

## Native route

Mathlib's `hasDerivAt_of_hasDerivAt_of_ne` has the desired conclusion but asks
for differentiability at every point other than the puncture.  The local API
here accepts the weaker, natural hypothesis of differentiability eventually in
the punctured neighborhood.  Its proof restricts that hypothesis to the left
and right filters, applies Mathlib's one-sided derivative extension theorems,
and unions the two resulting within-derivatives.

## Verification

Focused verification passed without warnings or placeholders.  The exported
module was refreshed for its downstream L-geometry consumer.
