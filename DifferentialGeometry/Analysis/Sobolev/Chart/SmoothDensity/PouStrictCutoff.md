# PouStrictCutoff

## Producer

`exists_pou_cutoff` is the metric- and chart-independent outer half of the
two-cutoff localization needed by the uniform Ricci--DeTurck parametrix.

Given a smooth partition of unity subordinate to inner sets `U i` and open
outer sets `V i` with `U i ⊆ V i`, it produces one smooth `[0,1]`-valued
function per index which

- equals one on a neighborhood of the partition function's topological
  support;
- vanishes on a neighborhood of `(V i)ᶜ`;
- has topological support contained in `V i`.

The proof is the same smooth Urysohn separation used by the canonical chart
strict cutoff, now factored over an arbitrary subordinate smooth partition.

`exists_strict_cutoff` is the single-function form used to add one more
collar.  Given `tsupport f ⊆ V` with `V` open, it produces a smooth
`[0,1]`-valued cutoff equal to one near `tsupport f`, zero near `Vᶜ`, and
supported in `V`.  This extra collar permits global extension of transition
coefficients while remaining exactly one on the preceding localization.

## Verification

Focused Lean verification passes without warnings. The producer assumes the
existing `NormalSpace M` condition required by Mathlib's smooth Urysohn
theorem; closed Hausdorff manifolds used by the Ricci-flow lane supply it.
This file contains no `sorry`, `admit`, axiom, opaque declaration, or
replacement hypothesis.

Endpoint completion remains 0%; this is localization machinery only.
