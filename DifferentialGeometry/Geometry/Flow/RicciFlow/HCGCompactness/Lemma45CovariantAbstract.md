# Lemma45CovariantAbstract.lean notes

## Current status

This file currently pins down the checked RicciFlower names for the covariant
`(0,s)` route to MSM135 Lemma 4.5.  It intentionally does not add a fake
abstract theorem whose proof would only restate the missing tensor-calculus
frontier.

Checked ingredients now available:

- constants and scalar algebra from `Lemma45Constants.lean` and
  `SumLemmas.lean`;
- scalar induction skeleton `lemma45Scalar`, which proves the full recursive
  Lemma 4.5 estimate from the book's lift step and one-step estimates;
- first-order `(0,s)` connection-change identity:
  `Tensor0SBundle.nabla0SFun_sub_cov`;
- mixed component first-order identity:
  `Tensor0SBundle.componentRS_nablaRSFun_sub`;
- checked action-form bridge:
  `Tensor0SBundle.componentRS_nablaRSFun_sub_connAct`;
- component action bound:
  `Tensor0SBundle.abs_connActTensor_le`;
- epsilon/factored component action corollaries in
  `ConnectionDifferenceAction.lean`.

The next real producer is an iterated covariant product/Leibniz theorem for
repeated `H`-derivatives of the connection-difference action.  Searches found
product smoothness and product norm splitting, but not this iterated derivative
estimate as an existing checked API.  Verification passed for the current
boundary file.

## 2026-06-02 scalar induction

Added `lemma45Scalar`.  It is geometry-free but no longer merely a constants
lemma: it formalizes the induction skeleton of MSM135 Lemma 4.5.  The theorem
assumes:

- `hLift`, the result of applying the lower-order estimate to `nabla_g T`;
- `hOne`, the one-step estimate for `H^k (nabla_g T)`.

It then proves the recursive `lemma45Const` bound for every `0 < r <= p`.
Verification passed.

The remaining tensor frontier is narrower: prove `hOne` from the first-order
connection-change identity plus an iterated `H`-Leibniz/product estimate for
the connection-difference action.

## 2026-06-02 action-form bridge

Added the tensor-layer file `ConnectionDifferenceActionIdentity.lean` and
imported it here.  The theorem `componentRS_nablaRSFun_sub_connAct` rewrites
the existing first-order mixed component identity directly as `connActComp`.

This makes the `k = 0` component identity checked in the same language as the
action estimates.  The remaining frontier is now the norm packaging and
iterated `H`-Leibniz/product estimate, not the first-order component formula.

## 2026-06-02 first-order norm producers

The first-order norm packaging has moved below HCG into
`ConnectionDifferenceActionIdentity.lean`.  The checked theorem
`Tensor0SBundle.totalNablaNorm_le` now gives the total first-order one-step
inequality from supplied total-nabla realizations, local basis/vector-field
data, and the connection-difference tensor norm.

The remaining Lemma 4.5 frontier is therefore narrower than before: prove the
iterated `H`-Leibniz/product estimate for the connection-difference action and
feed it into `lemma45Anti`.

## 2026-06-02 epsilon first-order producer

The tensor layer now supplies
`Tensor0SBundle.totalNablaNorm_bound`, which packages the first-order
connection-change estimate in the epsilon form needed for the `k = 0`
one-step bound.  This uses `connActNormConst` to keep the component-count
constant explicit.

The HCG abstract file intentionally does not add a theorem that simply repeats
the very large tensor-layer signature.  The next mathematical step is still to
prove the higher antidiagonal product-rule realization for repeated
`H`-derivatives of the connection-difference action, then feed that result
into `lemma45Anti`.  Searches found product norm lemmas and first-order
realization bridges, but not this iterated realization theorem.

## 2026-06-02 antidiagonal norm packaging

`ConnectionDifferenceAction.lean` now also supplies
`Tensor0SBundle.norm_connActAnti_bound_step`.  This is the scalar-facing
antidiagonal estimate: after a future realization theorem identifies the
components of an iterated action derivative with the antidiagonal Leibniz sum,
the theorem bounds its norm by
`eps * connActAntiStepConst ... B * S`, where `S` is a common bound for the
relevant tensor derivative norms.

Thus the remaining gap has moved again: not norm comparison, component sums, or
constant extraction, but the actual product-rule realization that produces the
antidiagonal components.

## 2026-06-02 mixed total-nabla linearity

`HigherOrder.lean` now supplies mixed total-derivative linearity:

- `Tensor0SBundle.nablaRSFun_add`, `.smul`, `.zero`, `.sum`;
- `Tensor0SBundle.TotalNablaRSRealizes.add`, `.smul`, `.zero`, `.sum`.

These are checked producer lemmas for future antidiagonal product-rule
assembly.  They do not prove the iterated product rule itself.  A generic
`HigherCovDerivRSRealizes.one` wrapper was attempted and intentionally not kept
because the inductive predicate uses `1 + s` while total-nabla uses `s + 1`;
that cast-normalization issue is separate from the total-realization linearity
now proved.

## 2026-06-02 covariant product-rule producers

`HigherOrder.lean` now also supplies covariant-field product and finite-sum
realization support:

- `Tensor0SBundle.nabla0SFun_product_eval_smooth_slots`;
- `Tensor0SBundle.TotalNabla0SRealizes.product_of_apply`;
- `Tensor0SBundle.nabla0SFun_zero`;
- `Tensor0SBundle.nabla0SFun_sum`;
- `Tensor0SBundle.TotalNabla0SRealizes.zero`;
- `Tensor0SBundle.TotalNabla0SRealizes.sum`.

This is real progress toward the Lemma 4.5 hidden "sum of products" step. The
remaining frontier is no longer linearity or finite-sum packaging; it is the
iterated antidiagonal product-rule realization for repeated `H`-derivatives of
the connection-difference action, including the required slot-normalized
product fields.

## 2026-06-02 constructed product derivative

`HigherOrder.lean` now constructs the actual one-step Leibniz product
derivative field and proves `Tensor0SBundle.TotalNabla0SRealizes.product`.
This is stronger than the previous supplied-field wrapper
`product_of_apply`: the derivative of `α ⊗ β` is now a concrete sum of the
left and right Leibniz product fields with checked slot permutations.

This moves Lemma 4.5 closer to the printed "sum of products" argument.  The
remaining gap is the all-order action-specific antidiagonal realization, not
the generic tensor product derivative.

## 2026-06-02 covariant-to-mixed zero-upper-slot bridge

The tensor layer now supplies the zero-upper-slot bridge needed to let the
covariant-first Lemma 4.5 route reuse mixed-tensor action estimates:

- `Tensor0SBundle.nablaRSFun_toRS0`;
- `Tensor0SBundle.TotalNabla0SRealizes.toRS0`;
- `Tensor0SBundle.IterNabla0SRealizes.toRS0`;
- `Tensor0SBundle.IterNabla0SJet.toRS0`.

This checked path is meaningful because it avoids creating a parallel
covariant-only action API.  A cast-heavy attempt through the older
`HigherCovDeriv0SRealizes` predicate was not kept; the normalized
`IterNabla0SRealizes` predicate is the correct route.  Verification passed for
the immediate HCG abstract consumer.

## 2026-06-02 valence normalization blocker

A direct attempt to unpack a first covariant higher-derivative witness
`HigherCovDeriv0SRealizes ... 1 alpha1` into `TotalNabla0SRealizes` was not
kept.  The obstruction is the same one already seen in the mixed case: the
recursive higher-derivative predicate stores zero and successor cases behind
valence casts such as `0 + s`, while the total derivative predicate is stated
at the normalized valence `s`.

This means the next useful producer is not another HCG-facing Lemma 4.5 wrapper
and not another finite-sum lemma.  The next smallest tensor API should be a
congruence/transport theorem for `nabla0SFun` or `TotalNabla0SRealizes` across
equal tensor valences.  Once that exists, the first-derivative unpackers and
then the antidiagonal product realization can be stated without fragile casts.

## 2026-06-02 transport helper progress

`HigherOrder.lean` now has checked `TotalNabla0SRealizes.congr` and
`TotalNabla0SRealizes.cast`.  These solve the ordinary problem of transporting
a total-nabla realization across equal valences.

The attempted `HigherCovDeriv0SRealizes.one` still failed and was not kept.
The remaining issue is more specific than ordinary realization transport:
the recursive higher-derivative constructors introduce nested casts around
the zero-stage tensor field and the successor field.  The next useful tensor
producer is a cast-cancellation lemma for those constructor-generated terms,
or a normalized higher-derivative realization API.  The HCG scalar induction
and product/norm infrastructure should wait for that tensor-layer bridge.

## 2026-06-02 normalized tensor realization route

`HigherOrder.lean` now provides a checked normalized route instead of trying to
repair the old `HigherCovDeriv*Realizes` casts:

- `Tensor0SBundle.IterNabla0SRealizes`;
- `Tensor0SBundle.IterNablaRSRealizes`;
- first-derivative and successor elimination lemmas for both;
- `Tensor0SBundle.IterNabla0SRealizes.product_one`.

This is real progress for Lemma 4.5: the covariant and mixed derivative towers
can now be expressed with valence `s + k`, so the future antidiagonal product
rule does not need to normalize `0 + s` constructor casts at every step.

The remaining frontier is still the full iterated Leibniz/product realization
for the connection-difference action.  The next likely tensor-layer helper is
compatibility of `TotalNabla0SRealizes` with slot permutations, because second
and higher derivatives of normalized product terms differentiate already
permuted product fields.
