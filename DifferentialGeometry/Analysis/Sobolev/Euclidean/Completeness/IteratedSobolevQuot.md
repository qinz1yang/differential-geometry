# IteratedSobolevQuot

## Purpose

The local heat parametrix needs a concrete separated Banach carrier for a
scalar Euclidean `W^{k,p}` space.  The pre-existing theory proved completeness
of `MemWkp` sequences but deliberately did not bundle that space.  This file
fills exactly that carrier-level gap.

## Source facts

- `EuclidWkp` is the `MemWkp` submodule on one fixed open domain.
- `EuclidWkpQ` quotients it by a.e. equality on that domain.
- `ewkpAddGroup`, `ewkpNormedGroup`, and `ewkpNormedSpace` are theorem-valued
  structures built from the explicit quotient operations and `wkpNorm`.
- Norm-zero separation is proved through the order-zero `eLpNorm` arm; no
  pointwise representative equality is assumed.
- `ewkpComplete` applies
  `MemWkp.exists_limit_of_wkpNorm_cauchy` to chosen representatives and then
  descends the limit to the quotient.

No global or scoped instance, class, or notation is introduced.  Finite chart
arrays will use this carrier through local `letI` declarations only.

## Verification state

The source has no placeholder.  The shared Lean lane remained reserved by the
parent task, so this file has not yet received its mandatory focused check.
Static line-count, forbidden-token, and diff checks are recorded separately;
any later elaboration repair must keep the zero-registration design and the
direct completeness proof above.
