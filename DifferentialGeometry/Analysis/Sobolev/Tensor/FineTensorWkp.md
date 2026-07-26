# FineTensorWkp

## Source facts awaiting focused verification

`FineTensorWkp.lean` packages the already proved explicit algebra, quotient
norm, and sequence completeness of `WkpTensorQuot` as theorem-valued Banach
structures.  It registers no global or scoped instances.

- `tensorQAddGroup` uses exactly `qzero`, `qadd`, `qneg`, and `qsub`.
- `tensorQNormedGroup` uses `wkpTensorQNorm.toReal` and the proved quotient
  triangle, homogeneity, finiteness, and separation laws.
- `tensorQNormedSpace` uses exactly the explicit real action `qsmul`.
- `tensorQComplete` derives metric completeness from `qdist_limit`; Banach
  completeness is not supplied as an assumption.

The auxiliary scalar-action laws are proved by quotient induction.  A
consumer installs the structure values locally with `letI`; when the proof
scope ends, there is no effect on global typeclass search.

The file also defines the actual local parametrix carrier:

- `FullWkpQ` is the separated scalar Sobolev quotient on the whole Euclidean
  model, appropriate after strict-cutoff zero extension;
- `FineWkpArray` is the atlas/component Pi product;
- `fineWkpGroup`, `fineWkpSpace`, and `fineWkpComplete` derive its Banach
  structures solely from `IteratedSobolevQuot` and Mathlib's Pi constructions.

The first concrete extraction layer is now source-complete as well:

- `fineLocComp` is the canonical POU tensor component multiplied by one
  additional smooth fine-atlas weight and extended by zero off its chart;
- `fineLoc_joint` proves target-domain `W^{k,p}` membership and a norm bound by
  one fixed constant times the genuine tensor norm;
- `fineLoc_mem_univ` and `fineLoc_norm_univ` promote the block to the full
  Euclidean carrier with no zero-extension norm loss;
- `fineLoc_ae` proves that tensor a.e. equality descends through localization;
- `fineLocMap` is therefore a well-defined quotient-level extraction block,
  with explicit additivity, homogeneity, and quotient-norm bounds;
- `fineExtractMap`, `fineExtract_add`, and `fineExtract_smul` assemble all
  blocks into the actual finite atlas/component array map.

The important design choice is that fine localization refines each canonical
POU component instead of localizing a bare chart component.  Consequently its
Sobolev bound uses the existing canonical component norm directly, while a
sum over the fine weights first reconstructs that canonical component and the
outer canonical sum reconstructs the genuine tensor.

## Parametrix role

This closes the source-level carrier gap for continuous linear maps and the
Neumann inverse on the genuine tensor `W^{3,p}` quotient and supplies the
actual finite extraction function.  The next producer packages its finitely
many block estimates as one continuous linear map, followed by bounded
reassembly and the exact `RF ∘ E = id` identity.

## Verification state

The source contains no placeholder and `git diff --check` passes.  It has not
yet received a focused Lean check because the parent thread is serializing the
shared Lean lane.  Thus none of the declarations above counts as verified yet;
the endpoint `ricci_flow_unif_existence` remains 0%.  Focused checking remains
mandatory as soon as the lane is handed over, and any elaboration repairs must
preserve the theorem-valued, non-registered design above.
