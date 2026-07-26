# LieCorr0Split

## Proved design encoded in the source

The zeroth-order DeTurck correction is packaged as four public smooth fields:
the insertion, vector--bilinear, mixed connection-difference, and fixed
curvature pieces.  The intended public equalities are:

- `lc0_decomp`, the exact four-piece realization of `lieCorr0Field`;
- `nEndo_base`, identifying the base insertion endomorphism with the negative
  DeTurck `W` endomorphism;
- `insert_base`, cancelling the base-background endomorphism arm and leaving
  a difference of insertion fields;
- `tail_base_split`, the resulting cancellation-preserving normal form.

This is the mathematically essential split: estimating `lieCorr0` and the
base `DLb` arm separately would reintroduce a highest-derivative term that is
not small at `H3` regularity.

## Verification

2026-07-25: **GREEN** — `lake build +LieCorr0Split` succeeds sorry-free (22s)
after the TensorRS TotalSpace topology dedup (Edits A/B/C in
`RSTensor/Defs.lean` + `…/TensorRSContRiemannianBundle.lean`) PLUS a mechanical
elaboration-config fix in this file: `set_option
backward.isDefEq.respectTransparency false` added after `noncomputable section`.
Rationale: the `SmoothCcTensor g 2 2` sections here elaborate `Cₛ^∞⟮…⟯` =
`ContMDiffSection`, whose instance stack needs `NormedSpace (TensorRSModel 2 2 ℝ
E)`; that model-fibre normed instance only synthesizes under reduced def-eq
transparency (the same option `Tensor/RSTensor/Defs.lean` uses at line 50).
Without the option the four `SmoothCcTensor` fields fail with `failed to
synthesize FiberBundle …`. Elaboration-config only — no statement/proof change.

Endpoint theorem progress remains 0%; this file is producer machinery only.
