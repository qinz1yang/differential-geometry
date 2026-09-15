# Invariance of domain and Brouwer fixed points

## Source and license

This is a native adaptation of material from
[mccorvie/classification-of-surfaces](https://github.com/mccorvie/classification-of-surfaces)
at commit `e3c7230fe78d7b056a415d9ecae6f77887046b32` (Ryan McCorvie,
2026-08-28), licensed under Apache-2.0. The complete upstream license is
preserved without modification in
[`classification-of-surfaces-LICENSE`](classification-of-surfaces-LICENSE).

The source files are:

- [`ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`](https://github.com/mccorvie/classification-of-surfaces/blob/e3c7230fe78d7b056a415d9ecae6f77887046b32/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean).
- [`ClassificationOfSurfaces/Moise/Brouwer.lean`](https://github.com/mccorvie/classification-of-surfaces/blob/e3c7230fe78d7b056a415d9ecae6f77887046b32/ClassificationOfSurfaces/Moise/Brouwer.lean), the source of the fixed-point ray construction.

The invariance-of-domain proof was adapted upstream from Kai Lam's
[Mathlib PR #36770](https://github.com/leanprover-community/mathlib4/pull/36770),
commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7`. The chart-independence
development was adapted upstream from Steven Sivek's
[TopologicalManifolds](https://github.com/stevensivek/TopologicalManifolds),
commit `05f80330d5a41b05376ae90eb8aa32c0166721db`.

The analytical proof follows Terry Tao, "Brouwer's fixed point and invariance
of domain theorems, and Hilbert's fifth problem" (2011): Tietze extension,
Stone-Weierstrass approximation, and a measure-theoretic perturbation argument.

## Preserved source notices

The following notices reproduce the original source headers verbatim. The
native Lean files contain no comments or docstrings, as required by the
project's instructions for this adaptation.

### `Topology/InvarianceOfDomain.lean`

```text
Copyright (c) 2025 Steven Sivek and 2026 Kai Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek, Kai Lam
```

### `Moise/Brouwer.lean`

```text
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
```

## Local modifications

### 2026-09-14: Native invariance-of-domain adaptation

The upstream `Topology/InvarianceOfDomain.lean` is modified and relocated to
`DifferentialGeometry/Topology/InvarianceOfDomain.lean`.

- Replace `LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain`
  with `DifferentialGeometry.Topology`.
- Remove source comments and docstrings while preserving the copyright,
  attribution, references, and license in this directory.
- Adapt declarations and proofs to this project's Lean 4.33.1 and Mathlib
  configuration, including explicit binders, current APIs, and the standard
  Mathlib linter requirements.
- Preserve the upstream analytical proof and its public declaration names.

This initial adaptation retains the explicit `BrouwerFixedPoint E`
assumption. Its invariance-of-domain results are conditional at this stage;
a standard-axiom audit alone does not discharge a class hypothesis appearing
in a theorem's statement.

The subsequent planned development uses this library's integral singular
homology of spheres and contractible spaces to prove the no-retraction
theorem in every positive finite dimension. It then generalizes the
upstream `Moise/Brouwer.lean` ray construction from the plane to arbitrary
finite-dimensional real inner-product spaces, supplies `BrouwerFixedPoint`,
and derives unconditional Euclidean and manifold endpoints. These later
steps are not certified by the initial conditional adaptation.

The upstream planar `Moise/NoRetraction.lean` is source material for review
only and is not included in the native adaptation.

### 2026-09-14: Homological no-retraction and Brouwer fixed points

`DifferentialGeometry/Topology/FixedPoint/NoRetraction.lean` is a native
proof in arbitrary positive finite dimension. In dimension one, a continuous
map from the contractible ball to the finite discrete sphere is constant,
contradicting the retraction identity on antipodal points. In higher
dimensions, the inclusion-induced homology map would have a left inverse
while the ball has zero positive-degree homology and the sphere's top
homology is isomorphic to the integers. The proof reuses
`integralSingularHomology_subsingleton_of_contractible` directly, without
introducing a reduced-homology conversion.

The upstream `Moise/Brouwer.lean` ray construction is modified and relocated
to `DifferentialGeometry/Topology/FixedPoint/Brouwer.lean`.

- Replace the planar model by an arbitrary universe-polymorphic real
  inner-product space in the ray scale, quadratic identity, sphere endpoint,
  continuity, and boundary identity proofs.
- Replace the planar no-retraction input by the native homological theorem.
- Handle dimension zero separately using the subsingleton vector space.
- Export `exists_fixedPoint_closedBall_of_continuous` and a proved
  `BrouwerFixedPoint E` instance for every finite-dimensional real
  inner-product space.
- Preserve the ray formula and algebraic proof; remove source comments and
  adapt the local instance syntax to the standard linter.

The no-retraction and fixed-point theorems have no unproved class hypotheses.
The analytical declarations in `InvarianceOfDomain.lean` retain their
abstract conditional signatures; importing `FixedPoint/Brouwer.lean`
supplies their fixed-point instance. Explicit Euclidean and manifold
endpoint declarations are the next development step.
