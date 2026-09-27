# The Jordan–Schönflies theorem in Lean

A Lean 4 / Mathlib formalization of the Jordan–Schönflies theorem:
every homeomorphism between two Jordan curves in the plane extends to a
homeomorphism of the whole plane.

The development proves the Jordan curve theorem along the way; it does not take
plane separation for Jordan curves as an assumption. The completed formalization
contains no `sorry`, `admit`, or `native_decide`.

## Main theorem

```lean
theorem Schoenflies.jordan_schoenflies_of_homeomorph
    {C C' : Set Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z
```

In words: a homeomorphism `e` between any two Jordan curves `C` and `C'`
extends pointwise to a self-homeomorphism `F` of the plane. An unbundled version
is available as `Schoenflies.jordan_schoenflies`.

The final assembly is in
[`Schoenflies/JordanSchoenflies.lean`](Schoenflies/JordanSchoenflies.lean).

## Proof at a glance

The proof follows the constructive cellulation argument developed in the
[companion blueprint](https://github.com/alonamaloh/jordan-schoenflies):

1. Establish the Jordan curve theorem and the general crosscut theorem.
2. Build matched cellulations on the source and target Jordan domains.
3. Repeatedly subdivide them while controlling the mesh on both sides.
4. Take the limiting interior homeomorphism and prove continuity at a dense
   family of retained boundary anchors.
5. Extend across the boundary, then use inversion to assemble a global
   homeomorphism of the plane.

Some useful entry points are:

| Topic | Modules |
|---|---|
| Jordan curve and crosscut theorems | [`JordanClosed.lean`](Schoenflies/JordanClosed.lean), [`GeneralCrosscut.lean`](Schoenflies/GeneralCrosscut.lean) |
| Matched cellulations and subdivision | [`FiniteTransfer.lean`](Schoenflies/FiniteTransfer.lean), [`CommonSubdivision.lean`](Schoenflies/CommonSubdivision.lean) |
| Shrinking stage recursion | [`QuantitativeRecursion.lean`](Schoenflies/QuantitativeRecursion.lean), [`StageTower.lean`](Schoenflies/StageTower.lean) |
| Boundary anchors and continuity | [`BoundaryAnchors.lean`](Schoenflies/BoundaryAnchors.lean), [`BoundaryContinuity2.lean`](Schoenflies/BoundaryContinuity2.lean) |
| Global extension | [`Endgame.lean`](Schoenflies/Endgame.lean), [`JordanSchoenflies.lean`](Schoenflies/JordanSchoenflies.lean) |

For a statement-by-statement correspondence with the blueprint, see the
[`ROADMAP`](docs/ROADMAP.md). The generated [`INVENTORY`](docs/INVENTORY.md)
lists every declaration and its source module.

## Building and checking

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/alonamaloh/schoenflies-lean.git
cd schoenflies-lean
lake build Schoenflies
```

The repository pins Lean and Mathlib through [`lean-toolchain`](lean-toolchain)
and [`lake-manifest.json`](lake-manifest.json).

Two additional checks keep the development honest:

```sh
python3 docs/regen-inventory.py
python3 docs/audit-axioms.py
```

The first regenerates the declaration inventory and rejects duplicate names.
The second checks every declaration for unresolved proof obligations and
unexpected axioms. The completed development depends only on the standard
axioms accepted by Mathlib: `propext`, `Classical.choice`, and `Quot.sound`.

The repository also provides a trusted statement and configuration for
[`leanprover/comparator`](https://github.com/leanprover/comparator). See the
[`Comparator` documentation](Comparator/README.md) for its scope and Linux setup. Project
provenance, automation, fidelity, and review status are recorded in
[`formalization.yaml`](formalization.yaml).

## Documentation

- [`docs/ROADMAP.md`](docs/ROADMAP.md) — status and Lean location of each
  labelled statement in the blueprint.
- [`docs/INVENTORY.md`](docs/INVENTORY.md) — generated declaration inventory.
- [Companion blueprint](https://github.com/alonamaloh/jordan-schoenflies) — the
  prose proof, citation index, and suggested module order.

## License

[Apache 2.0](LICENSE), matching Mathlib and the Lean ecosystem. The companion
blueprint is licensed under CC BY 4.0.
