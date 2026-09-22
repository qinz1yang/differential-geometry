# Planar disk union: relative boundary matching route

Date: 2026-09-22. Owner-supplied design advice against mirror `3b6b29fb`
(`3b6b29fb451c570f14c6335d30bcfbd23b327197`).

**Recorded for later work; NOT DISPATCHED, NOT FROZEN, proofs OPEN.** The owner requested
only decomposition and recording, without interrupting running processes. This note does
not change the active Gemini batch, its task order, file ownership or compiler leases.
The reviewer reports source inspection, but no Lean run or repository modification.
Lead source-level due diligence and independent compilation are deferred. The API claims
and proposed argument below are evidence to investigate, not accepted implementations.

Source attachment:
`C:\Users\liao9\.codex\attachments\924f99ad-6deb-4821-af9d-7a5339433052\Pasted text.txt`.
SHA256: `2678B65647553355AEC14BC35669BFFB67BF4FBF4C0A10EA5129F6E290422173`.
The separate worker report is recorded in the
[round-two intake](../Skeleton/GEMINI_PLANAR_UNION_ROUND2_INTAKE_20260922.md).
Its uncommitted source hashes must not be conflated with the reviewer's mirror snapshot.

## Target and change of suggested route

For `Plane := EuclideanSpace ℝ (Fin 2)`, the missing producer has exactly three disk
hypotheses: `A`, `B` and `A ∩ B` are homeomorphic to the closed unit disk. Its conclusion
is that `A ∪ B` is also homeomorphic to that disk. This permits non-PL disks and infinite
common boundary sets. It does not assume finite boundary intersections or a shared arc.

The reviewer changes the earlier suggestion to use nested-disk boundary matching, pasting
on two closed sets, and existing Schoenflies recognition. Full Janiszewski/continuum theory
and the stronger connected-nonpoint-intersection theorem are not proposed prerequisites.
The matching result itself is new mathematics to prove; making it an extra hypothesis of
the frozen endpoint would leave the producer missing.

## Suggested reusable source interfaces

These are the reviewer's source claims, pending lead verification against the source that
will actually be used for implementation:

| Module under `DifferentialGeometry/Topology/` | Claimed supply |
|---|---|
| `ClosedBallImage.lean` | Compactness, nonempty interior, open-ball interior image and sphere boundary image |
| `PlanarJordan/Crosscut.lean` | Topological crosscuts; `crosscut_regions` and `subset_crosscut_side_of_mem_closure` |
| `PlanarJordan/AmbientExtension.lean` | `isJordanCurve_range_of_isEmbedding_circle` |
| `PlanarJordan/CompactRegion.lean` | `interior_eq_inside_frontier_of_isCompact`, `closure_inside_frontier_eq_of_isCompact` |
| `PlanarJordan/ClosedInterior.lean` | A proved private plane version of closed-region recognition |

The last reported signature is:

```lean
private theorem closed_region_homeomorph_ball
    {U : Set Schoenflies.Plane}
    (hU : IsOpen U)
    (hconn : IsConnected U)
    (hbounded : Bornology.IsBounded U)
    (hC : Schoenflies.IsJordanCurve (frontier U)) :
    Nonempty (closure U ≃ₜ closedBall (0 : Schoenflies.Plane) 1)
```

Later, check its exact scope, proof, axiom closure, naming and existing public alternatives
before exposing a natural public interface in its original module. The reviewer suggests
avoiding an unnecessary conversion from the plane to `ℂ` and back. No export is made here.

## Deferred work packages

These labels are local planning references, not public declaration names or new batch IDs.
They do not reserve files or launch another pass. Packages 1 and 2 are mathematically
separable; package 3 consumes both, package 4 consumes 3, and package 5 consumes 4.

### 1. Order-preserving extension from closed interval subsets

Prove a reusable one-dimensional extension result with explicit order and endpoint
compatibility. A homeomorphism between arbitrary closed subsets is not sufficient.
On a complementary interval `(a,b)`, use the endpoint values to define

\[
\widetilde f(t)=f(a)+\frac{t-a}{b-a}(f(b)-f(a)).
\]

Prove agreement on the closed subset, strict monotonicity, surjectivity and the resulting
homeomorphism. Handle accumulation of complementary intervals using their endpoints,
for example `sSup`/`sInf`; do not assume a finite enumeration. Obtain a circle version by
cutting at a suitable marked point and identifying the endpoints again. Empty and singleton
common sets require explicit cases. Final weakest natural signatures remain to be designed
after checking existing order/topology APIs.

Deliverable: a proved extension theorem, including its behavior on the entire fixed subset.

### 2. Cyclic order of common boundaries of nested disks

For disk regions `C ⊆ D`, prove compatibility, up to the appropriate orientation choice,
of the cyclic orders on `frontier C ∩ frontier D`. An arc whose interior lies in
`interior C` also lies in `interior D`. The proposed contradiction takes two disjoint
inner-disk arcs whose four endpoints alternate on the outer boundary. Existing crosscut
separation and localization should rule this out.

Deliverable: the precise order compatibility required by package 1. Supplying only that
both boundaries are circles, or only pairwise distinct endpoints, does not establish it.
Constructing the proper crosscuts and justifying all endpoint conditions remain proof work.

### 3. Relative boundary matching for nested disks

Combine packages 1 and 2 to prove the proposed interface below. This is a design signature,
not an existing or frozen declaration:

```lean
theorem exists_frontier_homeomorph_fix_inter_of_subset
    {C D : Set Plane}
    (hC : Nonempty (C ≃ₜ Metric.closedBall (0 : Plane) 1))
    (hD : Nonempty (D ≃ₜ Metric.closedBall (0 : Plane) 1))
    (hCD : C ⊆ D) :
    ∃ e : frontier C ≃ₜ frontier D,
      ∀ x : frontier C,
        (x : Plane) ∈ frontier D →
          (e x : Plane) = (x : Plane)
```

The fixed set is every common boundary point. Retain equality and strict containment,
disjoint boundaries, a single common point and infinite common closed subsets. Ordinary
circle recognition alone does not provide a homeomorphism with this relative property.

### 4. Crossed pasting and exact frontier identification

Set `C=A∩B`, `S=frontier C`, `F_A=S∩frontier A`, `F_B=S∩frontier B`. The proposed proof
first establishes that `F_A` and `F_B` are closed in `S` and cover it. Use package 3 to
obtain `f:S≃ₜfrontier A` fixed on `F_A` and `g:S≃ₜfrontier B` fixed on `F_B`.
Define the ambient-valued map with crossed branches:

\[
\eta(x)=g(x)\quad(x\in F_A),\qquad
\eta(x)=f(x)\quad(x\in F_B).
\]

On the overlap both maps equal `x`, so pasting uses exactly two closed sets even when the
common boundary is infinite. Prove the preimage identities `f⁻¹(C)=F_A` and `g⁻¹(C)=F_B`
with subtype coercions made explicit. For a cross-branch collision `g(x)=f(y)`, the common
value lies in `C`; the identities put both arguments into the fixed sets and give `x=y`.

Define `U=interior A ∪ interior B`, then establish the exact image and closure formulas:

\[
\begin{aligned}
\eta(S)&=(\partial A\setminus B)\cup(\partial B\setminus A)
              \cup(\partial A\cap\partial B)\\
        &=(A\cup B)\setminus(\operatorname{Int}A\cup\operatorname{Int}B),\\
\overline U&=A\cup B,\qquad \eta(S)=\partial U.
\end{aligned}
\]

Do not assume `interior (A ∪ B) = interior A ∪ interior B` to start the argument.
Regular-closedness of the two disks supplies the closure equality. The two open interiors
are connected and meet in `interior C`, which is nonempty. Establish boundedness as well.

Deliverable: the continuous injective circle parametrization of this exact frontier,
together with the open, connected and bounded region certificate for this same `U`.

### 5. Disk recognition, frozen endpoint and later acceptance

Use the verified circle-embedding recognition and the public plane region interface to
prove the general disk-union theorem. Then consume `planarProjection_image_inter` for
`hc.overlap`, the existing cell transports in both directions, and
`IsTopologicalCellWithInterior.interior_mono` to prove the original Section 31 endpoint
without an additional `hdiskUnion` input. Its ambient space is three-dimensional; the
intrinsic-interior theorem avoids an invalid use of the ambient interior there.

The review identifies `PlanarDiskUnion.isPLBall_union_and_finite_frontier_inter` as an
unsuitable direct substitute: its disks are PL, with a one-dimensional intersection lying
in both boundaries. The present overlap is a two-dimensional topological disk.

At later acceptance, inspect actual statements and dependencies, recover fresh module
receipts, run the independent axiom/linter gate and compare the frozen endpoint bytes.
Only then perform imports, skeleton replacement and the sole ledger update in
`../FREE_INPUTS.md`. No such acceptance action accompanies this record.
