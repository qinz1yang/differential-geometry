# GPT Pro consultation prompt: D6 convergence reindex API

> **Resolved on 2026-07-10.**  The implemented route is
> `PointedRiemannianSeq.repoint` →
> `PointedRiemannianCGConverges.unrepoint` →
> `PointedRiemannianCGConverges.ofSubseq`, consumed by `tailMemberConv`.
> Keep this file only as the historical statement of the former blocker; it is
> not the current consultation target.

You are consulting on the live Lean repository at
`E:\testdifferential-geometry`, **branch `short-time-existence`**.  Base every
claim on that branch's current files.  Do not answer from `main`, another
checkout, an old commit, or a remembered Mathlib API.  The branch matters:
`StepDLimitMetrics.lean` and the new `StepDAssembly.lean` contain declarations
that do not exist in older snapshots.

We are completing MSM135 Chapter 4 Step D6 for the conditional endpoint
`MetricCompactnessInputs.metricCompactness`.  Please review the smallest clean
Lean API needed to align a checked Cheeger--Gromov convergence result with the
original pointed sequence.  Do not propose new mathematical assumptions and do
not hide the issue behind a new `sorry`-backed wrapper.

## Checked live state

- `C4/StepDLimitMetrics.lean`:
  - `tailLimitComplete` proves completeness of the shrunk-tail direct-limit
    metric.
  - `tailFlatSup_lt` proves compact-supremum metric convergence on the same
    shrunk stages.
  - `tailAmbientConv` proves ambient-target convergence, but its source sequence
    is `chainAmbientSeq`, whose member basepoint is the stage-zero center
    transported through the system.
  - `tailCenter_map` proves that transported center equals the stored stage
    center at every stage.
- `C4/StepDAssembly.lean`:
  - `tailMemberMaps` is checked and directly targets the original sequence `X`
    at subsequence `n ↦ σ (j₀ + n)`.
  - It uses the same lifted inclusion partial diffeomorphisms and
    `tailCenter_map` for its basepoint field.

## Exact formal blocker

The convergence data is indexed by the entire maps record:

```lean
MetricSourceData (Φ : PointedRiemannianCGMaps X L subseq) k
MetricTargetDomain Φ k
MetricCGConvergenceData Φ
```

The checked convergence uses

```lean
Φ₀ : PointedRiemannianCGMaps
  (chainAmbientSeq ...) L id
```

while the endpoint needs

```lean
Φ : PointedRiemannianCGMaps X L (fun n => σ (j₀ + n))
```

Their `partialDiffeomorph k` fields are the same lifted direct-limit inclusion,
and the target carrier/smooth metric at stage `k` is the same original member.
However, equality of the full maps records is ill-typed because their sequence
indices differ.  Re-running `PointedRiemannianCGConverges.ofRestrictPullback`
with a hypothesis

```lean
∀ k, Φ.partialDiffeomorph k =
  PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl
```

still leaves `MetricTargetDomain Φ k` non-definitional with
`tailBallOpen b j₀ k`; the target metric and pullback proof then require casts.

## Routes already rejected

1. Literal equality `chainAmbientSeq = X.subseq ...`: dependent topology and
   `ChartedSpace` record transport dominates the proof.
2. Equality/proof-irrelevance of the two full maps records: ill-typed across
   different sequence indices.
3. Locally duplicating the 200+ line ambient convergence proof with only a
   partial-map equality: it reaches the same target-domain casts and creates a
   parallel fragile proof.

## Consultation questions

1. What is the smallest Mathlib-style API that makes convergence insensitive
   to this basepoint-only change of the pointed source sequence?
2. Should we generalize `ambientCGConverges` to accept explicit maps and provide
   canonical equalities/equivalences for `metricSourceOpen` and
   `metricTargetOpen`, or add a `MetricCGConvergenceData` congruence theorem?
3. Please give a concrete Lean theorem statement and proof skeleton that avoids
   `HEq` proliferation, quotient/record equality, and a duplicate convergence
   proof.
4. Identify any existing Lean/Mathlib theorem names that should be checked on
   this pinned branch before implementing the API.

Acceptance criterion: the proposed API must let `tailFlatSup_lt` construct
`PointedRiemannianCGConverges X L (fun n => σ (j₀ + n)) tailMemberMaps`, with
the same `L` consumed by `tailLimitComplete`, and without additional geometric
hypotheses.
