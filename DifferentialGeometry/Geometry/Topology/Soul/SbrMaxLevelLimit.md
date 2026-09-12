# SbrMaxLevelLimit.lean

Verified 2026-09-08 in the dev checkout. Compactness and distance antitonicity construct the actual maximum-level point and full left limit, then its continuous closed-interval extension with exact levels.

Empty focused output: 9.4s. Lint-clean named build: 10.6s.
Fresh external public axiom audit: 8.8s; all 2 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrMaxLevelLimit-result1.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

## Scope, claim, and verification state

Assigned to `soul_distance_field` by the bounded Ch8 terminal-level brief
in `SOUL_PLAN.md`, 2026-09-08. Claim
`276e4e8d-fa3d-4749-a42e-df0c8f13f0e6` was acquired through
`E:/testdifferential-geometry/scripts/lake-locked.ps1` from the dev checkout.
The claim is retained for the parent's verification and integration.

Source-ready only: two public declarations, no private helper or new
definition. The parent owns all compiler operations. This worker ran no
Lean, Lake, REPL, check, build, refresh, or axiom audit, and made no root
registration, shared status/plan edit, earlier-leaf edit, or commit. No
compiler feedback exists for this leaf yet.

Static freeze: source Git blob `0397ec98bec3d556bbaf287f39ad7d74b5a69ce3`;
all four Mathlib import paths exist; no forbidden tokens or trailing
whitespace. Static checks do not establish Lean verification.

Book source: `master05a.tex:7895-7926`, `thm:sbr-maximal-flow`, specifically
the compact subsequence and distance-monotonicity argument for the endpoint
at the maximum level. The preceding gluing of finite-time trajectories and
the final trajectory-uniqueness claim are separate inputs/steps.

## Exact public API

Both declarations are in `DifferentialGeometry.Geometry.Topology`. Their
only ambient structure is `[MetricSpace M]`; no manifold, completeness,
proper-space, gradient, or derivative assumptions occur.

`exists_level_left_limit_of_dist_antitone` takes:

```lean
{C : Set M} (hC : IsCompact C)
(F : M → ℝ) (hF : ContinuousOn F C)
(eta : ℝ → M) {a m : ℝ} (ham : a < m)
(hetaC : ∀ s ∈ Ico a m, eta s ∈ C)
(hlevel : ∀ s ∈ Ico a m, F (eta s) = s)
(hdist : ∀ q ∈ C, F q = m →
  AntitoneOn (fun s => dist (eta s) q) (Ico a m))
```

It constructs

```lean
∃ q ∈ C, F q = m ∧ Tendsto eta (𝓝[<] m) (𝓝 q)
```

There is no assumed point of level `m`, assumed convergent subsequence,
Cauchy condition, or full-limit hypothesis. The first theorem does not
require continuity of `eta`; compactness, exact levels, and the specified
distance monotonicity suffice. Continuity of `F` is only needed on `C`.

`exists_continuous_level_extension_of_dist_antitone` has the same inputs
and additionally `ContinuousOn eta (Ico a m)`. It constructs a point `q`
in `C` with `F q = m` and retains the explicit extension

```lean
etaBar := Function.update eta m q
```

with all of:

- `ContinuousOn etaBar (Icc a m)`.
- `EqOn etaBar eta (Ico a m)`.
- `etaBar m = q`.
- For every `s ∈ Icc a m`, `etaBar s ∈ C` and `F (etaBar s) = s`.

Thus the extension includes the original initial value and the exact
terminal level, and uses the same actual compact set. It is an actual
function on the ambient real line, restricted by the displayed interval
properties, rather than an unspecified extension interface.

The bounded tail argument itself does not need the inequality `F ≤ m` on
all of `C`; it produces a point of the terminal level `m`. In the book's
application `m` is already the actual maximum, so that point lies in the
maximum set. No unsupported claim that `m` is a maximum is inserted into
the more general metric statement.

## Native construction and whole-tail control

`exists_seq_strictMono_tendsto' ham` constructs real times in `Ioo a m`
tending to `m`. Applying `IsCompact.tendsto_subseq` to their actual curve
values produces `q ∈ C`, a strictly increasing index subsequence, and
convergence to `q`. The subsequence remains in `C`, so `ContinuousOn F C`
can be applied using `tendsto_nhdsWithin_iff`. Exact calibration identifies
the scalar image sequence with the corresponding time sequence. Uniqueness
of real limits proves `F q = m`.

For each positive `eps`, the convergent subsequence supplies an actual
sample time with `dist (eta time) q < eps`. For every later time below
`m`, the distance monotonicity for this now-produced level point gives the
same strict bound. `Ioo_mem_nhdsLT` places that whole tail in the left
neighborhood filter, and `Metric.tendsto_nhds` gives the full left limit.
No subsequence-selection or distance-to-the-limit premise is assumed.

For the extension, `continuousOn_update_iff` reduces continuity to the
original curve on `Icc a m \ {m} = Ico a m` and the proved left limit.
`Function.update_self` and `Function.update_of_ne` retain the endpoint
and original values. The closed-interval containment and level identities
follow by splitting `s = m` from `s < m`.

The actual declarations in Mathlib's `Topology/Order/IsLUB`,
`Topology/Sequences`, `Topology/MetricSpace/Pseudo/Defs`,
`Topology/Separation/Basic`, and `Logic/Function/Basic` were inspected before
implementation. In this version the update API is `update_self`, and
`update_of_ne` takes the new value before the original function. All four
imports are Mathlib sources; this leaf has no pending Soul proof dependency.

## Verification and remaining scope

The parent can check this independent metric leaf without waiting for the
new generalized-gradient or Euler-limit artifacts, then perform its named
refresh and fresh audit of the two public declarations. Static review has
found no mathematical gap in this bounded argument; elaboration and lint
feedback remain pending.

The actual maximal-flow application must still supply the already
constructed curve on `[a,m)`, its continuity, compact containment, exact
levels, and distance monotonicity to every point of the maximum set. The
curve's existence and agreement of its finite-time pieces are not derived
here. This leaf also does not assert trajectory uniqueness, a coherent flow,
a Sharafutdinov map, or level-map surjectivity.
