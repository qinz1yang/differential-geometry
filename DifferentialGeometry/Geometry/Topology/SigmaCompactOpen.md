# SigmaCompactOpen.lean — note

## What this file provides

`DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen`: every open subset of
a σ-compact charted space over a finite-dimensional `ModelWithCorners ℝ E H` is
σ-compact (`IsSigmaCompact U`).  Weakest working hypotheses: no `T2Space M`, no
`IsManifold`, no `I.Boundaryless`, no `CompleteSpace E` — only
`[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`,
`(I : ModelWithCorners ℝ E H)` (explicit: not inferable from `M`),
`[ChartedSpace H M] [SigmaCompactSpace M]`.

Role: producer for the σ-compactness inputs of the flow-limit upgrade —
`FlowLimitData.hσsrc`/`hσtgt` (`HCGCompactness/FlowLimitUpgrade.lean`) and the
`hσsrc`/`hσtgt` arguments of `SourceDomainMetricData.ofRestrictPullback`
(`HCGCompactness/PointedConvergence.lean`), via `PointedCGHMaps.source_open` /
`target_open`.

## Route (all reused from Mathlib, nothing reproved)

1. `ModelWithCorners.locallyCompactSpace` + `ModelWithCorners.secondCountableTopology`
   (`Mathlib.Geometry.Manifold.IsManifold.Basic`): `E → H` transport.  The `E`-side
   instances are automatic: `FiniteDimensional.proper_real` → `ProperSpace E` →
   `secondCountable_of_proper` and local compactness.
2. `ChartedSpace.locallyCompactSpace H M` and
   `ChartedSpace.secondCountable_of_sigmaCompact H M`
   (`Mathlib.Geometry.Manifold.ChartedSpace`; both take `H M` explicit).
3. `IsOpen.locallyCompactSpace` (`Mathlib.Topology.Compactness.LocallyCompact`) —
   needs NO separation axiom (goes through locally-closed subsets).
   `SecondCountableTopology ↥U` is the automatic subtype instance.
4. Instance `sigmaCompactSpace_of_locallyCompact_secondCountable` +
   `isSigmaCompact_iff_sigmaCompactSpace.mpr`
   (`Mathlib.Topology.Compactness.SigmaCompact`).

## Verification (2026-07-02)

- Focused check and targeted build: PASSED, no warnings.
- `#print axioms isSigmaCompact_of_isOpen` = `[propext, Classical.choice, Quot.sound]`
  (checked via targeted build with a temporary print line, then removed —
  `lake env lean` suppresses `#print` output).
- Applicability: a temporary example (deleted after checking) instantiated both
  consumer shapes successfully — under
  `letI : TopologicalSpace L.M := L.topology` (+ `letI` for `L.charted`,
  `L.sigmaCompact`), `Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)`
  closes `IsSigmaCompact (Φ.source k)`, and the analogous call with
  `Φ.target_open k` under the `(X.term (subseq k))` instances closes the
  target-side goal.  No instance mismatch; no variant statement needed.
- Registered in the umbrella `DifferentialGeometry.lean`.

## Consumer recipe (for the FlowLimitData wiring)

```
letI : TopologicalSpace L.M := L.topology
letI : ChartedSpace H L.M := L.charted
letI : SigmaCompactSpace L.M := L.sigmaCompact
exact Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
```
