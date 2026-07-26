# ComponentRestrict

## Scope

This file is the source-level consumer bridge needed to apply a connected-manifold
DeTurck/harmonic-map uniqueness argument componentwise while keeping the public
`ricci_flow_forward_unique` statement on an arbitrary compact manifold.

For an arbitrary anchor `p : M`, set
`U := Geometry.Riemannian.Exponential.connCompOpen (I := I) p`.  No
`ConnectedSpace M` instance is introduced.  The family

```text
compRestrict g p t = (g t).restrictOpen U
```

has the exact four raw fields used by the endpoint theorem:

1. `compRestrict_init`: initial equality;
2. `compRestrict_smooth`: joint chart-Gram `C∞` on `Ioo a b`;
3. `compRestrict_cont`: joint chart-Gram continuity on `Ico a b`;
4. `compRestrict_pde`: the coefficientwise Ricci-flow equation on `Ici a`.

The file now also contains the reverse assembly:

5. `eq_of_compRestrict`: equality of the restrictions on every anchored
   component implies equality of the ambient metrics;
6. `forward_of_comp`: feeds all four transported fields and the initial
   equality to a connected-case uniqueness producer, then reassembles the
   ambient endpoint pointwise.

## Chosen route

The faithful route is the raw chart pullback.  The spacetime map

```text
ρ : ℝ × U → ℝ × M,   ρ(t,u) = (t, ↑u)
```

is smooth.  The subtype chart source is the inverse image of the ambient chart
source, so it maps the restricted chart-Gram domain into the original one.  The
already proved identity `Geometry.Riemannian.Geodesic.chartGram_open` identifies
the two component functions there.  It existed with the exact needed proof but
was private; `Geometry/Geodesic/OpenSubtype.lean` now exports that theorem.

The PDE transport is independent of coordinates:
`SmoothRiemannianMetric.restrictOpen_inner` identifies the time-dependent scalar
coefficient, and `HCGCompactness.ricciTensor_restrictOpen` identifies the Ricci
tensor by germ-locality.

For reassembly, to compare the two ambient metrics at `x`,
`eq_of_compRestrict` chooses the component anchored at `x`, evaluates the
restricted metric equality at `connCompPt x`, and unfolds
`restrictOpen_inner`.  Structure extensionality then upgrades equality of all
fiberwise inner products to equality of the smooth metrics.  No countability
or enumeration of components is used.

`forward_of_comp` deliberately takes the connected uniqueness proof as a
higher-order consumer rather than adding connectedness to the public endpoint.
When filling that consumer for an anchor `p`, the caller can locally install

```text
letI : ConnectedSpace (connCompOpen p) := connCompConnected p
letI : CompactSpace (connCompOpen p) := connCompCompact p
```

and invoke the connected DeTurck/HMF theorem with the transported fields.

## Static direction/type audit

- `chartGram_open` is stated in the direction
  `restricted chart-Gram = ambient chart-Gram`.  Precomposition of the ambient
  hypothesis produces the ambient field, while the consumer target is the
  restricted field, so both regularity proofs deliberately use
  `(chartGram_open ...).symm` inside `.congr`.
- For an open subtype, `TangentSpace I u` and `TangentSpace I (u : M)` are the
  same model fiber `E` definitionally.  This is exactly the shared-slot
  convention already used in the checked statement of
  `ricciTensor_restrictOpen`; consequently `hpde ... (u : M) v w` needs no
  `tangentMap` or cast.  The later focused check should nevertheless catch any
  elaborator sensitivity caused by unfolding `compRestrict`'s local compact
  instance.

## Audited alternatives

Three mathematically distinct routes were checked.

1. **Raw chart pullback — selected.**  This preserves the endpoint hypotheses
   verbatim and needs only the existing open-subtype chart identity.
2. **Package as `SolutionOn`.**  `solutionOn_of_joint` currently asks for joint
   `C∞` on all of `Ico a b`, whereas the endpoint intentionally supplies only
   `C∞` on `Ioo a b` plus `C⁰` on `Ico a b`.  Using it at the closed initial edge
   would strengthen the theorem and is therefore inadmissible.  On compact
   interior subwindows it remains useful later.
3. **Intrinsic `MetricFamilySmoothOn`.**
   `metricFamilySmoothOn_of_chartGram` accepts the split regularity, and
   `metricFamilySmoothOn_restrictOpen` transports an already bundled solution.
   But the latter is stated through `IsSolutionOn`; round-tripping back to the
   endpoint's raw subtype chart-Gram fields would add a larger adapter layer
   while proving the same chart identity.  It is not the shortest consumer path.

## Verification state

Source implementation and static review only, including the componentwise
reassembly theorems.  Per the active shared-workspace
instruction, no Lean/Lake process was started in this lane.  A later owner must
run a focused check of `ComponentRestrict.lean` and its newly public dependency
`Geometry/Geodesic/OpenSubtype.lean` before treating these declarations as
verified.

Component-restriction machinery: **100% source-written, 0% newly Lean-verified**
in this lane.

The endpoint theorem `ricci_flow_forward_unique` remains **0% complete** until
its exact statement is proved and checked.  This bridge now removes the whole
disconnected-manifold layer in both directions: restriction of every raw
hypothesis and reassembly of the final equality.  Connected Ricci-DeTurck
uniqueness, harmonic-map heat-flow gauge construction, and gauge removal remain
separate analytic producers.
