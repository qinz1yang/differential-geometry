# StepDAssembly.lean notes

## 2026-07-10: original-sequence maps checked; convergence alignment blocked

`tailMemberMaps` is focused-check green with no warnings or `sorry`.  It targets
the original pointed sequence at subsequence `n ↦ σ (j₀ + n)`, reuses the
direct-limit inclusion partial diffeomorphisms, and uses `tailCenter_map` to
prove the basepoint field.  `alignedMetric` uses
`MetricSpace.replaceTopology` so the realized proper metric has the stored
manifold topology definitionally available to the downstream manifold APIs.

The remaining D6 frontier is convergence, not maps or completeness.  The
checked `tailAmbientConv` is indexed by `chainAmbientSeq`, whereas
`tailMemberMaps` is indexed by the original sequence `X`.  Both use the same
partial diffeomorphisms and target metrics, but `MetricSourceData` and
`MetricTargetDomain` are indexed by the complete
`PointedRiemannianCGMaps` record.  Equality of the partial maps alone therefore
does not make `MetricTargetDomain Φ k` definitionally equal to
`tailBallOpen b j₀ k`.

Fresh route-error count reached 3/3:

1. Proving `chainAmbientSeq = X.subseq (fun n => σ (j₀ + n))` fails as a Lean
   route because equality of the dependent pointed-manifold records requires
   transporting topology, charted-space, and manifold fields, not only the
   now-checked center equality.
2. Direct maps are viable, but transporting `MetricCGConvergenceData` by
   equality of the two full maps records is ill-typed because the records are
   indexed by different pointed sequences.
3. Rebuilding convergence from an explicit partial-map equality reaches the
   same API boundary: target open subtypes and `MetricSourceData` remain indexed
   by the full maps record.  Continuing locally would require pervasive casts
   or a duplicate copy of the ambient convergence proof.

This is a missing congruence/generalization API, not a mathematical obstruction.
The next target is to generalize the ambient convergence constructor so it can
take an explicit `Φ : PointedRiemannianCGMaps X L subseq` together with the
fact that its partial maps are the lifted direct-limit inclusions, while
providing canonical source/target-domain identifications.  An alternative is a
basepoint-replacement API proving that metric convergence is invariant when
the sequence members keep the same carrier, smooth structure, and metric.

Honest accounting: the final D6 assembly theorem and
`MetricCompactnessInputs.metricCompactness` remain unstated/unproved, so both
are 0%.  Dedicated D6 machinery is about 40%; whole Step-D machinery remains
about 97%.  Route errors are 3/3 and the requested stop condition is met.

## 2026-07-10: D6 alignment and conditional assembly complete

The prior 3/3 stop was resolved without casts or a duplicate convergence proof.
`PointedRiemannianSeq.repoint` represents `chainAmbientSeq` as the relevant tail
of the original sequence with transported basepoints;
`PointedRiemannianCGConverges.unrepoint` removes that basepoint-only change using
`tailCenter_map`; and `PointedRiemannianCGConverges.ofSubseq` returns from the
tail sequence to `X` at `n ↦ σ (j₀ + n)`.  The checked consumer
`tailMemberConv` packages this chain.

`alignedProper` transports the realized metric's properness across
`MetricSpace.replaceTopology`, so the D6 direct-limit APIs see the stored
manifold topology definitionally while retaining the same distance and compact
closed balls.  `compactness_of_b1` then assembles the strict subsequence, common
limit, completeness, original-member maps, and convergence from
`StepB1RawInput`.  Focused verification passed with no warning or new `sorry`.
The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

A separate targeted object refresh, attempted only so a temporary downstream
axiom consumer could import the new module, crossed a five-minute dirty-
dependency performance threshold and was stopped.  Its interrupted upstream
cache was repaired by a narrow module refresh, after which the final focused
check passed again.  This was a build-cache performance issue, not a theorem or
elaboration failure; no temporary audit file remains.

Honest accounting: `compactness_of_b1` and the dedicated D6 consumer are 100%
proved; Step-D consumer machinery is 100%.  The working endpoint
`MetricCompactnessInputs.metricCompactness` remains 0% because its body is still
`sorry`, and the textbook Step-D theorem from endpoint inputs remains 0% until
the B/C lane constructs `StepB1RawInput`.  The next target is therefore the B1
producer in `B1_JOIN_HANDOFF.md`, not another D6 transport route.
