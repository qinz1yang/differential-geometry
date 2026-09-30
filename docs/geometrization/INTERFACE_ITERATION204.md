# Revision 204: actual observed-history endpoint descent

This bounded increment connects conditional endpoint assembly to the actual PC
event carriers, observed histories and original initial marking. It implements
consumer proofs. It does **not** produce the missing oriented event refinement,
exceptional endpoint certificates, late geometry, protected ports or common
global profile. The general geometrization theorem remains open.

## Concrete interfaces and compiling uses

`Topology/Reconstruction/EndpointDescent.lean` defines `ComponentsGeometrize M`
on the actual connected components of a possibly empty or disconnected closed
oriented manifold. Actual oriented component maps transport it, and it is
equivalent to `Geometrizes M` for a connected input. Its empty case is vacuous;
the nonempty initial endpoint is never inferred from emptiness alone.

`OrientedEventReconstruction E` retains an actual `CutCapSumData E`, with its
literal capped-component lists and sphere-product multiplicities. It requires
a bijection between reconstruction groups and source components and oriented
component maps. The `map_eq` field makes these maps the inverse of the same
stored smooth reconstruction, after inclusion into the source. An unrelated
map between diffeomorphism types is insufficient. The old target-slot
bijection is proved unchanged. **Existence of this refinement is open.** The
existing smooth reconstruction theorem does not already prove its orientation.

`OrientedEventReconstruction.componentsGeometrize` is proved: actual retained
and discarded component certificates, plus the exact PC sphere-product
certificate wherever the stored multiplicity is positive, give certificates
on every source component. The proof uses the actual event presentation's
oriented component restrictions and revision203's finite-family composition.
Repeated types retain their list slots. A zero multiplicity adds no premise.

`Endpoint/ObservedHistory.lean` defines `HistoryEndpointInputs H`, with a
completion and oriented refinement for each actual event of H, together with
discarded and required cycle certificates. `stages` proves endpoint descent
by finite reverse induction, including zero events and disconnected stages.
`initialOrientedDiffeomorph` reuses the actual `InitialIdentification.map`;
the checked orientation bridge converts its tangent orientation witness.
`initial` and `geometrizes` transport the result to the original manifold.
The initial metric identity remains in the supplied record; this topological
consumer does not use it to claim any analytic estimate.

`terminal` uses the empty final-stage component predicate and the same event
inputs. It requires no late geometry and assumes no extinction theorem.
`atZero` constructs the event inputs for a zero history without an event or
cycle premise. `GeometrizationChecks/ObservedHistoryConsumers.lean` proves a
complete sphere example through this actual history and its identity marking.

Two propositions expose the next producers on **one same observation tower**:

- `ObservedTopologySupply T`: every finite observation supplies the recorded
  event inputs. This is an explicit missing producer, not raw coherence.
- `LateComponentSupply T`: one threshold B works at all later regular,
  nonempty observed slices with the last event strictly before observation.
  Its output is the actual component endpoint. This coarse output obligation
  must be refined through controlled flow, thick/thin and relative refinement;
  it is not being counted as a proof of those developments.

`geometrizes_of_observation_supplies` consumes these propositions and the
already proved marked late-nonempty/absorbing-empty dichotomy. Only the late
branch uses the late supply. Both use the original marking.
`geometrizes_of_rawSurgery_supplies` and the downstream
`produced_raw_surgery_consumer` bind this composition to the actual
`RawSurgery.ofInitial` construction, keeping both missing supplies visible.

## Source review and exact boundaries

PC v0.1.3, commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, is unchanged.
Newly reopened source bodies and definitions:

- `Surgery/Topology/History.lean:15-88`: actual initial map, orientation and
  metric identity; zero history; empty-stage guard.
- `ClosedOrientedStage.lean:1-71`: actual carrier/orientation conversion and
  round trip, with no replacement manifold.
- `ControlledExtinctionAssembly.lean:59-126`: derivative equivalence and
  tangent-to-manifold orientation bridge. The positive-event history adapter
  is not used to exclude zero events from this interface.
- `EventBridge.lean:112-188`: completion and actual smooth-to-topological
  event conversion; discarded carrier, presentation and core inclusion.
- `ExtinctObservationNucleus.lean:35-45`: actual identity zero-history marking.
- `CutCapConnectedSumSmooth.lean:1-35`: smooth reconstruction into finite sums
  of actual cap components plus sphere products. Orientation and protected
  ports are not included in its conclusion.
- `CutCapUncutComponentRealization.lean:1-81`: actual oriented component
  restrictions and their derivatives; `PoincareStandardComponentwise.lean:34-64`
  gives the oriented component inclusion for a connected manifold.
- Existing GC `CutCapReconstruction`, `ReconstructionSlots`,
  `RetainedDiscardedLabels`, `MarkedReconstructionConsumer`, and revision203
  `Endpoint/Assembly`: actual slot coverage, retained/discarded map comparison,
  marked dichotomy and conditional finite-family assembly. These bodies were
  read, not reimplemented or edited.

Pinned Lean `Init/Data/Fin/Lemmas.lean:1002-1009` supplies finite reverse
induction. `Init/Data/List/Lemmas.lean:2205-2207` supplies literal replicate
membership, including the nonzero count needed for the cycle certificate.
The exact source hashes and inspected intervals are recorded in the blueprint
receipt `checks/evidence/revision204_sources.json` (copied with this increment).

Kleiner-Lott's archived February 20, 2013 version of the 2008 Notes was reopened:
Lemma67.5 and proof, printed2740-2741/PDF154-155; Lemma67.13 and proof,
printed2745/PDF159; Definition73.1, Remark73.3, Lemma73.4 and proof,
printed2760-2762/PDF174-176. Archive SHA256:
`55a24f25c1b7cfc793706b9b6b937fefbbd6030755f7c3d6f56878d7c60b1f1b`.
The tube/cap reconstruction and extra-discard convention distinguish actual
retained and discarded components. Their diffeomorphism-type statements are
not cited as proofs of the new orientation/marking fields. Existing AT21-AT24
and GA20-GA22 passages in master203 were compared directly.

The [author index](https://math.berkeley.edu/~lott/papers.html) was checked again
on September28,2026: the Notes item has no adjacent separate erratum link.
Revision181's archived-versus-author-copy comparison remains the reused record;
no new author-PDF hash match or exhaustive absence of corrections is claimed.
The read-only BooksPapers archive was not modified.

## Review findings and handoff

The oriented refinement is a precise proposed supplier contract, with a
compiling downstream use. It is **weaker than full relative AT21/AT24**: fixed
protected ports, the prescribed cycle ledger, a flattened decorated history
and torus maps into the original manifold are not encoded or exported here.
No theorem about those outputs is claimed. The endpoint consumer preserves
the cuts and metrics on the capped prime representatives already carried in
its supplied certificates. General classification/model-to-prime endpoint
conversion for discarded and cycle factors is also still needed; the older
`StandardGeometricPresentation` is not silently treated as this endpoint.

The existing DAG overlay links AT21/AT24/GA20/GA21/GA22/LP12 to these bounded
declarations and consumers. All parent acceptance states and dependency edges
are retained. Task cards T03/T09 remain open and unclaimed. No independent
tracking system is introduced and the semantic premise census stays incomplete.

Next: produce the oriented event refinement and exceptional endpoint witnesses,
retain the stronger marked-history obligations, and define one controlled
global profile before late analytic time choices. Then expose shared local
collapse, static collapse, persistence, incompressibility and relative-refinement
interfaces. Do not release a large chapter task merely because this consumer
compiles.

Narrow builds of all three new modules passed. The zero-history sphere and
terminal consumer passed. Full gate results are recorded separately in
`evidence/iteration204_verification.json`; they audit Lean elaboration and
transitive axioms, not adequacy or production of the conditional premises.

Full team gate passed:147 modules,4224 audited declarations, only propext,
Classical.choice and Quot.sound. All123 promoted baseline/vendor modules and
PC pins remain unchanged. This reused accepted build caches; no cold-machine
build or independent teammate acceptance is claimed. The receipt retains the
precommit HEAD and dirty flag and records exact checked Lean source hashes.

A final contract review checked carrier identity, orientation, literal factor
slots, zero events, empty/disconnected stages, cycle positivity and threshold
order. No remaining hypothesis was removed or promoted to a proved producer.

Potential next improvement, not yet proved: review endpoint invariance under
orientation reversal and arbitrary smooth diffeomorphisms. The accepted PC
finite-sum opposite law and existing orientation-correction argument suggest
a way to use the already proved smooth reconstruction for the endpoint, while
leaving the stronger protected-port reconstruction task separate. Check its
actual cut-carrier and orientation transports before adopting that route.
