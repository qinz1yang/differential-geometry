# Moise route audit and revised priorities (2026-09-19 UTC)

Baseline: integration source `982dd6062c3fc8e637a6015f6173122657d3d37a`,
with documentation published at `a05c940eb`. This review distinguishes mathematical
statement review, actual source constructions, focused compiler evidence and the
independent full-source build, stopped by the owner after this audit. It does
not certify classical endpoints merely because their propositions or
conditional consumers compile.

## Statement defects confirmed

| Interface | Current source evidence | Required repair |
| --- | --- | --- |
| `Moise252` (`MoiseChain.lean:34`) | The output is a proper embedded disk, with no assertion that its new boundary is noncontractible in the specified boundary component. | Restore non-nullhomotopy of the actual new boundary inclusion. The new boundary need not represent the originally supplied loop class. Book p183, Theorem 25.2, includes this as its third conclusion. |
| `Moise331` (`MoiseChain.lean:135`) | The fixed `derivedNeighborhood T L` must lie in every supplied open `U`, and its image must be an ambient neighborhood. No ambient three-dimensional neighborhood condition on `T` is supplied. | Existentially choose a genuine regular neighborhood using appropriate ambient triangulation/subdivision data, with containment in `U`. Record its relation to the graph and actual ambient neighborhood properties. |
| `Moise351` (`MoiseChain.lean:151`) | `K` is only relatively closed; no one-dimensional polyhedral condition is required. The output is a manifold neighborhood, without a regular-neighborhood relation to `K`. | Restore the one-dimensional, potentially noncompact polyhedral input and a faithful regular-neighborhood witness in the PL manifold. Preserve local finiteness, open-domain scope and pointwise positive error control. |

The singleton objection to `Moise331` is valid mathematically: take `T = L`
the one-vertex complex, `U = univ`, and `h = id`. The derived neighborhood and
its image remain singletons, so the required neighborhood of `h(L)` cannot exist
in three-dimensional Euclidean space. Independently, fixing the neighborhood
before choosing arbitrarily small `U` is the wrong quantifier order. This review
has not compiled a Lean refutation of that proposition. The other two findings
are statement-strength/faithfulness defects, not proofs that those propositions
are false or evidence of Lean inconsistency. Library-wide identifier searches
currently find all three names only at their definitions; their importing modules
still require recompilation after a change.

Book p230 (Theorem 33.1) explicitly chooses the regular neighborhood inside `U`.
It states a finite connected one-dimensional polyhedron with no endpoints, then
explains that the endpoint restriction can be removed with extra work. A source-
faithful first statement should retain it or separately prove the generalization.
Book pp247-248 defines regular neighborhoods relative to a rectilinear
triangulation of the open PL manifold and allows the graph to be noncompact.
Continuous positive error functions are sufficient for the current consumer;
no unsupported replacement by a uniform positive constant is allowed.

Original-source links: [33.1](https://link.springer.com/chapter/10.1007/978-1-4612-9906-6_34),
[chapter 35](https://link.springer.com/chapter/10.1007/978-1-4612-9906-6_36).
Relevant passages of the full local book were read at
`D:/differential-geometry-moise-plan/.lake/scratch/moise_gtm47.pdf`;
zero-based PDF indices are book page plus 9. Pages 217, 230 and 248 were also
rendered and visually checked.

## Normalization: a necessary correction to the proposed remedy

The reported gap is real. `NormalSystem` in `LoopTheorem/SingularCell.lean:514`
does not imply local injectivity or fibers of cardinality at most two.
`SingularGeneralPosition.lean:587` and its boundary-relative variants explicitly
consume those properties. `LoopTheorem/DoubleCarrier.lean:18` transports the real
carrier/frontier and proves exact preservation of the original fibers; changing
the ambient double or chart does not remove bad fibers. Generic two-dimensional
maps into three dimensions cannot be assumed to have no triple points.

However, the original Stallings route does not require applying Lemma 2 directly
to every initial NormalSystem. Book p184, Section 25, Lemma 2, already assumes local
injectivity and at most two preimages. Book pp188-189, Section 25, Lemma 3, first uses
complexity induction in a two-sheeted cover to obtain an embedded disk upstairs.
It then projects that new disk and invokes Lemma 2. Thus a natural preferred
producer is the projection of that embedded disk: the local covering property
and disk embedding produce local injectivity, and two-sheetedness bounds fibers.
The PL, boundary-neighborhood and normal-subgroup compatibility must also be
proved for that very map. This is a source-supported third option beyond direct
normalization of the original map or a new triple-point elimination theory.

Current `LoopTheorem/LemmaThree.lean:147` is insufficient for that step:
`DoubleCoverReduction` stores a topological projection, covering/fiber conditions
and a complexity decrease, but no PL compatibility, source-map lifting equations,
boundary-neighborhood map, or pullback-normal-subgroup relation. Its induction
consumer at line 157 accepts the entire Lemma 2 descent as a separate hypothesis.
There is also a domain distinction to repair: in the book the two-sheeted cover
is on the full covering manifold; the new regular neighborhood `M2` is a subset
of it. Restricting the projection to `M2` must not silently be asserted to remain
a surjective two-sheeted cover of the original manifold. Keep the ambient cover
and the smaller normal-system neighborhood as separate objects with inclusion
and commuting-map equations.

Prioritize this actual projection producer and source-faithful cover reduction.
Retain the independently useful local branch separation and PL neighborhood
results, but do not extend their wrappers while the producer is absent. The
whole-branch compatible two-sheet chart remains a real Lemma 2 obligation: a
finite pointwise chart cover supplies neither overlap compatibility nor one
injective global map. E3's `b195204ed` proves chart-conjugated supported homotopies,
not this missing chart construction or a global NormalSystem surgery.

## Endpoints and dependency order

`Endgame.plApproximationManifold_three_of_moise352` still requires `Moise352 3`.
`Smoothing.exists_isManifold_three_of_plApproximation_of_plSmoothing` still requires
both `PLApproximation 3` and `PLSmoothing 3`. The only literal `PLSmoothing` producer
in that source is the zero-dimensional one. No unconditional three-dimensional
producer was found in the current library search. The final smoothability goal
therefore retains two independent major inputs, even though its conditional
assembly is short.

A compact PL-to-smooth existence theorem is enough for the stated final compact
consumer. Schedule it as a separate mathematical lane after a current lane's
coherent delivery; first audit the finite triangulation/handle, smooth attaching
circle, framing and sphere-extension inputs. It is not final glue, and a smooth
structure already assumed upstream cannot serve as its own producer. This
compact restriction does not apply to PL approximation: `ChartGluing` uses the
open overlap and an error controlled by distance to its complement.

Book pp216-218 verifies the direction `30.6 -> 30.7`: Theorem 30.6 uses compression,
separation, van Kampen and surface-group identification; the proof of 30.7 then
explicitly starts from 30.6. Remove the reverse edge from the chain table.
Keep original CST production separate from a cylindrical diagram. S has since
delivered aa6ff83be for the actual product/finite 24.11 construction, pending
independent acceptance; its current lane is the 24.12 generating-loop bridge.

The source contains genuine unconditional PL Schoenflies endpoints in
`PLSchoenflies.lean`, using the actual `schoenflies_input` constructor.
`TameNestedCells.moise305_tame_of_moise304` constructs the narrower tame arrow
using a bicollared outer boundary and its proved complement connectedness.
General wild-cell Alexander duality is not a prerequisite of this tame arrow.

## Build coverage and acceptance

A complete static traversal of local `import` edges at the baseline reaches
9258 project modules, including the root itself. The five existing modules
`Approximation`, `ApproximationManifold`, `ChartGluing`, `Endgame` and `Smoothing`
are all unreachable from `DifferentialGeometry.lean`; the original audit's three
examples were correct but incomplete. `PLSchoenflies` is reachable transitively
through `SphereComplement`, although not directly registered as a flat-root leaf.
`TameNestedCells` is directly registered and reachable.

All seven modules listed above were independently recompiled against current
source. Their complete census contains 26 nonautomatic declarations: all
transitive axiom closures are subsets of the three standard foundational axioms,
and all 13 applicable environment linters passed. Only docBlame/docBlameThm are
excluded. Each compile and the combined audit returned exit 0 and zero diagnostics.
The first strict check found one existing long line in ChartGluing; it was wrapped
without changing the proof. Private compiled outputs were used for cross-imports
among these seven leaves; other imported objects remain shared. This is not a
completed full-source gate, nor a proof of the explicit proposition inputs.
Evidence is in `.lake/verified-route-audit-20260919.json` and
`C:/Users/liao9/AppData/Local/Temp/codex-moise-route-audit-20260919`.

The root coverage fix is prepared as `RootEndpointImports.patch` in that external
directory: five missing chain imports plus direct registration of PLSchoenflies.
It is not applied. The earlier stop attempt was rejected by automatic review
because the owner had asked to retain the build; no stop executed at that time.
The later explicit owner stop superseded that instruction: the coordinator
stopped the owned Lake/Lean processes at 2026-09-19 02:00 UTC, the wrapper
exited and no owned root workers remained. Outputs are preserved; local status
records interrupted_by_owner and automaticRestart=false.

Plan correction precedes further integration. Next accept pending source
deliveries, apply the six-import patch, verify reachability and check affected
modules/consumers. Keep the root stopped under the owner's instruction.
When it is resumed, reuse retained artifacts and the expanded import graph.
Neither the interrupted root nor focused leaf checks establish full-source
success.

## Priority and ownership decisions

1. h, Sol max: repair the three exact theorem contracts, their genuine geometric
   witnesses and importing consumers. Assigned at the completed `0a0876425`
   delivery boundary. Its verified trimmed ball pair remains accepted; the later
   full-arc containment delivery awaits independent integration acceptance.
2. F, Astra max: delivered source-collapse construction `495a3e343` during this
   audit, then received the source-faithful projection/cover producer round at
   that completed-work boundary. Its collapse delivery awaits independent
   integration acceptance and is not counted as the positive producer. No active
   round was interrupted.
3. E3, Sol max: owns 30.4, first the genuine 30.3 splitting/separation step; 26.4
   and 28.19 remain explicit dependencies. This owner was assigned when E3
   delivered its conjugation layer, before the current audit arrived.
4. S, Astra max: after product/CST delivery aa6ff83be, close 24.12 from one
   generating loop's nullhomotopy to all loops and actual CST. Compact PL
   smoothing is a separate next lane at delivery or a genuine blocker.
5. Coordinator: correct plans first, independently accept pending deliveries,
   and repair coverage. Keep the root stopped and artifacts retained.
   Distinguish conditional consumers from completed producers. The project
   remains in core proof construction.
