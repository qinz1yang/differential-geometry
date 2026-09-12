# TerminalBackwardExtension

Owner: worker W-M (2026-09-09). Scope: decision **D2** of the 2026-09-09 review
(`CANONICAL_NEIGHBORHOOD_PLAN.md` §2, "2026-09-09 review decisions"), plus the
D3 terminal-jet clause for this producer's output.

Claude's initial source was committed in62f1f9a4c; normalization and the first
review corrections landed in f055fce4d. The current D3 follow-up is verified:
focused101 EMPTY (26.28s), named101 passed (34.76s), fresh30-public audit101
standard-only (22.97s). The named build replayed only the two existing
Chapter25Convergence admissions at lines114/129. Current source SHA256:
444adf5a417f7e45206f2ce7c16380363b1761469099b1a035fe3b888bff41d4.
Exact receipts: E:/lean-tools/chapter25-terminal-local-20260909/curvature-jets-completion.json.
Root registration and current claim/release status are in WORKING_STATUS.

The current source uses TerminalRegularity.TerminalJetContinuous directly,
removing the temporary W_M predicate. TerminalSlabBounds and toStatic now accept
a chosen depthBound <= 2 * modelDepth eps, so the first short backward slab
does not require control over the full normalized source interval. The four
slab interfaces remain explicit inputs. TerminalCurvatureJets now proves the
fifth fact for the actual solution; TerminalCurvatureJetContinuity is removed,
and terminalJetContinuous_of_terminalBackwardSlab no longer takes hjet.

The review adds exists_terminalBackwardFlow_of_delta as the common analytic
entry point: it returns the SAME IsSlabLimit metric family and its flow equation
using only SlabLimitExists and SlabLimitIsFlow. The stronger slab producer now
calls this entry and adds SlabLimitSliceGeometry and SlabLimitCurvatureBound.
Thus Chapter23 need not supply a global bound before consuming the common
analytic output; Chapter25's BackwardExtension conclusion stays unchanged.
These are conditional assembly results, not proofs of the analytic interfaces.
The Chapter25 terminal scalar bound exists in TerminalLimit.scalar_bound but
is not a field of StaticTerminalLimit. Terminal nonnegativity alone is not
source pinching on earlier slices.

Continuation audit: `isSolutionOn_of_reg` also requires `hscalarTime` on the
whole carrier, beyond the interior metric equation and carrier continuity.
For a newly constructed limit, do not use a theorem already assuming
`IsSolutionOn` to produce that missing field. Pass the scalar evolution RHS
through the spatial jets first and apply one-sided calculus at time zero;
choose a smaller output window so the left endpoint lies inside the extracted
window. The verified norm/curvature-jet producer assumes an existing
`IsSolutionOn`, so it closes D3 but does not by itself close interface2.

The detailed worker record below describes the ORIGINAL source. Its duplicate
W_M predicate, fixed common depth, universal pullback-equality obstruction and
fifth interface are superseded by the current source. Use the current four
interfaces and signatures in Lean; this historical record is not current acceptance.

## Purpose

The one shared terminal-time spacetime-convergence producer. From a static
Cheeger--Gromov limit of the terminal slices (same maps for every later
statement) plus uniform curvature bounds on closed backward slabs of the members,
it produces smooth spacetime convergence on a closed window `[-δ, 0]` containing
the terminal slice, with the limit a Ricci flow. Consumed by

* Chapter 25 `prop:scn-first-backward-slab` (`Chapter25Extension.first_backward_slab`)
  through `first_backward_slab_of_terminal`, and
* Chapter 23 `thm:ksol-preliminary-compactness`, its "same maps, same limit,
  closed window containing 0, higher mixed derivatives" part, through
  `FlowSequence.ofPointedFlowSeq` and `exists_terminalBackwardSlab`.

Neither chapter may build a second one.

## Declarations and labels

| Declaration | Kind | Role / label |
|---|---|---|
| `flowOn`, `flowOn_metric` | def / simp | metric family as a `SolutionOn` |
| `StaticTerminalLimit` | structure | the generic input (below) |
| `StaticTerminalLimit.window_subset_carrier` | proved | `[-δ,0] ⊆` every member's carrier |
| `StaticTerminalLimit.open_window_subset_regular` | proved | `(-δ,0) ⊆` every member's regular set |
| `TerminalBackwardSlab` | structure | the generic output, twin of `BackwardExtension` |
| `TerminalBackwardSlab.pointed` | def | the native `PointedFlowData` of the slab |
| `TerminalBackwardSlab.pointed_atTime_zero` | proved | terminal slice **is** the static limit |
| `W_M.TerminalJetContinuous` | def | local restatement of `TerminalRegularity`'s predicate (D3) |
| `IsSlabLimit` | def | limit family + `ConvergesOn` on `[-δ,0]` |
| `SlabComparison` | def | the comparison half of `ConvergesOn` |
| `convergesOn_of_slabComparison` | proved | comparison ⟹ full `ConvergesOn` |
| `isSlabLimit_of_slabComparison` | proved | packaging |
| `SlabLimitExists` | **INTERFACE 1** | analytic core |
| `SlabLimitIsFlow` | **INTERFACE 2** | limit equation |
| `SlabLimitSliceGeometry` | **INTERFACE 3** | slice completeness and `SecLower` |
| `SlabLimitCurvatureBound` | **INTERFACE 4** | global slab curvature bound |
| `TerminalCurvatureJetContinuity` | **INTERFACE 5** | D3, single-flow, upstream candidate |
| `exists_terminalBackwardSlab_of_delta` | proved | producer, fixed window |
| `TerminalSlabAnalyticInputs` | def | the four window-dependent interfaces, bundled |
| `exists_terminalBackwardSlab` | proved | **the shared producer** |
| `terminalJetContinuous_of_terminalBackwardSlab` | proved | D3 output for the slab |
| `FlowSequence.ofPointedFlowSeq` (+ 2 simp lemmas) | def / proved | Chapter 23 entry point |
| `ancient_carrier_window`, `ancient_regular_window` | proved | Chapter 23 window containments |
| `TerminalSlabBounds` | def | Chapter 25's uniform slab bound |
| `TerminalLimit.toStatic` | proved | Chapter 25 entry point |
| `TerminalBackwardSlab.toBackwardExtension` | proved | back to `BackwardExtension` |
| `first_backward_slab_of_terminal` | proved | exactly the conclusion of `first_backward_slab` |

## The input structure

`StaticTerminalLimit X depthBound` carries

1. `carrier_window`, `regular_window`: one common closed window `[-depthBound,0]`
   inside every member's carrier, with regular interior;
2. `space`, `subseq`, `strictMono`, `maps`, `converges`, `canonical_domains`,
   `capture`: the static limit at time `0` on the SAME exhaustion maps, with the
   `conv.domain k = canonicalSourceData maps k` identity `Chapter25Convergence`
   insists on, and separate source capture;
3. `precompact`, `connected_domains`, `nested`, `connected`, `complete`,
   `nonnegative`: the geometry of that limit, copied from `TerminalLimit`;
4. `slab_bounds`: for every compact `K` of the limit, every `0 < width < depthBound`,
   a constant `C` with `∀ᶠ i, ∀ t ∈ [-width,0], ∀ y ∈ K,
   rmNormSq (X.term (subseq i)) t (maps i y) ≤ C`.

### Decision recorded here: containment instead of `carrier_eq`

The brief prescribed `carrier_i = Icc (-S_i) 0`, `regular_i = Ioo (-S_i) 0` with
`S_i ≥ S`. Inspecting the second consumer showed that Chapter 23's normalized
`κ`-solutions arrive as a `PointedFlowSeq` on the SINGLE interval
`ancientTimeInterval` (`carrier = Iic 0`, `regular = Iio 0`; see
`KappaSolutions/NormalizedKLimCompactness.lean`), which does not satisfy an
equality with a bounded `Icc` and would have needed a `timeRestrict` adapter.
The producer therefore asks only for the containments
`Icc (-depthBound) 0 ⊆ carrier i` and `Ioo (-depthBound) 0 ⊆ regular i`, which
Chapter 25 supplies from `carrier_eq`/`regular_eq`/`depth_buffer` and Chapter 23
from `ancient_carrier_window`/`ancient_regular_window` with no restriction of the
members. Nothing in the conclusion uses regularity at `0`, so this is strictly
the weaker common form; the intended and hard case (`Icc`/`Ioo`, terminal time
never regular by `RealTimeInterval.regular_isOpen`) is unchanged.

The `slab_bounds` shape was chosen the same way. `BoundedAtDistance` and
`TerminalDerivativeBounds` (`Chapter25Convergence`) are stated at the TERMINAL
time only and on metric balls around the original centres, so neither can serve;
the common form is the compact-set, closed-slab, eventually-in-`i` bound above,
which Chapter 25 gets from `bounded_curvature_at_distance` + `local_propagation`
and Chapter 23 from its `κ`-solution curvature bounds
(`exists_normalized_klim_local_curvature_constants`).

## What both chapters must pass

Chapter 25: `TerminalLimit.toStatic hb` with `hb : TerminalSlabBounds L`, then
`TerminalSlabAnalyticInputs (L.toStatic hb)`. The common depth is
`2 * modelDepth eps`; `NormalizedSequence.depth_buffer` supplies it. Output is
converted by `TerminalBackwardSlab.toBackwardExtension`, giving exactly
`∃ delta, ∃ hd : 0 < delta, Nonempty (BackwardExtension L (closed (-delta) 0 _))`
— the conclusion of `Chapter25Extension.first_backward_slab`.

Chapter 23: build `X := FlowSequence.ofPointedFlowSeq Y` (the pointed Riemannian
sequences agree definitionally, `ofPointedFlowSeq_atTime` is `rfl`, so the maps
and `MetricCGConvergenceData` of
`exists_normalized_klim_canonical_slice_limit` transfer unchanged), then a
`StaticTerminalLimit X T` for any `T > 0`, then `exists_terminalBackwardSlab`.
`TerminalCoordinateJets` / `HarnackTerminalJets` stay consumers.
Chapter 23 must instantiate its model at `I := I3` (universes `{u,0,0}`), because
`Chapter25Convergence.FlowSequence` is three-dimensional; a model-generic version
would require moving `FlowSequence` first and is out of scope for D2.

## Interfaces and the exact missing tree facts

1. **`SlabLimitExists`** — existence of the limit family `g` with
   `g 0 = space.metric` and the comparison records. *Missing:* a
   sequence-uniform Cauchy estimate for pulled-back metric jets across a sequence
   of maps with varying sources, up to and including the terminal time.
   `TerminalJetLimits.uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith` and
   `TerminalChartJets.solution_chartGram_jets_tendsto_terminal` control the TIME
   direction for one flow; `MetricCGConvergenceData` controls the SEQUENCE
   direction at the single time `0`; `Compactness/Limits/Hamilton.compactnessSol`
   and `SourceSpacetimeConvergenceData` need one common OPEN window
   (`RealTimeInterval.openInterval`, `0` in the interior) and a single
   `PointedFlowSeq.D`. Nothing combines the two directions on a closed window
   whose right endpoint is terminal.
   *Second requirement carried by this interface:*
   `Chapter25Geometry.MetricComparisonOn` demands `pullback s : Tensor0SField ∞ 2`
   — a globally smooth section — with `pullback_eq` at EVERY point, while
   `PartialDiffeomorph.contMDiffOn_toFun` gives smoothness only on the source
   (outside it `mfderiv` is the junk value `0`). Any producer of these records
   must supply global smoothness of each map's pullback field. This is a property
   of the existing comparison record; it is flagged for the Chapter 25 owner and
   was not changed here (no edits to existing files).
2. **`SlabLimitIsFlow`** — a limit family is a Ricci flow on `[-δ,0]`.
   *Missing:* `Compactness/Limits/Equation.lean` derives the limit equation from
   the tree's own `SourceMetricConvergenceData` on a common interval, and
   `Compactness/Limits/Construction.isSolutionOn_of_reg` wants the pointwise
   equation on `D.regular` plus carrier continuity of the scalar, Ricci and
   `Rm04` families. There is no lemma turning `MetricComparisonOn`-style
   closed-window convergence with varying member intervals into those hypotheses.
   The terminal endpoint itself is covered by
   `TerminalRicciRHS.solution_ricciPair_hasDerivWithinAt_terminal` once the
   interior equation is known, so the genuine gap is the interior equation plus
   carrier continuity.
3. **`SlabLimitSliceGeometry`** — completeness and `SecLower` of every slice.
   *Missing:* no transfer of `MetricComplete` along a uniform two-sided metric
   equivalence, and no passage of `SecLower` to a smooth limit of metrics.
   `Compactness/Metric/FlowUniformEquivalence.metric_uniform_equivalent_on_window_of_solutions`
   gives the equivalence but only on a window inside the REGULAR set and only
   from a Ricci quadratic bound.
4. **`SlabLimitCurvatureBound`** — the global bound of `compact_time_bound`.
   *Missing:* `slab_bounds` is compact-set only, so no global bound survives the
   limit; the global input is terminal (`TerminalLimit.scalar_bound` with
   `SecLower`), and the tree has no backward propagation of a global curvature
   bound for a complete flow from its terminal slice. Chapter 25's
   `terminal_limit_global_bound` states the terminal half and is itself open.
5. **`TerminalCurvatureJetContinuity`** — D3, for ONE flow with closed carrier
   `[a,b]` and regular interior: every evaluated spatial curvature jet is left
   continuous in time at `b`. *Missing:* the terminal machinery converges the
   fixed-chart Gram jets (`solution_chartGram_jets_tendsto_terminal`) and the
   chart Ricci jets (`solution_chartRicci_jets_tendsto_terminal`), but there is
   no transfer from those chart quantities to the intrinsic evaluated fields
   `nablaKRm04Field S t k x v` at arbitrary order `k`.

## Upstream candidates

* **`TerminalCurvatureJetContinuity`** is the clean upstream lemma: it is about a
  single flow, needs only `TerminalChartJets`/`TerminalRicciJetOperators` plus a
  chart-to-intrinsic transfer, and is what D3 asks every producer of an ancient
  limit to deliver. It belongs next to `TerminalRegularity.lean`.
* **`convergesOn_of_slabComparison`** (the containment bookkeeping of
  `ConvergesOn`) is generic in `FlowSequence` and could move to
  `Chapter25Convergence` when that file is next edited.
* **`FlowSequence.ofPointedFlowSeq`** and its two `rfl` lemmas belong with
  `FlowSequence` itself.
* A transfer of `MetricComplete` along `MetricUniformEquivalentOn`, and passage
  of `SecLower` to smooth limits of metrics (interface 3), are general Riemannian
  facts and belong under `Geometry/Metric/` and `Geometry/Curvature/`.

## D3 and `TerminalRegularity.lean`

`TerminalRegularity.lean` is committed (HEAD `ed1a6550a`) but still not registered
in `DifferentialGeometry.lean`, so it has no `.olean` and cannot be imported by a
`lake env lean` check. Its predicate is restated verbatim as
`W_M.TerminalJetContinuous` (specialised to `I3`, universes `{u,0,0}`). When
`TerminalRegularity` is registered at the next root window, replace the local
copy by the import and delete the `W_M` namespace; the statement is character-for-
character the same clause.

## Verification

```
cd E:/differential-geometry-dev
LEAN_NUM_THREADS=1 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/TerminalBackwardExtension.lean
```

2026-09-09, HEAD `ed1a6550a`, source sha1 `a076033da92910f5ac4fa7cbc6b357fc09b52bbe`
(567 lines): **empty output, 29.5 s** (zero errors, zero warnings; the file uses
`set_option autoImplicit false` only, no `sorry`, no `nolint`, no `show` tactic).
Host `lean.exe` count checked as `0` before each run; one worker, one thread; no
`lake build`, `clean` or `update` was run, and no existing file was edited.

A temporary `#print axioms` block over all 31 public declarations was appended,
run in the same way, and then removed. Every one reported exactly

```
[propext, Classical.choice, Quot.sound]
```

so the proved part of the chain is standard-axioms-only; the interfaces are
explicit hypotheses, not axioms, and no `sorryAx` appears.

Note that `lake env lean` writes no `.olean` and skips the package linter set, so
before any downstream file can import this module it needs a registered root
import and a named artifact refresh in an exclusive window.

## Rejected routes

* Reusing `Compactness/Limits/Hamilton.compactnessSol` or `FlowUpgrade`: both
  need `X.D = RealTimeInterval.openInterval α b 0 _`, one common OPEN window with
  `0` interior, and produce their OWN limit and subsequence rather than accepting
  a prescribed static limit with prescribed maps. Neither shape fits a terminal
  time.
* Restricting Chapter 23's ancient members with `SolutionOn.timeRestrict` to force
  `carrier_eq`: unnecessary once the input asks for containments (see the decision
  above), and it would have forced the consumer to re-derive `IsSolutionOn`.
* Making the producer's output `BackwardExtension` directly: that structure is
  indexed by `TerminalLimit X` for `X : NormalizedSequence`, so it cannot carry a
  generic `FlowSequence` conclusion. `TerminalBackwardSlab` is its field-for-field
  twin and `toBackwardExtension` is a definitional copy, because
  `TerminalLimit.toStatic` keeps the very `space`, `maps` and `subseq`.
