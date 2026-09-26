# Leaf S — `UniformDebitSurgeryStep`

Statement: `Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean`, `def UniformDebitSurgeryStep`.
Leaf: `Surgery/Skeleton/PoincareEndgame.lean`, `uniformDebitSurgeryStep`. Ledger: `Surgery/FREE_INPUTS.md`.

## What it says

Given a horizon `B`, choose an accuracy `ε < 1/11` (the accuracy of the canonical neighbourhoods
the cutoff will use; it may depend on `B` only). Then, given canonical constants `C1 C2`, a
threshold `qcan`, a derivative constant `Ctime` and admissibility bounds `δmax ρmax εcap` (all
chosen at that accuracy by the canonical-neighbourhood side, leaf C), produce once: cap parameters
`p₀` with `p₀.modelAccuracy ≤ εcap`, record bounds `δbound ≤ δmax`, `ρbound ≤ ρmax`, and one debit
`v > 0`. Then, for every history `H` in the class
`H.hasCanonicalCutoffRecords p₀ δbound ρbound` (initial identification, `time last = horizon < B`)
whose slabs satisfy `|∂ₜR| ≤ Ctime R²` above `qcan`, and every singular incoming slab `G` from its
end with `s ≤ B`, the same derivative bound and canonical witnesses
`CanonicalWitness G.flow ε C1 C2 x t` with `capTubeHasNeckChart ε` above `qcan`: return the next
`RetainedCoreEvent` with `E.incoming = G`, class closure for `H.appendEvent`, a
`GeometricCutoffRecord` at the last index whose fixed fields equal `p₀`'s,
`boundaryFrameReversing`, `poincareStandardDiscarded`, and the debit inequality with `v`.

## Base and porting cost (measured 2026-09-25)

This lane is based on the `codex/wt17-pc-build-warning` lineage (22a24821b; the branch has since
advanced 30 commits: cap survival, cap action bounds, standard comparison). The factory below lives
only on `origin/codex/pc-sorry-free`. Its import closure there has 10,682 modules: 10,584 identical
to wt17, 12 new files, 55 files changed only on pc-sorry-free (clean cherry-picks) and **31 files
changed on both sides since the merge base 8e09bcaf0** (`EventData.lean`, `HistoryAction.lean`,
`HistorySurvivor*`, `CapWindow*`, `StandardCap/Window*`, `Metric/Convergence/Metric/Evaluation.lean`,
`Topology/FirstExit.lean`, …). A partial cherry-pick is therefore not viable: either the two lines
are merged by their owners, or S is re-derived on the wt17 lineage with wt17's own cap-survival and
history machinery, using the pc-sorry-free factory as the route.

## What exists (branch `origin/codex/pc-sorry-free` @ 6d15b3ed9, not on this base)

`Contract/PoincareHornCutoffRecord.lean:461`
`exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods`
proves every conclusion of S: event, `Record` with `Record.delta = fun _ => δ`, all necks at scale
`Q`, canonical windows, `E.poincareStandardDiscarded`, `K.hasCanonicalCutoffRecords p₀ δold ρold`
(the closure, under `ηrecord ≤ δold` and `stepParameters.neckRadius s ≤ ρold`), the debit
`#cuts · v` with `v = Q^(-3/2)` and `Q` chosen before `H`, `boundaryFrameReversing`. The event is
returned as `Eappend : MetricCutCapEvent (H.stage last) Qout (H.time last) s` with
`K = H.appendEvent Eappend.incoming.lt (Eappend.toRetainedCoreEvent hOldAppend) hInitial`, so the
`RetainedCoreEvent` of S is `Eappend.toRetainedCoreEvent hOldAppend`; its `.incoming`, `.terminal`,
`.outputMetric`, `.transition` are the projections of `Eappend` (`RetainedCoreMetricEvent.lean:64`);
`E.incoming = D'.slab` and `(D.withNeckRadius ρ hρ).slab = D.slab` (`Contract/TerminalCutoffScale.lean:21`)
give `E.incoming = G`; `poincareStandardDiscarded` reads only `.discarded`.

## The gap: binder order

The factory takes `Ctime` first, then `∀ m accuracy ηrecord q0`, and only then produces
`∃ δ ε₀ Qmin, ∃ εcan …, ∀ C1 C2, ∃ C Λ, ∀ qcan floors, ∃ Q v, ∀ p₀ H …`. Its canonical-neighbourhood
hypothesis is at the *output* accuracy `εcan` and its derivative hypothesis is above the *input*
threshold `q0`, with the cap accuracy `accuracy` also an input. S needs the accuracy `ε` first: it
may be chosen freely for each `B`, but before `C1 C2 qcan Ctime δmax ρmax εcap` are known, whereas
`εcan` of the factory depends on `q0` and `accuracy`.

Where the dependence is created: `Contract/PreparedHistoryCutoff.lean:237`
(`exists_horn_cutoff_record_at_scale_of_prepared_history`) sets
`ε₀ := min εfactory (min (ηstar / 2) ((mstar + 1)⁻¹))` with `ηstar mstar Qmin` from
`exists_uniform_selected_neck_retained_append_backward … q0 …`, and that theorem
(`Topology/ProspectiveNeckSurvival.lean:3444`, private base at `:3322`) chooses
`ηstar mstar Qmin` by contradiction: a counterexample sequence with `η_n → 0`, `m_n → ∞`,
`scale_n → ∞` for a fixed `q0` is refuted by the subsequence lemma
`exists_subsequence_selected_neck_append_backward`. So `ηstar` is formally a function of `q0`
(and of `accuracy` through `εfactory`), and no reordering of the statements alone recovers S.

## Proof plan

1. Show that the derivative threshold enters the backward survival only through the minimal
   scale: restate the subsequence lemma and `:3322` so that `ηstar, mstar` are produced before
   `q0` and only `Qmin` after it (Perelman: the precision needed for a δ-neck to survive
   backward is a function of `δ, tol, r, D`, while the curvature scale at which the derivative
   bound is used is `≳ Q`). If the subsequence lemma cannot take a sequence `q0_n`, prove a
   monotonicity lemma: the conclusion for `q0` implies the conclusion for every `q0' ≥ q0`
   (the derivative hypothesis above `q0'` is weaker), and choose `q0 := qcan` with `Qmin` above it.
2. Likewise separate `accuracy` from `εfactory` in
   `exists_uniform_horn_cutoff_history_extension_at_scale_with_original_neck_bounds_and_canonical_windows`,
   or prove that CN at accuracy `εcan` near a cap of accuracy `accuracy ≤ εcap(εcan)` follows from
   the standard-cap comparison; then choose `accuracy` after `εcan` by running the factory twice
   is **not** valid (the second run may change `εcan`), so the separation has to be in the statement.
3. With the constants in Perelman's order, instantiate: `ε := εcan` once it no longer depends on
   `q0` and `accuracy`; `Ctime` from C; `m := ⌈tol⁻¹⌉₊ + 2`, `accuracy := min εold εcap`,
   `ηrecord := min δold δmax`, `q0 := qcan`; `C1 C2` from C; `qcan` from C; the step floors are
   internal to the proof (they fix `Q`, hence `v = Q^(-3/2)`); obtain `Q v`;
   `p₀ := ⟨fixed, recenterConstant, m, accuracy, Dbig, …⟩` with constant time-dependent fields;
   `δbound := min δold δmax`, `ρbound := min ρ_step ρmax`.
4. Bookkeeping: `hasCanonicalCutoffRecords_appendEvent` (`Topology/CanonicalCapWindows.lean:135`)
   for the closure at `(δbound, ρbound)`; `Fin.ext` on `i.val = H.eventCount`; `cases eq_of_heq`
   on `HEq Eappend E`; transport of `Kvol` along `E.incoming = D'.slab` by generalising the slab.

## Acceptance

No `sorry`, no `axiom`, no `nolint`, no heartbeat overrides. Build the changed modules and every
module depending on them; `#print axioms` of `uniformDebitSurgeryStep` must be
`propext`, `Classical.choice`, `Quot.sound`; the 13-linter audit (`docBlame`, `docBlameThm`
excluded) on all changed modules; then move the theorem out of `Skeleton/` into
`Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean` (or a producer module next to it),
register in the root aggregate, update `Surgery/FREE_INPUTS.md` in the same commit.

## Update 2026-09-25 (after the external review and Lane D)

* The interface now passes `τmin`, `Dcap` and `mcap` from C to S: S must choose `p₀` with
  `Dcap ≤ p₀.modelRadius` and `mcap ≤ p₀.modelOrder` (the factory takes `Dbig` and the model order
  as free inputs, so this is a choice, not an obstacle), and it receives the canonical-neighbourhood
  hypothesis only at points with `τmin ≤ R · (t − a)`. The factory's hypothesis
  `(∀ x t, t ∈ Ioo D.startTime D.endTime → qcan < R → ∃ W …)` has the old unrestricted shape and is
  unsatisfiable on any slab that follows a cut (fresh cap points have no `CanonicalWitness`); when
  the chain is ported it must be weakened to the age-restricted form, and the proof checked to use
  canonical neighbourhoods only at points with `R (t − a) ≥ τmin` (the horn near the singular time
  satisfies this for large `R`).
* The base-and-porting paragraph above is superseded by the measurement of 2026-09-25 afternoon:
  the five factory commits `c0f94726d a23551e62 e556f139e 95fb763bb 4fe90864a` cherry-pick cleanly
  onto this lineage (every file they touch is either new or identical to ours at their parent); the
  transitive need beyond that is 6 modules absent here, 31 changed only on `pc-sorry-free` and 2
  changed on both sides (`HistoryAction`, `HistorySurvivorIncoming`). Port bottom-up, compiling.
* **Uniform cutting scale under the age threshold (second external review, FIX 3,
  `consult/B-poincare-endgame-second-review-digest.md`).** S chooses the cutting scale and the debit
  before `H`, but slabs have no uniform positive length: after a cut at scale `h` at time `a`, the
  capped region evolves like the standard solution and can become singular near `a + h²`, and the
  necks of the new horn at scale `h` then have normalized age `h⁻²(t − a)` of order `1 < τmin`, so
  the age-restricted hypothesis gives them no witness. The port must therefore (i) record in the
  class a post-surgery curvature bound `sup R(·, a⁺) ≤ C h⁻²` (everything above `h⁻²` up to
  constants lies in the removed horns or in discarded canonical components), (ii) derive the slab
  length bound `s − a ≥ h²/(C·Ctime)` from the derivative clause, and (iii) cut at the smaller scale
  `h' := h / √(C·Ctime·τmin)`, whose necks have age `h'⁻²(t − a) ≥ τmin` at every `t ≥ s − o(1)`;
  the debit `v = h'³` stays uniform. For the first slab from `g₀` the initial curvature bound gives
  the length bound directly. Do not add a "uniform slab length" hypothesis instead.
* The reorder concerns more than `q0`: `Ctime`, `m`, `accuracy` and `ηrecord` also precede `εcan`
  in the factory; `Ctime` is dimensionless and cannot be absorbed by a large scale. Record for each
  input whether its dependence is deferred to `Qmin` or removed by a uniform derivative estimate.
  "C holds for every ε" does not by itself uncouple a factory whose cutting accuracy depends on the
  cap accuracy; the honest alternative, if the reorder fails, is a joint compatibility statement for
  each horizon (one tuple `ε C1 C2 qcan τmin Ctime p₀ δbound ρbound v` with the class closed under the
  step), which the assembly can consume as well.
