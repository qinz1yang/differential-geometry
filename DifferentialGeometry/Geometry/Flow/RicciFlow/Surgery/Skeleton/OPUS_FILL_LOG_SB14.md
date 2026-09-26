# SB14 — brick B14: `UniformDebitSurgeryStepStrong` from F* (bookkeeping), 2026-09-26

Worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf` @ a161fc07e). Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`. No git writes, no `lake build`.

## Progress
- start. Read AGENTS.md, Skeleton/README, HANDOFF_S (incl. 09-25/26 updates), DESIGN_S_FACTORY, logs SFR, SG3,
  the S contract (`Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:124`), F*
  (`Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:556`), `hasCanonicalCutoffRecords(_appendEvent)`,
  `toRetainedCoreEvent`, `withNeckRadius_slab` (rfl), `isKappaNoncollapsed_of_terminalNoncollapsedBefore`,
  `exists_admissiblePinchingFunction_for_identified_incomingSlabs`.
- Plan: G1 hypothesis in SFR's shape (precisions quantified, since F* exports `εP ε̄` existentially); the
  pinching and κ premises of G1 are derived here (records from the class; κ from S's terminal clause at
  radius `ε`); long slab as `∀ B θ, ∃ Qθ, … 2θ ≤ Qc (s − a)`; F* needs `L : G.TerminalLimitMetric`, which S
  does not supply: gap hypothesis.
- 06:10 first draft of `Contract/UniformDebitSurgeryStepOfFactory.lean` written (≈190 lines). Compile method:
  read-only olean mirror `E:\sb14-mirror\lean` (junctions + hard links of `E:\differential-geometry-pc3-lake\build\lib\lean`,
  real dirs along `…/Surgery/Contract` and `…/Perelman/CanonicalNeighborhood`), `lean -o/-i` into the mirror with
  LEAN_PATH = mirror first, then lake's path; `LEAN_NUM_THREADS=2`; lakefile options passed by `-D`. SG3's file
  compiled into the mirror (exit 0, no output); SFR's three files compiling (uncommitted, hence the mirror).
- 06:40 conditional version (hfine + hlong + hterm) compiled clean in the mirror; axioms
  `[propext, Classical.choice, Quot.sound]`, `#lint` clean (14 linters).
- 06:45 brief updated by the coordinator: B12 delivered (`Contract/HornFineCutNecksLongSlab.lean`), instantiate it,
  keep only the long-slab hypothesis. Binder facts: B12's `εcone` sits after `κ C1 C2 Ctime Cgrad phi` (BCD:171,
  value numeric), and F*'s `εP` is fixed internally (`min εcoarse etaDisc`) with no bound `≤ eta_B12`.
  Plan: private restatements in this file, proofs copied verbatim with the quantifier moved: BCD headline with
  `∃ εcone` first; B12's ball lemma and headline with `∃ eta εcone` first; F* with an input `η` and output `εP ≤ η`.
  Mirror: `…/Surgery/Topology` junction replaced by a hard-linked real dir (2335 links; shared build untouched);
  compiling SB12's two files into the mirror.
- FINDING (not bookkeeping, not in the ledger): F* needs `L : G.TerminalLimitMetric`; S hands only
  `G.SingularEndpoint`. No producer of `TerminalLimitMetric` for a general singular incoming slab exists in the tree
  (only closed slabs, `SlabTerminalConvergence:140`, and extinction models). Kept as hypothesis `hterm`.
- 07:05 full version compiles clean (mirror, `lean -o`, `-Dweak.linter.mathlibStandardSet=true` and the lakefile
  options): exit 0, no output. 772 lines. `#print axioms` (scratch file outside the tree):
  `[propext, Classical.choice, Quot.sound]`; `#lint`: 0 errors, 9 declarations, 14 linters. Mirror removed
  (junctions unlinked first; shared build dir count unchanged). No git writes, no `lake build`.

## Outcome
`Contract/UniformDebitSurgeryStepOfFactory.lean`, public headline (ns `…Surgery.Topology`):
```
theorem uniformDebitSurgeryStepStrong_of_long_slabs (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hlong : ∀ B θ : ℝ, 0 < B → 0 < θ → ∃ Qθ : ℝ,
      ∀ H : RetainedCoreHistory P₀, InitialIdentification P₀ g₀ H.toHistory → H.horizon < B →
      ∀ s (G : (H.stage last).IncomingSlab (H.time last) s), s ≤ B →
        G.flow.base.metric (H.time last) = H.initialMetric last → G.SingularEndpoint →
        ∀ Qc : ℝ, Qθ ≤ Qc → 2 * θ ≤ Qc * (s - H.time last))
    (hterm : ∀ H : RetainedCoreHistory P₀, InitialIdentification P₀ g₀ H.toHistory →
      ∀ s (G : (H.stage last).IncomingSlab (H.time last) s),
        G.flow.base.metric (H.time last) = H.initialMetric last → G.SingularEndpoint →
        Nonempty G.TerminalLimitMetric) :
    UniformDebitSurgeryStepStrong P₀ g₀
```
Private restatements in the same file (proofs copied verbatim, only the quantifier moved):
- `RetainedCoreHistory.exists_uniform_scalar_bound_at_distance_of_final_slab_window` (BCD:171 with `∃ εcone` first;
  value `min (neckModelTolerance (1/4000000/26000)) (1/4000000/26000/64) / 13000²`);
- `RetainedCoreHistory.exists_uniform_terminal_scalar_bound_on_ball_of_final_slab` (B12 ball lemma, same move);
- `TerminalCorePresentation.exists_uniform_fineCutNecks_of_long_terminal_slab` (B12 headline, `∃ eta εcone` first);
- `exists_horn_cutoff_record_of_fineCutNecks_of_le` (F* with input `η > 0`, output `εP ≤ η`;
  `εP := min (min εcoarse etaDisc) η`); helpers `fineCutNecks_of_le`, `hasCanonicalCutoffRecords_of_le`,
  `exists_compact_volume_debit_of_incoming_eq`.
Instantiation: `Λ := recenterConstant`; `ε := min εbar (min εF εcone)` (SG3 mono to F*'s `εF`; B12 at `εbar := ε`);
`tol = 1/1000`, `Dbig := max Dcap (Dtrace+1)`, `m := max mcap (⌈tol⁻¹⌉₊+2)`, `accuracy := min εold εcap`,
`ηrecord = δbound := min δold δmax`, `ρbound := min ρmax 1`, `p₀` = step parameters (δ ≡ 1/2, neck ≡ ρbound,
protected ≡ 1), floors `ρbound/2`, `1`; B12 at `εc := min εcut (1/4)`, `ρ := ε`, `phi` from
`exists_admissiblePinchingFunction_for_identified_incomingSlabs`; `Kfine := max K Qθ`; closure by
`hasCanonicalCutoffRecords_appendEvent`, `Fin.ext`, `eq_of_heq` subst, volume transport along `E.incoming = G`.
S clauses NOT read: history/slab `CanonicalBefore` (age-restricted), `NoncollapsedBefore`, Hamilton–Ivey `a₀`,
history gradient, history spatial clause, `τmin`, `C1 C2`.
Remaining hypotheses: `hlong` (B13) and `hterm` (terminal limit metric on the regular region; no producer in the
tree; not in FREE_INPUTS; needs its own brick: smooth convergence of `g(t)` on `terminalRegularOpen` via local Shi).
- 07:20 coordinator: discharge `hterm` (planned new file `Topology/SingularSlabTerminalLimit.lean`). CORRECTION of the
  06:45 finding: the producer already exists, committed (2ee32d01c) and in the root aggregate:
  `OrientedThreeStage.IncomingSlab.nonempty_terminalLimitMetric (G : P.IncomingSlab a s) : Nonempty G.TerminalLimitMetric`
  (`Topology/TerminalMetricExistence.lean:84`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`).
  My earlier grep missed it (statement split over two lines). No new file created. `hterm` removed; the theorem now
  uses `G.nonempty_terminalLimitMetric` (import `Topology/TerminalMetricExistence`).
- Recompiled (mirror; SFR's/SG3's files now committed in 0798da941 with shared oleans, only SB12's two files and
  mine compiled into the mirror): all exit 0, no output. Axioms of `uniformDebitSurgeryStepStrong_of_long_slabs`:
  `[propext, Classical.choice, Quot.sound]`; `#lint` 0 errors / 9 declarations / 14 linters. Mirror removed.
  Final: the ONLY hypothesis is `hlong` (B13). 767 lines.
