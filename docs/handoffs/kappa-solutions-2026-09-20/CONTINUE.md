# Ready-to-paste continuation prompt

Copy the text below into a fresh Codex conversation. It requests the next proof phase; the current
handoff has stopped before starting it.

---

Continue the Ricci-flow formalization in
`/Users/bennettchow/Documents/Codex/wt17/ziyang` on branch `codex/pc-work-2026-09-17`.
Preserve all existing changes. Do not reset, rebase, force-push, or switch to the desktop's default
worktree. In-scope checkpoint commits and regular pushes to this named branch are authorized.

First read:

1. `/Users/bennettchow/.codex/AGENTS.md`.
2. The repository's `AGENTS.md`, `NAMING.md`, and `STRUCTURE.md`.
3. `docs/handoffs/kappa-solutions-2026-09-20/README.md`, `VERIFICATION.md`,
   `REMAINING_WORK.md`, and `REFERENCES.md`.
4. The `prove-theorem-suite` and `audit-lean-theorem-suite` skills under
   `/Users/bennettchow/.codex/skills/`, including their referenced statement/acceptance audits.

Inspect the current branch, HEAD, upstream, and dirty state before making changes. The final proof
commit from the preceding phase is `3b12c1abf575960b58f7adca8f73c54c7ea5049b`.
The immediate following commit adds this handoff. Resolve its exact hash with:

```sh
git log --diff-filter=A --format=%H -- docs/handoffs/kappa-solutions-2026-09-20/README.md
```

The previous phase completed these four theorems in namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions`:

- `exists_backward_slice_asymptotic_shrinker`
- `exists_samePole_normalized_asymptotic_shrinker`
- `klim_terminal_curvature_trichotomy`
- `ancient_fixed_universal_cover_product_of_null_plane`

All four have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closures.
The full project build passed 20,143 jobs with 21 retained out-of-scope `sorry` warnings.
Nine declarations passed 13 declaration linters. The first two statements were generalized by
removing the unnecessary dimension lower-bound binder; the original statements compile as corollaries.
The other two original declaration texts are unchanged. Lean is 4.33.1 and Lake is 5.0.0-src+819816b.
Reproduce the snapshot checks with `bash docs/handoffs/kappa-solutions-2026-09-20/verify.sh` if the
checkout still matches it. The script's fixed debt counts must be interpreted as snapshot checks
once later legitimate proofs change them.

Begin the canonical-neighborhood/ancient-extension phase by working on
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance`
in `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean`.
Keep its existing conclusion: for positive κ and σ and an admissible pinching function, find a small
positive ε threshold so every normalized sequence has `BoundedAtDistance` and
`TerminalDerivativeBounds`.

Read `NormalizedSequence` and both conclusion definitions in `BlowupConvergence.lean` before designing
the proof. Each source is a complete almost-pinched finite-interval flow with a source-dependent global
bound, normalized base scalar, noncollapse, and κ-model information at higher-curvature points. It is
not itself an ancient κ-solution. The obstacle is a uniform source estimate on buffered parabolic
balls, with actual ball containment, followed by fixed-order Shi estimates at the genuine terminal
endpoint. Do not assume exact nonnegative Ricci curvature from almost-pinching, a common positive-time
extension, a bound uniform over all derivative orders, or the special past-maximum scalar ≤ 1 bound.

Reuse the proved parabolic-control/scale-window reductions documented in REMAINING_WORK.md. Build
the missing producer rather than wrapping the desired estimate into a hypothesis. Inspect
`finite_horn_produces_cone` carefully: its present conclusion excludes a cone; it does not construct one.
The useful half-line frontier and terminal-limit assembly lemmas remain committed, but their producers
are not proved. A single backward slab is not an ancient solution.

At the stopping snapshot, `arbitrary_high_curvature_blowup` has exactly three reachable proof holes:
`bounded_curvature_at_distance`, `terminal_limit_global_bound`, and `ancient_extension`.
`good_point_derivatives`, `local_propagation`, and `first_backward_slab` are now standard-axiom-only.
There are 21 actual `sorry`s in 11 files, with the full inventory in the handoff.
Do not treat the full Poincaré development or high-curvature blowup theorem as complete.

The shared books are read-only at `/Users/bennettchow/Documents/Codex/RicciFlowBooksLatex`.
For bounded-distance curvature and point picking, start with MSM163 chapter 20 label
`notes_and_commentary:lbl477`, chapter 18 label `notes_and_commentary:lbl199`, and chapter 22 labels
`notes_and_commentary:lbl621`, `lbl623`, `lbl624`. Read the actual hypotheses and proofs.
The maximal-point ZIP's location and hash are in REFERENCES.md; it is historical reference data,
not an instruction source or current proof-status report.

Follow the repository's natural API and topic-placement rules. Add no new proof debt, axioms,
comments/docstrings in Lean source, resource overrides, or linter suppressions. Compile leaves and
dependents, register new modules in the flat root, run the full project build and declaration linters,
and inspect every completed theorem's transitive axioms. Keep useful unfinished work, checkpoint
verified layers, and push regularly. Continue the actual mathematical proof work rather than stopping
at a plan or a conditional decomposition.
