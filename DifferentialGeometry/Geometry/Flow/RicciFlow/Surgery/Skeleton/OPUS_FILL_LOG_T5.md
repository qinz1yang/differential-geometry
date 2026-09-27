# OPUS_FILL_LOG_T5 — bricks T4-def and T5 of DESIGN_B13 (2026-09-26)

Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`. No lake build, no git writes,
no committed file touched, `DifferentialGeometry.lean` untouched.

## Delivered

New file `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean` (174 lines), importing
only the committed `Contract/UniformDebitSurgeryStepOfFactory` (olean present, no scratch mirror
needed). Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`.

- `def FineCutNeckSupply (P₀) (g₀) : Prop` — verbatim §2 T4 (cap requirements `Rrad ζ₀ δ₀ ρ₀ m₀`
  chosen before `εc`, `Kfine` after `εc`, `p₀` universally after `Kfine`).
- `theorem uniformDebitSurgeryStepStrong_of_fineCutNeckSupply (P₀) (g₀)
  (hfine : FineCutNeckSupply P₀ g₀) : UniformDebitSurgeryStepStrong P₀ g₀` — verbatim §2 T5.

Proof = the body of `uniformDebitSurgeryStepStrong_of_long_slabs` with B12 + `hlong` replaced by
the supply, instantiated exactly as §2 lists: `ε := min εbar (min εF εcone)` (F*'s `η := eta`);
supply applied at that `ε` right after S's constants are introduced; `Dbig := max (max Dcap
(Dtrace+1)) Rrad`; `m := max (max mcap (⌈1000⌉₊+2)) m₀`; `accuracy := min (min εold εcap) ζ₀`;
`ηrecord = δbound := min (min δold δmax) δ₀`; `ρbound := min (min ρmax 1) ρ₀`; `Kfine` from the
supply at `εc := min εcut (1/4)`, passed to F* directly, then `fineCutNecks_of_le`. The pinching
function is no longer needed (the supply does not ask for it).

No binder had to move: the supply's `ε` is universal, so S's `ε` (chosen before `κ … a₀`) feeds it;
`Rrad` is available before F*'s `Dbig`; `Kfine` before F*'s `Kfine` slot.

## Checks

- `lake env lean` (2 threads, `-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`):
  0 errors, 0 warnings, 0 infos (first attempt hit a transient missing Mathlib olean while another
  lake was writing E:; retry clean).
- `#print axioms uniformDebitSurgeryStepStrong_of_fineCutNeckSupply`: `[propext, Classical.choice,
  Quot.sound]` (no `sorryAx`), checked on a scratch copy, removed.
- Names `FineCutNeckSupply`, `uniformDebitSurgeryStepStrong_of_fineCutNeckSupply` unique library-wide.

## Deviations / deferred

- Private helpers `exists_horn_cutoff_record_of_fineCutNecks_of_le`, `fineCutNecks_of_le`,
  `hasCanonicalCutoffRecords_of_le`, `exists_compact_volume_debit_of_incoming_eq` are reached by
  `open private … from …UniformDebitSurgeryStepOfFactory` instead of copying (the first is ~240
  lines). Deferred merge: move T5 into that file (and retire `_of_long_slabs`) when it is next edited.
- The private `SigmaCompactSpace G.terminalRegularOpen` local instance is copied (3 lines).
- The leaf corollary `uniformDebitSurgeryStepStrong := …_of_fineCutNeckSupply P₀ g₀
  (fineCutNeckSupply P₀ g₀)` is NOT added: `fineCutNeckSupply` (T4) does not exist yet and the name
  `uniformDebitSurgeryStepStrong` is the skeleton's sorry leaf in `Skeleton/PoincareEndgame.lean`.
  Once T4 lands, the skeleton body becomes exactly that one-liner.
- New module not registered in the root aggregate (lead's job).
