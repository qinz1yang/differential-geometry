# TameNemytskii.lean — R1τ ruling item 4 (abstract two-orientation form)

## What this file is

Small-lemma-frontier **item 4** of the R1τ ruling
(`Geometry/Flow/RicciFlow/ShortTime/UNIF_N_PRO_RULING.md`), built ABSTRACTLY
per the №12 design decision in `ShortTime/UNIF_EXISTENCE_PLAN.md`: the
second-order two-orientation tame bound is taken as a HYPOTHESIS (the shape
ruling item 2 / the deTurckLie-threeArm machinery will instantiate), the
carriers follow the `LowScaleCutoff.lean` pattern (`X` top scale, `H`
admissibility scale via `ι : X →L[ℝ] H`, `Y` codomain), and the conclusion is
the `timeL2` contraction estimate parallel to the committed
`nemytskiiMixedForcingMap_dist_le`
(`Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:381`).

## Declarations

- `timeL2_norm_le_of_ae_three_bound` — three-term time-`L²` Minkowski bound
  (sibling of the committed two-term `timeL2_norm_le_of_ae_mixed_bound`).
- `nemytskiiTame_time_bound` — the two-orientation splitting estimate
  `‖w − w'‖ ≤ K(1+Minf)·‖u − v‖ + K·Dinf·‖u‖ + K·Dinf·‖v‖`.
- `nemytskiiTame_time_bound_L2` — `M₂`-substituted headline shape
  `K(1+Minf)·‖u − v‖ + 2·(K·Dinf·M₂)`.

## Constant-discipline audit (planner, 2026-07-24)

PASSES the calibrated stop-signal discipline: the leading `‖u − v‖`
coefficient `K(1+Minf)` carries NO top-scale radius and NO
`‖·‖_top × ‖·−·‖_top` product; the ambient top norms `‖u‖, ‖v‖` enter only
against the lower-scale difference bound `Dinf` (the allowed tame cross
term).  `max → sum` relaxation is the ruling-permitted factor 2.

## Provenance and verification status

Authored by the item-4 executor session that the user stopped before it
could verify or report (file mtime 2026-07-23 21:09); swept into commit
`126aaebda` unverified.  Planner statement-level acceptance done 2026-07-24
(this note).

VERIFIED GREEN 2026-07-24: one mechanical repair was needed (line 116:
`add_le_add_right step2 _` resolved to the left-addition shape on the
ENNReal goal; replaced by `add_le_add step2 le_rfl`), after which
`lake build +...TameNemytskii` completed successfully and the axiom audit
returned exactly `[propext, Classical.choice, Quot.sound]` for all three
declarations.  Ruling item 4 is DONE.

## Consumers / next

- Ruling item 5 (fixed-horizon representative) instantiates these lemmas as
  a drop-in.
- The concrete instantiation of `htame` comes from the item-2 lane
  (threeArm/deTurckLie engines) once the field-level bounds are assembled.
