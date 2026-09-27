# Review H16 (single statement: `SpatialCrossingContinuation` (SX), C4 case (C) young spatial canonical neighbourhoods), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-p` @ 68e7a9253 (`DESIGN_C4_ASSEMBLY.md`), not compiled.
Overall: **FIX, not FALSE.** The positive-accuracy version's quantifier layout and the "no split by age" route can
stand; but C3's output cannot replace the full Crossing limit construction. The listed configurations test
intermediate transport lemmas and do not refute the final statement.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| no lower bounds on `C1…Cgrad` | OK, monotone relaxation | Enlarge inputs to `max 1 C`, raise the strong-witness age gate to `max 1 τmin`: this only weakens the needed hypotheses and does not force the final `Cx` to inherit them. In the source `Ctime Cgrad : ℝ≥0`, never negative. |
| only `ε ≤ εbar` | FIX | State the usual `0 < ε` and take `εbar` ≤ the cone-exclusion accuracy thresholds. `SpatialCanonicalWitness` carries `eps_pos`; for `ε ≤ 0` the conclusion can hold only by emptiness of the target set — missing positivity is not a counterexample by itself, but the emptiness proof may not be omitted. |
| `Cx` depends on `ε` only | OK | The κ-solution canonical-neighbourhood supplier chooses constants before quantifying κ; take finer accuracy and reserve transport margins. BUT the written `∀ B ε, ∃ Cx` still allows dependence on `B`: to force "ε only" put `∀ B` AFTER `∃ Cx`. |
| window order and C3 | order OK; substitution limited | `Dcap, θcap` after `θ, κ` legal; `θ = τmin` needs `τmin > 0` (else `max 1 τmin`). C3 should enter as an independent input `∃ η₃ > 0, OutputsOn η₃`, then choose `η ≤ η₃` not crossing the slab end. It patches the short right-hand window; it CANNOT by derivative bounds alone give cross-event survival, completeness, or the global curvature bound of the ancient limit. |
| just after an event / near a cap / age in `(θcap, 1)` | this argument must stay | `¬CapWindowPoint` ≠ far from caps: it may only mean the cap's normalized age exceeds `θcap`. Distinguish cap age from `R(t − a)`; the contradiction sequence needs `θcapₙ ↑ 1`, then the standard solution's terminal curvature blow-up + trace curvature bounds control the captured age. Merely enlarging `Dcap` is not enough. |
| many close events | not a counterexample | No uniform event spacing needed, but for every point of the common ball one must prove crossing of ALL intermediate events with estimates independent of the event count; iterating a single short-window dichotomy once does not give arbitrary depth. |

`whole` branch: distinguish "restrict" from "push forward". Restricting an ambient whole witness to an open `U` can
fail; but if B8 already produces a genuine whole witness ON `U`, its domain is the compact connected component of
the base point in `U`; manifold components are open, compact images are closed in a Hausdorff ambient, so after
push-forward along the open embedding it equals the ambient base-point component. Three `S³` need not all enter
`U`; only the base point's component is handled. One may not claim "does not contain the whole base component"
while holding that whole witness.

Ball capture scale must be uniform: `ρₙ = Aₙ/√Rₙ`, `rₙ ≤ Cx/√Rₙ`; hence `Aₙ > 4Cx` gives `2rₙ < ρₙ/2`, eventually
true along `Aₙ → ∞`. This refutes an unconditional "any small `U` transports" lemma, not the expanding-common-ball
route. Use the radii RESCALED BACK to the original flow.

Decision (lead): SX cleared for proof with the fixes: `0 < ε`, `εbar ≤` cone thresholds; `∃ Cx` BEFORE `∀ B`;
`max 1 C` / `max 1 τmin` relaxation; C3 as `∃ η₃ > 0, OutputsOn η₃` input with `η ≤ η₃` inside the slab; keep the
`θcapₙ ↑ 1` age-control argument (cap age ≠ `R(t − a)`); cross-ALL-events tracing with event-count-independent
estimates (= B5/B13 machinery, not one dichotomy); `whole` via push-forward of the on-`U` witness; capture with
`Aₙ > 4Cx` in original-flow radii. Statement to be re-elaborated by the proof lane with these deltas and recorded.
