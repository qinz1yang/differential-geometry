# Review H1 (single statement: round components in the small-scale leaf), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-g` @ 6ffb82257 and `codex/pc-target-c-psf`
@ 9126abc30, answering the prompt on `DESIGN_SMALLSCALE.md` failure 1 (round witnesses carry no volume;
lens spaces `S³/ℤₙ` collapse at every scale).

| Item | Verdict | Content |
|---|---|---|
| (a) components simply connected | OK, exists | `rfs_simply_connected_history` (`Topology/Ancestry.lean`): stage-0 components simply connected ⇒ all stages' components simply connected (via `SmoothCutCapTransition.child_simplyConnected`, `capped_children_simply_connected`); from `initialIdentification_components_simplyConnected P₀ g₀ H.toHistory hH.1.some` under `[SimplyConnectedSpace P₀.Carrier]` (precedent `FiniteHorizonExtinction.lean`). `RetainedCoreHistory P₀` alone is not enough: the class's initial identification is needed. |
| (b) round ⇒ volume | OK, via rigidity | The model `Z` is compact with sectional curvature `1/6`; `U ≅ Z` (`source_eq`/`target_eq`) so `Z` is simply connected; Killing–Hopf ⇒ `(Z, h) ≅ S³(√6)`; the field `metric_bounds` (`½h ≤ Q f*g ≤ 2h`) gives `vol_g(U) ≥ 2^{-3/2} Q^{-3/2} vol_h(Z) = 6√3 π² Q^{-3/2}` (ε-independent). Proposed lemma `SpatialRoundComponent.volume_lower_of_simplyConnected`. No change to `requiresVolume`. |
| (c) literature | split | Perelman II §4.4 discards near-round quotients and §5.1 excludes them from the canonical list; KL Remark 73.3 keeps them. Our leaf is for the simply connected endgame only. |
| (d) counterexample | refutes only the static no-SC version | Round `S³/ℤₙ` with `C1 = 4`, `C2 = 1`, witness radius `4/√Q`: all fields hold, `Q^{3/2} vol → 0`; excluded by (a). |

Decision: add `[SimplyConnectedSpace P₀.Carrier]` to `SmallScaleNoncollapsingThroughSurgery` (and the C2
aggregate as needed; the strong/hext assembly already carries the instance); the round volume bridge is a
brick with a space-form-rigidity dependency (to be located or built). Closing failure 1 does not close
the leaf; the other bricks of `DESIGN_SMALLSCALE.md` remain.
