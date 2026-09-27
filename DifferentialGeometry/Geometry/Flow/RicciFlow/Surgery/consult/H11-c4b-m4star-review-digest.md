# Review H11 (single statement: M4★, spatial canonical witnesses on the standard-solution window, C4 case (B)), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-k` @ 5a91c963d (`DESIGN_C4B.md` §2 M4★, §0, §3), not
compiled. Overall: **M4★'s statement holds and `Cw` can be chosen before `Θ`; the proof design is FIX and is
not a delivered proof.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (1) constants before `Θ`, old points | OK | Fix B8's `H = 1`; choose `δ, τ′, Θ₃` first, then `Cw = max(C_old, 1000·C_std(Θ₃))`, none depending on `Θ`. Folding the uniform scalar comparison `R_S ≥ R_Q/2` into the tolerance makes every `T ≥ Θ₃` an old point. L6e's `τQ` precedes `Θ` and allows the age equality; B8 builds the witness on `S` itself, avoiding its non-uniform buffers. |
| (2) uniform quantifiers | OK, merge parameters fully | Enlarge the inner radius for the whole ball and the neck-chart window FIRST, then feed L6e to get ONE `D` (never swap `D` afterwards); `N` = max of the needs; `e` = min of L6e's, the scalar comparison's and the post-reference-conversion tolerances. The transport tolerance is chosen from the SOURCE constant `C`, not the later-quantified target `C2`. `e` may degenerate as `Θ ↑ 1` but is uniform in `(Q, T, z, C2)`. |
| (3) existing supply | partial | L6e, B8, `toSpatial`, 27c at `Θ₃` (margin-free) and the uniform reference conversion exist. M1a (margin production), M2 (comparison assembly), M4 (uniform transport) are bricks to PROVE; the old "witness first, tolerance later" lemmas cannot stand in. |
| (3) `m = 1/20` arithmetic | holds, two roundings fixed | Neck: `9.45 < 10√(10/11)` and `16√(12/11) < 17.55` (`≈ 16.711455`, not `≤ 16.71`). Tip: do not use `0.995` as a lower bound of `√0.99`; use the code's `α ≥ 0.9`, `β ≤ 1.1`: normalized depth `≥ 10079`; the outer bound `< 13ρ/7` from the definition of `r`; with `ρ′ = 20ρ/21` the inner ball radius is `1.05ρ′ = ρ`, the outer `< 1.95ρ′`, other radius conditions kept. |
| M4 hidden supply gap | FIX, repairable | `SpatialOrderedNeckChain` has NO "centres inside the tube" field, so the in-domain curvature bound cannot be invoked from it: use `capTubeHasNeckChart` to rebuild the chain as the `[0,1]` SINGLE-neck chain of that neck, whose centre is in the tube. M4 need not keep the original chain; M4★ needs no strengthening. |
| (4) counterexamples / boundaries | none refute M4★ | Exact inner/outer ratio 2 is excluded by compact domain + open outer ball; families approaching 2 only show margins cannot be made uniform after the fact. Depth equality blocks direct transport of the original cap data, but the strengthened producer excludes it. `T·R_S = τ′` is an old point; the open time window may start at 0. `‖z‖ → r` is fine; `‖z‖ → D+1` violates the inner-window condition; `D` must still be enlarged for the whole ball and the neck-chart window. |

Decision: proof lane C4B2 for M1a, M1b, M4, M4★ with these corrections (single-neck chain rebuild in M4; `D`
once via L6e; tolerance by source `C`; the `α/β`-based margins with `ρ′ = 20ρ/21`); M5 after M2/M3/G (C4B1).
