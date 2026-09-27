# Review H8 (single statement: BS5, the corrected application of B3e at the bad-point slice), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-j` @ 48aed2c67 (`DESIGN_BASESLICE.md` §2 BS5, §4), not
compiled. Overall: **BS5 (event slab) and its terminal counterpart are mathematically valid; they cover
only `a < t₀`, so the Crossing branch is not closed by them alone (Case II = BS6).**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) interior-slice route | OK | For the fixed history and bad point pick ONE `σ ∈ (a, t₀)` close enough to `t₀` (no limit). `SpatiallyCanonicalBefore` gives the witnesses on the slice `σ` directly; the other before-clauses restrict downwards. Two scalar/metric comparisons carry the bound to `t`; nothing is needed at `t₀` or on the sliver, no `C^p`. The terminal form keeps its extra pinching and `TerminalNoncollapsedBefore` inputs. |
| (b) constants | all OK | With `R = R(t, y)`: `R/2 ≤ Rσ ≤ 3R/2`, `σ ≥ t₀/2`, `gσ ≤ 2 g_{t₀}`; target ball ⊆ `Bσ(y, √(2e)A/√R)` ⊆ ball of radius `2√e·A/√Rσ`; scalar bound `(3Q_B/2 + 1/2)R ≤ (2Q_B + 1)R`; `Rσ·σ ≥ R·t₀/4` so `Λ = 4Λ_B`; `Cq_B = 2Cq`, `θ_B = θ/2` correct. |
| (c) ordinary inputs | OK | Take `q = qsₙ`, `Cq = Cs`, `ρ = ε`, witness constants `C1s, C2s`; the derivative clause by threshold relaxation `qcanₙ ≤ qsₙ`; noncollapsing up to `t₀` is Crossing's explicit hypothesis, not derived from the sliver; records, accuracy, order, radius, `Λ ≤ R`, `Λ ≤ ε√R` are eventually supplied by the sequence. |
| (c) `η` and cap exclusion | OK, with margins | Choose `η` from the whole-slice bound and uniform continuity BEFORE `y`; the metric `e`-comparison must be built into `η` separately (scalar closeness does not imply it). BS3 gives `¬CWP(t₀, Dₙ, θcapₙ − 1/(n+2))`; with `θcapₙ = 1 − 1/(n+2)` take `θ = 1/2` in BS5 and `θ_B = 1/4` at `σ`. |
| (c) `Λ ≤ R·t₀` | conditional OK | `Rₙt₀ₙ ≥ Rₙtₙ − 1/(n+1)`, so M7(c) `Rₙtₙ → ∞` is REQUIRED; the three `η` smallness conditions do not imply it. It must come from the uniform initial-time control of the cutoff class (initial data), a cross-`n` argument, not from fixed-history continuity. |
| (d) counterexample | old push-back FALSE; not a BS5 counterexample | One cap of scale `S` born at `τ`, a traced point in the window, `t₀ − τ = θcap/S < t − τ`: CWP at `t₀`, over-age at `t`, sliver arbitrarily short — so `¬CWP` cannot be pushed back with the same parameters; this violates BS5's `t₀`-exclusion hypothesis, so it does not refute BS5. `t₀ = a`: `(a, t₀)` empty, before-clauses vacuous; BS6 only. |

Decision: BS5 goes to proof with the stated constants (`θ = 1/2` / `θ_B = 1/4`); the supply table must list
the fixed positive cap-age margin, the metric `e`-comparison inside `η`, and M7(c); `t₀ = a` stays a separate
branch (BS6, review H9 pending).
