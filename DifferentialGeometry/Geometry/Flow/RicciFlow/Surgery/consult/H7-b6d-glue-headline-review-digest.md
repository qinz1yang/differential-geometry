# Review H7 (single statement: B13, the composed B6d-glue headline), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-i` @ 02e85b47a (`DESIGN_B6D_GLUE.md` §0–§2), not compiled.
Overall: **the conditional composition route of B13 is viable; "Crossing can already supply every
hypothesis" is FIX** (two supply gaps). B13 is still an elided design signature.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) F-a/F-b vs the old `hEreg` | supply FALSE; old conditional theorem not refuted | The old headline explicitly ASSUMES `∀ s ≤ 0, ∀ᶠ n, s ∉ E n`; Crossing's before-clauses cannot supply data at the base time, and a fixed negative time may always be an event. Wording fix: a POSITIVE-width sliver is what makes `E n` infinite; when `tₙ = t₀ₙ` that reason fails but `0 ∈ E n` still. |
| (a) time shift to `G(s)` | OK, hinges on finishing B7 | Fix `s, K, p`, choose `k` with time margin; B8 gives `‖φₙ*hₙ(σₙ) − G(s)‖_{C^p(K)} ≤ L_{k,p,K}|σₙ − s| + o(1)`, so `s = 0` and event times are handled without assuming `C^p` time continuity of the limit at 0. "Each slab smooth" is NOT uniform Lipschitz: B7 must deliver uniform Shi jets, the reference-metric conversion and the closed-endpoint identification. |
| (b) parameters and before-clauses | OK | Shrink `ηₙ` FIRST, then pick the counterexample point; the sliver theorem gives `0 ≤ Rₙ(tₙ − t₀ₙ) ≤ 1/(n+1)`. `Cq = 1`, `qcanₙ < Rₙ`, `qsₙ ≤ Cs·qcanₙ`; shrinking `εbar ≤ epsW` outside is legal. Only `v < t₀ₙ` witnesses/derivatives are consumed: no F-c circularity; demanding `SpatiallyCanonicalOn` would be illegal. |
| (b) "all hypotheses suppliable" | FIX: two open | ① `hnc` asks κ-noncollapsing for ALL `v ≤ tₙ`; Crossing gives only `NoncollapsedBefore … t₀` (and the terminal version): add an independent short-interval noncollapsing transfer across the sliver, OR restrict B6b′'s input. ② `htraced` must be produced independently: MAXWINDOW §3.2b step 1 still calls B3e at `tₙ` (= F-g); B7/B13, which depend on `htraced`, cannot be used to supply it. |
| (c) F2 constant, F-e | OK, mind the factor 2 | With Crossing's `C ≥ 1` the window radius is strictly below `1/e` for the stated `qW`, `k`-free. From B7(vii) get a scalar upper bound `Bₖ`, then rescaled curvature-operator lower bound `−1/(2(k+1))` gives `Ric ≥ −h/(k+1)`; integrating `∂ₛh = −2Ric` gives `h(0) ≤ e²·h(s)`. The tail index may depend on `k` without affecting `qW`. Clamp `C` to `max 1 C` in B13's signature to meet B11's constant lower bound directly. |
| (d) counterexample (old interface) | supply counterexample only | `Rₙ = n`, `tₙ − t₀ₙ = n⁻²`, `tₙ − aₙ = c/n`, `0 < c < θ`, a far event at `aₙ`: `E n ⊇ [−1/n, 0] ∪ {−c}` — finite after removing the sliver, but `0, −c` always exceptional; no subsequence restores `hEreg`. Not a counterexample to B13 under its full hypotheses. |

## Lead's decisions (2026-09-26)

1. Keep the time-shift route of B13; `C` clamped to `max 1 C`.
2. Gap ①: restrict B13's `hnc` to `(v : ℝ) < t₀ n` (what Crossing supplies) and add ONE limit-level
   brick NC0: for a smooth solution on `Iic 0` (or `[−T, 0]`) that is κ-noncollapsed at every time
   `s < 0` (balls with `|Rm| ≤ r⁻²` on `P(x, s, r, −r²)` have `vol ≥ κ r³`), the same holds at `s = 0`
   (for `s < 0` the approximant time `tₙ + s/Rₙ < t₀ₙ` eventually since `ζₙ → 0`; at `s = 0` shrink the
   radius to `r' < r`, compare `B_s(x, r')` with `B_0(x, r)` under the curvature bound on the parabolic
   neighbourhood, let `s ↑ 0`, `r' ↑ r`). This replaces the "short-interval transfer" at the approximant
   level, where the sliver carries no data.
3. Gap ②: `htraced` = the BASESLICE design (F-g) → then a proof lane for the base-case production.
