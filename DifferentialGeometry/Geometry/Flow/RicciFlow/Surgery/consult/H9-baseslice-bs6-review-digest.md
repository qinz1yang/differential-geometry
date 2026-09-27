# Review H9 (single statement: BS6, the ball bound at a post-surgery stage start), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-j` @ 48aed2c67 (`DESIGN_BASESLICE.md` §2 BS6), not
compiled. Overall: **with B3e as a delivered input, BS6 is TRUE; the design's proof route is FIX. Keep the
signature; enlarge the existentially quantified `Dcap`/`Rrad` and bypass the recentred B3e.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) F3/F4 | OK | In the slab after `a`, a point without a preimage under that event lies in its cap; `scale·(t − a) ≤ Sη ≤ θcap` plus the capture radius makes it a CWP, so the bad point has a preimage. This controls only the centre, not the whole ball. F4 is right: same-slab continuity cannot cross the event. |
| (b) compact convergence | sufficient, after controlling paths | `old_compact` makes `oldTerminal '' univ` itself a compact subset of the terminal regular region containing the retained-side boundary of the cut ball; uniform `C²` convergence holds on it directly (no need for the design's step 3 whole-ball regularity). The convergence time may depend on the history; paths entering the new cap still cannot be pulled back. |
| (c) recentring | the call is invalid, and unnecessary | `CapWindowPoint.mono` and BS3 keep the spatial point fixed; they cannot transfer `¬CWP` from `y` to a new centre on the cut ball; cut-ball points at `a` are age-zero CWPs anyway, and `¬CWP` at a pre-surgery recentred point is not obtained. Step 5 cannot call B3e that way. |
| (d) near-cap configuration | not a BS6 counterexample | Points close enough to the true cap boundary are inside the enlarged window, violating `¬CWP(a)`; near the outer edge of the exclusion window with `R(y) ≍ λ` (cap scale) the true cap is still `≈ Dcap/√λ` away, so it cannot also be within a fixed normalized radius. |

Repair (reviewer): prove the ball never touches the cap. With `R = R_t(y)`: first apply the pre-surgery
B3e with an enlarged radius and fix its constants; suppose an `a`-length path shorter than `√e·A/√R`
first touches the cap at `p`; before touching it lies in the retained side, pull it back and use the
compact convergence: `R_a(p) ≤ C_B·R` and `λ/2 ≤ R_a(p)`, hence `λ ≤ 2C_B·R` (no recentring at `p`). Then
take `Dcap > max {D_B, c₀ + c₁·A·√C_B}`, enlarge `Rrad`, shrink the accuracy: the scaled ball capture of
`WindowRadius` captures `y` into that cap window, contradicting the age-zero `¬CWP`. So the whole ball
avoids the cap, can be pulled back entirely, and the two sliver hypotheses carry the bound to `t`.
Constant order: `C_B` first, then the enlarged window; no circularity; the `λ/R → ∞` candidate
counterexample is excluded by the scale bound at the first touching point.

Decision: BS6 proof lane with exactly this route; BS6's signature unchanged.
