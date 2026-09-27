# Review H19 (single statement: B9w, window neck-alternative transfer with the compactness third alternative), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-s` @ 820226675 (`OPUS_FILL_LOG_XP2.md` "F1 statements"), not compiled.
Overall: **B9w's mathematical statement holds and route F1 is viable; X4's SUPPLY of the approximant third
alternative is not acceptable as worded — add a "buffered path lifting and capture" lemma, not the too-strong
"every intersecting component survives".**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (1) B9w, compactness alternative | holds | View `Z = connectedComponent z` as a subset of the ambient manifold: compact, and open because `W` is an open submanifold and locally path connected. `hWF` gives `Z ⊆ F.target`; via `F.partialDiffeomorph` the preimage `A = F.symm '' Z` is open in the open source, hence in `P.M`; the inverse is continuous on the target, so `A` is compact hence closed; `x ∈ A`; connectedness gives `A = P.M`. A general continuous map is NOT enough — the open source and homeomorphism properties of the partial diffeomorphism are what is used. Window cover + monotonicity allow choosing large space and time indices simultaneously. |
| (2) distance clause, constant 4 | correct, but the original transfer's conclusion must be strengthened | Original B9 drops the distance, so it cannot be called directly. Its local transfer already has `G_s ≤ 2φ*h` and approximant scalar `r_j > a/2`, `a = R_s(x)`; lifting the connecting path inside the controlled ball gives `d_s(x,w) < √2·C2/√r_j < 2C2/√a < 4·max(C2,1)/√a`. The scalar factor 4 has its own lemma. Keep the distance estimate for the SAME neck centre, not merely "a centre exists in a big ball". |
| (3) pre-event slices | repairable; NOT "identical to terminal slices" | W1′ gives the pulled-back metric comparison on the survivor map, not a global distance comparison of the whole old slice. A short old-slice path may try to leave the image, but a first-exit argument WITH A STRICT BUFFER stops it (below). Case II is not a counterexample and no "all intersecting components survive" lemma is needed. |
| (4) X4a′ far field | complete with the remaining hypotheses | Noncompact case excludes alternative 3; alternative 1: `w = y`; alternative 2 gives `d(y,w) < 1` once `R_y > C²`, with `R_w ≥ R_y/C` — exactly the "nearby high-curvature neck" the old proof extracted from the witness; the small neck core / separation / ball-complement arguments need no witness. Time-0: noncompact via the neck-alternative scalar bound, compact via the maximum. Accuracy must satisfy `2α ≤ εfar` (merely `2α < 1/11` is not enough). |
| (5) counterexamples | refute the simplified reduction, not B9w | `K = S³` with the survivor image a proper open ball: "intersecting compact component ⇒ whole component in the image" is false and the ball's component is not compact — this is exactly what the buffer prevents. Round cylinder `S² × ℝ`: constant scalar yet noncompact, so "whole component bounded curvature" cannot replace compactness (not a counterexample to the new alternative). |

Buffered capture lemma to add (rescaled, source metric `g₀`): `W = B_{g₀}(p, k+3)`, `K ⊆ B_{ḡ}(f z, D)`,
`D = 2C1/√r`. W1′ gives `g₀ ≤ e²·f*ḡ`. If `d_{g₀}(p, z) + e·D < k + 3`, then any old-slice short path from `f z` to
`y ∈ K` has source length `< e·D` on the part that lifts; the lift stays inside a COMPACT closed sub-ball `⋐ W`, so it
can be continued and never escapes through the boundary of the survivor image; hence `K ⊆ f(W)`. This does not
presuppose the whole path lies in the image, so it is not circular.

Quantifier note: `hW` asks for every `k` and ALL `z ∈ closedBall(p, k+1)`; "for large `k`" does not discharge it. A
direct fix: raise the fixed threshold to `q ≥ e²·C1²` (then `r > q` gives `e·D < 2`, exactly the buffer between the
two balls); otherwise enlarge the buffer or change the interface to require only sufficiently large `k`.

Decision (lead): B9w cleared; XP2 must (a) strengthen the local transfer's conclusion to keep the distance for the
same centre; (b) prove the buffered capture lemma (strict buffer `e·D < 2`, threshold `q ≥ e²C1²` or an enlarged
buffer) for BOTH terminal and pre-event slices; (c) `2α ≤ εfar` in X4a′; (d) use the partial-diffeomorphism
facts (open source, continuous inverse) in the compactness step.
