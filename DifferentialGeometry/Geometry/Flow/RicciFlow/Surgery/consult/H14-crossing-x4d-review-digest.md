# Review H14 (single statement: X4 with X4d as engine — bounded curvature at bounded distance about an arbitrary anchor, no ¬CapWindowPoint), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-n` @ 92abc53a7 (`DESIGN_CROSSING_ASSEMBLY.md` §2/§4), not compiled.
Overall: **X4's conditional assembly route stays; X4d as written is FIX (not proved, not FALSE): it drops several
inputs of the cap-window persistence lemma it cites.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) young standard cap curvature comparability | OK | For all standard solutions and `0 ≤ τ ≤ 1/2` the source has uniform `1 ≤ R_std ≤ C_{1/2}` on the whole space, so a sufficiently accurate second-order comparison gives `λ/2 ≤ R ≤ C'λ`. BUT `λ ≤ 2R_t(w)` must be proved through the EVOLVED comparison, not by citing the birth-slice scalar lower bound. |
| (a) X4d's supply interface | FIX | `CapWindowStandardComparison:20` also needs `δbound ≤ δ₀`, `m₀ ≤ modelOrder` (with `m₀ ≥ 4`), `q ≤ C_birth·λ`, `a₀·λ ≥ 1`, the initial Hamilton–Ivey region and the scalar lower bound. X4d states only `modelOrder ≥ 2`, radius and accuracy. A supply gap, not a history counterexample. |
| (a) later surgeries at the same scale | must prove whole-window persistence first | One anchor's `BackwardPointTrace` ≠ survival of a whole nearby ball. Route: first get the survival embedding of the ENLARGED model window, then a first-exit argument shows the current metric ball is captured by it (KL §74: small δ excludes a local cut-in, or the whole block disappears; anchor survival excludes the latter). H9's known-non-CWP centre cannot be swapped for an arbitrary centre. |
| (b) anchors, bootstrap, constants | OK, weaker version exists | Base-centred `A(s) = T*Q₀/(s+T*)` diverges, so `C(A(s), D)` gives no uniform bound. Only the far-field escape anchors and the bootstrap's FIXED `A*, D*` need the bound, not all anchors. Distance error `(20/3)√(2T*Q₀)√T*` is right, but the whole `[a, 0]` bound must exist before the call. "No Harnack" is inaccurate: the distance lemma uses finite-left-endpoint Harnack internally (not ancient `R_t ≥ 0`). |
| (c) time quantifiers and events | OK, keep margins | Must be `∀ A D, ∃ C, ∀ s, ∀ᶠ n`, with `n₀ = n₀(s, A, D)`. After avoiding the countable event set, recover all times by the `A+1, D+1` margin and limit continuity. X4's conclusion at ACTUAL event-time trace points needs W1's cross-event uniform convergence, not just "avoid events". |
| (d) W1 depth change | OK, on inner windows | `β_k = (k+1)/(k+2)`: Shi's time margin `(1−β_k)τ_k > 0`, constants may depend on `k`; with `τ_k = T*β_k` the inner depth `T*β_k² ↑ T*` exhausts. The κ check still needs `[σ − r², σ] ⊂ [−τ_k, 0]` and spatial capture; the unconditional "any scale" reading at infinite depth may NOT be kept. |
| (e) counterexample | none found | No history satisfying all of `Σ`'s hypotheses was constructed. After whole-window persistence, far-field transport and the uniform anchored bound, the bootstrap excludes the early-end blow-up; before those bricks, "slice-wise bounded" may not be promoted to "uniformly bounded down to −T*". |

Cheapest repair (reviewer): prove X4d in its `Σ`-SEQUENCE version, not the wider single-history version. `Σ.hpar`
gives `δₙ → 0`, order and radius → ∞, accuracy → 0; `hscale` gives `λ ≥ (n+1)·qcan`, initial metric fixed. These
supply the persistence inputs, and the choices can precede the fixed backward time `s`, keeping `C(A, D)` uniform in time.

Decision (lead): X4d → redesign as the Σ-sequence statement with the full persistence input list (δ₀, m₀ ≥ 4,
C_birth, a₀, Hamilton–Ivey, scalar floor), whole-window persistence brick (enlarged window survival + first exit),
evolved comparison for `λ ≤ 2R_t(w)`, hRP restricted to far-field escape anchors with fixed `A*, D*`, event-time
trace points via W1's cross-event convergence, κ check windows inside `[−τ_k, 0]`. One statement to review H15
before proof. X0/X2/X5c/X5d (XA1) unaffected.
