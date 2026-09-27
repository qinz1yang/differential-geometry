# Review H18 (single statement: the depth-1/5 `HistoryStrongNeck` predicate; "1/5 suffices for §4.3 and removes S2e"), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-r` @ 563ea9bfd (`HistoryStrongNeck.lean`, `TruncatedNeck.lean`, SP1 log), not compiled.
Overall: **definition OK; fixed depth 1/5 suffices in place of §4.3's unit-depth input; S2e's "extend beyond the
record's left end" obligation is gone; but whole-tube survival and the higher-order comparison across the surgery
seam are NOT thereby done.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (1) degenerate witnesses | OK; mind the existential | `∃ z, z.val = y` excludes an empty survivor domain; the neck chart must contain the whole `S² × (−ε⁻¹, ε⁻¹)`. `first = k` needs `t − time k ≥ 1/(5R)`; an earlier `first` must satisfy all real slab-metric equalities and `IsSolutionOn`. The cylinder reference's time evolution is fixed and the comparison controls time jets, so no "almost static model" can fake it. BUT `∃ W` only strengthens the CHOSEN neck witness: where a cap can be chosen no strong neck need be supplied (not "any spatial neck must be strong"). |
| (2) §4.3 and the cylinder conclusion | OK, rewrite the iteration proof | Take effective step `θ₀/(2R_max)` leaving a fixed inner margin. One must prove UNIFORM curvature control on a finite target window so the steps do not sum to a finite total; "each step positive" is not enough. Completeness, splitting and canonical-type exclusion still have to be transported. Hamilton–Ivey limit nonnegativity needs no depth exactly 1; cone exclusion's strong maximum principle needs only a positive time window; Shi may consume a fixed fraction of it. Cylinder rigidity comes only AFTER the ancient limit (original §4.3 also does not conclude "cylinder" from a line on one slice). |
| (3) S2e constants | OK, with premises | `λ ≥ N/2` also uses `Λδ ≤ 1/2` (not automatic from the bare record); `R ≥ λR_Q/2` needs the second-order comparison tolerance small enough; the existing scalar comparison theorem supports that factor. |
| (4) old points cut to 1/5 | OK, no accuracy loss | `StrongNeck.time_domain` already guarantees the full window (no `τmin ≥ 1` needed); the source uses `1/5 < 1` for interval differentiability of the jets, then `ofStrongNeck`, `restrictOpen`, keeping the accuracy and order of `ε`. This really uses `CanonicalBefore`'s strong-neck data; a purely spatial hypothesis would not do. |

Arithmetic: with `N = r⁻²`, `t = T + τ/λ`, under the smallness premises and `R_Q ≥ 1`: `R ≥ λ/2 ≥ 1/(4r²)`,
`t − θ₀/R ≥ T − r² + (1 − 4θ₀)r²`; so `1/5` gives the uniform margin `r²/5`, `1/4` only non-strict inclusion. This
is the threshold of the present crude bound, not a geometric necessity. Strictly, it is the PRE-surgery part of
the window that lies in the incoming certified range; the whole window lies in `[T − r², t]`.

(5) Two boundary configurations: a newborn cap point with `R(t − T) < 1/5`: `first = k` violates (i) and an earlier
`first` has no survivor preimage — so the scalar inequality + time inclusion alone do NOT produce a
`HistoryStrongNeck`; one must still prove "a cap can be chosen" or whole-tube survival (SP2's cap-witness route
does exactly this at cap-window points). A non-round but nearly round `S²` short-time Ricci flow × `ℝ` has a line
and satisfies fixed-accuracy short-window neck comparison but is not a cylinder — it refutes skipping the ancient
limit step, not full §4.3.

Acceptance wording (reviewer): drop S2e's "extra left extension" obligation; keep SP2's whole-tube survival,
same-common-flow and cross-seam-jets obligations; no record-structure change for this window shrink.

Decision (lead): predicate accepted at θ₀ = 1/5. For the consumer (SC3/T4′): effective step `θ₀/(2R_max)`;
uniform curvature control on each finite target window (not step positivity) — X4a-style bootstrap on the
traced common flow; cylinder rigidity only after the ancient limit (T3A-2 → limit → SC2's line ⇒ strong neck).
SP2's cap-witness route covers the newborn-cap boundary case (item (5)).
