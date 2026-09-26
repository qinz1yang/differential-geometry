# Review H15 (single statement: X4d-Σ with P1/P2/P3 as engine), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-o` @ b33ef2860 (`DESIGN_X4D.md`), not compiled.
Overall: **TRUE under the repository's full `Σ`; quantifier order `∀ A D ∃ C ∀ σ ∀ᶠ n` correct; `C` needs no
dependence on `σ` or `T*`.** The abbreviated statement must keep the full `Σ`'s `hrec`, the common pinching
clause and `Rₙ > qcanₙ` (the last is not implied by the two scales tending to infinity separately).

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) truth, quantifiers | TRUE | Choose B3e constants, enlarged window and comparison tolerances from `A, D` and the fixed background constants first, then let `n` grow. For fixed `σ < 0`, eventually `0 < v < t₀ₙ` and `Rₙv = Rₙt₀ₙ + Rₙ(tₙ − t₀ₙ) + σ → ∞`; only the starting index depends on `σ`. |
| (b) P1 binders | OK, list must be completed | `:20`'s derivative threshold is `qcan`; taking the local `θcap = Θ = 1/2` is legal (do NOT pass Σ's parameter tending to 1). Also supply explicitly: `IsCanonicalCutoffRecordFamily`, slab initial-metric match, `EventSlabsDerivative`, current `DerivativeBoundBefore`, a real `BackwardPointTrace` with its birth-point equation, and two positive comparison tolerances `ε, η`. The theorem needs the target time strictly inside the slab; initial Hamilton–Ivey and the scalar floor are indeed only at `initialMetric 0`. |
| (c) X4a anchors | sufficient | X4a's `hRP` binder quantifies over all `A, D` and anchors; using only fixed `A*, D*` inside adds no requirement. Our conclusion is stronger: one `C` passes to the limit time by time; nonpositive `A, D` covered by positive enlargement. |
| (d) later cut-in | excluded | `:20` outputs an embedding of the WHOLE specified window into the final survivor domain (not a local chart near the anchor); its survival step uses first loss + survivor trace to exclude partial cut-ins = KL §74 dichotomy. Surgeries OUTSIDE the window remain allowed; do not strengthen to "the whole component is never cut". |
| (e) age in (1/2, 1) | no age gap | B3e needs only `0 < θ`, so `θ = 1/2` works; take `D₁` covering its returned `Dcap`. BUT "age > 1/2 relative to some old cap" ≠ `¬CWP`: the point may have a NEWER birth trace. The case split must be on the full existential predicate. |
| (f) rebase threshold | OK | `q = max qcan qs`, `Cq = max 1 Cs` gives `q ≤ Cq·Rₙ ≤ Cq·R(w)`; B3e's three scale gates from `R(w) ≥ Rₙ → ∞`, `R(w)·v ≥ Rₙ·v → ∞`, `ε√R(w) → ∞`. Its ball-radius parameter should be `A_B = 2D√A'`, not `D`. |

Corrections to carry into the bricks:
- **P2/P3 constant order:** take `Lc` first as the standard solution's radial comparison constant independent of
  `D₂`, then `r > 2·D·Lc·√(2A')`, `D₂ = D₁ + 1 + r`; then `λ ≤ 2A'Rₙ` makes the capture radius exceed `2D/√Rₙ`.
  Apply P2 to the composite embedding `F = backwardSurvivorIncomingMap ∘ Ξ` into the actual slice, with a
  first-exit argument on a compact sub-ball to exclude outside shortcuts (`:20` provides this composite and the
  normalized pulled-back metric).
- **`R_Q ≥ 1` is NOT an output of `:20`.** The source gives a uniform `c* > 0` with `R_Q ≥ c*/(1 − τ)`; use it and
  replace the `2` by `2/c*` (do not bet on the normalization being exactly 1).
- **Event-time step, no quantifier swap:** fix a large `n` first, prove the same constant on a small right
  neighbourhood of `v`, then use the `A+1, D+1` margins and a right limit; do NOT argue "for each fixed σ′
  eventually" and then let `σ′ ↓ σ` inside a fixed `n`. The strict margin `v < t₀ₙ` suffices for the former.

Decision (lead): X4d-Σ, P1 and X4 are cleared for proof with these corrections (P1s must supply the full `:20`
binder list; P3 via `c*`; P2 on the composite embedding with `Lc` fixed before `r`; case split on the full
`CapWindowPoint` existential; B3e ball radius `2D√A'`; event-time step by right neighbourhood at fixed `n`).
