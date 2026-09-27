# Review H13 (single statement: T4′ `FineCutNeckSupplyStrong` with `HistoryStrongNeck` / `StronglyCanonicalBefore`), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-m` @ 542fe7232 (`DESIGN_S_SUPPLY.md` §0–§2), not compiled.
Overall: **T4′ is OK as a conditional theorem and the two definitions are sound; the CN → strong-class
supply is FIX — S is not closed by this.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| definitions | OK | `StrongNeck` maps the whole neck tube into `backwardSurvivorDomain` and the common flow agrees with the real slabs, so it is not "only the centre survives". `StronglyCanonicalBefore` is "∃ a suitable `W`", NOT "every spatial neck witness upgrades". |
| (1) `Kfine` independent of `p₀` | OK, conditionally | The strong class supplies Perelman §4.1's cross-surgery strong necks directly; the records' `curvature_preserving` passes uniform pinching from the initial data; §4.2 cone exclusion → §4.3 repeated extension need no fixed-`p₀` cap-window comparison. "`p₀` unconstrained" ≠ "history unconstrained". |
| late-age caps / just-glued points | not counterexamples; proof wording FIX | "entering the cap region ⇒ the chosen `W` is a cap" is false. Correct: at each fixed backward depth, capture the WHOLE canonical neighbourhood (scale-bounded diameter) inside a large ball of the splitting limit, exclude the cap and compact-component alternatives, then trigger the strong neck. Do not exclude caps from a finite-length `ε₁`-neck alone; do not conflate `CapWindowPoint` with the cap alternative. |
| (2) parameter order | OK, with a substantive premise | `ε₁ → εbar(ε₁) → ε → CN constants, δmax, εcap` has no inherent cycle. K1 must be UNIFORM IN κ (a fixed-κ compactness statement is not enough). Splicing/transport must reserve an error budget smaller than `ε₁` up front; `εbar` may not depend on cap parameters or `εc` at the end. |
| (3) C3b | FIX: ≥ 3 obligation groups | The standard solution's "full strong neck / truncated neck" dichotomy; whole-tube survival and quantitative splicing across the gluing time; transport on the comparison chart. `IncomingBackwardNeck` gives a nominal depth `r²`, not the target point's exact `R⁻¹`. Splicing onto the old slab still needs the high-curvature threshold, the cap-exclusion trigger and chart compatibility re-proved; "the old slab has the strong clause" does not do it. |
| (3) C3c / C4 | FIX, route viable | C3c: two new geometric obligations (K1, history E3) while keeping its `Dcap`/`θcap` freedom. C4: the old-point embedding `first := k`, choosing a `W` compatible with the strong property, carried through `Before/On` and the continuation induction — not a mere output-predicate swap. |
| explicit error | S1 FALSE as read | "Neck witnesses of all ages are full strong necks on the standard solution" fails: far cylindrical region of the standard solution at small `t > 0` has a spatial neck with `R ≈ 1` but `t − R⁻¹ < 0`, violating `StrongNeck.time_domain`. Perelman §2 Claim 5 keeps the "truncated neck back to the birth time" branch. Minimal fix: full strong neck when the window fits in the standard solution's lifetime; otherwise a truncated comparison PLUS a proof that the whole chosen tube avoids the modified region and connects to the incoming window ("centre outside `capRegion`" is not enough). |
| T3A-2 supplier | not a supplier | `TerminalScalarAncientLimit.lean:475` ASSUMES arbitrary-length windows `S n j`, `hslab`, `hneckRegular`; it does not produce them: stepwise extension, event-endpoint handling and the uniform subsequence are new proofs. |

Decision (lead): recommend adopting option A (Perelman's architecture; B/C/D dead per DESIGN_S_SUPPLY), staged:
(i) design the interface change exactly (the two predicates, the strong class conjunct, the new S/CN leaf
statements and the composed extinction theorem) and send it as ONE statement to review; (ii) producer bricks
per leaf with the H13 obligations (C3b: full/truncated dichotomy + whole-tube survival + splicing; C3c: K1
uniform in κ + history E3; C4: old-point embedding + strong-compatible `W`), K1 uniform in κ; (iii) the §4.3
consumer in S. The existing spatial leaves stay as they are (the strong clause is additive). Owner decision
pending (interface change to the frozen skeleton, 6.7–13k+ lines).
