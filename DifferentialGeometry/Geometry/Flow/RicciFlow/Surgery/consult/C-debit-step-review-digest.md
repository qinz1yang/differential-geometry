# Third external review (target af4bf4f5b), digested

Date: 2026-09-26. Reviewer: GPT, on `liao/codex/pc-target-c-psf` @ af4bf4f5b, answering
`C-debit-step-review-request.md`. Overall: **S is FIX, not FALSE**; the precision obstacle is real;
"S must receive κ from C2" is not forced by the literature.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| F1 precision direction | OK | `εcan ≤ ε₀/104000 ≤ ηstar/208000 ≤ δ/208000`; feeding the factory from C's `ε`-witnesses needs `δmax ≥ 208000·ε`, against the small-surgery direction. Refutes the factory's wiring, not abstract S. Perelman II 4.5 shrinks δ further; 5.1 has `δ̄ⱼ < ε²`. S may use ONE fixed small `ε̄`; compatible with C's `∀ ε`. |
| F2 Lemma 4.3 route | FIX | Deep-horn neck improvement is right, but 4.3 only improves the CUT position: split the factory into "coarse terminal decomposition + fine cutting neck"; do not demand fine CN everywhere. KL 69.6/71.1 need only pinching and canonical neighbourhoods (injectivity radius from canonical geometry); κ from C2 is admissible, not the only decoupling. |
| F3 `q₀`/`Ctime` | FIX | `q₀` deferral needs the variable-threshold sequence version (`q₀ₙ/Qₙ → 0`), not simple monotonicity (raising the threshold weakens the derivative hypothesis); `Ctime` chosen first. Existing dependence ≠ mathematical non-decouplability. |
| F4 terminal-threshold age gap | OK | Real; the derivative can be supplied independently; the "exactly five sites" count not independently verified. |
| F5 cutting-scale repair | FIX | Rejecting the scale repair is right (new caps at `h'` have curvature `h'⁻²`); but "young ⇒ in an evolved cap region" is **FALSE**: three `S³` components dying at `a < s < b`; at `a` the first is discarded with no cut (`no_cuts_discard`, `retained_meets_protected` with a high protected threshold, empty neck/cap fields); the third is a round shrinking sphere `R(t) = 3/(2(b − t))`, `∂ₜR = (2/3)R²`, `∇R = 0`; with `qcan < L`, `b − s = 3/(4L)`, `s − a = τmin/(8L)`: `R(s) = 2L`, `R(s)(s − a) = τmin/4`, so young points above `L` near `s` with no retained boundary, `CapWindowPoint` false. Refutes "young ⇒ cap", not S. These points carry the `round` alternative (the four alternatives are neck/cap/positive/round; a round sphere is not refuted by "no strong neck"). |
| F6 survivor-flow witness | FIX | Right direction: spatial data at the point plus history strong necks on the real `backwardSurvivor` `SolutionOn`, with charts to the stages, metric compatibility, the full backward window and a spatial buffer; the tip needs only spatial data; the selected cap tube's history strong necks must be proved separately. `HistoryParabolicBall` gives the common flow but not completeness. `capTubeHasNeckChart` is bound to the original flow: adapt the interface. Crossing's limit pullback gives a witness on the common history flow first, not a `CanonicalWitness G.flow`. |
| Q2 restated S | FIX | Reorder + κ alone still fails to feed the factory: age-restricted input cannot feed its age-free spatial classification. Take `Ctime` from `hcn B (1/22)`, then the working `ε`, merge the two calls' thresholds. C must keep a stronger joint output (κ, gradient, past slabs' CN), old C as its projection. The noncollapsing input must be `TerminalNoncollapsedBefore` with `G` attached, not `NoncollapsedBefore κ ε s` of the old horizon. The C2–C3 induction itself does not consume S. |
| Q3 short slabs | (c) | (a) raising the threshold gives a cut scale depending on `s − a`, no uniform debit; (b) FALSE (above); (c) sound and cheapest as a NEW age-free spatial CN interface predicate beside the old age-restricted witness; no library-wide witness replacement. |
| Q5 Crossing size | — | Do not assume 5–9k and do not rewrite compactness: reuse `IncompleteLocal`/`TracedTerminalCompactness` upgraded to all finite radii and backward windows with compatible exhaustions, then diagonalize; the real gap is the survival/scathed dichotomy per buffered region. Slabs can all be short: "find a long previous slab" is not a general exit. Spatial completion ≠ Ricci-flow extension (KL App. E distinguishes time-0 completeness from all-time completeness). |
| Q6 refutations | none | No configuration refutes S / C2 / C3a–c as wholes. `θcap ≤ 0` empties the cap predicate but Crossing takes the complement, so the assembly is not vacuous. `GradientBoundBefore`'s `R^{3/2}‖v‖_g` factor is right. |

## Decisions (lead, 2026-09-26)

1. Interface revision (queue entry 13, staged in NEW files so running lanes are not disturbed):
   define `SpatialCanonicalWitness` (time-slice data, four alternatives on `SpatialNeck`) with the
   projection `CanonicalWitness.toSpatial`; an age-free spatial clause `∀ (y, t), qcan < R →
   SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y`; a strong joint output
   `CanonicalNeighborhoodsThroughSurgeryStrong` (old clauses + gradient clause + spatial clause +
   κ-noncollapsing through `TerminalNoncollapsedBefore` with `G`), with the old C as a projection;
   S restated `∀ B Ctime, ∃ ε, …` consuming the spatial clause, the age-restricted strong witnesses,
   the derivative clause and the κ input; the assembly consumes the strong C.
2. Entry 14 (deep-horn neck improvement) keeps its κ hypothesis; a κ-free variant from canonical
   geometry is optional later.
3. The `q₀` sequence version of `ProspectiveNeckSurvival` is a separate brick (entry 16).
4. Crossing: plan the bricks on the collaborator's local tools (all radii, all windows,
   diagonalization, per-region scathed dichotomy), not on localizing `NormalizedSequence`.
5. `HANDOFF_S.md`'s cutting-scale bullet is retracted.
