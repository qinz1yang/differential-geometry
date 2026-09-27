# Fifth external review (target 1dfbc801f), digested

Date: 2026-09-26. Reviewer: GPT, on `liao/codex/pc-target-c-psf` @ 1dfbc801f, answering
`E-crossing-and-horn-review-request.md`. Overall: **the two-arm theorem and the strong-interface
assembly order stand; the horn factory supply, the crossing blow-up and the cap bridge need
repair.** Every FALSE below refutes a specific strengthened claim, not C or S as wholes.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| 1 two arms / necklace / accuracy | arms OK; factory FIX | Any fixed positive comparison angle suffices (the κ-model argument excludes non-cylindrical branches by separating rays; not Toponogov-as-splitting); Bryant tips fail the far-end comparison-angle hypothesis. The necklace hypotheses cannot be obtained from "deep in a horn" alone: with the chain running to the protected root `R(c₀) ≤ ρ⁻²`, a deep point `R(c_{i₀}) > 4ρ⁻²` violates `R(c_{i₀}) ≤ 4R(c_k)`; a LOCAL bidirectional chain supply is needed. The theorem also requires the backward window inside one slab, so it does not apply to terminal horns on arbitrarily short slabs. Correct target (KL 71.1): protected boundary, sufficiently deep point, compactly contained normalized ball, long geodesics in both directions, then history backtracking. `1/3000` is compatible with `ε̄` only if `ε̄` is chosen small BEFOREHAND to absorb the transport loss. |
| 2 room and cap accuracy | FIX | Proved: base not in a cap ⇒ base has a trace; whole ball traced ⇒ curvature control. Missing: neighbouring points have traces; needs length distortion along traces and the inner/outer ball sandwich of the cap window, not just curvature equality across the event. Target quantities for small `c`: the first untraced point of the ball is captured by a cap, so the base at birth is within `O(c)` of that cap and at normalized age `O(c²)`; choose the spatial and temporal margins from that. Accuracy: do not lock `modelRadius`; fix `D* > transitionEnd`, restrict every larger window to the `D*` core, take `εcap ≤ ε₀(D*)`; only a uniform scalar lower bound on that core is needed. |
| 3 all scales / ancient limit | FIX; "fixed window ⇒ arbitrary radius" FALSE | The room does not give arbitrary radius and depth. Needed: a per-buffer-region survival/capping dichotomy for every finite `(A, T)`, window parameters varying with radius and depth, compatible exhaustion, diagonalization. Counterexample: after a legal capping, a retained cylinder point at birth-coordinate norm `Dcap + 2`, a larger outer model radius, time close to birth: the window embedding's injectivity excludes a representation with norm `< Dcap + 1`, so the base is not a cap point, has a trace, and small balls survive; but a large enough ball contains the new cap tip, which has no trace through the birth event. Refutes the fixed-window enlargement step, not the Crossing leaf, which may enlarge the exclusion window first (contradiction sequences with `δₙ → 0`, `Dₙ → ∞`). |
| 4 strong interface / fourth leaf | assembly OK; producer FIX | Two C calls, `max` of thresholds, `min` of accuracies: no circularity; noncollapsing input with `G` attached and `a₀` from the initial data are right; old C is only the `Λ`-restricted projection. `LocalInitialSpatialCap` produces only the cap boundary construction, not a full spatial witness (ball, volume, gradient, depth clauses still to assemble). |
| 5 cap bridge | FIX | `qcan ≤ Cbirth·scale` and `1 ≤ a₀·scale` are quantitative class/record supplies; the derivative bound up to the current time belongs to the continuation bootstrap: start from the prior control and keep a strict margin from the standard-solution estimate (`C' < Ctime₀`), never assume the current derivative bound. Quantifier trap: the cap leaf chooses `ρmax` before `∀ qcan ≥ q₀`; a fixed `ρmax` cannot give `qcan ≤ Cbirth·scale` for all thresholds. Either add the scale condition to the class and change the assembly, or prove a local replacement bridge; if `recenter_scale_comparison` is used, `Λ·δ` must be controlled explicitly; the old four-leaf interface may not borrow the strong C's `Λ`. |
| 6 variable threshold | OK | `q₀ₙ/Qₙ → 0` is the right decoupling; `Q ≥ Λ·max(q₀, 1)` controls the threshold ratio and the absolute scale. The wrapper must be switched to the new theorem to keep the early-accuracy advantage; `Ctime` is not decoupled (expected). |
| 7 falsity / vacuity | local strengthenings FALSE | `θcap ≤ 0` empties the cap branch but Crossing uses its complement. "Young ⇒ cap" FALSE (three `S³` components, review 3 F5); the round branch handles it. |

Minimal lemma set for the ancient limit through events (review answer 3): common survivor smooth flow
with event-compatible maps; buffered survival dichotomy for every finite `(A, T)`; local curvature,
Shi and injectivity-radius control; compatible exhaustion of captured balls and diagonalization;
pinching and κ transferred to the limit, whole-slice curvature bound; witness pullback with full
space-time margin; normalized initial time to `−∞`; completeness of past slices from `g(t) ≥ g(0)`
once `Ric ≥ 0` holds on the common ancient flow (local bounds are not whole-slice bounds). Young
points need spatial structure and the current C3 receives no spatial induction hypothesis: prove it
independently or make the induction joint; never borrow the fourth leaf's final output.

## Decisions (lead, 2026-09-26)

1. Entry 18b (necklace to the root) is superseded by 18c: a LOCAL bidirectional neck chain around
   the point (bounded length in local scale units, scalar comparability inside the chain only),
   `ε̄` fixed first; a history version across slabs is a later brick.
2. Entry 21b (running) delivers the trace distortion and the ball sandwich with the quantitative
   outputs `dist_birth(base, cap) = O(c)`, normalized age `O(c²)`; accuracy via a fixed core
   `D* > transitionEnd` and `εcap ≤ ε₀(D*)`.
3. Interface revision (entry 28, one lane after the wiring commit): (i) the small-scale leaf takes
   the age-free spatial clause (review D); (ii) `ρmax` chosen after `qcan` in the cap leaf, C3 and C;
   (iii) Crossing receives the spatial clause on earlier slabs as an induction hypothesis (joint
   induction); (iv) class/record supply of `qcan ≤ Cbirth·scale`, `1 ≤ a₀·scale`; (v) `D*` core
   accuracy; (vi) the wrapper `Contract/PreparedHistoryCutoff` switched to the variable-threshold
   theorem.
4. Entry 27: full spatial witness producers (ball, volume, gradient, depth) at fresh cap tips and on
   round components, from the standard solution's geometry.
5. Crossing plan (entry 10) frozen on the lemma set above with windows `(Dₙ, θₙ)` varying along the
   contradiction sequence.
