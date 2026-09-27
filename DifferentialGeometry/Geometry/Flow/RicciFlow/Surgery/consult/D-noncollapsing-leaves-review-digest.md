# Fourth external review (target 1dfbc801f), digested

Date: 2026-09-26. Reviewer: GPT, on `liao/codex/pc-target-c-psf` @ 1dfbc801f (Lean locked there; the
request file is at 1682df442, which differs only by the two request files), answering
`D-noncollapsing-leaves-review-request.md`. Overall: **no configuration satisfying the full
cutoff-class hypotheses refutes any of the four leaves**; the initial lower bound and the small-scale
leaf are FIX (their proofs need bricks the class does not yet make explicit), not FALSE.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| 1 `reducedVolume` | FIX | The object is right. The `limsup_{B→∞}` is eventually constant: finitely many compact stages give a common scalar floor `R ≥ −b` on the legal range, so cost, endpoint set and density are stable for large `B`; the density is `≤ (4πv²)^{-3/2} e^{bv²/3}`, so the integral over a compact slice is finite. Measurability of the endpoint set is a lemma still to prove. Configuration: post-surgery slab, `p` in the component of a new cap `U`, `T` before the next event, `v = √(T − s)`: `first = k = j`, ordinary minimizers, empty crossing quantifier, `U` of positive volume is integrated; but the cap birth points `(q, s)` are not in KL 78.11's `Y` (not a null set). So "identical to KL's `Y` at all times" is FALSE; the definition uses a **post-surgery one-sided endpoint convention**. Not a monotonicity counterexample. |
| 2 monotone | OK | True as stated, no class hypotheses; do NOT require the whole curve inside the retained cores (a curve may enter a horn that is later discarded and leave again). Mechanism: truncations of global minimizers are global minimizers, so the initial-velocity domains nest `Ω_{v₂} ⊆ Ω_{v₁}`; integrate the non-increasing weighted Jacobian. At a seam: `Dψ γ̇₋ = γ̇₊`, Jacobi fields and the Riemannian volume Jacobian must match so the weighted density has no upward jump; `exists_survivor_solution_across_event` supplies the local smooth Ricci-flow seam; the history `L`-exp, the minimizing domain and the change of variables are still missing. |
| 3 local upper bound | OK | `σ` may depend on `η` only. Parabolic rescaling to `r = 1` makes the small-velocity confinement, the interior gradient estimates and the volume comparison dimensionless; the `ρ` in the existing single-flow theorem is an API artefact. The Gaussian tail must be estimated in initial-velocity space, never as "small density × whole-stage volume". A weaker `∀ η ρ, ∃ σ` interface would still assemble with `ρ = ε`. |
| 4 initial lower bound | FIX | `r₀ ≤ r` is the right division of labour. Two missing bricks: (a) a quantitative action barrier that also excludes low-action curves terminating at bad endpoints of intermediate surgeries (birth points have no crossing to check), with threshold above `3√τ` and `δ` shrunk (KL strengthens the barrier for the whole block); (b) a positive-volume endpoint block in the initial geometry whose global minimizers are regular — a single `l ≤ 3/2` point gives no mass. `MinimumTime:957` needs a common `X`, a compact `K` and an explicit escape inequality, so it is not the direct supply. `c` must NOT depend on `r₀` (assembly order chooses `c` before the small-scale leaf). |
| 5 small scale | FIX | Age filter gap: `R > qcan` with `R (t − a) < τmin` includes not only fresh cap points but unchanged old high-curvature points whose stage start `a` was reset by a distant surgery. Refutes the reasoning "every high-curvature point has a witness", not noncollapsing. Repair: the leaf takes the AGE-FREE spatial clause (C4 output, `SpatialCanonicalWitness`) beside the age-restricted one, and is proved by the trichotomy of the maximal controlled radius (Perelman I 4.2 / II 5.2): controlled up to `r₀` ⇒ Bishop–Gromov from the `r ≥ r₀` bound; control fails at `ρ ∈ (r, r₀)` ⇒ a point of curvature `≈ ρ⁻² > qcan` at distance `≈ ρ` with a spatial witness. `hasCanonicalWindow` is static; parabolic persistence is a separate bridge. C2 itself cannot be used to guarantee this leaf. |
| 6 assembly | OK | `κ = min(cσ³/(2C₀), κ₂)`; legal balls have `r > 0`, `r² ≤ t`, so the `v = 0` / `first > k` zero branches are never used. A fresh cap tip that cannot complete the backward trace violates the ball hypothesis, so it does not refute the leaves. |

## Decisions (lead, 2026-09-26)

1. Keep `reducedVolume`; record the post-surgery one-sided endpoint convention in `HANDOFF_C.md`;
   new brick (queue entry 26): eventual constancy of the truncation (`reducedVolume = value at
   B₀`), finiteness, measurability of `regularMinimizerEndpoints`.
2. Monotonicity and local upper bound statements stay; entry 22 (our own C2 tools) is refined to:
   history `L`-exp map on initial-velocity space through regular crossings, nested domains
   `Ω_{v₂} ⊆ Ω_{v₁}`, seam velocity matching `Dψ γ̇₋ = γ̇₊` and Jacobian continuity from
   `exists_survivor_solution_across_event`, weighted-Jacobian monotonicity, change of variables,
   Gaussian tail in velocity space, `σ = σ(η)`.
3. Initial lower bound: split into bricks 24a (quantitative barrier excluding bad terminal endpoints
   at intermediate surgeries, threshold above `3√τ`) and 24b (positive-volume initial endpoint block
   with regular global minimizers); `c` independent of `r₀`.
4. Small-scale leaf: interface edit (entry 25) adding the age-free spatial clause to
   `SmallScaleNoncollapsingThroughSurgery`'s hypotheses, after the wiring commit lands; proof by the
   maximal-controlled-radius trichotomy.
