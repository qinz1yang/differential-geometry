# Second external review of the Poincaré endgame skeleton (target a9ec9ee7b), digested

Date: 2026-09-25 (evening). Reviewer: GPT, on the mirror `liao/codex/pc-target-c` @ a9ec9ee7b. The
reviewer did not compile. Each item below was checked against the Lean statements by the lead.

## Verdicts, checked

| Reviewer item | Lead's check | Action |
|---|---|---|
| OK: global backward trace = unscathed; crossed events lie in `(t − r², t]`, so the `Ioc` endpoint of C2 (E) stays; `r² = t − a` does not cross the bottom event; `eventCount = 0` handled by the terminal extension; `t₀ = a` needs the separate `H.NoncollapsedBefore … a`; a zero-cut event must discard something | Agrees with `HistoryParabolicBall.lean:75`, `CanonicalNeighborhoodInduction.lean:126-153`, the assembly | none |
| FALSE: an unconditional parabolic→spatial bridge at a fixed scale `ρ` with the same constant (flat `S¹_ℓ × S¹_L × S¹_L`, `T = ℓ²/100`: every tested parabolic ball has `r ≤ ℓ/10` and is Euclidean, but `Vol B(x, ρ) ≤ π ℓ ρ² < ρ³`) | Correct, and it does not hit the tree: Lane V's `exists_spatial_noncollapsing_of_parabolic_of_derivative_bound` (`SlabSpatialNoncollapsingBridge.lean:106`) concludes only for balls with `a ≤ τ − r²`, `c r ≤ ρ₀`, `r ≤ 1`, `qcan r² < 9`, under the derivative bound; on the torus `a ≤ τ − r²` forces `r ≤ ℓ/10` again, so nothing is claimed at radius `ρ`. Lane L's F1: the blow-up machinery only needs balls with `r² ≤ θ/R` at the window times, which lie inside the slab once the age is `≥ 2θ`. | none; but see the residual gap below |
| FIX 1: the young layer cannot all be handed to the standard solution (old points on an untouched component become "young" when another component is cut); `DerivativeBoundBefore` has no spatial gradient bound, so the backward-cylinder theorem of Lane B cannot be invoked at young high-curvature points; keep the unrestricted derivative clause | Correct. This is also why the lead's attempt (same evening) to move `τmin` after `κ` was reverted: at young unscathed points the derivative clause (with `Ctime` chosen before `κ`) needs bounded curvature at bounded distance, i.e. canonical structure in the young layer, i.e. the crossing blow-up. The reorder only moved the machinery from the witness clause to the derivative clause. | reverted; recorded in `HANDOFF_C.md` |
| FIX 1 brick: along a backward trace on `[u, t]` with the derivative bound on every slab and scalar agreement at crossings, `M ≥ max(qcan, R(γ(t), t))`, `Ctime M (t − u) ≤ 1/2` ⇒ `R(γ(v), v) ≤ 2M` on `[u, t]` | Provable by integrating `d/dt (1/R) ≥ −Ctime` on the pieces where `R > qcan`; the event count does not enter | next brick after Lane G |
| FIX 2: keep the quantifier order (`κ` before `qcan` in C2 as in KL 79.12; `C1 C2 τmin Ctime` before `κ phi` in C3); do not set `τmin := θ(κ)`; do not confuse the blow-up depth `θ(κ)` with the comparison time `θ_cap < 1` | Conclusion correct (see FIX 1). | order kept |
| FIX 2 (class): `recenterConstant ≥ 4` only; `δ_n → 0`, `Λ_n = (2δ_n)⁻¹` keeps `Λ_n δ_n = 1/2`, so "δ → 0 ⇒ comparison error → 0" fails; add a fixed bound `Λ` to the class, fixed before `C1 C2 τmin Ctime` in C3 and before `κ` in C2, chosen by S with `ε`; `a₀` must come from the fixed `g₀` via `curvature_preserving`, not as a free input | Correct as a parameter-consistency point (`CutoffParameters.recenterConstant`). | to add at the next interface revision |
| FIX 3: S chooses the cutting scale and the debit before `H`; slabs have no uniform positive length, so the cutting neck's normalized age `h⁻²(t − a)` need not reach `τmin` | Correct and independent of the order. A cap-induced singularity at `a + h²` gives cutting necks of age about `1` at scale `h`. Fix inside S: record the post-surgery curvature bound `≤ C h⁻²` in the class, get the slab length `≥ h²/(C·Ctime)` from the derivative bound, and cut at `h' = h/√(C·Ctime·τmin)` (uniform debit `h'³`); the age at the cut is then `≥ τmin`. | `HANDOFF_S.md` |
| Suggested: local route must feed the blow-up with PARABOLIC noncollapsing on the common flow for every finite `A`; or supply a spatial noncollapsing theorem for the whole class (Qi S. Zhang) independently, never as a corollary of C2 | Agreed; Lane L (follow-up) is assessing the parabolic-form refactor of `ClosedModelHypotheses.noncollapse`. | in progress |
| Fixture: asymmetric dumbbell `S³` neck pinch, one horn cut at time `a` keeping one side (`CutIndex = Unit`, `one_retained_side`), `eventCount = 1`, `horizon = a`, capped component continuing to `s > a`; check the new-cap derivative bound at `a + σ h²` | Not built. | later |

## Residual gap found while checking (lead, not the reviewer)

Even with Lane L's F1 weakening, `UniformKappaCanonicalThreshold.lean:224-262` feeds the model
theorem with `SpatiallyKappaNoncollapsedBelowScale S3 kappa 1`: spatial noncollapsing at every centre
and every window time at original radius up to `√(θ/R)`, i.e. curvature scale `R/θ`. The bridge can
only supply curvature scales `≳ qcan/9`. Bad points with `R ∈ (qcan, 9 qcan θ)` are therefore not
covered by the deep-inside route as formalized. Perelman's hypothesis is parabolic; the machinery
must consume the parabolic form (global in space, so recentering is unaffected). Assessment pending.
