# Reviews H2 (measurability of the minimizing domain) and H3 (closed-start extension), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-h` @ 9f9b7d94d (`DESIGN_C2_ASSEMBLY.md` §1(a),(c), §5.2).
Overall: both routes have valid proofs; no counterexample under the full hypotheses; M3's domain and
the G1c hook-up must not be skipped. Probes with `sorry` are not proofs.

## H2 — M / M1 / M3

| Item | Verdict | Condition |
|---|---|---|
| (a) Bernstein set, measurable hull | OK (meaning limited) | `lintegral` approximates from below by measurable simple functions on the whole space; for a Bernstein `K`, `∫⁻_K 1 = 1` but `∫⁻_K 1_K = 0`. A measurable hull keeps the restricted measure but cannot extend a comparison or injectivity valid only on `K`. G7 rightly demands `MeasurableSet K`. |
| (b) `K` relatively closed in `U` | OK | Needs `U ⊆ historyLExpDomain` and finite-action competitors on ALL of `U` (M3). Then `K = {Z ∈ U : ↑A(Z) ≤ c(fZ)}` with `A` continuous, `c` u.s.c. in the endpoint (M1): `↑A(Z) = lim c(fZₙ) ≤ c(fZ) ≤ ↑A(Z)`. No minimizer subsequence, no weak-l.s.c., no Arzelà–Ascoli. |
| (c) statements | provable; supply to complete | `regularizedExtendedAction_historyLCurve_eq_historyLAction` has `hZ ∈ historyMinDomain`: the version on the whole exp domain must be added (M3). Event-boundary limits are not counterexamples: a crossing landing on the non-regular boundary is not in `U`. |

M1 proof: at a finite-cost endpoint take an ε-optimal finite-action competitor, perturb its
positive-length first-stage tail by a cutoff coordinate perturbation fixing all event nodes and the base;
finite action + scalar floor + local uniform positive-definiteness give `L²` velocity control, so the
perturbed action tends to the original; at cost `⊤` u.s.c. is automatic; `A` continuous in `Z` from the
locally jointly smooth family with a fixed finite time partition. H4's image identity and the truncation
nesting do NOT give measurability; `ReducedVolumeTruncation`'s `hclosed` is a separate assumption.

## H3 — E / E2a

| Item | Verdict | Condition |
|---|---|---|
| (a) phase convergence on a compact stage | OK | E2a's `hmetric` on a compact physical tail `[a, a+η]` gives `λg* ≤ g(t) ≤ Λg*`, `|Ric| + |∇R| ≤ C`; with `∇_s V = 2s²∇R − 4s Ric♯V`, `e = |V|²` satisfies `|e'| ≤ C(1+e)`: Gronwall bounds the velocity, metric comparison makes `γ` Cauchy, then the ODE in a chart gives the velocity limit — a genuine `TangentBundle` phase limit. |
| (b) joint `C^∞` family near `Z` | OK; hook-up FIX | G1b's phase flow `Ψ` (two-sided open interval, equation on the legal side) with the seed `σ(Z) = (γ_Z(c₀), V_Z(c₀))` at `c₀ < v` close to the end gives `β(Z, s)`; ODE uniqueness for `s < v`, `IsHistoryLGeodesicOn`'s endpoint continuity at `s = v`; `f(Z) = β(Z, v)` smooth. API gap: G1c's `Ico 0 v ⊆ lRegularizedDomain` on ONE flow does not fit multi-stage tails whose base time is not in the first-stage flow: use G1b's arbitrary phase seed directly (or a positive-parameter-seed G1c); H3b's `hend ∈ Ioo` cannot be dropped in the old open domain: build a new closed-start open-set package. |
| (c) event endpoint vs time 0 | same | Both use only the post-surgery/initial side of the stage; `β` past `v` is an extension, never the real history (fresh caps have no predecessor). |
| (d) counterexample | none under full hypotheses | Without compactness the flat punctured example fails; E2a alone gives existence of a phase limit, not that it projects to a prescribed `γ(v)` — the history's endpoint continuity supplies that. |

Decisions: proof lanes for (M1, M3, M) and (E2a, E, the closed-start open-set package) with these
exact routes; both unconditional.
