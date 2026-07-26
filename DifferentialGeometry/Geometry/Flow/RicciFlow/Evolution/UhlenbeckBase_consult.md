# GPT Pro consultation — Uhlenbeck base `∂ₜRm` route (Lean 4 / Mathlib, Hamilton 3D)

I am formalizing Hamilton's 3D positive-Ricci theorem in a large Lean 4 / Mathlib project.
Do NOT write Lean code first. Validate the STRATEGY and point me to the shortest correct route;
I suspect I may be over-engineering the current step.

## Big picture / where this sits

- End goal: `ham3_main` (compact 3-manifold, `Ric>0` ⇒ round-sphere convergence under normalized
  Ricci flow).
- Pillar A = long-time existence: the black box `extends_of_rmBounded`
  ("`|Rm|≤K` on `[0,T)` ⇒ the flow extends past `T`"), proved via Bernstein–Bando–Shi (BBS)
  derivative estimates `|∇ᵏRm| ≤ Cₖ K / t^{k/2}`.
- BBS rests on the curvature reaction–diffusion equation
  **`∂ₜRm = ΔRm + Rm∗Rm`** (Hamilton's evolution of the (0,4) Riemann tensor). In the code this
  is the predicate `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`:
  `∂ₜR_{ijkl} = ΔR_{ijkl} + 2(B_{ijkl}−B_{ijlk}+B_{ikjl}−B_{iljk}) − ricciDrift_{ijkl}`,
  with `B_{ijkl}=g^{pr}g^{qs}R_{ipjq}R_{krls}` and `ricciDrift = R_i^pR_{pjkl}+…` (4 terms).
  This is the ONE remaining un-proved geometric theorem gating the whole pillar.

## What is ALREADY built (sorry-free unless noted)

1. **Time-side assembly is done**: `∂ₜ∇ᵏRm` for a solution at every level `k`
   (`nablaKRm_timeDeriv_of_solution`), with the connection evolution `∂ₜΓ`
   (`christoffelEvolution_of_solution`) genuinely derived from the PDE `∂ₜg = −2Ric`. The
   downstream Uhlenbeck pullback `∂ₜRm04 → ∂ₜ(ι^*Rm)=Δ_D(ι^*Rm)+2B` and the iterated-tower
   `∂ₜ∇ᵏRm` machinery are BANKED and CONSUME `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`
   as a hypothesis.
2. **Ricci evolution (traced)**: `∂ₜRic = ΔRic + Rm∗Ric` is fully proved (Lichnerowicz route via
   differentiated contracted Bianchi + Ricci identity).
3. **Scalar evolution**: `∂ₜS = ΔS + 2|Ric|²` is proved.
4. **3D curvature algebra**: the Weyl=0 / Kulkarni–Nomizu decomposition `Rm04 = KN(Ric,S,g)` is
   present (`RiemannFromRicci.lean`); I just added the **basis-free metric-form** version
   `rm04_kn_gform`: `Rm04(X,Y,Z,W)=R(X,Z)g(Y,W)−R(Y,Z)g(X,W)−R(X,W)g(Y,Z)+R(Y,W)g(X,Z)
   −(S/2)(g(X,Z)g(Y,W)−g(Y,Z)g(X,W))` for arbitrary vectors. Also `RicciControlsRm.lean`
   (`|Rm|≲|Ric|` in 3D).
5. **A-half of the Uhlenbeck base** (alternative, off the route below): `realizedRmBase_timeDeriv`
   gives `∂ₜRm04` already, but in an *un-reduced* `∇²Ric`-expanded form.

## The strategic decision I want validated

Two routes to `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`:

- **(General)** the standard Hamilton derivation: differentiate curvature, then second Bianchi +
  curvature commutators to turn `∇²Ric` into `ΔRm + Rm∗Rm`. This is the UN-TRACED (rank-4, 4 free
  indices) analogue of the ~1250-line traced Ricci-Lichnerowicz proof. Big. (Deferred in my plan.)
- **(3D algebraic — my chosen primary)** since `ham3_main` only needs dim 3 where Weyl=0:
  differentiate the KN identity `Rm04(t)=KN(Ric(t),S(t),g(t))` using the already-built
  `∂ₜRic`, `∂ₜS`, `∂ₜg=−2Ric`; because `∇g=0`, `Δ` passes through the `⊙g` so
  `ΔRm04 = KN(ΔRic,ΔS,g)` for free; the leftover reaction is then a FINITE dim-3 ALGEBRAIC
  identity `= 2B − ricciDrift`, with NO Bianchi/commutators (those are already inside `∂ₜRic`,
  `∂ₜS`). `rm04_kn_gform`'s conclusion is basis-free, so I evaluate at fixed coordinate-frame
  vectors and differentiate in a fixed frame (no moving-frame issue).

## Current position + planned next steps (3D route)

- ✅ B3a: `rm04_kn_gform` (basis-free metric-form KN), done + axiom-clean.
- B3a′: discharge `RiemannFromRicci3DTraceDataAt (g t)(Ric t)(S t)(Rm04 t)(orthonormal basis_t)`
  for the SOLUTION at each regular `t` (curvature symmetries via
  `algebraicCurvatureSymmetries3_…_of_leviCivita_realizes`; 3D Ricci/scalar trace relations;
  orthonormal basis per `t`; a known `−Ric`/`−scalar` sign bridge between the "displayed" and
  geometric conventions).
- B3b: apply `rm04_kn_gform` at fixed coord-frame `e_a,e_b,e_c,e_d` ⇒ scalar identity in `t`;
  differentiate (product rule, built `∂ₜRic`/`∂ₜS`/`∂ₜg`).
- B3c–e: substitute evolutions; match leftover `= 2B − ricciDrift` (finite dim-3 algebra);
  package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`.

## Relevant files

- `Geometry/Flow/RicciFlow/Evolution/Uhlenbeck.lean` — target predicate
  `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`; pullback
  `uhlenbeckCurvatureEvolution_of_solution_components`.
- `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean` — KN decomposition + my
  `rm04_kn_gform`; `RiemannFromRicci3DTraceDataAt`. Also `RicciControlsRm.lean`, `CurvatureAlgebra.lean`.
- `Geometry/Flow/RicciFlow/Evolution/Ricci/Lichnerowicz.lean` — proved `∂ₜRic`.
- `Geometry/Flow/RicciFlow/Evolution/Scalar/*.lean` — proved `∂ₜS`.
- `Geometry/Flow/RicciFlow/Evolution/Connection/{MetricCovDerivProducer,Rm13DerivProducer,NablaKRmTimeDeriv}.lean`
  + `Evolution/UhlenbeckBaseProducer.{lean,md}` — time-side assembly + A-half + B3a entry + the full plan.
- `Geometry/Flow/RicciFlow/Basic/Core.lean` — `IsSolutionOn` / `MetricVariationEquationOn` (`∂ₜg=−2Ric`).

## Questions

1. **Is the 3D algebraic route the right call** (shortest correct path to the dim-3 instance), or
   is the general Bianchi route actually safer/standard and I'm cutting a corner that will bite?
2. **Is there an even shorter overall route for `extends_of_rmBounded`** that avoids the full
   `∂ₜRm` evolution — e.g., in dim 3 running BBS on `Ric`/`|Ric|` directly (given `|Rm|≲|Ric|`)
   and the already-proved `∂ₜRic`? Would that re-architect less than finishing `∂ₜRm`?
3. For B3c–e, **will the dim-3 algebraic match actually close** to exactly
   `2(B−B+B−B) − ricciDrift`? Any sign/normalization traps (the `−Ric`/`−scalar` displayed-vs-
   geometric convention; the `B`-tensor index pattern; the `1/2 S` term)?
4. Cleanest way to discharge `RiemannFromRicci3DTraceDataAt` for the moving solution (B3a′)?
5. **Sanity check**: am I over-engineering? Given the downstream already consumes the Uhlenbeck
   base as a hypothesis, is finishing it the right priority now, or should I assemble the rest of
   the pillar first and leave `∂ₜRm` as the last black box?

Please: classify the strategy (sound / risky / replaceable), name the smallest next lemma, and
flag the failure signal that should make me abandon the 3D route for the general one.

---

## UPDATE (2026-06-09): route executed; STUCK on one `2|Ric|²` convention in the reaction match

Steps 1,2 + the B3b time-derivative are PROVED + axiom-clean. Realization discharge
`traceData_can` (gives trace data with `−Ric`/`−scalar`) is banked. The remaining crux is the 3D
reaction match. I tested it as a self-contained orthonormal `Fin 3` `ring` identity (g = δ,
`rm04 = KN(R)`). The `ring` machinery WORKS (KN trace `Σ_k rm_{ikjk} = −R_{ij}` closes). But the
full reaction identity is **off by exactly `2|Ric|²`** and I cannot find which convention is wrong.

I verified these forms are EXACTLY as the project defs state them (read precisely):
- KN (from proved `solution_rm04_kn_field`, geometric `Ric`/`S`):
  `rm04_{abcd} = −R_{ac}δ_{bd} + R_{bc}δ_{ad} + R_{ad}δ_{bc} − R_{bd}δ_{ac} + (S/2)(δ_{ac}δ_{bd} − δ_{bc}δ_{ad})`.
- `uhlenbeckBTensorInFrame` (g=δ): `B_{abcd} = Σ_{e,f} rm_{aebf} rm_{cedf}`.
- `riemann04RicciDriftInFrame`: `drift_{abcd} = Σ_p (R_{ap}rm_{pbcd}+R_{bp}rm_{apcd}+R_{cp}rm_{abpd}+R_{dp}rm_{abcp})`.
- target RHS `= roughLapRm04 + 2(B_{ijkl}−B_{ijlk}+B_{ikjl}−B_{iljk}) − drift_{ijkl}`.
- scalar reaction `Q_S = 2·ricciNormSq = 2|Ric|²` (confirmed: scalar evo RHS = `roughLapS + 2|Ric|²`).
- B3b reaction (from proved `solution_rm04_timeDeriv_kn`, with `∂ₜg=−2Ric`):
  `b3bReac_{abcd} = 4R_{ac}R_{bd} − 4R_{ad}R_{bc} + S(−R_{ac}δ_{bd} − δ_{ac}R_{bd} + R_{bc}δ_{ad} + δ_{bc}R_{ad})`.

My claim (which fails by `2|Ric|²`): with `roughLapRm04 := KN(ΔRic, ΔS, δ)` (diffusion split via
`∇g=0`), the reaction is `KN(Q_Ric, Q_S, δ) + b3bReac = 2(B−B+B−B) − drift`, where
`Q_Ric_{ij} = −2·(Σ_{kl} rm_{ikjl} R_{kl}) − 2(R²)_{ij}` from `lichnerowiczRHSInFrame`
(`= roughLapH − 2 Σ_{kl} rm04_{ikjl} hRaised_{kl} − ricciLeft − ricciRight`, `hRaised=R` orthonormal).

Test results (single component `(0,1,0,1)`, explicit symmetric `R`, `ring`):
- with `Q_Ric` curv-action sign `−2`: messy mismatch.
- with `+2`: **clean `LHS − RHS = 2|Ric|²`**.

QUESTIONS:
1. Where is the `2|Ric|²`? Likely candidates: (a) is the diffusion split `ΔS` independent, or does
   `ΔS = trace(ΔRic)` introduce a `|Ric|²` when combined with `∂ₜg` in the trace? (b) is `Q_Ric`'s
   `ricciLeft+ricciRight = 2(R²)` correct, or is it `−2`/different? (c) sign of the `lichnerowiczRHS`
   curvature-action contraction relative to the geometric `rm04`?
2. Give the corrected `Q_Ric` (and/or `roughLapRm04`) so the `Fin 3` identity closes.
3. Confirm `roughLapRm04 := KN(ΔRic, ΔS, δ)` is the right diffusion choice (or the correction).

GitHub (push to offsyn): files `Evolution/UhlenbeckBaseProducer.lean` (steps 1,2,B3b),
`Evolution/Ricci/Lichnerowicz.lean` (`lichnerowiczRHSInFrame`), `Evolution/Uhlenbeck.lean`
(`uhlenbeckBTensorInFrame`, `riemann04RicciDriftInFrame`, target predicate),
`Evolution/Scalar/RmTrace.lean` (scalar evo), `Curvature/DimensionThree/RiemannFromRicci.lean`
(`rm04_kn_gform`).
