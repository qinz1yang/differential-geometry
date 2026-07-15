# Uhlenbeck base `∂ₜRm04` discharge — plan (Lemma 6.1)

**Target.** Prove `Riemann04BTensorWithRicciDriftEvolutionInFrameOn Rm04 roughLapRm04 B ricciOneUp`
(`Uhlenbeck.lean:727`) for a Ricci-flow solution in the coordinate frame:
`∂ₜR_{ijkl} = ΔR_{ijkl} + 2(B_{ijkl} − B_{ijlk} + B_{ikjl} − B_{iljk}) − drift_{ijkl}`,
with `drift = riemann04RicciDriftInFrame ricciOneUp Rm04` (the four `R_·^p R_{p···}` contractions).
This is Hamilton's curvature evolution — the **un-traced** analogue of the built Ricci
Lichnerowicz evolution.

## Mathematical route (Morgan–Tian / Hamilton), mirroring the proven Ricci case

The Ricci case (`Evolution/Ricci/{Bianchi,Commutator}.lean`) factors as
`ricciVariationExpandedRHS` (the ∇²Ric form of `∂ₜRic`) **=** evolution RHS
(`ΔRic + Rm∗Ric`), the second equality via the *differentiated contracted Bianchi*
+ *Ricci commutators*. The (0,4) discharge factors the same way:

**Lemma A — variation/lowering (the `∇²Ric` form of `∂ₜRm04`).**
1. `∂ₜΓ^k_{ij} = −g^{kl}(∇_iR_{jl}+∇_jR_{il}−∇_lR_{ij})`  [`christoffelEvolution_of_solution` — DONE]
2. `∂ₜR^l_{ijk} = ∇_i(∂ₜΓ^l_{jk}) − ∇_j(∂ₜΓ^l_{ik})`  [`rm13Deriv_of_solution` — DONE]
3. Lower: `∂ₜR_{mijk} = g_{ml}∂ₜR^l_{ijk} + (∂ₜg_{ml})R^l_{ijk}`,
   with `∂ₜg = −2Ric` ⇒ the `−2R_{ml}R^l_{ijk}` drift contribution.
4. Substitute (1) into `g_{ml}∂ₜR^l_{ijk}` using `∇g = 0`:
   `= −∇_i∇_jR_{km} − ∇_i∇_kR_{jm} + ∇_i∇_mR_{jk} + ∇_j∇_iR_{km} + ∇_j∇_kR_{im} − ∇_j∇_mR_{ik}`.
   Call this `rm04VariationExpandedRHS` (a `∇²Ric` combination), analogous to
   `ricciVariationExpandedRHSInFrame`.

**Lemma B — Bianchi+commutator (the `∇²Ric` form = `ΔRm + 2B − drift`).**
5. `(∇_j∇_i − ∇_i∇_j)R_{km}` etc. = curvature commutators (Ricci identity) ⇒ `Rm∗Ric` terms
   [banked: `curvComm`, `second_bianchi`, the `tensor0S_ricciIdentity` used in the Ricci case].
6. The remaining `∇∇Ric` terms convert to `Δ R_{ijkl}` via the *differentiated second
   (contracted) Bianchi* `∇_pR^p_{ijk} = ∇_jR_{ik} − ∇_kR_{ij}` and `Δ = ∇^p∇_p`
   [banked general identities in `Geometry/Curvature/Bianchi.lean`: `second_bianchi`,
   `contracted_bianchi`, `contractOfSecond`; to be specialized to the moving solution].
7. Collect ⇒ `ΔRm04 + 2(B…) − drift`.

## Banked pieces to reuse
- `rm13Deriv_of_solution` (`∂ₜRm13`) — built this session.
- `christoffelEvolution_of_solution` (`∂ₜΓ`) — built this session.
- `solution_rm04LowersRm13At`, `rm13_apply_eq_rm04_raise` (`RmRaisingBridge.lean`) — lowering realization.
- `Geometry/Curvature/Bianchi.lean`: `second_bianchi`, `contracted_bianchi`, `curvComm`,
  `contractOfSecond` — the abstract (0,4) Bianchi identities.
- The Ricci-case templates `ricciVariationExpandedRHSInFrame`,
  `RicciContractedCommutatorsInFrame_of_tensor0S_ricciIdentity_lc`,
  `differentiatedContractedBianchiInFrameOnLocal_of_regular` — structure to mirror un-traced.

## Decomposition into Lean lemmas (effort: multi-session)
- A1: `rm04VariationExpandedRHS` def (the ∇²Ric combination) + sign bookkeeping.
- A2: `∂ₜRm04 = rm04VariationExpandedRHS` (lower `rm13Deriv` + `∂ₜg=−2Ric` product rule).
  Needs a time-derivative raise/lower bridge (`∂ₜ(g·rm13) = (∂ₜg)·rm13 + g·∂ₜrm13`) at the
  component level — the first genuinely new sub-theorem.
- B1: differentiated second-Bianchi for the moving solution (un-traced).
- B2: (0,4) curvature commutators (Ricci identity at rank (0,4)).
- B3: `rm04VariationExpandedRHS = ΔRm04 + 2B − drift` (assemble B1+B2).
- C: package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` from A2+B3, then feed the
  banked `uhlenbeckCurvatureEvolution_of_solution_components` → pulled heat form.

## STATUS — A-half of Lemma 6.1 DONE (2026-06-08, GREEN build 3716, axiom-clean target)
- ✅ **Brick 1:** `metricCompInFrame_timeDeriv` — `∂ₜ metricCompInFrame = −2·ricciCompInFrame`
  from `hS.equation`.
- ✅ **Brick 2 (the gateway realization, was the "missing API"):**
  `realizedRmBase_eq_curvCoeff_lower` — `Rm04_{m₀m₁m₂m₃} = Σ_p curvCoeff^p_{m₀m₁m₂}·g_{m₃p}`,
  by chaining `solution_rm04LowersRm13At` + `rm13_eval_eq_christoffelCurvCoord` + the metric
  flat (`dualToCotangent_apply_gen`/`tangentFlatLinear_apply_gen`, both `rfl`).
- ✅ **A2:** `realizedRmBase_timeDeriv` — `∂ₜRm04` in the expanded `∇²Ric` form, by the
  product rule `HasDerivWithinAt.sum`/`.mul` on Brick 2, with `∂ₜcurvCoeff = rm13Deriv_of_solution`
  and `∂ₜg = metricCompInFrame_timeDeriv`. (Lean: `HasDerivWithinAt.sum`'s `f'` is a
  higher-order metavar — give per-summand derivs explicitly via a `hterm` hyp; `.congr` needs
  `Finset.sum_apply` to match the sum-of-functions form.)

  **So `∂ₜRm04` is now ESTABLISHED** (the whole variation/lowering half). The RHS is the
  expanded `Σ_p (∂ₜΓ-covderiv difference)·g + curvCoeff·(−2Ric)` form.

## B — PRIMARY ROUTE (3D algebraic, via Weyl=0) — `ham3_main` only needs dim 3

**Why this route.** In `dim 3` the Weyl tensor vanishes, so `Rm04` is an explicit *algebraic*
function of `(Ric, S, g)` (Kulkarni–Nomizu). The `∂ₜRm04` evolution then follows by
*differentiating that algebraic identity* using the already-built `∂ₜRic`, `∂ₜS`, `∂ₜg` — **no
second-Bianchi / curvature-commutator re-derivation at all** (that work is already inside
`∂ₜRic`/`∂ₜS`). `ham3_main` only needs the dim-3 instance, so this is the shortest path.
*Tool is the 3D decomposition, NOT contracted Bianchi (which goes ∇Ric→∇Rm and cannot invert
the trace; only Weyl=0 makes the trace invertible).*

**Banked pieces (confirmed present):**
- 3D decomposition `Rm04 = KN(Ric,S,g)`: `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean`
  — `rm04Comp_displayedRiemannFromRicci3D_at` (orthonormal `Fin 3` basis):
  `R_{ijlk} = R_{il}δ_{jk} − R_{jl}δ_{ik} − R_{ik}δ_{jl} + R_{jk}δ_{il} − (S/2)(δ_{il}δ_{jk}−δ_{jl}δ_{ik})`,
  given `RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis`. Also `RicciControlsRm.lean`,
  `CurvatureAlgebra.lean`.
- `∂ₜRic = ΔRic + reaction` ✅ (`evol_ricci_lichnerowicz_...`).
- `∂ₜS = ΔS + 2|Ric|²` ✅ (scalarEvolution, tasks #8–10).
- `∂ₜg = −2Ric` ✅; `∇g = 0` ✅ (Levi-Civita) ⇒ **`Δ` passes through the KN `⊙g`**, so
  `ΔRm04 = KN(ΔRic, ΔS, g)` (diffusion term for free).

**Route (each step bounded, NO Bianchi):**
- ✅ **B3a DONE** (`rm04_kn_gform`, `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean`,
  GREEN build 3586, axiom-clean): the **basis-free metric-form KN identity** in dim 3,
  `Rm04(X,Y,Z,W) = Ric(X,Z)g(Y,W) − Ric(Y,Z)g(X,W) − Ric(X,W)g(Y,Z) + Ric(Y,W)g(X,Z)
  − (S/2)(g(X,Z)g(Y,W) − g(Y,Z)g(X,W))` for ALL vectors, from `RiemannFromRicci3DTraceDataAt`.
  Proof: lift the banked δ-form via `tensor0S_apply_eq_sum`+`sum_fin_four_fun`+`inner_eq_sum_repr3`
  + `Ric`/`g` expansions, brute-forced on `Fin 3` (`simp [Fin.sum_univ_three,…]; ring`).
  **FRAME WORRY RESOLVED:** the conclusion is *basis-free* — the orthonormal basis is internal to
  the proof, so at each `t` (with its own orthonormal basis) the identity holds for FIXED vectors
  (e.g. coordinate-frame `e_a` at `x₀`, `t`-independent). So differentiation in a fixed frame is
  direct; no moving-frame reconciliation needed.
- **NEXT — B3a′ (trace-data discharge):** for the solution at each regular `t`, build
  `RiemannFromRicci3DTraceDataAt (g t) (Ric t) (S t) (Rm04 t) (orthonormal basis at t)`. Banked:
  `algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes` (symmetries),
  the Ricci/scalar trace relations (3D), an orthonormal basis at each `t` (Gram–Schmidt). Sign
  convention: displayed `Ric`/`scalar` vs geometric — use the `−Ric`/`−scalar` bridge as in
  `rm04_firstTrace_einstein3_at`.
- **THEN B3b:** apply `rm04_kn_gform` at fixed coordinate-frame `e_a,e_b,e_c,e_d` ⇒
  `Rm04(t)(e_a,e_b,e_c,e_d) = KN(Ric(t),S(t),g(t))` (scalar identity in `t`); differentiate by the
  product rule.

### GPT Pro consult — VALIDATED (2026-06-08). Route is sound; refinements:

- **Stay on the 3D route.** It is the dim-3 specialization of Hamilton's evolution via Weyl=0,
  not a bad shortcut. Do NOT switch to general Bianchi (longer, duplicates the proved Ricci/scalar
  evolutions). Do NOT re-architect BBS around Ricci (replaceable mathematically, worse
  architecturally — needs a whole new ∇ᵏRic tower; downstream already consumes the Rm base).
- **THE trap = sign convention.** `traceDataOfFirst` produces `RiemannFromRicci3DTraceDataAt g
  (−Ric) (−scalar) Rm04 basis` (displayed-slot vs geometric). Isolate the sign in ONE wrapper.
- **Lemma sequence (revised, build in THIS order):**
  1. ✅ **`solution_traceDataOfFirst_at` = `traceData_can` ALREADY BANKED**
     (`ImprovedPinching/BookData.lean:275`): `traceData_can S horth : RiemannFromRicci3DTraceDataAt
     (S.base.metric t)(−(S.ricciAt t x))(−(S.scalar t x))(S.base.rm04 t x) basis` — only needs `S`
     + a `g t`-orthonormal `Fin 3` basis (realizations proven internally from Levi-Civita). Big
     de-risking: no realization discharge to build.
  2. ✅ **`solution_rm04_kn_firstTrace_gform_at` DONE** (`UhlenbeckBaseProducer.lean`, GREEN 3730,
     axiom-clean): `rm04_kn_gform (traceData_can S horth)` + `simp [ContinuousMultilinearMap.neg_apply]`
     + `ring` ⇒ sign-correct geometric KN for the solution:
     `Rm04 t x (X,Y,Z,W) = −Ric(X,Z)g(Y,W)+Ric(Y,Z)g(X,W)+Ric(X,W)g(Y,Z)−Ric(Y,W)g(X,Z)
     +(S/2)(g(X,Z)g(Y,W)−g(Y,Z)g(X,W))` (geometric `S.ricciAt`/`S.scalar`/`S.base.metric`).
     The sign bridge lives ONLY here; basis is invisible (basis-free conclusion).
  - ✅ **Step 1 DONE** `exists_orthonormalBasisAt` (`RicciControlsRm.lean`, GREEN, axiom-clean):
    `∃ basis, OrthonormalBasisAt g x basis` via `ricciEigenBasis3` at the ZERO Ricci tensor.
  - ✅ **Step 2 DONE** `solution_rm04_kn_field` (`UhlenbeckBaseProducer.lean`, GREEN 3730,
    axiom-clean): the `s`-pointwise geometric KN identity, basis hidden (uses step 1).
  - ✅ **Step 4 time-deriv (B3b) DONE** `solution_rm04_timeDeriv_kn` (GREEN 3730, axiom-clean):
    `∂ₜRm04(X,Y,Z,W)` = product rule on the KN field (Ric/scalar `∂ₜ` as hyps, `∂ₜg=−2Ric`
    internal via `hS.equation`). Lean: combinator derivative carries `Pi.neg`/`Pi.mul` atoms →
    `convert hd using 1; simp only [Pi.neg_apply, Pi.mul_apply, Pi.sub_apply]; ring`.
  - **REMAINING (the multi-session geometric core):**
    - **3. DIFFUSION SPLIT** `roughLapRm04 = KN(roughLapRic, roughLapScalar, g)`: needs the
      tensor-FIELD KN section identity (lift step 2 to `Tensor0SField` sections) + `∇²`-of-KN via
      `nabla0S_product_realizes` (twice) + `nabla_metric_zero` (`∇g=0`) + trace (`roughLap0STensor`).
      Substantial formalism-A computation.
    - **4 remainder. REACTION MATCH + PACKAGE**: substitute the Lichnerowicz Ricci evolution +
      scalar evolution (`∂ₜS=ΔS+2|Ric|²`) into B3b's `ricXZ'`/`sc'`; identify diffusion via step 3;
      match reaction `= 2(B…)−drift` to the SPECIFIC `uhlenbeckBTensorInFrame` (slot order `i?j?/k?l?`)
      + `riemann04RicciDriftInFrame` (4 one-up contractions, minus). 3D algebra: prove in an
      orthonormal `Fin 3` basis (g=δ, `ring`) → export tensorial → coordinate `FourComp`. Then
      package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`. Carries the Lichnerowicz
      regularity hypotheses.

### REACTION-MATCH `ring` — ATTEMPTED 3× (stuck on the convention/sign trap, 2026-06-09)
Tested the crux as a self-contained orthonormal `Fin 3` `ring` identity (R symmetric matrix,
`rm04 = KN(R)`, `B_{abcd}=Σ_{ef} rm_{aebf}rm_{cedf}`, `drift=Σ R·rm04` (4 terms),
`Q_Ric = −2·Σ rm_{ikjl}R_{kl} − 2(R²)`, `Q_S = 2|Ric|²`, `b3bReac` from B3b):
claim `KN(Q_Ric,Q_S,δ)+b3bReac = 2(B−B+B−B)−drift`.
- ✅ `ring` machinery WORKS over `Fin 3` (verified the KN trace `Σₖ rm_{ikjk}=−R_{ij}` cleanly).
- ✗ Wall 1: full `∀ a b c d` → `whnf` timeout (81 cases × big `B` polys). Need single-component
  or `maxHeartbeats`↑ + leaner tactic (`simp only [Fin.sum_univ_three, Fin.reduceEq, reduceIte]; ring`).
- ✗ Wall 2: single component `(0,1,0,1)`, original curv-action sign `−2` → messy mismatch.
- ✗ Wall 3: flipped curv-action `+2` → **clean mismatch `LHS−RHS = 2|Ric|²`**.
### ✅ FIX APPLIED + VERIFIED (2026-06-09)
Flipped `+ 2 * (B#)` → `- 2 * (B#)` at all five `Uhlenbeck.lean` sites (target
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `uhlenbeckCurvatureEvolutionRHSInFrame`,
the private `uhlenbeckPullbackRmDerivRHSInFrame`, and the two `+2*Q`/`(L+2*Q-Drift)` lines
inside the proof `pullbackDerivRHS_eq_evolutionRHS` → now `-2*Q`/`(L-2*Q-Drift)`).
`uhlenbeckBTensorInFrame`/`riemann04RicciDriftInFrame` kept unchanged. Targeted build
`+...NablaRiemannHeatSolution` GREEN (3629 jobs, 0 errors): `Uhlenbeck`, `RiemannNormHeatProducer`,
`NablaRiemannHeat`, `MultiNormHeat`, `NablaRiemannHeatSolution` all rebuilt. All importers
consume the predicate as a hypothesis (sign-agnostic), so nothing broke. The base target now
encodes the trace-free `−2C` reaction; the 3D reaction match (B3d) is UNBLOCKED.
**Latent note:** `rmReactionInFrame` (RiemannNormHeatProducer.lean:308) is defined `+4·Σ R·B#`
but the corrected base implies the genuine norm-heat reaction is `−4·Σ R·B#`. It does NOT break
(its only consumer `abs_rmReactionInFrame_le` uses the absolute value, so the BBS bound is
sign-insensitive), but the eventual discharge of the `Rm04NormDerivativeSimplifiesInFrame`
frontier must use `−4`.

### FIX CONFIRMED (GPT Pro follow-up consult + `ring` verified, 2026-06-09)
**The error is ONE sign: the target's `+2(B#)` must be `−2(B#)`** (keep `B`, `drift`, and the KN
identity unchanged). Verified by `ring` at components (0,1,0,1),(0,1,2,0),(1,1,2,2),(0,2,1,2):
`KN(−2C−2R²,+2|R|²,δ) + G = −2·(B−B+B−B) − drift`  (closes). Diagnostics GPT Pro gave:
`B# = KN(C,−|R|²,δ)` and `drift+G = KN(2R²,0,δ)`, which mechanically imply it.
**APPLY:** flip `+ 2 * (...)` → `- 2 * (...)` in `Uhlenbeck.lean`:
(1) `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` RHS;
(2) `uhlenbeckCurvatureEvolutionRHSInFrame` (pulled RHS);
(3) the pullback proof `pullbackDerivRHS_eq_evolutionRHS` (`L + 2*Q` → `L − 2*Q`, two appearances);
consumers `UhlenbeckCurvatureEvolutionInFrameOn`/`…_of_ricciFlow`/`…_of_solution_components` flip
automatically through the corrected RHS defs. Then close the reaction match with `Q_Ric=−2C−2R²`,
`Q_S=+2|R|²`, `roughLapRm04=KN(ΔRic,ΔS,δ)`.

### ROOT CAUSE FOUND (GPT Pro consult + confirmed `ring`, 2026-06-09)
**The `2|Ric|²` is NOT a bug in my forms or the diffusion split — it is a CONVENTION
INCONSISTENCY in the project's own Uhlenbeck target.** GPT Pro read the branch and diagnosed,
and I confirmed with a `ring` test that CLOSES:
`KN(+2C−2R², −2|R|², δ) + G = 2(B−B+B−B) − drift`  (C = Σ rm₍ikjl₎R₍kl₎, G = b3bReac).
So the current `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` RHS (`uhlenbeckBTensorInFrame` +
`riemann04RicciDriftInFrame`) traces to the Ricci reaction `+2C − 2R²` and scalar `−2|R|²` —
the **OPPOSITE curvature-action sign** from the PROVED Ricci/Lichnerowicz/scalar package
(`lichnerowiczRHSInFrame` = `ΔRic − 2C − 2R²`; scalar evo = `ΔS + 2|Ric|²`).
- My forms are CORRECT against the proved evolutions: `Q_Ric = −2C − 2R²`, `Q_S = +2|R|²`,
  `roughLapRm04 = KN(ΔRic, ΔS, δ)` (diffusion split confirmed right; `S` is the independent scalar
  field with `∂ₜS = trace(∂ₜRic) + 2|Ric|²`, the `+2|Ric|²` from `∂ₜg⁻¹`).
- **So proving `∂ₜRm04 = current target RHS` is FALSE against the proved package.** The target
  predicate (or the `B`/`drift` defs in `Uhlenbeck.lean`) needs its curvature-action convention
  reconciled with the proved Ricci package BEFORE the reaction match can close.
- **FIX (next):** GPT Pro's recommended order — (1) diagnostic trace lemma confirming the current
  `2B−drift` traces to `+2C−2R²` (essentially the `ring` test above); (2) patch the pre-Uhlenbeck
  curvature RHS convention/slot-sign in `Uhlenbeck.lean` (and its downstream consumers
  `uhlenbeckCurvatureEvolution*`) to the project `−2C` convention; (3) THEN state the real
  reaction-match with `Q_Ric=−2C−2R²`, `Q_S=+2|R|²`, `roughLapRm04=KN(ΔRic,ΔS,g)`. NOTE: this is a
  project-level convention fix touching `Uhlenbeck.lean` + consumers — a design decision.

**ORIGINAL diagnosis (superseded):** the structure is right (off by a single Ricci-invariant `2|Ric|²`),
so the bug is ONE convention: most likely (a) the `Q_S` scalar-reaction slot in `KN(Q_Ric,Q_S,δ)`
(maybe the displayed-vs-geometric `S.scalar` sign, or it double-counts vs the diffusion split),
or (b) the diffusion-split `ΔS = trace(ΔRic)` vs independent-`ΔS` treatment introducing the
`|Ric|²`. **Fix: nail the exact `S.scalar` evolution sign + the `Q_S` KN-slot, OR push to `offsyn`
and have GPT Pro check the exact `lichnerowiczRHSInFrame`/scalar-evolution/`uhlenbeckBTensorInFrame`
conventions against the actual files** (the consult anticipated this trap precisely).
- **ABANDON-3D-route signals** (else stay): (a) can't state `solution_rm04_kn_firstTrace_gform_at`
  in the proved-evolution Ric/scalar convention; (b) the `Δ`-through-KN lemma becomes as hard as
  general Bianchi because `roughLapRm04` API isn't tensorial enough to express `∇g=0`;
  (c) the reaction only closes in an orthonormal frame with no tensorial bridge to `FourComp`.
- Full consult prompt + answer context: `UhlenbeckBase_consult.md`.
- B3b: differentiate (product rule on the multilinear KN): `∂ₜRm04 = KN(∂ₜRic,∂ₜS,g) + KN(Ric,S,∂ₜg)`.
- B3c: substitute the three built evolutions + `Δ`-through-`g`:
  `∂ₜRm04 = ΔRm04 + [KN(Ric-reaction, scalar-reaction, g) + KN(Ric, S, −2Ric)]`.
- B3d: the bracket `= −2(B#) − ricciDrift` — a **finite dim-3 algebraic identity**.
  ### B3d STATUS (2026-06-09): identity CONFIRMED ✓, brute-force `∀` INFEASIBLE (perf wall), needs structural proof
  The orthonormal `Fin 3` identity (`R : Fin 3 → Fin 3 → ℝ` symmetric, `δ`=Kronecker):
  `KN(Q_Ric, Q_S, δ)_abcd + G_abcd = −2·B#_abcd − drift_abcd`, with
  `rm = -R_ac δ_bd + R_bc δ_ad + R_ad δ_bc - R_bd δ_ac + (S/2)(δ_ac δ_bd − δ_bc δ_ad)` (S = tr R; first trace `Σ_b rm_abcb = -R_ac`),
  `Bt_abcd = Σ_ef rm_aebf rm_cedf`, `B# = Bt_abcd − Bt_abdc + Bt_acbd − Bt_adbc`,
  `drift = Σ_p (R_ap rm_pbcd + R_bp rm_apcd + R_cp rm_abpd + R_dp rm_abcp)`,
  `C_ij = Σ_kl rm_ikjl R_kl`, `(R²)_ij = Σ_p R_ip R_pj`, `Q_Ric = −2C − 2R²`, `Q_S = 2|R|²`,
  `G = 4R_ac R_bd − 4R_ad R_bc + S(−R_ac δ_bd − δ_ac R_bd + R_bc δ_ad + δ_bc R_ad)`,
  `KN(A,s,δ) = -A_ac δ_bd + A_bc δ_ad + A_ad δ_bc - A_bd δ_ac + (s/2)(δ_ac δ_bd − δ_bc δ_ad)`.
  **CONFIRMED CORRECT** by `ring` at 7 diverse components: (0,1,0,1),(0,1,2,0),(1,1,2,2),(0,2,1,2),
  (0,1,1,2),(0,2,0,2),(1,2,1,2). Per-component tactic that closes:
  `simp only [all defs, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, reduceIte]; simp only [hR 1 0, hR 2 0, hR 2 1]; ring`.
  **PERF WALL:** one component ≈ 150–200k heartbeats ≈ ~7 s wall (the `Bt` double-contraction
  `Σ_ef rm·rm` with `S` expanded blows up `ring`). 81 components ≈ ~9.5 min wall — INFEASIBLE as
  a `lake build` target (wall-clock timeout, not heartbeats; splitting into per-`a` lemmas does not
  reduce total work). `S` (=tr R) CANNOT be kept opaque: `Bt` has a genuine `S²` term that only
  cancels once `S = R00+R11+R22` is substituted, so the expensive expansion is unavoidable brute-force.
  **STRUCTURAL FIX (next):** prove `B# = KN(C, −|R|², δ)` (diag1) by *symbolic* `Finset.sum`
  algebra — expand `rm = KN(Ric)` inside `Σ_ef rm_aebf rm_cedf`, distribute, collapse each
  `Σ_e δ_e? · X_e = X_?` once symbolically in `a,b,c,d` (NOT 81-case). Then:
  diag2 `drift + G = 2·KN(R², 0, δ)` is cheap brute-force (single `Σ_p`, no `Bt`; ~30–50k/component);
  KN-linearity `KNQ = −2·KN(C,−|R|²,δ) − 2·KN(R²,0,δ)` is cheap; assembly
  `KNQ + G = −2·KN(C,−|R|²) − 2·KN(R²,0) + G = −2 B# − drift` is `ring` on KN expressions (no `Bt`).
  So the ONLY remaining hard brick is diag1 via sum-algebra.
  ### ✅✅ B3d FULLY CLOSED (2026-06-09 session 2): `UhlReaction3.lean` is 0-sorry GREEN (lake build 3731)
  `bsharp_eq_knC` (diag1) PROVED via the closed-form decomposition (NOT symbolic sum-collapse,
  NOT 81-case brute force — both were wrong guesses):
  * `cc_closed`: `C = 2R² − (3S/2)R + (S²/2 − |R|²)δ` (9-case brute).
  * `bt_closed`: sum-free closed form of `Bt` (split `bt_a0/a1/a2`, 27-case each, CHEAP because
    only ONE `Bt` per goal): `Bt = −R_ab R_cd + 2R_ac R_bd + δ_ac(R²)_bd + (R²)_ac δ_bd
    − 2δ_ab(R²)_cd − 2(R²)_ab δ_cd + (3S/2)(R_ab δ_cd + δ_ab R_cd) − S(δ_ac R_bd + R_ac δ_bd)
    + (|R|² − ¾S²)δ_ab δ_cd + (S²/4)δ_ac δ_bd` (hand-derived, verified at R=I and diag).
  * `minor_adj3`: 3×3 adjugate/minor identity (Cayley–Hamilton face) — THE genuine dim-3 input:
    `R_ac R_bd − R_ad R_bc = −KNanti(R²) + S·KNanti(R) − ((S²−|R|²)/2)δδanti` (81 small cases).
  * assembly `linear_combination h1−h2+h3−h4 + kd_bd·hc1 − kd_ad·hc2 − kd_bc·hc3 + kd_ac·hc4 + hm`
    after orienting only the `(d,c)` atoms (`hR d c`, `rsq_comm hR d c`, `kd_comm d c`).
  Lean lessons: `fin_cases a` + per-slice `exact` works (defeq Fin.mk↔OfNat at default transparency);
  `decide` can't prove free-var disjunctions; linear_combination coefficient = the literal coefficient
  of the hypothesis-LHS atom in goal_lhs − goal_rhs (sign trap).
  ### ✅ B3e CORE + BRIDGES + htr BANKED (2026-06-09 session 2, producer GREEN, lake 3731)
  In `UhlenbeckBaseProducer.lean` (new imports: `Evolution.Uhlenbeck`, `DimensionThree.UhlReaction3`):
  * `uhlBt_eq_bt` / `uhlDrift_eq_drift` (section Dim3Bridges): at `gInv=δ` + comps in KN form
    `rm R`, `uhlenbeckBTensorInFrame = Dim3Reaction.Bt R` and `riemann04RicciDriftInFrame = drift R`
    (Fin.sum_univ_three expansion; first one closes by simp alone).
  * **`rm04BaseEvolution_at` — the pointwise B3e core**: at a `g_t`-orthonormal e-family at `(t,x)`,
    given `hRicDot : ∂ₜR_ij = lap_ij − 2Cc − 2Rsq` (Lichnerowicz shape), `hScDot : ∂ₜS = lapS + 2|R|²`,
    `htr : S.scalar = sc R`, concludes `∂ₜRm04(e_a..e_d) = KN(lap,lapS,δ) − 2·B#(R) − drift(R)`.
    Proof = B3b (`solution_rm04_timeDeriv_kn`) + `ricciSym_can` + `reaction_match` via congr_deriv +
    `linear_combination hmatch`. GREEN FIRST TRY.
  * `scalar_eq_trace_ortho`: htr discharger from `scalarTrace_delta` + `scalar_eq_metricTrace`
    (defeq-cast needed: simp lemma uses `S.family.metric`, h uses `S.base.metric` — rw is syntactic).
  ### ✅✅ ALL FOUR PER-POINT DISCHARGERS BANKED (2026-06-09 session 2 cont., producer GREEN,
  lake 3731, 0 warnings). The producer now imports `Evolution.Ricci.Lichnerowicz` too. New:
  * `rm04CompknOrtho` (hkn): `rm04Comp (Rm04 t) frame x = rm R` from `solution_rm04_kn_field` +
    section realization `hsec` (rfl when the assembly takes `Rm04 := S.base.rm04`) + orthonormal
    inners + `htr`. First try green.
  * `ricDot_ortho` (hRicDot): from `RicciLichnerowiczEquationInFrame` at `(t,x)` with `gInv t x = δ`:
    one-up/raised collapse, curvature contraction → `Cc` (via hkn), left+right actions → `2·Rsq`
    (via `hsym` concrete instances `hsym j 0/1/2, hsym 0/1/2 i` — generic ∀-hsym loops in simp).
    Lean: full `Fin.sum_univ_three` literal expansion beats symbolic `Finset.sum_ite_eq` collapse
    (the double-raising nests ites the collapse lemma can't reach; all if-conditions are
    bound-bound → literal after expansion, free `i j` never appear in conditions).
  * `scalarDot_ortho` (hScDot): from `ScalarEvolutionEquationOn S.scalar scalarLap (ricciNorm S)`
    (= `scalarEvolOfSmooth` output, FULLY proven from `IsSmoothSolutionOn` per BookData) via
    `ricciNorm_inner` + `orthonormal_invBasis3` + `ricciCompAt_apply`.
  * `scalar_eq_trace_ortho` (htr): via `scalarTrace_delta` + `scalar_eq_metricTrace`
    (defeq-cast: the simp lemma says `S.family.metric`, rw is syntactic).
  **PER-POINT PIPELINE COMPLETE:** standing inputs (`hlich` ← the h_ricci conditional layer,
  `hsc` ← `scalarEvolOfSmooth`(proven), frame+`gInv` supply, `hsec` rfl-able) →
  4 dischargers → `rm04BaseEvolution_at` → `∂ₜRm04 = KN(lap,lapS,δ) − 2B# − drift` →
  bridges → component API. Axiom hygiene: expect propext/choice/Quot only (no sorryAx anywhere
  in the new chain — UhlReaction3 is 0-sorry and all inputs are proven or hypotheses).
  ### ✅ #45 RESOLVED BY INSPECTION (2026-06-09): NOT a design fork — a mechanical brick
  Read the tower's actual `hrm` consumption (`nablaKRm_timeDeriv_of_solution`,
  `Connection/NablaKRmTimeDeriv.lean:117-120`):
  `hrm : ∀ m, HasDerivWithinAt (fun s => realizedRmBase S x₀ s x₀ m) (rm04Dt t x₀ m) D.carrier t`
  — i.e. (1) PER regular time `t` (the theorem is per-t, NOT one frame ∀t); (2) at the single
  centre `x₀`; (3) `rm04Dt` is a FREE value array (the tower itself does not constrain the
  derivative's structure; the Uhlenbeck-base shape is only needed later at the #44 BOUND step).
  Since the coordinate frame AND a `g_t`-orthonormal frame `e` at `x₀` are both fixed in time,
  the transition matrix `C` (coords of `∂_m` in `e`) is time-INDEPENDENT, and by multilinearity
  `realizedRmBase s x₀ m = Σ_{abcd} C⁴ · rm04(s)(e_a,e_b,e_c,e_d)` holds for ALL `s`.  Hence:
  **(45a)** `hrm` discharges from the per-point pipeline by a CONSTANT 4-linear combination of
  the `rm04BaseEvolution_at` derivatives (`HasDerivWithinAt.sum` + `.const_mul` + `.congr` along
  the all-`s` expansion identity), with `rm04Dt := C⁴-transform of (KN(lap,lapS,δ) − 2B# − drift)`.
  No general-gInv algebra, no predicate redesign, no new analysis.
  **(45b)** The STRUCTURE of `rm04Dt` for the #44 heatEq/StarSum2 bound transforms covariantly;
  handle at the bounds level via the k=1 Route (b) norm-invariance
  (`NablaRiemannHeatFrameInvariant.lean` pattern: orthonormal comp norms = intrinsic `normSq0S`).
  ### ✅ (45a) BANKED (2026-06-09 session 2 cont.): `rmBaseDeriv_basis` (producer GREEN, lake 3731)
  The tower's `hrm` from per-basis derivatives: given `hD a b c d : ∂ₜ rm04(s)(basis a..d) = V abcd`
  (the `rm04BaseEvolution_at` outputs), concludes
  `∂ₜ realizedRmBase(s, x₀, m) = Σ_{slots} V(slots)·∏ₐ basis.coord (slots a) (∂_{m a})`.
  Proof: `realizedRmBase_apply` (rfl) + `tensor0S_apply_eq_sum` at every `s` + `component0S_apply`
  + vec4-funext + `HasDerivWithinAt.fun_sum`/`mul_const`.  Lean: an UNannotated
  `fun slots _ =>` lambda for `HasDerivWithinAt.sum` leaves the binder type a metavariable
  ("Function expected at slots, ?m") — use `refine HasDerivWithinAt.fun_sum ?_; intro slots _`.
  ### ✅✅✅ CAPSTONE BANKED (2026-06-09 session 2 final): `rm04HrmProducer` (GREEN, lake 3731)
  ONE theorem from the standing analytic layer to the tower's `hrm`: inputs = regular `t`, centre
  `x₀`, `hdim`, a `g_t`-orthonormal `basis` + frame family with `frame i x₀ = basis i` and
  `gInv t x₀ = δ`, `Rm04` section realization (`hsec`, rfl for `Rm04 := S.base.rm04`), the standing
  `hlich` (Lichnerowicz; from `h_ricci` + `ricciSymFrame_can` + symmetric-gInv via
  `..._of_ricciEvolution_and_symm` — wire VERIFIED frame-generic, no new code) and the PROVEN
  `hsc` (`scalarEvolOfSmooth`); output = `∂ₜ(realizedRmBase)(t,x₀,m)` with the explicit value
  `Σ_slots (KN(ΔRic,ΔS,δ) − 2B# − drift)(slots)·∏ basis.coord (slots a) (∂_{m a})` — exactly the
  `hrm` of `nablaKRm_timeDeriv_of_solution`. Composes: horthf/hsym/htr/hkn dischargers →
  `ricDot_ortho`/`scalarDot_ortho` → `rm04BaseEvolution_at` → `rmBaseDeriv_basis`. GREEN first try.
  Also banked this pass: `ricciSymFrame_can` (RicciSymmetricInFrameOn from `ricciSym_can` — the
  hlich wire's only new piece) and `solution_rm04_kn_all` (all-slots KN field identity, B3c step 0).
  **AUDIT (hlich frame-genericity):** the Commutator-layer producers
  (`ricciEvolution_of_variation_commutators`, `..._OnLocal_...`) are FRAME-GENERIC — arbitrary
  `(gInv, frame, nabla2Ric)` with conditional `h_var`/`hcomm` in that frame. So the orthonormal-at-x₀
  instantiation needs NO new transfer; the openness is the layer's own conditional status
  (`h_var`/`hcomm` discharge — the long-standing project-wide Ricci-evolution frontier).
  **STATUS: the dim-3 Uhlenbeck base is DISCHARGED INTO THE TOWER modulo the standing layer**
  (`h_var`+`hcomm` at a chosen frame family, `hswap`, `hmetricFrame`/`hmix` regularity boxes) +
  per-instantiation frame data (orthonormal basis exists via `exists_orthonormalBasisAt`; the
  constant-coefficient frame-family builder around `coordinateFrameAt` is a small pending def).
  The PREDICATE-form packaging (`Riemann04BTensorWithRicciDriftEvolutionInFrameOn` ∀(t,x)) remains
  unassembled but is NOT on the tower's critical path (the tower consumes `hrm` directly).
  ### REMAINING for the full base discharge (next sessions)
  2. B3c realization: `lap`-array := genuine `ΔRic` comps and `KN(ΔRic,ΔS,δ)` realizes `ΔRm04`
     (the diffusion split — needed at the #44 bound step, not by the tower).
     ### B3c TOOLKIT FULLY MAPPED + first piece BANKED (2026-06-09 session 2 final round)
     The ∇-through-KN split assembles ENTIRELY from existing + one new Tensor-layer lemma:
     * `nabla0S_product_realizes` (ProductNablaLeibniz.lean) — ⊗-Leibniz with the
       `leibnizLeft/RightEquiv` slot bookkeeping;
     * **✅ NEW `totalNabla0SRealizes_domDomCongr`** (NablaDomDomCongr.lean, BANKED this session,
       lake 2758 GREEN): realizer-level slot-permutation closure
       (`nablaZ` realizes `∇Z` ⟹ `(∇Z)·frontExtendEquiv e` realizes `∇(Z·e)`), from
       `nabla0SFun_domDomCongr` + `cons_apply_frontExtendEquiv`.  Lean: after
       `domDomCongr_apply` the composite is eta-expanded — use the pointwise `@[simp]`
       cons-lemma + defeq-`exact (hZ …).trans (…).symm`, not `rw` on the `∘`-form;
     * `TotalNabla0SRealizes.add` / `.smul` (HigherOrder.lean:957/988) — linear closure;
     * `zero_realizes_metric` + `metricDerivsZero : CanonicalSpatialDerivs0S cov (metricTensorField g)`
       (MetricCompatibility.lean:381 — ∇g = 0 AND ∇²g = 0 in package form);
     * `nabla_smul_metric` (MetricCompatibility.lean:249) — `∇(S·g) = dS⊗g` in realizer form
       (the KN scalar term: build the rank-4 `S·(g⊗g)` as `(S·g)⊗g` via the product Leibniz —
       NO new function-smul API needed);
     * each KN term = ±`domDomCongr σᵢ (product Ric g)`: σ₁=(1 2)-swap for `Ric(v0,v2)g(v1,v3)`, etc.
     ✅ Ric-side handles BANKED (same session, producer GREEN): `connSmoothSol` (∞-smooth
     Levi-Civita at any `t`, from `metricCov_smooth`) and **`ricNablaRealizes`** — the canonical
     `∇Ric` realizer for the solution (`totalNabla0S_realizes` at `S.ricci t`, HigherOrder.lean:398;
     `S.ricci t` IS directly a `Tensor0SField 2`, the same construction as IntrinsicDerivation's
     private `nablaRicField`).
     ✅✅ MORE BANKED (continuation rounds, producer GREEN, lake 3736):
     * `metricCompatSol` (public Levi-Civita compatibility at any `t`);
     * **`knTermRealizes`** — the GENERIC slot-permuted `(Ric⊗g)·e` covariant-derivative
       realizer (e : Fin (2+2) ≃ Fin (2+2) arbitrary): covers KN terms T1–T4 in one lemma via
       `nabla0S_product_realizes` (∇g-half = 0) + `totalNabla0SRealizes_domDomCongr`.
       T1–T4 instances: e₁ = `swap 1 2`; e₂ = `(swap 1 2).trans (swap 0 1)` (0↦1,1↦2,2↦0);
       e₃ = `(swap 2 3).trans (swap 1 3)` (1↦3,2↦1,3↦2);
       e₄ = `((swap 3 2).trans (swap 1 3)).trans (swap 0 1)` (0↦1,1↦3,2↦0,3↦2).
     * dS-side INVENTORY COMPLETE: `duSec u hu : OneFormSection` + `duSec_apply` +
       `differential1FormFun_apply_eq_extDerivFun` (`Geometry/Operator/HessianTraceRealization.lean`
       :140/164) — exactly `nabla_smul_metric`'s `(df, hdf)` shape; only solution input =
       `ContMDiff ∞ (S.scalar t)` at regular `t` (regularity layer).
     **LEAN LESSON (instance wall):** the `+`/`0` instances on `MultilinearSection`/`Tensor0SField`
     at arithmetic ranks (`2+2+1`) DO NOT synthesize under default transparency — every file in
     this stack sets `set_option backward.isDefEq.respectTransparency false`; scope it (`... in`)
     onto any theorem whose statement uses those instances outside the Tensor stack.
     ✅✅ T5 + SUM ASSEMBLY BANKED (further rounds, producer GREEN, lake 3736):
     * **`knScalRealizes`** — generic `((S·g)⊗g)·e` realizer via `nabla_smul_metric`
       (f := `S.scalar t`, hf := `scalarSmoothOfSol` (Regularity.lean:37, works at ANY t),
       df := `DifferentialGeometry.Integral.Connection.duSec` + `duSec_apply` +
       `differential1FormFun_apply_eq_extDerivFun`; producer now imports
       `Geometry.Operator.HessianTraceRealization`).  `OneFormSection` IS
       `Tensor0SField … 1` (abbrev, RicciIdentity/OneForm.lean:45).
     * **`knField` (private def)** — the dim-3 KN field as the signed combination
       `−T₁+T₂+T₃−T₄+(1/2)T₅ₐ−(1/2)T₅ᵦ` of `knRicT`/`knScalT` at the perms `knE1..knE4`
       (knE1 = swap 1 2, knE2 = (swap 1 2).trans (swap 0 1), knE3 = (swap 2 3).trans (swap 1 3),
       knE4 = ((swap 3 2).trans (swap 1 3)).trans (swap 0 1)).
     * **`knFieldRealizes` (private, ∃-form)** — the sum-closure end-to-end:
       `∃ knField', TotalNabla0SRealizes (2+2) cov (knField S t) knField'` via the 6 term
       realizers + `.add`/`.smul`.  (∃-form is a stepping stone: the explicit realizer shape
       gets fixed at the B3c-2 design; the canonical `totalNabla0S` is always available via
       `totalNabla0S_realizes`.)
     ✅✅✅ (iii) EXT-TRANSPORT BANKED (final round, producer GREEN, lake 3736, 0 warnings):
     **`knField_eq_rm04`** — `knField S t = S.base.rm04 t` as sections (`Tensor04Section` IS
     `Tensor0SField ∞ 4`, abbrev at Curvature/Tensor.lean:117). Proof: one `letI :=
     tensor0SBundle_topology (s := 2+2)` + `DFunLike.ext` + `ContinuousMultilinearMap.ext` +
     a GENERIC `hric` tuple-bridge (`∀ w a b, w 0 = v a → w 1 = v b → Ric x w = ricciAt (vec2
     (v a) (v b))`; `change` to ricci-form (defeq), `congr 1`, funext+fin_cases — avoids 4
     separate vec2-rewrites) + `rw [solution_rm04_kn_all]` + the apply-evaluation `simp only`
     (coe_add/Pi.add_apply/CMM.add_apply, coe_smul/…, domDomCongr_apply ×2,
     tensor0SField_product_apply, tensor0SField_smulByFun_apply, metricTensorField_apply,
     Function.comp_apply) + the four `hric` rewrites + final
     `simp [knE…, Equiv.trans_apply, Equiv.swap_apply_def, Fin.ext_iff]; ring`.
     **Lean lessons:** (a) `Fin.natAdd 2 0`-style indices do NOT reduce under `simp only` with
     `Fin.reduceEq/reduceIte` — use FULL `simp` (default simprocs) with `Fin.ext_iff` for the
     index arithmetic; (b) side-goals like `((v∘e)∘castAdd 2) 0 = v 0` close by plain
     `simp [knE_, Equiv.swap_apply_def]` (no `rfl` after — it overshoots).
     ✅✅✅✅ **B3c-1 COMPLETE AND PACKAGED (final round, lake 3736 GREEN, 0 warnings):**
     `knRicD`/`knScalD`/`knFieldD` (private defs) spell the explicit 6-term realizer, and
     **`nablaRm04Kn`** (private; B3c-2 is its consumer in this file) states the endpoint:
     `TotalNabla0SRealizes (2+2) (conn t) (S.base.rm04 t) (knFieldD S t)` — i.e.
     **∇Rm04 IS realized by the explicit KN combination of (∇Ric, dS, g)** for the dim-3
     solution.  Proof: `rw [← knField_eq_rm04]` + the literal `.smul`/`.add` combination of
     `knTermRealizes`/`knScalRealizes` (the def unfolds by defeq under the section's
     respectTransparency setting).  GREEN first try.
     ✅ (iv) B3c-2 OPENED + first pieces BANKED (continuation, lake 3736 GREEN, 0 warnings):
     * `ric2NablaRealizes` / `duNablaRealizes` — the canonical `∇²Ric` and `∇(dS)` (Hessian)
       realizer handles (`totalNabla0S_realizes` at ranks 2+1 and 1).
     * **`knTerm2Realizes`** — the generic SECOND derivative of a Ric⊗g KN term:
       `∇(knRicD e)` realized by the one-rank-up closure stack (outer
       `frontExtendEquiv (frontExtendEquiv e)`, both Leibniz branches differentiated:
       `∇²Ric⊗g` + `∇Ric⊗0`-corrections; `zero_realizes_nabla` for the 0-field leaves).
       Same composition pattern as level 1; the rank-6 witness is explicit in the statement.
     ✅ `knScal2Realizes` BANKED (continuation, lake 3736 GREEN, first try): the scalar-term
     second derivative — `∇((dS⊗g)⊗g)`-branch via nested product-Leibniz (`duNablaRealizes`
     Hessian + metric-zeros), `∇((S·g)⊗0)`-branch via `nabla_smul_metric` + `zero_realizes_nabla`.
     **ALL SIX level-2 term realizers now exist** (4 Ric via generic `knTerm2Realizes`,
     2 scalar via generic `knScal2Realizes`).
     ✅✅ **`rm04DerivsKn` BANKED (continuation, lake 3736 GREEN, first try): the COMPLETE
     first+second derivative KN package** — `CanonicalSpatialDerivs0S (conn t) (S.base.rm04 t)`
     with `nablaA := knFieldD` (KN of ∇Ric, dS, g), `first := nablaRm04Kn`, `second :=` the
     signed `.smul`/`.add` combination of the six level-2 realizers, and `nabla2A` INFERRED
     from the proof term (anonymous-constructor `_` trick — no need to spell the rank-6 witness
     def; the structure projection `.nabla2A` exposes it).  No `knRicD2`/`knScalD2` defs needed.
     **B3c DERIVATIVE SIDE COMPLETE.**  REMAINING = THE TRACE STEP ONLY.
     **USER DESIGN DECISION (2026-06-10): the component/brute-evaluation route for the trace is
     REJECTED** — a giant pointwise evaluation of the rank-6 witness (and the follow-up
     81-component trace at the centre) has no reuse value and is the wrong abstraction.  A
     first attempt (`rm04Nabla2Eval`, a generic-slot evaluation with `congrArg+decide`
     side-goals) was DELETED after hitting the rw-rematching trap (each `h4`-rewrite re-matched
     the previous rewrite's `vec4` output — `T w`-shaped too).  File restored green through
     `rm04DerivsKn`.
     **CORRECT DESIGN for the trace step: small reusable trace-algebra lemmas at the
     Tensor/Operator layer**, then a 10-line producer-level composition.
     ✅✅ STRUCTURAL LEMMA SET BANKED (2026-06-10, lake 3554 GREEN):
     * **`totalNabla0SRealizes_unique`** (NablaDomDomCongr.lean, canonical Tensor-layer home;
       the HCG copy in the in-flight `ProductMFoldNorm.lean` should redirect here once that
       thread lands) — realizer uniqueness, the keystone: identifies `knFieldD` with the
       canonical `∇rm04` and `rm04DerivsKn.nabla2A` with the canonical `∇²rm04`, so the split
       can be stated about the SAME canonical objects the StarSum layer uses
       (`Δ(∇ᵏRm) = metricTraceFirstTwoField g (∇^{k+2}Rm)`, RoughLapNablaK.lean convention).
     * **`metricTraceFirstTwoField_eq_sum`** (NablaTraceGen.lean) — pointwise coordinate
       formula with the canonical centred-chart inverse metric (deterministic-instance form;
       the workhorse for the algebra lemmas).
     * **`metricTraceFirstTwoField_add` / `_smul`** — trace linearity.
     * **`metricTraceFirstTwoField_domDomCongr`** — trace commutes with tail reindexing:
       `trace₁₂(A·frontExt(frontExt e)) = (trace₁₂ A)·e`.  Lean: Mathlib's
       `domDomCongr_apply` RHS is eta-form — close sub-haves with `rfl`; use
       deterministic-instance rewrites (`hL/hrhs/hR` haves), not bare `rw [lemma]` chains.
     ✅ **`metricTraceFirstTwoField_domDomCongr_gen` BANKED (2026-06-10, lake 3554 GREEN):**
     the GENERAL trace-through-reindexing — for ANY `e : Fin (s+2) ≃ Fin (s'+2)`, `e' : Fin s ≃
     Fin s'` with `hcompat : metricTraceInput X Y tail ∘ e = metricTraceInput X Y (tail ∘ e')`,
     `trace₁₂(A·e) = (trace₁₂ A)·e'`.  This covers the leibniz/finCongr value-cast equivs (all
     `frontExt(LL/LR)` are value-preserving, so `e'` is the matching value-cast and hcompat is a
     small `Fin.cases`), not just `frontExt²`.  The `frontExt²` special case
     `metricTraceFirstTwoField_domDomCongr` is now a 6-line corollary (hcompat by double
     `Fin.cases` + `frontExtendEquiv_zero/_succ`).  Lean: `domDomCongr_apply` RHS is eta —
     close the trivial sub-have with `rfl`.
     ✅ **`metricTraceFirstTwoField_product` BANKED (2026-06-10, lake 3555 GREEN):** the
     front-factor trace `trace₁₂(domDomCongr (finCongr h) (product (s:=k+2) A B)) =
     product (trace₁₂ A) B` (`h : k+2+q = k+q+2`).  Plus the reusable helper
     **`metricTraceInput_apply`** (value characterization
     `= dite i.val=0 X (dite i.val=1 Y (tail ⟨i.val-2,_⟩))`) — the key that lets
     `finCongr/castAdd/natAdd`-reindexed evaluations reduce by `.val` + `omega` instead of
     `Fin.cases_succ` (which won't fire on cast indices).  Proof = `_eq_sum` +
     `tensor0SField_product_apply` (needs `import …ContractionLeibniz`) + fact1/fact2 (value-level)
     + `Finset.sum_mul` ×2 + `ring`.  **Lean lessons:** (a) the dite tail index is dependent, so
     `simp only [hv]` (NOT `rw [hv]`, which fails "motive not type correct") to rewrite the index
     value; (b) `domDomCongr_apply` yields the comp in `fun i_1 => F (e i_1)` lambda form (not
     `F ∘ ⇑e`), and `← Function.comp_def` does NOT convert it — STATE fact1/fact2's LHS in the
     `(fun i_1 => metricTraceInput X Y tail ((finCongr h) i_1)) ∘ castAdd q` lambda form so
     `rw [fact1, fact2]` matches syntactically.
     ### REMAINING: the producer composition only (no new reusable lemmas)
     The full trace toolkit is now banked: `_eq_sum`, `_add`, `_smul`, `_domDomCongr_gen`
     (+ `_domDomCongr` corollary), `_product`, `metricTraceInput_apply`, and
     `totalNabla0SRealizes_unique`.  Next round = thread `metricTraceFirstTwoField g
     (rm04DerivsKn.nabla2A)` through them:
     1. `nabla2A` = signed sum of the 6 `knTerm2Realizes`/`knScal2Realizes` witnesses (the `.add`/
        `.smul` realizer-field) → split by `_add`/`_smul`.
     2. each witness `domDomCongr(frontExt² e)(inner)` → `_domDomCongr` peels `frontExt² e`.
     3. inner `+` of `domDomCongr(frontExt(LL/LR))(...)` → `_add` + `_domDomCongr_gen` (the
        leibniz equivs are value-casts; their hcompat is a small `metricTraceInput_apply`+`omega`).
     4. leaves `domDomCongr(LL/LR)(product …)`; bridge `leibnizLeftEquiv s q = finCongr (rfl-proof)`
        (proof-irrelevant `finCongr`), then `_product` ⟹ `(trace₁₂ ∇²Ric) ⊗ g` = `ΔRic ⊗ g` etc.
     5. zero-branches (`product … 0`) vanish.  ✅ `metricTraceFirstTwoField_zero` BANKED
        (2026-06-10, lake 3555).  **Instance wrinkle (recorded):** the generic
        `domDomCongr e 0 = 0` / `product A 0 = 0` FAIL `OfNat 0` synthesis at statement time —
        the bundle topology/`Zero` instance is only pinned once a concrete-rank function fixes
        it (a bare `(0 : Tensor0SField s)` in a generic-`s` MultilinearSection statement has no
        anchor; `metricTraceFirstTwoField g (0 …)` works because the function pins it, and so
        does `zero_realizes_nabla` because its `0` is anchored by `TotalNabla0SRealizes`).  So
        handle those two collapses INLINE in the producer at the concrete witness ranks
        (where `0` is anchored), not as generic Tensor-layer lemmas.  Needs
        `[IsManifold I 2 M]` in scope for the `0` to resolve at all.
     6. assemble ⟹ `Δrm04 = KN(ΔRic, ΔS, g)` as canonical fields; then component form for #44.
     **TRACE TOOLKIT NOW COMPLETE** (`NablaTraceGen.lean`): `_eq_sum`, `_add`, `_smul`,
     `_domDomCongr_gen` (+ `_domDomCongr`), `_product`, `metricTraceInput_apply`, `_zero`;
     plus `totalNabla0SRealizes_unique` (`NablaDomDomCongr.lean`).  Lean lessons banked:
     deprecated `Fin.coe_cast/_castAdd/_natAdd` → `Fin.val_cast/_castAdd/_natAdd`.
     ### ✅ COMPOSITION FEASIBILITY CONFIRMED (2026-06-10, producer GREEN lake 3737)
     The one non-obvious composition step — the **leibniz-layer hcompat** for
     `_domDomCongr_gen` — was PROVED by a throwaway probe (now removed): for the
     value-preserving `frontExtendEquiv (leibnizLeftEquiv 2 2)`, the tail reindex `e'` is
     `Equiv.refl` and hcompat closes by `funext q; …metricTraceInput_apply ×2; hval; simp`
     where `hval : (frontExt(LL 2 2) q).val = q.val` is a 2-line `Fin.cases` +
     `frontExtendEquiv_zero/_succ` + `leibnizLeftEquiv`/`finCongr_apply`/`Fin.val_cast`.
     So EVERY leibniz/LR layer peels the same way (all value-preserving ⟹ `e' = refl`,
     identical hcompat). The producer now imports `…MetricTrace.NablaTraceGen`.
     **All composition pieces are now verified-feasible** (frontExt² peel ✓, leibniz peel ✓,
     `_product` ✓, `_add`/`_smul` ✓, zero-collapse inline ✓).  Next round = write the full
     `metricTraceFirstTwoField g (rm04DerivsKn.nabla2A) = KN(ΔRic, ΔS, g)` assembly
     (mechanical, ~150 lines: 6 terms × {outer peel, 2 leibniz peels via the refl-hcompat,
     product/zero}, then the rank-4 KN-shape identity collapsing the residual value-casts).
     The dim-3 KN-specific layer stays at the SECTION level (knField/knFieldD/rm04DerivsKn);
     only the trace-algebra lives at the Tensor layer where it serves any rank.
  3. Wire the standing `hlich` input: `RicciLichnerowiczEquationInFrame` ←
     `ricciLichnerowiczEquationInFrame_of_ricciEvolution` (Lichnerowicz.lean:576) ← the
     `RicciEvolutionEquationInFrame` conditional layer (Commutator.lean producers + the ∂ₜΓ work).
  4. (45b) at #44: norm-level transfer of the transformed reaction structure.
  Namespace `DifferentialGeometry.Dim3Reaction`. Defs `kd, sc, rm, Bt, Bsharp, drift, Cc, Rsq,
  normSq, QRic, QS, KNQ, Gg, knC, knRsq` (bare `Fin 3 → ℝ`). Theorems:
  • `driftG_eq_knRsq` (diag2) — PROVEN, cheap `Fin 3` brute force (~50 s/81 cases).
  • `bsharp_eq_knC` (diag1) — `sorry` (the one standing frontier; needs symbolic `Finset.sum`).
  • `reaction_match` (B3d target) — PROVEN modulo diag1, by `linear_combination 2*hd1 + hd2`
    after `simp only [KNQ, QRic, QS, knC, knRsq] at hd1 hd2 ⊢` (KN-linearity; no `Bt`, cheap).
  **Lean tactic lesson (key):** `fin_cases` over `Fin 3` emits `⟨k, _⟩` (Fin.mk) indices while
  `Fin.sum_univ_three` emits OfNat `0,1,2`; `ring` treats `R 1 ⟨2,_⟩` and `R 1 2` as DISTINCT atoms.
  Add the simproc **`Fin.reduceFinMk`** (with `Fin.isValue, Fin.reduceEq, reduceIte`) to normalize
  `⟨k,_⟩ → k` before `ring`. Symmetry via `(try simp only [hR 1 0, hR 2 0, hR 2 1])`. Without
  `Fin.reduceFinMk` the brute force silently leaves `ring` mismatches (looks like a formula bug).
  **NEXT for B3d:** discharge `bsharp_eq_knC` by symbolic sum-algebra (the only `sorry`), then B3e.
- B3e: package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (dim 3) via `HasDerivWithinAt.congr_deriv`.

A2 (`realizedRmBase_timeDeriv`, the `∇²Ric` form) stays as a verified alternative establishment
of `∂ₜRm04` but is NOT on this route — the 3D route differentiates the KN identity instead.

- Downstream already built: pullback (`uhlenbeckCurvatureEvolution_of_solution_components`) +
  `∂ₜ∇ᵏRm` assembly (`nablaKRm_timeDeriv_of_solution`).

## B3c-2 TRACE STEP — DONE + VERIFIED (2026-06-10, targeted build 3737 jobs, 0 sorry)

The diffusion identity `ΔRm04 = trace₁₂ ∇²Rm04 = KN(ΔRic, ΔS, g)` (dim 3) is now a proved
theorem `traceRm04Kn`:
`metricTraceFirstTwoField g (rm04DerivsKn S t hdim).nabla2A = lapRm04Kn S t`.

Architecture (all structural, NO component brute force):
- **Foundational MLS lemmas** (added to `Tensor/Multilinear/DomDomCongrSection.lean` +
  `Tensor/Multilinear/Tensor.lean`, generic bundle layer, `@[simp]`):
  `domDomCongr_refl`, `domDomCongr_zero`, `product_zero`, and
  `domDomCongr_id_of_valPres` (a value-preserving reindex `(e i).val = i.val` forces
  `e = Equiv.refl` by `Fin` ext, so the section is unchanged).  **Gotcha:** the MLS namespace
  has an EXPLICIT `variable (n : WithTop ℕ∞)`, so `domDomCongr_id_of_valPres` takes `n` as its
  first explicit arg — call it as `… (∞ : WithTop ℕ∞) (frontExtendEquiv …) (by …)`, not with
  the equiv first (else "expected WithTop ℕ∞" mismatch).
- **Generic shape lemmas** `traceRicWit` / `traceScalWit` (private, variables `A,B,C,gf` /
  `Hess,D1,Sg,gf` for the leaves): trace the explicit `knTerm2Realizes` / `knScal2Realizes`
  witness shapes.  Proof skeleton (≈8 lines each): `metricTraceFirstTwoField_domDomCongr`
  peels `frontExt(frontExt e)`; `congr 1`; `simp only [product_zero, domDomCongr_zero,
  add_zero]` collapses the three `∇g=0`/`∇0=0` Leibniz branches; `domDomCongr_id_of_valPres`
  kills the value-preserving `frontExt(leibnizLeftEquiv 2 2)` layer; `simp only
  [leibnizLeftEquiv]` exposes the `finCongr` so `metricTraceFirstTwoField_product` fires
  (×1 Ric, ×2 scalar for the nested `(∇²S⊗g)⊗g`).
- **Target defs** `knRicLapT e` = `domDomCongr e (product ΔRic g)`, `knScalLapT e` =
  `domDomCongr e (product (product ΔS₀ g) g)` (ΔRic = `trace₁₂ ∇²Ric` rank 2, ΔS₀ =
  `trace₁₂ ∇²S` rank 0), `lapRm04Kn` = the signed six-term KN combination mirroring `knField`.
- **Endpoint** `traceRm04Kn`: `simp only [rm04DerivsKn]` exposes `nabla2A` as the `•`/`+`
  combination of the six explicit witnesses; `simp only [metricTraceFirstTwoField_add,
  _smul]` distributes the trace; `rw [traceRicWit ×4, traceScalWit ×2]; rfl`.

NOTE on namespace: producer is in `DifferentialGeometry.PDE.RicciFlow`; the trace toolkit is
in `DifferentialGeometry.Integral.Connection` — used via `open … in` per declaration.

REMAINING to wire this into the capstone `rm04HrmProducer` (separate brick): bridge the
bundled `metricTraceFirstTwoField g (∇²Ric)` to the component `roughLapRic` in the
orthonormal frame (RoughLaplacian realization), discharging the `hlich`/`roughLapRic`
hypotheses the capstone currently assumes.

## TODO (deferred) — B GENERAL-DIMENSION route (un-traced second Bianchi)

Only needed if the project later wants the Uhlenbeck base in `dim ≠ 3`. **Not required for
`ham3_main`.** This is the un-traced (rank-4, 4 free indices) analogue of the entire
~1250-line `Ricci/Commutator.lean` + the differentiated second Bianchi:
- final reduction = short `rw`+`ring` delegating to an `Rm04ContractedCommutators` package
  (mirror `ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators`, `Commutator.lean:1093`);
- package proven from (i) un-traced *differentiated second Bianchi* (build; cf.
  `DifferentiatedContractedBianchiInFrameOnLocal`) and (ii) rank-4 `tensor0S_ricciIdentity_of_torsionFree`
  (`Tensor/RicciIdentity/Tensor0S/Formula.lean:975`, rank-general — usable directly).
- Starts from A2's `∇²Ric` expanded RHS (`realizedRmBase_timeDeriv`).
- Hardest single theorem in the pillar; warrants GPT Pro route consultation on the index
  bookkeeping. **Deferred.**

## 2026-06-14 hcov cleanup

Removed the caller-facing local-smoothness hypothesis from the realized base
curvature coefficient/time-derivative bridge.  The fixed-time solution
connection now derives the Koszul local smoothness internally from the metric.

Verification passed for the edited file and downstream module refresh.

## 2026-06-14 manifold instance cleanup

Removed all explicit `infty+1` manifold binders from the Uhlenbeck base producer.
These theorem surfaces already carry the smooth/finite-order manifold context
they need, and the file's metric-specific connection smoothness and metric
compatibility facts are produced internally by `connSmoothSol` and
`metricCompatSol`.

Verification passed for the edited file and module refresh.

## 2026-07-12 opaque-fiber compatibility

The short-time branch alignment exposed two stale proof assumptions.  First,
the pointwise negation of the Ricci `(0,2)` tensor must now be evaluated through
`Tensor0SSpace.neg_apply`; the old continuous-multilinear-map rewrite no longer
sees through the opaque fiber.  Second, the old single large simp in
`knField_eq_rm04` could no longer lower the signed section combination and slot
reindexings to scalar components, and attempting to keep that route eventually
hit the recursion-depth limit.

The repaired proof keeps the existing KN mathematics and public statements.
It evaluates section addition and scalar multiplication explicitly, proves
pointwise producer equalities for `knRicT` and `knScalT` through the public
`Tensor0SSpace` / tensor-field product APIs, uses `SolutionOn.family_metric` for
the canonical metric bridge, and records the four concrete slot permutations
before the final scalar ring calculation.  No tensor representation internals,
new assumptions, or new mathematical frontier were introduced.

Focused verification passed.  The Uhlenbeck-base producer remains theorem-
complete (100%); this file's branch-compatibility repair is complete (100%);
Hamilton-target integration is approximately 99% pending its final downstream
rebuild; short-time branch alignment is approximately 99% pending Hamilton and
the remaining direct consumer check.  The merge commit remains 0% until those
checks, final diff review, and merge-state cleanup pass.  This compatibility
repair does not change the separate Hamilton positive-Ricci endpoint or HCG
compactness theorem completion percentages.
