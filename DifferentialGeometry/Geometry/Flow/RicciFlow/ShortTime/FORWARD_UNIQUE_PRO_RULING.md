# GPT Pro ruling — black box (B) forward-uniqueness statement + route (2026-07-25)

Answer to `FORWARD_UNIQUE_PRO_PROMPT.md`, relayed by the user 2026-07-25.
Archived verbatim below (§Verbatim); distilled decisions first.

**EXECUTION FREEZE (user directive, 2026-07-25): the e87b tree is about to be
merged back into ste-align (`codex/short-time-existence-align`). Do NOT
implement this ruling on e87b; it is recorded here as the post-merge plan.
The K1 kickoff prompt at the bottom is ready to dispatch after the merge.**

## Distilled ruling

1. **Statement surgery APPROVED; Burkhardt-Guim rough-C⁰ route REJECTED for
   this consumer.** Smallest signature change: (N) `ContMDiffOn` output domain
   `Ioo 0 τ₀ → Ico 0 τ₀` (KEEP the now-redundant `ContinuousOn` field —
   deliberate, minimizes churn); (A) conclusion `t_star ∈ Ioo α omega` + thread
   the `Ico` field; (B) `h1smooth`/`h2smooth` domains `Ioo a b → Ico a b`, keep
   `h1cont`/`h2cont`/PDE/`h0` unchanged. `MaximalTime` rewiring mechanical
   (restrict ambient `Ioo α ω` smoothness to `Ico t_star ω` via `α < t_star`;
   shift map `Ico → Ico`; Brick U unchanged via `.mono` back to `Ioo`).
   CORRECTION to one sentence in the ruling: it says our local (A) "has already
   been changed to Ioo" — false; that was a PROPOSAL in the prompt. No local
   edit exists; (A) still concludes `Ico` everywhere. Nothing to synchronize.
2. **(N) corner-cost ruling**: up-to-corner C∞ from smooth data is
   mathematically standard (closed M ⟹ no compatibility sequence; time
   derivatives at 0 recursively determined), but in the L²-max-reg
   formalization it is a REAL medium-sized dedicated endpoint-bootstrap layer.
   Correct pattern: a-posteriori bootstrap of the ONE low-regularity solution
   on its already-established horizon τ₀ — NEVER re-run the fixed point per
   derivative order and intersect shrinking horizons. The common lifetime keeps
   depending only on ellipticity + order-≤3 bounds; per-datum higher constants
   may depend on all higher derivatives of that g₀. FALLBACK if full `∞`-at-edge
   proves disproportionate: interior C∞ + FINITE up-to-edge regularity
   sufficient for Route K (the estimates need only bounded Rm and ∇Rm at the
   edge) — never a return to the rough-C⁰ statement. (N) lane must co-sign
   after checking its trace/linear-regularity APIs bootstrap on a fixed horizon.
3. **Route ruling: (K) Kotschwar energy, NOT (G).** (G)'s tension algebra is
   real but not the missing producer (no tension-field Nemytskii; TimeTame
   fixed point failed its build on (0,2)-hard-coded Duhamel lemmas; diffeo
   persistence + HMF→RDT gauge construction are new geometric work; the
   pullback theorem's ODE-generation is hypothesis; neither RDT-uniqueness half
   removes the HMF bottleneck). (K)'s one dominant heavy gap = the tensor-level
   divergence-form evolution of the curvature difference — bounded tensor
   calculus, no auxiliary nonlinear PDE / map-valued spaces / diffeo theory.
4. **Carrier ruling: moving g₁(t), NOT fixed ḡ.** The fixed-background variant
   is mathematically sound (coercivity survives; B_t/ρ_t discrepancies absorb
   by Young) but is the WRONG Lean formulation — it would need a new weighted
   cross-metric IBP layer, whereas the existing tensor Green identity wants ONE
   metric providing connection + inner product + measure simultaneously.
   Energy: `E(t) = ∫ (|h|² + |A|² + |S|²)_{g₁} dμ_{g₁}`; ∇¹g₁ = 0; norm
   derivative = zero-order Ricci reaction; ∂ₜdμ_{g₁} = −scal·dμ_{g₁}.
   `MovingEdgeEnergy.lean` = design evidence, not an import (blocked upstream).
5. **Variances**: lower everything with g₁(t) to `Tensor0S`: `h₀₂ := g₁−g₂`,
   `A₀₃ := g₁(∇¹−∇², ·)`, `S₀₄ := g₁(Rm¹³₁−Rm¹³₂, ·)`. Lowering adds only
   ∂ₜg₁ = −2Ric₁ zero-order terms.
6. **The exact system** (per compact slab `Icc a c`, c < b; constants slab-local,
   no global `Ico a b` constant): flux
   `Uᵃ = (g₁ᵃᵇ−g₂ᵃᵇ)∇²_b Rm₂ + g₁ᵃᵇ(∇¹_b−∇²_b)Rm₂`;
   `|∂ₜh| ≤ C|S|`; `|∂ₜA| ≤ C(|h|+|A|+|∇¹S|)`;
   `|∂ₜS − Δ₁S − div₁U| ≤ C(|h|+|A|+|S|)`; `|U| ≤ C(|h|+|A|)` (U contains NO
   ∇S — that is the divergence-form point). With `D = ∫|∇¹S|²`: principal gives
   −2D; the div U and ∂ₜA cross terms `∫|U||∇S|`, `∫|A||∇S|` absorb by Young
   into one D; `E′ ≤ CE − κD ≤ CE`. Edge: `h0` ⟹ h(a)=A(a)=S(a)=0, closed-edge
   continuity ⟹ E(a)=0; derivatives only on `Ioo a c`, close via the
   `edgeGronwall_zero` pattern; then E ≡ 0 ⟹ pointwise h = 0 by continuity +
   positivity, per subslab, sup over c.
7. **Brick board**: K1 `christoffelEvolutionDiffInFrameOn` (pure `.sub` of the
   two existing `ChristoffelEvolutionEquationInFrameOn` derivative facts +
   smallest pointwise identification with `connectionDiffLoweredInFrame`; NO
   star-sum API, NO new class) → K1-corollary pointwise `|∂ₜA₀₃|² ≤
   C(|h₀₂|²+|A₀₃|²+|∇¹S₀₄|²)`; K2 `rmDiffLowered_evolution_div_bound`
   (∂ₜS₀₄ = roughLap₁S₀₄ + div₁U₀₅ + R₀₄ with norm bounds on U₀₅, R₀₄ — THE
   dominant brick; needs single-flow tensor Rm evolution in one fixed variance,
   principal subtraction, flux extraction, reaction/flux estimates; the all-k
   Shi files are sources of realization/contraction lemmas, NOT substitutes);
   K3 `forwardUniqueEnergy`/`forwardUniqueRate` + `forwardUniqueEnergy_hasDerivAt`
   (exact differentiation only, zero estimation; mirrors
   `movingDiffEnergy`/`movingRate`); then `forwardUniqueRate_le`
   (≤ K·E − κ·Dissipation), edge-Gronwall, integral-zero-to-equality.
8. **Consume**: `Evolution/Connection/Christoffel.lean` (∂ₜΓ),
   canonical curvature realization/evolution (single-flow identity — confirm
   variance; not the scalar Bernstein route),
   `Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow`,
   `FiniteParametricIntegral.hasFDerivAt_integral_compact`,
   the lower-level moving-volume derivative that `MovingEdgeEnergy` uses
   (without importing that unverified file), `TensorConnLapLoweredIBP.lean`,
   `ricciEdgeMetric`, `edgeGronwall_zero`/integral Gronwall.
   **Do NOT rebuild**: HMF, RDT existence, rough-C⁰ stability, fixed-background
   weighted IBP, the all-orders Shi tower, a general star-sum framework,
   dim-3 curvature identities.
9. **Stop/re-consult gates**: (N)-gate — endpoint bootstrap only yields
   order-dependent shrinking horizons ⟹ stop, re-consult on the finite-order
   edge contract for K. K2-gate — needing a GLOBAL rm13/rm04 representation
   change, Shi-architecture modification, or a new cross-module commutator
   framework ⟹ stop and reassess (K2 must stay a local evolution/difference
   file + small bridges). K2 second signal — tensor IBP cannot pair
   `div₁U₀₅` against `S₀₄` invariantly without a global frame ⟹ stop; no
   chartwise-partition or fixed-background workaround without review.

## Verbatim ruling (as relayed; LaTeX markup as pasted)

Ruling
Approve the statement surgery. Reject the rough-(C^0) Burkhardt–Guim route for this consumer. For the resulting smooth-class theorem, choose route (K), using a moving (g_1(t))-carrier energy rather than fixed-(\bar g) norms and measure. Keep the theorem dimension-generic.
That ruling follows the architectural facts in the uploaded brief. The fetched branch still has `(N)` returning interior `Ioo` smoothness plus `Ico` continuity, `(A)` returning `t_star ∈ Ico α omega`, and `(B)` imposing `Ioo` smoothness plus `Ico` continuity. Your prompt says the local `(A)` has already been changed to `Ioo`; that local state is ahead of the fetched branch and should be synchronized before the consumer rewrite.
1. Statement surgery
Land the smallest possible signature change:

1. In `ricci_flow_unif_existence`, change only the domain of the `ContMDiffOn … ∞` output from `Set.Ioo 0 τ₀ ×ˢ baseSet` to `Set.Ico 0 τ₀ ×ˢ baseSet`. Keep the separate `ContinuousOn` field for now, although it becomes logically redundant.
2. In `ricci_flow_interior_restart`, require `t_star ∈ Set.Ioo α omega` and thread the strengthened `Ico 0 TT` smoothness field unchanged.
3. In `ricci_flow_forward_unique`, change the domains of `h1smooth` and `h2smooth` from `Ioo a b` to `Ico a b`. Keep `h1cont`, `h2cont`, both PDE hypotheses, and `h0` unchanged.

Keeping the continuity fields is deliberate. It minimizes API churn, preserves the current `MaximalTime.lean` and Brick-U wiring patterns, and avoids a cleanup commit being mixed into the analytic change.
The `MaximalTime.lean` rewiring is mechanical once `t_star > α` is available:

* For the ambient flow, restrict `chartGram_smooth_of_soln`, currently known on `Ioo α omega`, to `Ico t_star omega`. The needed inclusion uses the strict inequality `α < t_star`.
* For the shifted restart, change the current shift map proof from `Ioo t_star omega → Ioo 0 TT` to `Ico t_star omega → Ico 0 TT`.
* For `extend_construction_of_restart`, restrict the new `Ico 0 TT` restart smoothness field back to `Ioo 0 TT` with `.mono`; Brick U need not change.

The current consumer constructs exactly these two regularity adapters immediately before calling `(B)`.
Cost of up-to-corner (C^\infty) in the `(N)` lane
There is no apparent mathematical compatibility obstruction. The spatial manifold is closed, so there are no boundary operators and hence no spatial boundary compatibility sequence. For smooth initial data, the time derivatives at (t=0) are recursively determined by the quasilinear Ricci–DeTurck equation. Standard quasilinear parabolic theory on closed manifolds produces a solution smooth up to the initial time from smooth initial data. (arXiv:1010.0733)
However, it is not a free corollary of the existing interior-smoothing theorem in an (L^2)-maximal-regularity formalization. The sibling lane needs a real endpoint bootstrap:

1. Preserve the already constructed low-regularity solution and its same uniform horizon (\tau_0).
2. Bootstrap that solution on every compact `Icc 0 c`, (c<\tau_0), through arbitrarily high spatial Sobolev levels.
3. Identify the recursively determined time derivatives at (0).
4. Convert arbitrary finite parabolic regularity into mixed chart-Gram `ContMDiffOn` regularity and then assemble `∞`.

The wrong proof pattern would be to rerun the fixed point at each derivative order with horizons (\tau_k) and then take their intersection; those horizons could shrink to zero. The correct pattern is an a posteriori bootstrap of the one low-regularity solution on its already established horizon.
A useful qualification is that `(N)` does not need uniform high-order estimates over all admissible (g_0). Its common lifetime may continue to depend only on the existing ellipticity and order-(\le 3) bounds. For each individual smooth (g_0), the higher-order constants may depend on all of its higher derivatives. This makes the strengthening materially smaller than a new uniform (C^\infty) existence theory.
My cost ruling is therefore:

* mathematically standard;
* formally a material, medium-sized extension of `(N)`, probably a dedicated endpoint-bootstrap layer;
* still much smaller and much better aligned with `(N)` than building rough-(C^0) Ricci–DeTurck existence and stability.

The sibling lane should co-sign only after confirming that its trace and linear regularity APIs can bootstrap on a fixed horizon. If full `ContMDiffOn … ∞` proves disproportionately expensive, the correct fallback is interior (C^\infty) plus finite up-to-edge regularity sufficient for Kotschwar, not a return to the rough-(C^0) theorem. The estimates below only need bounded curvature and first covariant curvature derivative at the edge; a conservative finite joint-order contract can be chosen after the curvature-difference representation is fixed.
Keeping `(B)` as currently stated would commit the project to the two genuinely missing rough inputs identified in `RicciEdgeBounds.md`: a common-horizon Ricci–DeTurck solver for small (C^0) perturbations and a corresponding (C^0)-stability estimate. Burkhardt–Guim's theorem does give the relevant regularizing-flow uniqueness up to a stationary diffeomorphism, but formalizing its input theory here would be a new Koch–Lamm/Simon-scale foundation rather than an adapter. (arXiv:1907.13116)
2. Route ruling: choose (K), not (G)
Kotschwar's route is specifically designed to bypass both harmonic-map heat-flow existence and Ricci–DeTurck existence. In the compact case it uses the unweighted energy with (h=g_1-g_2), (A=\nabla^1-\nabla^2), and (S=\mathrm{Rm}_1-\mathrm{Rm}_2), obtaining (E'(t)\le CE(t)). Kotschwar takes one evolving metric as the reference metric for contractions, norms, and measure. (arXiv:1206.3225)
Route (G) has substantial algebra already, but that algebra is not the missing producer:

* `HarmonicTension.lean` proves `idTension_eq`, `tension_eq_push`, `tension_eq_DT`, and the HMF gauge-velocity identities.
* The HMF fixed-point layer has no geometric tension-field Nemytskii producer.
* More seriously, its claimed generic `(r,s)` support failed the first real build because two consumed Duhamel lemmas remain hard-coded to `(0,2)`. The file explicitly remains at 0% and is marked not to consume.
* Diffeomorphism persistence and the HMF-to-RDT gauge construction remain new geometric work.
* The existing pullback theorem still takes the raw variational-flow identity and an additive joint chain rule as honest hypotheses.
* Neither RDT-uniqueness half removes the HMF bottleneck. `MovingEdgeEnergy.lean` has the exact energy derivative and the Grönwall closure, but still needs its coercivity estimate; `DeTurckUniqueWindow.lean` is source-only and blocked upstream.

By contrast, route (K) has one dominant heavy gap: the tensor-level divergence-form evolution of the curvature difference. That is substantial, but it is a bounded tensor-calculus project. It introduces no auxiliary nonlinear PDE, no map-valued solution space, no diffeomorphism-persistence theorem, and no new gauge-back regularity theory.
3. Fixed background is sound, but do not implement it
The proposed fixed-(\bar g) formulation is mathematically sound on each compact slab `Icc a c`, (c<b).
Let (B_t) denote the positive bundle endomorphism converting the (g_1(t))-tensor inner product to the (\bar g)-inner product, and write (d\mu_{\bar g}=\rho_t\,d\mu_{g_1(t)}). Then (\int_M \langle S,\Delta_{g_1}S\rangle_{\bar g}\,d\mu_{\bar g}) can be integrated by parts using (g_1). Its leading term is (-\int_M \rho_t \langle B_t\nabla^1S,\nabla^1S\rangle_{g_1}\,d\mu_{g_1}), which is uniformly coercive on a compact slab. Derivatives of (B_t) and (\rho_t), equivalently the discrepancies involving (\nabla^1\bar g) and the two volume forms, produce terms bounded by (C|S||\nabla^1S|+C|S|^2). Young's inequality absorbs the first term into the coercive gradient term. Thus the fixed-background argument is valid.
It is nevertheless the wrong Lean formulation. It would require a new weighted, cross-metric tensor integration-by-parts layer that packages (B_t), (\rho_t), their covariant derivatives, and uniform ellipticity. The existing tensor Green identity is naturally stated with one metric simultaneously providing the connection, tensor inner product, and volume measure.
Use the Kotschwar carrier instead: (E(t)=\int_M (|h|_{g_1}^2+|A|_{g_1}^2+|S|_{g_1}^2)\,d\mu_{g_1}). Then:

* (\nabla^1g_1=0);
* the connection-Laplacian integration by parts has its exact principal sign;
* the derivative of the tensor norm contributes only a zero-order Ricci reaction;
* (\partial_t d\mu_{g_1}=-\operatorname{scal}(g_1)d\mu_{g_1}), again zero order.

The source-only `MovingEdgeEnergy.lean` already demonstrates the exact moving-norm/moving-measure first-variation pattern and the edge Grönwall closure. Treat it as design evidence rather than an import until its blocked dependencies build.
Recommended tensor variances
For the Lean implementation, lower the mixed differences with the carrier (g_1(t)): (h_{02} := g_1-g_2), (A_{03} := g_1(\nabla^1-\nabla^2,\cdot)), (S_{04} := g_1(\mathrm{Rm}^{1,3}_1-\mathrm{Rm}^{1,3}_2,\cdot)).
This has three advantages: (1) all three energy fields are `Tensor0S` objects; (2) the rank-uniform moving-metric norm derivative can be reused; (3) no new generic mixed-tensor time-derivative theory is needed. Lowering with (g_1) adds only terms involving (\partial_tg_1=-2\operatorname{Ric}_1), hence zero-order terms already absorbed into (CE).
4. The exact Kotschwar system to formalize
Fix (c\in(a,b)). All estimates are on the compact slab `Icc a c`; no global uniform constant on `Ico a b` is required.
Set (h=g_1-g_2), (A=\nabla^1-\nabla^2), (S=\mathrm{Rm}_1-\mathrm{Rm}_2). Define the curvature flux
(U^a = (g_1^{ab}-g_2^{ab})\,\nabla^2_b\mathrm{Rm}_2 + g_1^{ab}(\nabla^1_b-\nabla^2_b)\mathrm{Rm}_2).
The required pointwise system is
(|\partial_t h| \le C|S|),
(|\partial_t A| \le C(|h|+|A|+|\nabla^1S|)),
(|\partial_tS-\Delta_1S-\operatorname{div}_1U| \le C(|h|+|A|+|S|)),
and (|U|\le C(|h|+|A|)).
These are exactly the divergence-form organization in Kotschwar: the difference of the two Laplacians is not expanded into a dangerous second derivative of (h); it is packaged as `div U`, and (U) contains no (\nabla S). (arXiv:1206.3225)
Define (D(t)=\int_M|\nabla^1S|_{g_1}^2\,d\mu_{g_1}). The curvature principal term gives (-2D). The `div U` term and the (\partial_tA) term produce cross terms of the forms (\int |U||\nabla S|), (\int |A||\nabla S|). Young's inequality absorbs these into one copy of (D), leaving (E'(t)\le C E(t)-\kappa D(t)\le CE(t)).
At (t=a), `h0` implies: (h(a)=0); the two Levi-Civita connections agree, hence (A(a)=0); their curvature tensors agree, hence (S(a)=0).
Closed-edge smoothness gives continuity of all three fields, so (E(a)=0). The proof needs derivatives only on `Ioo a c`; it can use the same `edgeGronwall_zero` pattern as `movingEnergy_zero`, rather than proving a derivative at the endpoint. Kotschwar's compact argument likewise needs no weights or singular time powers. (arXiv:1206.3225)
Finally, (E(t)=0) implies the metric-difference integral is zero. Continuity and positivity of the norm then give (h(t,x)=0) for every (x), hence (g_1(t)=g_2(t)). Prove this on every strict compact subslab and choose (c) beyond the requested (t<b).
5. Small lemma frontier
A preliminary compactness lemma may collect slab constants, but it should remain private or file-local. The first three substantive bricks should be the following.
K1. Christoffel-difference time derivative
First prove the exact component subtraction, without star-sum estimates:

```lean
theorem christoffelEvolutionDiffInFrameOn
    {D : RealTimeInterval}
    (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (gInv₁ gInv₂ : ℝ → InverseMetricComponents M Idx)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic₁ nablaRic₂ : ℝ → M → Idx → Idx → Idx → ℝ)
    (h₁ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₁ gInv₁ frame hframe nablaRic₁)
    (h₂ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₂ gInv₂ frame hframe nablaRic₂) :
    ∀ (t : RealTimeInterval.RegularTime D) (x : M), x ∈ u →
      ∀ i j k,
        HasDerivWithinAt
          (fun s =>
            christoffelSymbolInFrame
                (S₁.family.connection s) frame hframe x i j k -
              christoffelSymbolInFrame
                (S₂.family.connection s) frame hframe x i j k)
          (christoffelEvolutionRHSInFrame
              gInv₁ nablaRic₁ t x i j k -
            christoffelEvolutionRHSInFrame
              gInv₂ nablaRic₂ t x i j k)
          D.carrier t
```

Its proof should be only subtraction of the two existing derivative facts. `ChristoffelEvolutionEquationInFrameOn` and the pointwise Christoffel derivative API already exist.
The immediate intrinsic corollary, still within K1, is the pointwise squared bound (|\partial_tA_{03}|_{g_1}^2 \le C(|h_{02}|_{g_1}^2+|A_{03}|_{g_1}^2+|\nabla^1S_{04}|_{g_1}^2)). This should consume inverse-metric difference, connection-difference-on-tensors, and Ricci-as-curvature-trace lemmas. Do not expose the exact expanded star expression as a public API.
K2. Divergence-form curvature-difference evolution
The dominant theorem should have this shape:

```lean
theorem rmDiffLowered_evolution_div_bound :
  ∃ C ≥ 0, ∃ U05 R04,
    -- componentwise time derivative on Ioo a c
    (∂ₜ S04 = roughLap₁ S04 + div₁ U05 + R04) ∧
    (∀ t ∈ Ioo a c, ∀ x,
      normSq0S (g₁ t) x 5 (U05 t x) ≤
        C * (normSq h02 + normSq A03)) ∧
    (∀ t ∈ Ioo a c, ∀ x,
      normSq0S (g₁ t) x 4 (R04 t x) ≤
        C * (normSq h02 + normSq A03 + normSq S04))
```

The equality should be represented by the project's existing componentwise `HasDerivAt`/`HasDerivWithinAt` convention, not by inventing a new Banach bundle derivative.
This theorem requires four honest pieces: (1) a tensor-level single-flow Riemann evolution in one fixed variance; (2) subtraction of the two principal operators; (3) extraction of the flux `U05`; (4) reaction and flux norm estimates.
The existing all-(k) files are single-flow norm heat equations; they are useful sources of realization and contraction lemmas, but they are not this difference-tensor theorem and should not be treated as a substitute.
K3. Moving triple-energy differentiation
Define `forwardUniqueEnergy` and an exact scalar `forwardUniqueRate`, following the structure of `movingDiffEnergy` and `movingRate`. Then prove

```lean
theorem forwardUniqueEnergy_hasDerivAt
    (t : ℝ) (ht : t ∈ Ioo a c) :
    HasDerivAt
      (forwardUniqueEnergy g₁ g₂)
      (forwardUniqueRate g₁ g₂ t)
      t
```

This theorem should do no analytic estimation. Its job is only: differentiate the three pointwise moving norms; differentiate the moving volume form; differentiate under the compact integral; assemble the exact rate.
After K3, the remaining assembly is cleanly separated:

```lean
forwardUniqueRate_le :
  forwardUniqueRate g₁ g₂ t ≤
    K * forwardUniqueEnergy g₁ g₂ t -
      κ * forwardUniqueDissipation g₁ g₂ t
```

followed by an edge-Gronwall lemma and the integral-zero-to-metric-equality lemma.
6. Existing layers to consume
Use the existing repository layers as follows:

* `Evolution/Connection/Christoffel.lean` for the exact (\partial_t\Gamma) component identity and `connectionDiffLoweredInFrame`.
* The canonical curvature realization/evolution files for the single-flow tensor identity, after confirming the exact variance. Do not route through the scalar Bernstein estimate.
* `Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow` for the rank-uniform moving-norm reaction.
* `Analysis/Integration/Measure/FiniteParametricIntegral.hasFDerivAt_integral_compact` for fixed-measure pieces of differentiation under the integral.
* The lower-level moving-volume derivative used by `MovingEdgeEnergy`; do not import the whole unverified DeTurck file merely to reuse its proof.
* `TensorConnLapLoweredIBP.lean` for the moving-(g_1) tensor integration by parts.
* `ricciEdgeMetric` for compact-slab metric equivalence rather than reproving it.
* `edgeGronwall_zero` or the already proved integral Grönwall layer for the final scalar closure.

Do not rebuild: harmonic-map heat flow; Ricci–DeTurck existence; rough-(C^0) stability; fixed-background weighted tensor IBP; the all-orders Shi tower; a general star-sum framework; dimension-three curvature identities.
7. Stop and re-consult signals
There are two hard gates.
`(N)` gate: stop if the endpoint bootstrap can only produce order-dependent existence times and cannot improve the already constructed solution on its fixed (\tau_0). Do not intersect shrinking horizons. Re-consult about replacing full `∞` at the edge by the finite regularity actually required by K.
Route-(K) gate: stop during K2 if obtaining the tensor-level curvature-difference equation requires changing the repository's canonical `rm13`/`rm04` representation globally, modifying the all-(k) Shi architecture, or introducing a new general curvature-commutator framework across several unrelated modules. K2 should be a local evolution/difference file plus small representation bridges. If it is not, the route cost must be reassessed before more infrastructure is built.
A second K2 stop signal is that the existing tensor IBP cannot pair `div₁ U05` against `S04` invariantly without assuming a global frame. Do not replace that gap with chartwise partitions or fixed-background weighted IBP without a new review.

## K1 kickoff prompt (dispatch AFTER the ste-align merge, path-adjusted if needed)

```text
Repository:
https://github.com/liao9yuan/differential-geometry
branch: codex/analytic-producers-e87b

Do only the first Route-(K) brick. Do not edit
ricci_flow_unif_existence, ricci_flow_forward_unique, MaximalTime.lean,
the HMF files, the curvature heat tower, or any energy file.

Create a small file, preferably

DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/
  ForwardUniqueConnectionDiff.lean

importing Evolution/Connection/Christoffel.lean.

Goal:

1. Prove an exact local-frame theorem
   christoffelEvolutionDiffInFrameOn:

   from two ChristoffelEvolutionEquationInFrameOn hypotheses for S₁ and S₂
   using the same local frame, derive the HasDerivWithinAt formula for

     Γ(S₁) - Γ(S₂)

   with derivative

     christoffelEvolutionRHSInFrame(S₁)
       - christoffelEvolutionRHSInFrame(S₂).

   The proof should be the direct `.sub` of the two existing derivative facts.
   Do not introduce a new class, axiom, wrapper assumption, or star-sum API.

2. Add only the smallest pointwise evaluation lemma needed to identify that
   component difference with the existing connection-difference component
   (`connectionDiffLoweredInFrame` or the raised equivalent). Do not yet prove
   the h/A/∇S norm estimate.

3. Give the theorem a focused build and print its axioms. It must be sorry-free
   and depend only on the standard logical axioms already present in the file.

STOP and report the exact type mismatch rather than broadening scope if:
- the two RF Christoffel evolution hypotheses cannot be instantiated with a
  common local frame without changing SolutionOn or frame APIs; or
- passing from the component difference to the intrinsic connection-difference
  object would require a global frame or a new atlas/partition construction.

Do not begin the curvature-difference evolution or the energy assembly in this
step.
```
