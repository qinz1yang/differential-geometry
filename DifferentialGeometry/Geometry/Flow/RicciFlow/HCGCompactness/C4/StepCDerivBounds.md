# StepCDerivBounds.lean — MSM135 C2 (`lbl430`), the QUANTITATIVE derivative-bounds half

## 2026-07-19: (c4) and the (c5) induction-step engine LANDED

`C4/StepCDerivAll.lean` (new leaf file, focused-green, no `sorry`) now
provides sub-brick (c4) — `norm_iteratedFDeriv_clmComp_le`, the bilinear
collection at `compL` in `ContDiffAt` currency — and the (c5) induction-step
engine `implicitDeriv_succ_le`:
`‖∇^{m+1} f‖ ≤ 2^m·(m!·(m!·(max Λ 1)^{m+1})·(max DA 1)^m)·CB` from the
neighbourhood formula + block bounds.  The remaining all-order work is now
assembly: the recursive majorant definition, the strong induction, and the
cm-wiring generalizing `cmChartDerivLe2` — scoped in `StepCDerivAll.md`.
This discharges the "explicit recursive numerical majorant" precondition
below for finally stating the arbitrary-order theorem.

## Current state — 2026-07-09: false all-order statement removed

The former `cmChartDerivLe` was unprovable: it assumed only `C²` regularity and constrained
`Ctil` only at orders 0, 1, and 2, yet concluded bounds for every `j ≤ pOrd`.  It has been removed.

The checked replacement is `cmChartDerivLe2`, which states exactly the order-0/1/2 result and has
no `sorry`.  The arbitrary-order textbook theorem remains 0% and is deliberately not stated until
the API carries both:

- order-`p` regularity for the center family and the joint equation;
- an explicit recursive numerical majorant constructing `Ctil j` from `Λ`, `B`, and lower-order
  constants.

The existing inverse/graph Faà-di-Bruno lemmas are reusable machinery, but the common-open-set
bilinear estimate, recurrence design, and strong induction are substantive remaining work, not
“pure threading.”

The generic Banach-algebra inverse estimates formerly local to this file now
live in `Analysis/Calculus/RingInverseDeriv.lean`; this module imports and reuses
that canonical API.  The extraction and focused verification passed.  It does
not change the separate arbitrary-order center-map frontier described above.

## Goal
`lbl430`(i) bounds half (eq `lbl431`): the center of mass has **uniform-in-configuration**
covariant-derivative bounds `|∇_q^α ∇_μ^β cm| ≤ C̃_{|α|+|β|+1}` for all orders, at the book scale
`r < c(n)/√C₀`, `inj(q) > 3r`. This gates production of the arbitrary-`p` bounds carried by
`StepB1RawInput` (B1 consumes the
`comp_cov_le`/`comp_cov_accum` shape). `centerOfMass_contDiffAt` (lbl430(ii), the C^n REGULARITY)
gives smoothness but NOT the uniform constants — regularity ≠ bounds.

## Route (verified against the book BEFORE coding — chapter4.tex L2709+, proof of `lbl430`(i))
The book applies the IFT to `G(q) = Σ μᵢ exp_q⁻¹ qᵢ`, `cm` = the unique zero, then:
1. `∇_q G` positive definite, smallest eigenvalue `≥ λ_min(C₀, Σμ)` (**Lemma `lbl413`**) ⟹
   `‖(∇_q G)⁻¹‖ ≤ Λ := 1/λ_min`.
2. `∇_{qᵢ} G = μᵢ ∇_{qᵢ} exp_q⁻¹ qᵢ`, `∂_{μᵢ} G = exp_q⁻¹ qᵢ`; their `≤j` derivatives are bounded
   by `B_j` via **Prop `lbl418`(i)** (= S6, `ExpInverseDerivBoundInput`, r₁-capped, audited TRUE).
   Weights enter LINEARLY (`Σ μᵢ • …`), so `‖∇^j G‖ ≤ (Σ|μᵢ|)·B_j`.
3. Differentiate the implicit relation `G(cm(params), params) = 0` (eq `lbl432`): at order 1,
   `∂_z G · D cm + ∂_p G = 0` ⟹ `D cm = −(∂_z G)⁻¹ ∂_p G`, `‖D cm‖ ≤ Λ·B₁`. Higher orders: take
   `|α|+|β|−1` derivatives of `lbl432`, isolate the top term `∂_z G · D^j cm = −(polynomial in
   `D^{<j} cm` and `D^{≤j} G`)`, so `D^j cm = −(∂_z G)⁻¹ · poly`, bounded by induction with `Λ`,
   `B_{≤j}` and the lower `C̃_{<j}`. Endpoint: `|∇^j (chart∘cm)| ≤ C̃_j(Λ, B_{≤j}, Σμ)`, `j ≤ p`.

**Explicitly NOT** a general quantitative-IFT engine, and NOT via `Φ⁻¹`-derivative bounds
(Mathlib has none): the book inducts on the implicit relation, which we mirror.

## Feasibility (which sub-steps reduce to existing API)
- **(1) `‖L⁻¹‖ ≤ Λ`** — pure structure/Prop field. The invertibility `L` is already the
  `CmHessianInput` datum; the new content is the norm bound. Honest input (lbl413 Neumann), green.
- **(2) `‖∇^j G‖ ≤ B_j`** — `chartCmEqn'` is `Σ μᵢ • readoutᵢ` with `readoutᵢ` the trivialization
  readout of `diagExpInv` = (up to the trivialization CLE) the double-exp `exp_{exp_p z}⁻¹(exp_p ξ)`.
  `norm_iteratedFDeriv_comp_le` (Mathlib `ContDiff/Bounds.lean`) + `norm_iteratedFDeriv_mul_le` are
  the Faà-di-Bruno BOUND engine. `j=0` reduces to S6-`p=0` boundedness on the r₁ ball directly;
  `j≥1` needs the readout-chain comp-bound transfer (a minimal Faà-di-Bruno-bounds sibling of
  `MapConvergenceComp` — the double-exp composition + trivialization-CLE constant). Stated as an
  honest input `CmGDerivBound` with the reduction documented; the transfer is deferred (not a
  framework).
- **(3) base case `j=1`** — PROVABLE natively and done here (`implicitDeriv_one_le`): chain-rule
  `fderiv` of `G(f,·)=0`, extract the z-block `L`, `Df = −L⁻¹ ∂_pG`, `‖Df‖ ≤ Λ·B`. Uses only
  `HasFDerivAt.comp`/`.unique`, `opNorm_le_bound`, `le_opNorm`. Green.
- **(3) general `j`** — the Faà-di-Bruno EXPANSION of `iteratedFDeriv^j (G∘(f,id))` isolating the
  leading `∂_z G · D^j f` is the genuine frontier. Mathlib's `norm_iteratedFDeriv_comp_le` gives the
  BOUND but not the algebraic isolation of the top term.  No arbitrary-order endpoint is currently
  stated; the recurrence, common-neighborhood bookkeeping, and strong induction remain to be built.

## Historical state (2026-07-06)
- `implicitDeriv_one_le` (abstract, E-only): GREEN — the j=1 base, real math content.
- `CmHessianBoundInput` (structure, `‖L.symm‖ ≤ Λ`): GREEN honest input, audit-rule docstring.
- `CmGDerivBound` (Prop, `∀ j ≤ p, ‖iteratedFDeriv j G‖ ≤ B j`): GREEN honest input, S6-reduction
  docstring.
- `cmChartFDerivLe` (j=1 chart-center endpoint, `‖iteratedFDeriv 1 (chart∘cm)‖ ≤ Λ·B₁`): GREEN,
  specializes `implicitDeriv_one_le` at `chartCmEqn'`.
- **`norm_iteratedFDerivWithin_ringInverse_le` / `norm_iteratedFDeriv_ringInverse_le`
  (+ `contDiffOn_ringInverse`): GREEN, axiom-clean (2026-07-06)** — the quantitative Neumann bound
  `‖∇^i (Ring.inverse) x‖ ≤ i!·‖x⁻¹‖^{i+1}` (Route A ingredient 2), the minimal missing Mathlib API.
- **`implicitFDeriv_eq` (pointwise) + `implicitFDeriv_eventuallyEq` (neighbourhood): GREEN,
  axiom-clean (2026-07-06)** — Route A **ingredient (a)**, the neighbourhood implicit-derivative
  formula `∇f =ᶠ[𝓝 params₀] fun p => −(Ring.inverse (∂_zG(f p,p))).comp (∂_pG(f p,p))`, where
  `∂_zG = Dⱼ∘inl`, `∂_pG = Dⱼ∘inr` are the joint-derivative blocks.  Abstract (general `P`), from
  `f`/`G` eventually differentiable + the IFT relation `G(f,·)=0` + eventual `z`-block invertibility;
  the per-point proof chain-rules `G(f,·)=0`, reads off `∂_zG∘Df = −∂_pG`, and left-composes
  `Ring.inverse` via `Ring.inverse_mul_cancel` (with `ContinuousLinearMap.mul_def`/`one_def`).
- **(b) j=2 DONE (2026-07-07, GREEN, axiom-clean):** `graphBlockDeriv` (step (1) engine: the block
  family `p ↦ (H (f p,p)).comp j` is differentiable with `‖D'‖ ≤ ‖H'‖·max ‖Df₀‖ 1`, for `‖j‖ ≤ 1`
  — the book's `‖∇(∂G∘graph)‖ ≤ ‖∇²G‖·(‖∇f‖+1)`); `implicitDeriv_two_le` (the abstract order-2
  bound `‖∇²f‖ ≤ Λ²·a₂·b₁ + Λ·b₂`, differentiating the neighbourhood formula once via
  `hasFDerivAt_ringInverse` + `clm_comp`); `CmHessianNbhdInput` (the neighbourhood Hessian input
  bound to the center family, audit-rule docstring); and the **endpoint j=2 case fully wired** —
  `hf2`/`hG2` (`C²` regularity from lbl430(ii)) → eventual differentiability, `hnbhd` → eventual
  invertibility + `Λ`, `graphBlockDeriv` at `inl`/`inr` from `‖∇²G‖ ≤ B 2` and `‖∇f‖ ≤ Λ·B₁`,
  constant `C̃₂ = Λ'²·a₂·B₁ + Λ'·a₂`, `a₂ = B₂·(Λ·B₁+1)` (`hC2`).
- Historical: the former `cmChartDerivLe` discharged j=0/j=1/j=2 and left j≥3 as a `sorry`.
  That statement has now been removed because its hypotheses did not justify the higher orders;
  the checked low-order replacement is `cmChartDerivLe2`.
- Historical verification passed; `implicitDeriv_one_le`, `cmChartFDerivLe`,
  `norm_iteratedFDeriv_ringInverse_le`, `implicitFDeriv_eq`, `implicitFDeriv_eventuallyEq`,
  `graphBlockDeriv`, `implicitDeriv_two_le` all axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Partial j≥3 reusable machinery (2026-07-07); no all-order endpoint
- `multilinear_prod_opNorm_le` (`‖M.prod N‖ ≤ max ‖M‖ ‖N‖`), `norm_iteratedFDeriv_id_le`,
  `norm_iteratedFDeriv_graph_le` (`‖∇^i (f,id)‖ ≤ max ‖∇^i f‖ 1` via `iteratedFDeriv_prodMk`).
- `norm_iteratedFDeriv_invComp_le`: `‖∇^m (Ring.inverse ∘ A) x‖ ≤ m!·(m!·(max Λ 1)^{m+1})·D^m`
  (Faà-di-Bruno on the open unit set, Neumann outer bounds; eventually-unit + `C^m` inputs).
- `norm_iteratedFDeriv_graphComp_le`: `‖∇^m (H(f·,·)) x‖ ≤ m!·C·D^m` (Faà-di-Bruno through the
  graph; with `H := fderiv G` this bounds `‖∇^i ∂G‖` from `B_{i+1}` + the induction hypotheses).
- Elaboration notes: `ContDiffAt.contDiffOn le_rfl (by simp)` (the `m = ∞ → n = ω` guard);
  MapsTo defeq walls fixed via intermediate `have h : p ∈ {q | …}` + `simpa [Set.mem_setOf_eq]` /
  `Set.mem_preimage.mp`; pow monotone names are `pow_le_pow_left₀` / `pow_le_pow_right₀`
  (`pow_le_pow_right'` needs `MulLeftMono`, fails on ℝ); `ContDiffAt.differentiableAt` takes
  `n ≠ 0` (not `1 ≤ n`) — `(by norm_num)`.

**Remaining higher-order work (c4/c5):** this is substantive producer work, not merely assembly.
(c4) the bilinear collection
`‖∇^m ((inverse∘A)·B)‖ ≤ Σ C(m,k)·…` via `norm_iteratedFDerivWithin_le_of_bilinear` at `compL`
(`norm_compL_le`), + `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` for the fixed
`Φ = (compL).flip inl/inr` post-composition (`‖Φ‖ ≤ 1` via `norm_flip` + `norm_compL_le`);
(c5) recursive constants `C̃` + the strong induction for a future honest all-order theorem, feeding
(c4) with `Dj q := fderiv G (graph q)`, the IH, `hnbhd`, and per-order `CmGDerivBound`/regularity
(order-`pOrd` hypotheses).  The existing bricks substantially reduce the problem, but c4/c5 still
require a real recurrence/API design and common-neighborhood bookkeeping.

## What (c) j≥3 still needed (pre-brick scoping, superseded)
Strong induction with IH `‖itF i f‖ ≤ C̃ i` (i < j): bound `‖itF (j−1) RHS‖` by (i) the bilinear
engine `norm_iteratedFDerivWithin_le_of_bilinear` at `compL` for the product `(inverse∘A)·B`;
(ii) `norm_iteratedFDeriv(Within)_comp_le` for `inverse∘A` (outer bounds = the proved Neumann
`i!·Λ^{i+1}`; inner `‖itF k A‖` from ANOTHER comp_le on `(fderiv G)∘graph` — outer bounds
`‖itF k (fderiv G)‖ = ‖itF (k+1) G‖ ≤ B_{k+1}`, inner = the pair `(f,id)` whose itF needs a
prodMk-itF lemma + the IH); (iii) Within-set bookkeeping on an open nbhd (the global-`ContDiff`
demands of the comp/bilinear lemmas don't hold; work `Within` an open set where the eventual
hypotheses hold, as in the Neumann lemma).  Genuinely a full session: the pair-itF algebra, the
`D^i`-shape conversion (`D := 1 + Σ Cᵢ`), and the recursion constants.

## Historical pre-order-two scoping (2026-07-06; superseded)

At that snapshot ingredient (a) (the neighbourhood formula) was green, while the old
`cmChartDerivLe` proof still had a `sorry`; the CM
wiring remains (all API paths confirmed to exist, but the CM-specific bounds are substantial):
1. **Neighbourhood invertibility input** (component ①): the endpoint needs
   `∀ᶠ p in 𝓝 params₀, IsUnit (∂_zG(chart(c p), p)) ∧ ‖Ring.inverse (∂_zG(chart(c p), p))‖ ≤ Λ`.
   Depends on the center family `c`, so it is an **endpoint hypothesis / new input tied to `c`**, NOT
   a field of `CmHessianBoundInput` (which does not know `c`).  Audit-rule docstring: why-true =
   below convexity radius `∂_z(exp⁻¹) ≈ −id` + Neumann, same as the point version; scale = lbl413;
   discharger = per-configuration honest input.
2. **`f`, `G` eventually differentiable** — from lbl430(ii) `C^n` regularity: `ContDiffAt … n … ⟹
   ∀ᶠ HasFDerivAt` (Mathlib `HasFTaylorSeriesUpToOn.eventually_hasFDerivAt` family / `ContDiffAt →
   ContDiffOn → eventually`).  Feed `implicitFDeriv_eventuallyEq` to get `∇f =ᶠ RHS`.
3. **(b) j=2 bound**: `‖iteratedFDeriv 2 f‖ = ‖fderiv (fderiv f) params₀‖ = ‖fderiv RHS params₀‖`
   (via `norm_iteratedFDeriv_one` + `norm_iteratedFDeriv_fderiv` + `EventuallyEq.fderiv_eq` on
   `∇f =ᶠ RHS`).  `fderiv RHS` via `HasFDerivAt.clm_comp` (CompCLM.lean:61) of `invA = Ring.inverse ∘
   A` (chain rule with `hasStrictFDerivAt_ringInverse`) and `Bp`.  Bounding `‖fderiv RHS‖` needs
   `‖Ring.inverse (A p₀)‖ ≤ Λ`, `‖fderiv (inverse∘A)‖ ≤ Λ²·‖fderiv A‖` (from `fderiv_inverse` /
   `norm_iteratedFDeriv_ringInverse_le` i=1), and **the CM-specific `‖fderiv A‖`, `‖fderiv Bp‖`,
   `‖Bp‖` bounds — these relate to `∇²(chartCmEqn')` (via `A p = ∂_zG(f p,p)` = a block of the joint
   fderiv, differentiated through `(f,id)`) and are the genuinely large remaining CM piece**, drawn
   from `CmGDerivBound` at order 2 + the j=1 bound.
4. **(c)** general-`j`: strong induction `D^j f = D^{j−1}(RHS)` via `norm_iteratedFDeriv_comp_le`,
   `C̃` recursive.

## Audit of Route A's missing API (2026-07-06) — what Mathlib has vs. lacks
- **HAS**: inverse *regularity* `contDiffAt_ringInverse` / `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`
  (`ContDiffAt 𝕜 n inverse`, all `n`); the *first-order* formula `fderiv_inverse` /
  `hasStrictFDerivAt_ringInverse` (`∇(inverse) = −mulLeftRight x⁻¹ x⁻¹`); the bilinear iterated
  bound `ContinuousLinearMap.norm_iteratedFDeriv(Within)_le_of_bilinear`; `analyticAt_inverse`;
  `norm_iteratedFDeriv_comp_le` (Faà-di-Bruno composition bound).
- **LACKED** (now supplied here): the quantitative `‖∇^i inverse‖ ≤ i!·Λ^{i+1}` Neumann bound
  (only the scalar `1−z•a` power series was in Mathlib) — proved by strong induction on `i` from
  `∇(inverse) = −mulLeftRight(inverse, inverse)` + the bilinear bound (`‖mulLeftRight‖ ≤ 1`) +
  `Σ_{k≤m} C(m,k)·k!·(m−k)! = (m+1)!`.  Still LACKS: any inverse-*function* iterated-derivative
  bound (why Route A goes through the CLM `inverse`, not `Φ⁻¹`).

## Elaboration lessons for the inverse bound (cost real time)
- The nested-CLM `Norm (R →L R →L R →L R)` does NOT synthesize when written STANDALONE (`have hBle :
  ‖-mulLeftRight 𝕜 R‖ ≤ 1`), but DOES inside the bilinear-lemma application (its signature carries the
  instance).  FIX: never write the norm term yourself — inline `(opNorm_neg _).trans_le
  (opNorm_mulLeftRight_le 𝕜 R)` into `mul_le_mul`, unifying the norm instance with the goal's.
  A `synthInstance.maxHeartbeats` bump does not fix it (genuine, not a timeout).
- `Norm`-instance diamond: `norm_neg` uses `SeminormedAddGroup.toNorm`, the CLM opNorm term uses
  `hasOpNorm` — they don't unify; use the CLM-specific `ContinuousLinearMap.opNorm_neg`.
- `Σ` (U+03A3) is a RESERVED token (Sigma-type binder) — cannot be used in an identifier (`hΣ`
  fails to parse); use `∑` (U+2211) for sums and ASCII names.
- `contDiffOn_ringInverse` built from `contDiffAt_ringInverse` via `obtain ⟨u, rfl⟩ := hy`
  (destructure `IsUnit`) `.contDiffWithinAt`; the `Within` induction uses
  `norm_iteratedFDerivWithin_fderivWithin` (n+1↔n), `EventuallyEq.iteratedFDerivWithin_eq` +
  `fderivWithin_of_isOpen` (rewrite `fderivWithin inverse S` to `−mulLeftRight(inverse·)(inverse·)`),
  `iteratedFDerivWithin_of_isOpen` (ambient corollary).

## Elaboration lessons (cost real time)
- **Instance setup for `chartCmEqn'` in a downstream file:** each declaration referencing it needs
  `attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup Tensor0SBundle.tangentSpace_normedSpace in`
  BEFORE its docstring, AND `[IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]` as a
  per-declaration hypothesis (NOT a section variable).  Removing the `Tensor0SBundle` instances is
  what *enables* the scoped `Bundle.RiemannianBundle` inner-product chain (`∀ x, InnerProductSpace ℝ
  (TangentSpace I x)`, a prereq of `IsContinuousRiemannianBundle`); with them present a diamond blocks
  it.  Mirror StepCSmoothness exactly (attribute → docstring → decl).  A section variable fails.
- **`HasFDerivAt.comp` for `fun p => G (f p) p`:** Lean mis-guesses the inner map as
  `Prod.mk (f params₀)` (it fits `hGf`'s point `(f params₀, params₀)`, unlike a constant-second-comp
  inner as in `hLz`).  FIX: fully pin `HasFDerivAt.comp (𝕜:=ℝ)(E:=)(F:=)(G:=)(f:=)(g:=) params₀ hGf
  hpair`, and take the result via `have hcomp := …` **unascribed** — ascribing `hcomp`'s type inserts
  a coercion that leaves a `Module ?m E` metavar which stucks every later consumer (`.unique`,
  `.fderiv`).  Then `hcomp.unique hconst` with `hconst` in the matching raw `_ ∘ _` form.
- **`(x, 0) + (0, y) = (x, y)`** has no simp lemma (`Prod` add projections aren't `@[simp]`); it is
  definitional, so `Prod.ext (add_zero x).symm (zero_add y).symm` closes it by defeq.

## Honest position
This is the QUANTITATIVE half of C2.  The regularity half and the order-two quantitative theorem are
checked; the arbitrary-order theorem is not stated and remains 0%.  Its dedicated reusable
machinery is roughly 70–80%, but B1's arbitrary `(ε,p)` producer remains gated on the recurrence and
strong-induction endpoint.  At project scale, the whole HCG program is conservatively about **45%
machinery**, while its endpoint theorems remain **0%**.
