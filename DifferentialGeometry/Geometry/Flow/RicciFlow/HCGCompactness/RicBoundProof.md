# Lemma 3.11 — corrected formalization spec (user-supplied, 2026-06-08)

Canonical proof to formalize against. Replaces MSM135's schematic argument (whose
telescoping and mixed-derivative Leibniz do not line up). Constants change line to
line, may depend on `n, C, β, ψ, t₀, {C_p}, {C̄_p}` (where `|∇_k^p Rm_k|_k ≤ C̄_p`
is the assumed curvature bound), but **never on `k`**.

`I = [β,ψ]`. `∇, Γ, |·|` = Levi-Civita / Christoffel / norm of the FIXED background
`g`. `∇_k, Γ_k, |·|_k` = same for `g_k(t)`. `S ∗ T` = a universal finite linear
combination of contractions of `S⊗T`, constants depending only on `n` and types.

## KEY CORRECTIONS (load-bearing — do NOT revert)
- Do NOT use `∇−∇_k = Γ−Γ_k` directly as `∇g_k`. Define `A_k := ∇−∇_k` (a genuine
  (1,2)-tensor), then use `A_k = g_k⁻¹ ∗ ∇g_k` and `∇g_k = A_k ∗ g_k`, and prove
  `|∇^m A_k| ≤ C_m (1 + |∇^{m+1} g_k|)` separately (Claim 1).
- Gronwall uses `|t−t₀|` (both time directions), else only `t ≥ t₀` is covered.
- Mixed derivatives: expand `∇ = ∇_k + A_k∗`; the curvature factor stays PURE `∇_k`
  (Shi-bounded), the `A_k`-factors are fixed-`∇` (Claim-1-bounded). No mixed-
  curvature factor survives.

## Step 1 — uniform equivalence `g_k(t) ~ g`  [= eq (3.3), ALREADY DONE in P1]
`|Rm_k|_k ≤ C̄_0 ⇒ |Rc_k|_k ≤ C(n)C̄_0 ⇒ −C'_0 g_k ≤ Rc_k ≤ C'_0 g_k`.
`∂_t g_k(V,V) = −2 Rc_k(V,V)` ⇒ `|∂_t log g_k(V,V)| ≤ C'_0` ⇒ integrate ⇒
`e^{−C'_0|t−t₀|} g_k(t₀) ≤ g_k(t) ≤ e^{C'_0|t−t₀|} g_k(t₀)`. With initial
`C⁻¹g ≤ g_k(t₀) ≤ Cg`: set `B_* = C e^{C'_0(ψ−β)}`, get `B_*⁻¹ g ≤ g_k(t) ≤ B_* g`
on `K×I`. Hence uniform norm equivalence `|T| ≤ C|T|_k`, `|T|_k ≤ C|T|`.

## Step 2 — first-order `|∇g_k| ≤ C`  (the p=1,q=0 case)
`A_k := ∇−∇_k`, `(A_k)^c_{ab} = Γ^c_{ab} − (Γ_k)^c_{ab} = −½ g_k^{cd}(∇_a g_{k,bd}
+ ∇_b g_{k,ad} − ∇_d g_{k,ab})` (both torsion-free). Schematically `A_k = g_k⁻¹∗∇g_k`;
conversely (`∇_k g_k = 0`) `∇g_k = (∇−∇_k)g_k = A_k ∗ g_k`, so `|∇g_k| ≤ C|A_k|`.
Bound `A_k`: `∂_t A_k = −∂_t Γ_k` (Γ fixed), `∂_t Γ_k = −g_k⁻¹∗∇_k Rc_k`, so
`|∂_t A_k|_k ≤ C|∇_k Rc_k|_k ≤ C|∇_k Rm_k|_k ≤ C`, hence `|∂_t A_k| ≤ C`. At `t₀`,
`|A_k(t₀)| ≤ C|∇g_k(t₀)| ≤ C`. Integrate: `|A_k(t)| ≤ |A_k(t₀)| + ∫_{t₀}^t |∂_s A_k| ≤ C`.
So `|∇g_k(t)| ≤ C|A_k(t)| ≤ C`.

## Step 3 — two bookkeeping lemmas
**Claim 1 (derivatives of A_k).** For every `m ≥ 0`, `∇^m A_k` is a universal finite
sum of contractions `g_k⁻¹ ∗ ⋯ ∗ g_k⁻¹ ∗ ∇^{a_1}g_k ∗ ⋯ ∗ ∇^{a_ℓ}g_k` with `ℓ≥1`,
`a_j≥1`, `Σa_j = m+1`. Hence `|∇^m A_k| ≤ C_m(1 + |∇^{m+1}g_k|)`, provided
`|∇^r g_k|` (1≤r≤m) are already bounded. Proof: differentiate `A_k = g_k⁻¹∗∇g_k`
`m` times; whenever `∇` hits `g_k⁻¹` use `∇(g_k⁻¹) = −g_k⁻¹∗(∇g_k)∗g_k⁻¹`.

**Claim 2 (mixed derivatives).** If `|∇^r g_k| ≤ C_r` for `1≤r≤L`, then for all
`a,b≥0` with `a+b ≤ L`: `|∇^a ∇_k^b Rm_k| ≤ C_{a,b}` (same for `Rc_k`, `R_k`).
Proof: expand `∇^a T` (via `∇=∇_k+A_k`) as a finite sum of
`∇^{r_1}A_k ∗ ⋯ ∗ ∇^{r_ℓ}A_k ∗ ∇_k^s T` with `s + Σ(r_j+1) = a`. Apply to
`T = ∇_k^b Rm_k`: curvature factor `∇_k^{s+b}Rm_k` is Shi-bounded (`s+b ≤ a+b ≤ L`),
`A_k`-factors bounded by Claim 1 (`r_j+1 ≤ a ≤ L`).

## Step 4 — induction on N≥1 for all spatial derivatives of g_k
`(A_N): |∇^N Rc_k| ≤ C'_N |∇^N g_k| + C''_N`.  `(B_N): |∇^N g_k| ≤ C̃_{N,0}`.
N=1: `∇Rc_k = ∇_k Rc_k + A_k∗Rc_k`, both bounded ⇒ `|∇Rc_k|≤C`; with `|∇g_k|≤C` gives
(A_1),(B_1).
Step N (assume (A_r),(B_r) for 1≤r<N):
- Telescoping: `∇^N Rc = ∇_k^N Rc + Σ_{i=1}^N ∇^{N-i}(A_k ∗ ∇_k^{i-1}Rc)`
  (from `∇^N − ∇_k^N = Σ_{i=1}^N ∇^{N-i}(∇−∇_k)∇_k^{i-1}`, `∇−∇_k = A_k∗`).
- `|∇_k^N Rc| ≤ C` (Shi).
- i=1 term `∇^{N-1}(A_k∗Rc)`: Leibniz `≤ C Σ_{j=0}^{N-1}|∇^{N-1-j}A_k||∇^j Rc_k|`.
  j=0: `|∇^{N-1}A_k| ≤ C(1+|∇^N g_k|)` (Claim 1) × `|Rc_k|≤C` ⇒ `C(1+|∇^N g_k|)`.
  j≥1: `|∇^j Rc_k|` bounded (IH), `|∇^{N-1-j}A_k|` bounded (Claim 1, order ≤N-2). So
  `|∇^{N-1}(A_k∗Rc)| ≤ C|∇^N g_k| + C`.
- 2≤i≤N terms: `≤ C Σ_{j=0}^{N-i}|∇^{N-i-j}A_k||∇^j∇_k^{i-1}Rc_k|`; `N-i-j ≤ N-2` (A_k
  bounded, Claim 1), `j+i-1 ≤ N-1` (mixed bounded, Claim 2). So each `≤ C`.
- Combine ⇒ `(A_N)`.
- `(B_N)`: `∂_t∇^N g_k = ∇^N∂_t g_k = −2∇^N Rc_k` (∇ fixed in t). `u := |∇^N g_k|²`
  (norm w.r.t. fixed g): `∂_t u = −4⟨∇^N Rc_k, ∇^N g_k⟩`, `|∂_t u| ≤ 4|∇^N Rc_k||∇^N g_k|
  ≤ (A_N) ≤ λ_N u + μ_N`. Integrate from t₀ both directions (|t−t₀|≤ψ−β):
  `u(t) ≤ e^{λ_N|t−t₀|}u(t₀) + (μ_N/λ_N)(e^{λ_N|t−t₀|}−1)`, `u(t₀)≤C_N²` ⇒
  `|∇^N g_k(t)| ≤ C̃_{N,0}`.
p=0 case from metric equivalence.

## Step 5 — time derivatives `|∂_t^q ∇^p g_k| ≤ C̃_{p,q}`, q≥1
`∂_t^q∇^p g_k = ∇^p∂_t^q g_k = −2∇^p∂_t^{q-1}Rc_k` (∇ fixed). Reduce to bounding
`|∇^p∂_t^m Rc_k|`. Curvature evolution `∂_t Rm_k = Δ_k Rm_k + Rm_k∗Rm_k`, commutator
`[∂_t,∇_k]T = (∇_k Rc_k)∗T`: by repeated t-differentiation, `∇_k^r∂_t^m Rm_k` is a
universal finite sum of contractions of `∇_k^{a_j}Rm_k` (the `a_j` bounded by `r,m`),
so `|∇_k^r∂_t^m Rm_k|_k ≤ C_{r,m}` (Shi); same for `Rc_k`,`R_k` (5). Convert `∇_k→∇`
via `∇=∇_k+A_k` and `|∇^a A_k|≤C_a` (Claim 1, all metric derivs now bounded):
`|∇^p∂_t^m Rc_k| ≤ C_{p,m}`. With m=q-1 ⇒ `|∂_t^q∇^p g_k| ≤ C̃_{p,q}`.

## Formalization DAG (dependency order)
0. [DONE] Step 1 = eq(3.3) (`metricUniformEquivalentOnWindow_of_solutions`).
   [DONE] Piece-1 tower realization `iterCovComp_eq_iterCov` (gRef ∇^a of any field).
1. `∗`-contraction + base norm bound `|S∗T| ≤ K|S||T|` + `∇`-commutes-`∗`(∇g=0).
2. **Contraction-Leibniz norm bound** `|∇^m(S∗T)| ≤ K Σ_c binom(m,c)|∇^c S||∇^{m-c}T|`
   (the crux; reuses tensor-product single-step Leibniz `nabla0S_product_realizes`
   + naturality + `normSq0S_product`, all built).
3. Inverse-metric `∇(g⁻¹)=−g⁻¹∗∇g∗g⁻¹`, `|∇^m g⁻¹| ≤ C_m`; A_k = `connectionDifferenceTensorAt`,
   `A_k=g⁻¹∗∇g`, `∇g=A_k∗g`; Claim 1 `|∇^m A_k| ≤ C_m(1+|∇^{m+1}g|)`.
4. Claim 2 mixed `|∇^a∇_k^b Rm_k| ≤ C` (∇=∇_k+A_k expansion bound).
5. Step 4: telescoping + (A_N) + (B_N) Gronwall (`metricCovOrderWindow_of_evolution`).
6. Step 5: time derivatives.
Strategy: formalize NORM BOUNDS directly via the contraction-Leibniz bound (do NOT
materialize the universal `∗`-sums); the "universal sum" language becomes a strong
induction producing a numeric bound, splitting off the single top-order term.

## ROUTE DECIDED (2026-06-08, user) — raw frame components, ZERO new ∇-machinery
Key simplifications settled in discussion:
- **Only ONE upper-index object needs covariant derivatives: `A_k`.** `g⁻¹` needs
  NONE — it enters only as the scalar bound `|g_k⁻¹| ≤ C` (Step-1 metric equiv).
  Claim 1 does NOT differentiate `g⁻¹`: differentiate the all-`(0,s)` relation
  `∇g_k = A_k ∗ g_k`, get `∇^{m+1}g_k = Σ_c binom(m,c)(∇^c A_k)∗(∇^{m-c}g_k)`,
  isolate `(∇^m A_k)∗g_k`, invert via `|T| ≤ |g_k⁻¹|·|T∗g_k| ≤ C|T∗g_k|`. So the
  documented "`g⁻¹` not a bundled `(2,0)` field" obstacle is MOOT.
- The `∇_k`-towers of `Rc`/`Rm` and the mixed `∇^a∇_k^b Rm` (Claim 2) are all
  `(0,s)` (lower indices throughout; "mixed" = mixing the two CONNECTIONS, not valence).
- **`A_k` dissolves with NO new machinery.** In a gRef-ON frame, `A_k` lowered to
  `(0,3)` has components EXACTLY the Christoffel difference `Γ − Γ_k` = `connDiffCompEq`
  (eq 3.7, coded, `AllTimesBounds.lean:3027`); its ∇-tower is the EXISTING `(0,s)`
  `covDerivStepComp` = Piece-1 `iterCovComp`; contractions `A_k ∗ S` are plain index
  sums (gRef-ON ⇒ raising = identity). No mixed-valence `covDerivStepComp`, no `g⁻¹` field.

## COMPONENT ∗-CALCULUS FOUNDATION EXISTS — `Evolution/Ricci/GammaAlgebra.lean` (confirmed 2026-06-08, user)
Do NOT treat `∇g⁻¹` as an obstacle (earlier `NablaRiemannCommutatorBound.lean:691` note was a
FAILED bundled route). The COMPONENT calculus is built:
- `covD3 Γ B dB i j l` = the `(0,3)` covariant-derivative step (`dB − Σ Γ_pi B_pjl − …`, all lower `−Γ`).
- `covDChristoffelVariation Γ A dA dir k i j` = the `(1,2)` step (upper `k` gets `+Γ`, lowers `−Γ`) —
  so `A_k`'s covariant derivative directly, no lowering needed.
- `covDInv Γ G dG k l` = the inverse-metric step (`dG + Σ Γ_ka G_al + Σ Γ_la G_ka`, upper `+Γ`).
  **`covDInv = 0` IS `∇g⁻¹ = 0`**, discharged as `hginv_zero` in `Ricci/Bianchi.lean:403`,
  `Ricci/CoordinateIdentities.lean:936` (for the LC connection of `g`).
- `raised_contract_covD_of_inv_zero` (GammaAlgebra:334) = **the contraction-Leibniz**: given
  `covDInv = 0`, `∇(G^{kl}B_{ijl}) = G^{kl}(covD3 B)_{ijl}` (metric pulls through `∇`).
- `covD3_lowerRHS` (GammaAlgebra:346) = `covD3` commutes with the Koszul permutation `lowerRHS`
  (`lowerRHS N i j l = −N i j l − N j i l + N l i j`); `connDiffCompEq` gives `2 A_k = lowerRHS(∇g_k)`
  in a g_k-ON frame (but that's frame-stuck — does NOT iterate, since `g_k⁻¹` differentiation breaks it;
  use the invert-`∇g_k = A_k∗g_k` trick + `|g_k⁻¹|≤C` instead).
These are SINGLE-STEP (fixed-direction / specific valence). The order growth (`∇^m`) is via the
rank-uniform `iterCovComp`/`covDerivStepComp` on the lowered `(0,s)` objects (Piece 1); the
contraction-Leibniz to iterate is the `raised_contract_covD_of_inv_zero` pattern.

## PROGRESS (2026-06-08)
**`AkContractLeibniz.lean` DONE + in oleans** — `covD3_starAg_leibniz`: the single-step
natural-contraction Leibniz `covD3 Γ (A∗g) ∂(A∗g) = (covD12 Γ A ∂A)∗g + A∗(covD2 Γ g ∂g)`.
Defs `covD2`/`covD12` (the `(0,2)`/`(1,2)` fixed-direction steps, matching `covD3`'s
`−Γ`-lower/`+Γ`-upper convention), `starAg`/`dStarAg` (the natural upper–lower contraction +
its directional derivative). **Metric-free**: the contracted-index corrections (`+Γ` on A's
upper, `−Γ` on g's lower) cancel by a pure index relabel — proved by explicit `Finset`
distribution + `conv_lhs => rw [Finset.sum_comm]` + `sum_congr`/`ring` (the `ring`/`linarith`
auto-close fails because it can't reorder `Finset` sums; needed explicit reorder `have`s
hC1/hC2/hC3 + hcancel). This is the engine for Claim 1's invert-`∇g_k=A_k∗g_k` trick.

## PROGRESS 2 (2026-06-08, same session)
- `AkContractLeibniz.covD3_starAg_leibniz` — single-step natural-contraction Leibniz (named-index,
  fixed-direction). DONE + oleans.
- `Evolution/CovDerivStepCompLinear.lean` — `covDerivStepComp_add`/`covDerivStepComp_smul` (the
  component-`∇`-step linearity for the binomial induction). DONE + oleans.

## OPEN FORK — the m-fold contraction-Leibniz reshuffling (decide before grinding)
Iterating to `∇^m(A∗g) = Σ_c binom ∇^c A ∗ ∇^{m-c}g` needs, at the TOWER (`covDerivStepComp`/`iterCovComp`)
level, the **derivative-slot reshuffling** (which of the m derivatives land on A vs g — the rank-cast
reindexing `(p+1)+q` vs `p+(q+1)`, `Fin.cycleRange`-style). VERIFIED: no component helper for this exists
(`towerReactionSum` is only the scalar Gronwall convolution; Shi takes the reaction bound as input). So
component-side it is ~200 lines of fresh `Fin` work.
**BUT the single-step ⊗-version WITH that exact reshuffling is already BUILT (bundled):**
`Tensor/RSTensor/ProductNablaLeibniz.nabla0S_product_realizes` (leibnizLeft/RightEquiv + cycleRange),
`NablaDomDomCongr.totalNabla0SFun_domDomCongr` (naturality), `NormSqProduct.normSq0S_product`/`normSq0S_domDomCongr`.
**Bundled-lowered m-fold (reuse path):** lower A_k→`Ǎ_k` (0,3) via `lowerAllUpperIndicesEquiv`
(`Connection/MetricCompatibility/TensorLoweringParallel.lean`); `Ǎ_k⊗g_k`=`MultilinearSection.product`
(0,3)⊗(0,2); gRef-trace via `nabla_metric_zero`/`nabla_metricPow_zero` (∇ commutes with gRef-trace);
iterate `nabla0S_product_realizes`; bridge to components via Piece 1 + `normSq0S_identity_eq_sum_sq`. All
(0,s) (no (r,s) wall since A_k lowered), reuses 4 built lemmas. The connection/`∇g⁻¹` FOUNDATION stays
component (GammaAlgebra); only the m-fold ⊗-ENGINE would reuse the bundled product-Leibniz.
DECISION NEEDED: grind component reshuffling (~200 lines Fin) vs reuse bundled ⊗-engine (less, but bundled).

## FORK RESOLVED (2026-06-08, user): COMPONENT — `Tensor/Auxiliary` has the machinery, casts = `omega`
No bundled detour. `Tensor/Auxiliary/DerivationAlgebra.contractUpper_first_product_of_local_rules` = the
rank-uniform contraction-Leibniz PATTERN (my `covD3_starAg_leibniz` is it). `Tensor/Auxiliary/Fin.lean`,
`Perm.lean` = reindex/cast helpers; `Shuffle/` = antisymmetric only (not needed). Rank casts = `omega`, and
with the `Fin.cons`/`Fin.append` framing the contraction casts are even DEFINITIONAL (no omega).

## PROGRESS 3 (2026-06-08): tower single-step STATEMENT locked + verified scaffolding
`Evolution/CovDerivStepCompContr.lean`: `contrTail A B` (natural last-slot contraction of two component
arrays) + `contrTail_apply` + `castAdd_append`/`natAdd_append` (the `Fin.append` block accessors) — ALL
type-check. **`covDerivStepComp_contrTail_leibniz`** — the tower single-step `∇(A∗B)=∇A∗B + A∗∇B` STATEMENT
is locked (framed with `Fin.cons d (Fin.append aPart bPart)` so the derivative-slot placement is explicit —
firstTerm derivative at front of A-block, secondTerm at position p; NO abstract permutation, casts definitional;
`hext` = the directional-derivative product-rule hypothesis, isolating the Christoffel algebra). PROOF is
sorried with a precise 3-step plan in-file (unfold+hext ⇒ ext halves match; split LHS `∑_{s:Fin(p+q)}` via
`Fin.sum_univ_add`/addCases into A-block=firstTerm-free + B-block=secondTerm-free; contracted-slot corrections
cancel exactly as `covD3_starAg_leibniz`'s `hcancel`). ~150-line `Fin` grind, well-specified.

## CORRECTION (2026-06-08): the tower single-step STATEMENT was WRONG (caught before proving)
`covDerivStepComp_contrTail_leibniz` used `covDerivStepComp` (`−Γ` on EVERY slot) for both `A` and `B`. But a
natural last-slot contraction needs `A`'s contracted slot to get `+Γ` (upper) and `B`'s `−Γ` (lower) — exactly
the `covD12`(+Γ)/`covD2`(−Γ) pairing that makes `covD3_starAg_leibniz`'s `hcancel` work. With both `−Γ`, the two
contracted-slot corrections DON'T cancel (would need `chr` antisymmetric = neighborhood-ON frame, NOT available
pointwise). FIX (detail in `CovDerivStepCompContr.lean` doc): **(a)** define `covDerivStepCompU` = `covDerivStepComp`
with `+Γ` on the contracted last slot (rank-uniform `covD12`/`covDInv` upper rule), keep `covDerivStepComp` for `B`,
natural contraction — METRIC-FREE, any frame, matches verified `covD3_starAg_leibniz`; or **(b)** lower `A→Ǎ`(0,3) +
raised contraction carrying inverse metric `G`, Leibniz via `raised_contract_covD_of_inv_zero` (needs `covDInv G=0`).
Lean (a). NOTE: the iterCovComp tower for `∇^c A_k` (1,2+c) is then the `covDerivStepCompU` tower (new), while
`∇^{m-c}g_k` uses the existing `iterCovComp`.

## PROGRESS 4 (2026-06-08): corrected design + crux verified
`Evolution/CovDerivStepCompContr.lean`: **`covDerivStepCompU`** (upper-index step: `+Γ` on the contracted
last slot, `−Γ` on the first `p` + the new front derivative) DEF + type-checks. **`contrTail_contracted_cancel`**
(the CRUX — `A`'s `+Γ` upper contracted correction = `B`'s `−Γ` lower one, so they cancel in the Leibniz;
pure `Finset` relabel `sum_comm`+`ring`) VERIFIED. Corrected statement **`covDerivStepCompU_contrTail_leibniz`**
type-checks (sorry). The FULL derivation (every term matched: ext halves ✓, A-contracted+B-contracted=0 via the
cancel lemma, LHS Christoffel `Fin.sum_univ_add`-split = firstTerm-A-free + secondTerm-B-free) is worked out by
hand and written in-file as the proof plan — remaining = transcription into Lean tactics.

## PROGRESS 5 (2026-06-08): Fin helpers verified, simp reduction works, goal explicit
`CovDerivStepCompContr.lean`: the 6 Fin helpers all VERIFIED — `snoc_cons_zero`, `tail_snoc_cons`,
`update_snoc_last`, `update_snoc_castSucc` (the fiddly ones; needed `: Fin _ → Idx` ascriptions for the
dependent-motive issue, and `Y : Fin p` not `Fin (p+1)`), `castAdd_append`, `natAdd_append`. The main proof's
`simp only [covDerivStepComp, covDerivStepCompU, contrTail, …helpers…] ; rw [hext]` REDUCES cleanly (verified
via `extract_goal`) — the firstTerm (covDerivStepCompU) is fully split free/upper by simp; only the secondTerm's
`covDerivStepComp` correction `∑_{x_1:Fin(q+1)}` stays unsplit. The explicit remaining goal + the 4-step Finset
assembly plan (castAdd/natAdd reduce → `Fin.sum_univ_add` split chrLHS → `Fin.sum_univ_castSucc` split secondTerm
→ `contrTail_contracted_cancel`) is written in-file at the sorry. ~80 lines of Finset reorder left.

## PROGRESS 6 (2026-06-08): tower single-step DONE — sorry-free + in oleans
`covDerivStepCompU_contrTail_leibniz` (`Evolution/CovDerivStepCompContr.lean`) FULLY PROVEN. The assembly:
`rw [hext]; simp only [castAdd_append, natAdd_append]; rw [Fin.sum_univ_add]; simp only [..append/snoc/update
helpers.. , Fin.sum_univ_castSucc]` reduced the goal to the explicit 4-piece form; then `hA`/`hB` (triple-sum
reorders via `Finset.sum_congr _ (fun _ => Finset.sum_comm) , Finset.sum_comm`), `hcancel = contrTail_contracted_cancel`,
and a final `simp only [Finset.sum_*_distrib, sum_mul, mul_sum, …] ; simp only [← sum_mul, ← mul_sum] at hcancel ⊢ ;
linarith [hcancel]`. All helpers verified: `contrTail`, `castAdd/natAdd_append`, `castAdd_ne_natAdd`,
`update_append_castAdd/natAdd`, `snoc_cons_zero`, `tail_snoc_cons`, `update_snoc_last/castSucc`, `covDerivStepCompU`,
`contrTail_contracted_cancel`. So the single covariant derivative of a natural contraction is done, rank-uniform.

## PROGRESS 7 (2026-06-08): contraction norm bound DONE
`Evolution/CovDerivStepCompContrNorm.lean` (sorry-free, in oleans): `compL2Sq` (component ℓ²-norm²) +
**`compL2Sq_contrTail_le`** (`|A∗B|² ≤ |A|²·|B|²`, Cauchy-Schwarz on the contracted index via
`Finset.sum_mul_sq_le_sq_mul_sq`, then `sum_append_split`/`sum_snoc_split` factor the free-index sums).
This is the m=0 base AND the per-term bound `|∇ᶜA∗∇^{m-c}B| ≤ |∇ᶜA||∇^{m-c}B|` for the m-fold.
GOTCHA: `Fin.snoc`/`Fin.append` dependent-motive — build the reindex equivs as `let e : _ ≃ _ := {…}` with
explicit type; `Fin.snoc_last` arg order finicky → use `simp [Fin.init_snoc, Fin.snoc_last]` for `right_inv`.

## PROGRESS 8 (2026-06-08): compL2 norm layer + m-fold towers DONE; m-fold scoped as FIELD-level
`Evolution/CovDerivStepCompContrNorm.lean` (sorry-free, oleans): `compL2` (=√compL2Sq), `compL2_add_le`
(**Minkowski**, via Cauchy-Schwarz+nlinarith), `compL2_contrTail_le` (`|A∗B|≤|A||B|`), `compL2_comp_equiv`
(**slot-reindex invariance** — absorbs ALL Fin-casts/perms at the norm level; via `Fintype.sum_equiv`+`arrowCongr`).
`Evolution/CovDerivStepCompContrMFold.lean` (sorry-free, oleans): abstract tower iterators `iterDl` (rank `r+m`)
+`iterDU` (rank `(p+c)+1`, ranks defeq → no casts in defs) + 4 simp lemmas.

**ARCHITECTURAL FINDING (load-bearing): the m-fold must be FIELD-level, not single-point.** `iterCovComp`
(MetricCovDerivTower.lean:62)'s step is `covDerivStepComp (frameExtData frame (level-a FIELD) x) (chr x) (level-a x)`
— the ext at each level is the directional derivative of the whole FIELD, NOT a function of the point value. So the
single-point `iterDl` (fixed `D : array→array`) does NOT model the frame tower (whose `D` varies per level via
`frameExtData`); `iterDl` is a valid abstract lemma but a DEAD END for the frame. Work with `iterCovComp` (field,
bridged to bundled `iterCov` by `iterCovComp_eq_iterCov`).

## ✅✅ ANALYTIC CORE FULLY PROVEN (2026-06-08): `iterCov_product_sqrtNormSq_le` — SORRY-FREE, PERSISTED
`HCGCompactness/ProductMFoldNorm.lean` is COMPLETE (no sorry, no error, in oleans). The bundled m-fold tensor-product
fiber-norm bound `√normSq0S(∇^m(A⊗B) x) ≤ Σ_{c≤m} binom(m,c)·√normSq0S(∇^c A x)·√normSq0S(∇^{m-c}B x)` is PROVEN by
induction on m. All 10 supporting lemmas proven sorry-free: `totalNabla0SRealizes_unique`, `covStep_domDomCongr`,
`iterCov_shift` (the hard cast obstacle), `normSq0S_iterCov_shift`, `iterCov_domDomCongr`, `normSq0S_iterCov_domDomCongr`,
`sqrt_normSq0S_add_le` (fiber Minkowski via compL2), `iterCov_one`, `iterCov_product_one` (single-step eq via uniqueness),
`pascal_sum` (Pascal convolution). The succ case = norm-shift + single-step + iterCov_add + triangle + 2×(naturality+IH+
norm-shift-in-sum) + pascal_sum. **This is the hardest analytic piece of Claim 1 — DONE.**
**REMAINING for the geometric Claim 1** `|∇^m A_k| ≤ C(1+|∇^{m+1}g_k|)` — GEOMETRIC WIRING, precisely scoped
(a fresh ~200-line construction on the proven analytic core; multi-session). Existing infra: `connectionDifferenceTensorAt`
(cov cov' → (1,2) tensor, `Tensor0SBundle`), `connDiffVec`/`connDiffLow`, `normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum`
(Geometry/Connection/LeviCivita/Variation/Connection.lean — but `varLowDeriv` etc. are TIME-variation, NOT spatial ∇^m; not reusable here).
STEPS:
  (a) **Key relation** `∇g_k = A_k∗g_k`: `A_k=∇−∇_k`, and `∇_k g_k=0` (metric compat of g_k's LC connection); so
      `∇g_k=(∇_k+A_k)g_k=A_k∗g_k`. NEEDS: the metric-compat lemma `∇_k g_k=0` for the LC connection (search Connection/MetricCompatibility),
      and `A_k=∇−∇_k` as the connection-difference acting on g_k.
  (b) **contraction m-fold from ⊗ m-fold**: `iterCov_product_sqrtNormSq_le` (PROVEN) bounds `|∇^m(A⊗B)|`. Need
      `A_k∗g_k=trace(Ǎ_k⊗g_k)` (Ǎ_k = lowered A_k, (0,3)) + `∇`-commutes-trace (from metric-parallel + `nabla_metricPow_zero`-style)
      + trace-norm bound `|trace T|≤K|T|`. CHECK: bundled trace API (contract 2 slots via gRef inverse) — may be partial/missing.
  (c) **invert-trick**: `|g_k⁻¹|≤C` (from `g_k` two-sided bounds, eq 3.3 `AllTimesBounds`), isolate `∇^m A_k∗g_k` from `∇^{m+1}g_k`.
  (d) **`(A_N)/(B_N)` double induction** → `|∇^m A_k|≤C(1+|∇^{m+1}g_k|)`.
SMALLEST NEXT STEP: (a) the `∇g_k=A_k∗g_k` relation (find `∇_k g_k=0` = `nabla_metric_zero`, ContractionLeibniz.lean); then (b) the bundled trace + ∇-commutes-trace.
TRACE API FOUND: `Tensor/RSTensor/Derivation/Contract.lean` — `contract_Tensor0SField`, `contract_trace`/`model_contract_trace`,
`contract_covariantField`/`contract_contravariantField`, `contract_TensorRSField`. So the bundled trace EXISTS; step (b)
= relate `A_k∗g_k` to `contract_trace(Ǎ_k⊗g_k)`, prove `∇`-commutes-`contract_trace` (from `nabla_metricPow_zero`-style +
the contraction-Leibniz `nabla0SFun_product_eval`), and the trace-norm bound `|contract_trace T|≤K|T|` (Cauchy-Schwarz).
SESSION NOTE (2026-06-08): analytic core (iterCov_product_sqrtNormSq_le, 11 lemmas) DONE this session; geometric wiring
(steps a–d, ~200 lines using the above existing APIs) is a FRESH multi-session task — start with (a) then (b).
DEEPENED UNDERSTANDING (2026-06-08): `A_k = connectionDifferenceTensorAt ∇ ∇_k` is a **(1,2) tensor**
(`ConnectionDifference.lean:179`; `A_k x α v = α((∇−∇_k)_{v 1}(v 0))`). PRECISE relation (step a): from `∇_k g_k=0`,
`(∇_X g_k)(Y,Z) = −g_k(A_k(X,Y),Z) − g_k(Y,A_k(X,Z))`, i.e. **`∇g_k = A_k∗g_k`** (a (0,3) tensor) and
**`A_k = g_k⁻¹∗∇g_k`**. **STRUCTURAL FINDING: `∇^m A_k` needs the (r,s)=(1,2) covariant-derivative TOWER, but
`iterCov` is (0,s)-only.** So either (i) build a (1,2) iterCov analog, OR (ii) lower A_k by gRef to Ǎ_k (0,3) — then
`|∇^m A_k|_{gRef}=|∇^m Ǎ_k|_{gRef}` (gRef-lowering is a gRef-isometry, ∇gRef=0), and ∇^m Ǎ_k uses the (0,3) iterCov +
the proven m-fold; the g_k-vs-gRef discrepancy and |g_k⁻¹| give the `C(1+·)` (not equality). Route (ii) reuses the
proven analytic core; route (i) needs new (r,s)-tower infra. RECOMMEND route (ii).

## ANALYTIC CORE NOW STATED (2026-06-08): `iterCov_product_sqrtNormSq_le` (ProductMFoldNorm.lean)
`HCGCompactness/ProductMFoldNorm.lean` (typechecks, persisted, ONE documented `sorry` = the proof):
`√normSq0S(iterCov (A⊗B) m x) ≤ Σ_{c≤m} binom(m,c)·√normSq0S(iterCov A c x)·√normSq0S(iterCov B (m-c) x)`.
This is the analytic core of Claim 1, correctly typed. **3 PROOF SUB-LEMMAS NOW PROVEN sorry-free** (same file,
persisted 2026-06-08): `totalNabla0SRealizes_unique` (realizer uniqueness), `covStep_domDomCongr` (field naturality
`∇(Z·e)=(∇Z)·frontExtendEquiv e`), and **`iterCov_shift`** (THE HARD CAST OBSTACLE — RESOLVED): `iterCov(r,T,m+1) =
domDomCongr (shiftEquiv r m) (iterCov(r+1, covStep T, m))` with `shiftEquiv r m : Fin((r+1)+m)≃Fin(r+(m+1))` defined
recursively (refl / frontExtendEquiv), induction via `iterCov_succ`+`covStep_domDomCongr` (base = `domDomCongr refl =
id` by eta-defeq, `rfl`). **REMAINING for the m-fold proof**: (i) single-step eq `iterCov(A⊗B,1)=⊗-expr` (inline:
`totalNabla0SRealizes_unique (iterCov_realizes (A⊗B) 0) (nabla0S_product_realizes … (iterCov_realizes A 0)(iterCov_realizes B 0))`);
(ii) norm-shift via `iterCov_shift`+`normSq0S_domDomCongr`; (iii) gRef-ON basis at x (gramSchmidt/`stdOrthonormalBasis`
of the positive-definite metric → `MetricInverseInBasis_gen … identityInvMetric`) for `normSq0S_product`/`_domDomCongr`;
(iv) the binomial induction (triangle `√normSq0S=‖·‖` + `iterCov_add` + Pascal). **PROOF = the remaining frontier** (induction on m):
step needs (a) **realization uniqueness** ✅ DONE — `totalNabla0SRealizes_unique` (same file, sorry-free): two
realizers of ∇α are equal (DFunLike.ext + ContinuousMultilinearMap.ext + `exists_eq_at_gen` for v 0 +
`Fin.cons_self_tail`). Gives `iterCov(A⊗B,1) = (∇A⊗B)·σL+(A⊗∇B)·σR` via
`totalNabla0SRealizes_unique (iterCov_realizes gRef (A⊗B) 0) (nabla0S_product_realizes … (iterCov_realizes A 0)(iterCov_realizes B 0))`;
(b) **shift** [NEXT OBSTACLE — CONSTRUCTION MAPPED 2026-06-08]: rank cast `r+(m+1)` vs `(r+1)+m` (`Nat.succ_add`,
NOT defeq for variable m). FIELD RELATION by induction on m: `iterCov gRef r T (m+1) = MultilinearSection.domDomCongr
(finCongr h_m) (iterCov gRef (r+1) (covStep gRef r T) m)`, h_m : (r+1)+m = r+(m+1) (omega). Step: `covStep(domDomCongr
(finCongr h_m) Y) = domDomCongr (frontExtendEquiv (finCongr h_m)) (covStep Y)` via `totalNabla0SFun_domDomCongr`
(NablaDomDomCongr.lean:109, `∇(Z·e)=(∇Z)·frontExtendEquiv e`, lifted to fields by DFunLike.ext) + `iterCov_succ`;
then need `frontExtendEquiv (finCongr h_m) = finCongr h_{m+1}` (small Equiv.ext lemma — frontExtendEquiv of a rank
relabel is the +1 rank relabel). m=0 base: `domDomCongr (finCongr rfl) = id` (domDomCongr_refl). NORM: `normSq0S(LHS)
= normSq0S(RHS)` via `normSq0S_domDomCongr` (absorbs finCongr). This dissolves the cast at the norm level.
`iterCov(T,m+1)=iterCov(covStep T,m)` (succ_add cast); (c) `iterCov_add`; (d) **naturality**
`totalNabla0SFun_domDomCongr` (DONE earlier) ⇒ `iterCov(T·σ,m)` norm = `iterCov(T,m)` norm via
`normSq0S_domDomCongr`; (e) base m=0 = `normSq0S_product` (needs a gRef-ON basis at x — check existence lemma);
(f) triangle (`√normSq0S=‖·‖` from inner0S) + Pascal (`Nat.choose_succ_succ`). THEN trace→contraction + invert + double-induction → Claim 1.

## ROUTE DECISION (2026-06-08): use the BUNDLED route for the m-fold — ALL pieces confirmed present
The bundled ⊗ m-fold reuses built infrastructure and its differentiability is supplied by the realization
framework (`iterCov_realizes`), which the component `frameExtData` route lacks. Confirmed-present pieces:
`nabla0SFun_product_eval` (ContractionLeibniz.lean:122, evaluated ⊗-Leibniz), `iterCov_succ`/`iterCov_add`
(MetricCovDerivLinear.lean:236/246), `iterCov_realizes` (MetricCovDerivTower.lean:98), `normSq0S_product` +
`normSq0S_domDomCongr` (NormSqProduct.lean:36/94), triangle = `norm_add_le` on the fiber (√normSq0S = ‖·‖).
**Bundled m-fold ⊗ NORM bound** (induct on m, ∀ A B; same shape as the component plan but bundled):
`√normSq0S(iterCov(A⊗B,m)x) ≤ Σ_c binom(m,c)√normSq0S(iterCov(A,c)x)√normSq0S(iterCov(B,m-c)x)`. Step uses: FIELD
⊗-single-step `∇(A⊗B)=∇A⊗B+(A⊗∇B)·σ` (de-evaluate `nabla0SFun_product_eval` via slot-ext) + iterCov shift
(succ_add cast, absorb via `normSq0S_domDomCongr`) + `iterCov_add` + `normSq0S_product` + `normSq0S_domDomCongr` +
triangle + Pascal. THEN contraction = trace(⊗): need bundled trace + ∇-commutes-trace (from `nabla_metricPow_zero`
style) + trace norm bound; OR use lowered `Ǎ_k=∇g_k` to land on g_k-products directly. THEN invert-trick + double-induction → Claim 1.
The component files (`covDerivStepCompU_contrTail_leibniz`, `compL2*`) remain valid but are the FALLBACK route.

## (FALLBACK) component FIELD-level m-fold NORM bound
Statement (∀ FIELDS X Y, pointwise at x): `compL2(iterCovComp … (X∗Y) m x) ≤ Σ_c binom(m,c)·compL2(iterCovComp… X^U c x)·compL2(iterCovComp… Y (m-c) x)`, induct on m. SUB-PIECES (all FIELD-level):
1. **field single-step**: `∇(X∗Y) = ∇X∗Y + X∗∇Y` (as fields, up to reindex) — from `covDerivStepCompU_contrTail_leibniz`
   + the **frameExtData product rule** (`frameExtData(contrTail X Y) = product-rule`, via `ricci_extDerivFun_mul/_add`). THE key frame piece.
2. **field shift**: `iterCovComp…(m+1) = iterCovComp…(∇·) m` (rank cast (r+1)+m vs r+(m+1) = succ_add; absorb at norm via `compL2_comp_equiv`).
3. **field linearity**: `iterCovComp…(X+Y) = iterCovComp…X + iterCovComp…Y` (needs frameExtData additive + `covDerivStepComp_add`).
4. **perm-commute**: `compL2(iterCovComp…(Z∘ρ) x) = compL2(iterCovComp…Z x)` (∇ commutes with slot reindex; component analog of `totalNabla0SFun_domDomCongr`, OR via the iterCov bridge).
Then triangle (`compL2_add_le`), contraction bound (`compL2_contrTail_le`), Pascal. THEN: S-bound (isolate ∇^m A_k∗g_k), invert-trick (`|g_k⁻¹|≤C`), geometric relations (`contrTail A_k g_k = ∇g_k`), normSq0S bridge → Claim 1.
**ALT route** (bundled, reuses MORE built machinery): `A_k∗g_k = trace(Ǎ_k⊗g_k)`; bundled ⊗-Leibniz m-fold (iterate
`nabla0S_product_realizes`) + `normSq0S_product`/`_domDomCongr` + ∇-commutes-trace + trace bound. Needs bundled trace.

## INFRASTRUCTURE FOUND (2026-06-08 — improves outlook, USE next session)
- **`Tensor/RSTensor/ContractionLeibniz.lean` `nabla0SFun_product_eval`**: the EVALUATED bundled ⊗-Leibniz
  `∇(A⊗B)(slots) = ∇A(X::slots₀..ₛ)·B(slotsₛ..) + A(slots₀..ₛ)·∇B(X::slotsₛ..)` for smooth `(0,s)`,`(0,q)` fields —
  handles differentiability INTERNALLY (bundled smooth sections). Plus `nabla_product_zero_of_zero`, `metricPow`,
  `nabla_metricPow_zero` (`∇(g^⊗r)=0`). This is the bundled single-step; the bundled m-fold iterates it.
- **`extDerivFun_mul_real`** (`Tensor.Coordinates`, public) + **`extDerivFun_finset_sum_real`** (RicciCoord.lean:471
  uses it) + `Bundle/PartialMfderiv/Basic.lean` `extDerivFun_finset_sum_mul_at`/`_sum_sum_mul_at`: the frame
  single-step's analytic inputs (product rule + finset-sum linearity of the directional derivative) ARE available.
  ⇒ the component **frameExtData product rule** is buildable GIVEN tower differentiability (the remaining dependency).
- **KEY SIMPLIFICATION (verify next session): lowered `Ǎ_k = ∇g_k` (up to index perm).** `(A_k)^p_{ij}=(g_k⁻¹)^{pq}(Ǎ_k)_{qij}`
  and `(∇g_k)_{lij}=(Ǎ_k)_{lij}`. So Claim 1 ⇔ m-fold of `A_k = g_k⁻¹ ∗ ∇g_k` with `∇^c(g_k⁻¹)` controlled by
  `∇g_k⁻¹=−g_k⁻¹∗∇g_k∗g_k⁻¹`. STILL an m-fold of a contraction, but the bundled `nabla0SFun_product_eval` may give it
  more directly than the component frame single-step. **Open decision: component (frameExtData) vs bundled (⊗+trace).**
- REMAINING DEPENDENCY either route: tower DIFFERENTIABILITY/smoothness (`iterCovComp…c` smooth) — check the Shi-tower
  (`iteratedRmComp`) smoothness machinery for a reusable lemma before building fresh.
via `covDerivStepComp_add` + Pascal (`Nat.choose_succ_succ`), then invert-trick (`|g_k⁻¹|≤C`) + Cauchy-Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) → Claim 1. Older note (the m-fold target): `∇^m(A∗g) = Σ_c binom(m,c)
∇^c A ∗ ∇^{m-c}g`. SHAPE ISSUE to resolve: the single-step is at the FIXED-DIRECTION
`covD3`/`covD12` level (result same rank, `∂` baked in); the order growth `∇^m` is at the
ADD-INDEX `covDerivStepComp`/`iterCovComp` (Piece 1) level (rank grows). Either bridge
covD3↔covDerivStepComp, or build an iterated covD3-tower. Then: the invert-trick (isolate
`(∇^m A_k)∗g_k`, bound by `|g_k⁻¹|·|·|`, `|g_k⁻¹|≤C`) + Cauchy-Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`)
→ Claim 1 `|∇^m A_k|≤C_m(1+|∇^{m+1}g_k|)`. Then Claim 2 → Step 4 → Step 5.
Original first-lemma note (superseded by the above):
`|∇^m A_k| ≤ C_m (1 + |∇^{m+1} g_k|)`, with
- base array `= Γ − Γ_k` (from `connDiffCompEq`, eq 3.7),
- tower `= iterCovComp` (Piece 1, in `MetricCovDerivTower.lean`),
- bound via Cauchy–Schwarz on components (`Finset.sum_mul_sq_le_sq_mul_sq`) + the
  invert-`∇g_k = A_k∗g_k` trick (needs `|g_k⁻¹| ≤ C` only).
Then Claim 2 (`∇=∇_k+A_k` expansion → mixed-curvature bound), then Step 4
(telescoping + `(A_N)` + `(B_N)` Gronwall = `metricCovOrderWindow_of_evolution`),
then Step 5 (time derivatives). All raw frame components; bridge final `(0,s)`
`∇^N Rc`/`∇^N g` to `normSq0S` via `normSq0S_identity_eq_sum_sq` at the end.
Need to locate first: the `∇g_k = A_k∗g_k` component identity + `|g_k⁻¹| ≤ C` accessor.

## ROUTE FINALISED + PROGRESS 9 (2026-06-08, user-prompted realignment): COMPONENT (route i) is THE path
After a digression onto an abstract `(r,s)` LOWERING route (G1 isometry `normSqRS=normSq0S(lowerAll)`,
`RSLoweringNorm.lean` — DONE sorry-free, a CORRECT but OFF-critical-path norm bridge; the "∇-commutes-lowering"
I framed as a frontier is actually the already-proven component `nabla_metricPow_zero`/
`nabla0SFun_metricPow_contraction_eval`, see `important_lesson.md`), the route is FIRMLY back to COMPONENT (i),
the user's original twice-emphatic resolution. WHY: `A_k` is `(1,2)`; its tower is the purpose-built UPPER step
`covDerivStepCompU` (`+Γ` on the contracted upper slot), NOT the `(0,s)` `iterCov`. The `∗g_k` contraction is the
NATURAL `starAg`/`contrTail` pairing (no metric); its Leibniz has BOTH terms (g_k not gRef-parallel) → the binomial.
So `iterCov_product_sqrtNormSq_le` (route-ii bundled ⊗ core) and G1 are correct but OFF this path.
**DONE this session in `HCGCompactness/AkMFold.lean` (sorry-free, oleans) — 3 m-fold pieces:**
- **Piece 1 `iterCovCompU`** — the field-level UPPER tower `∇_U^c A_k` (`covDerivStepCompU` analogue of
  `iterCovComp`; `ext` per level = `frameExtData` of the running field; `+1` upper slot kept LAST so ranks
  `(r+a)+1` stay defeq).
- **Piece 2 `frameExtData_contrTail`** — the frameExtData product rule for the natural contraction (the
  field-level `hext`): `∂(A∗B) = Σ_c (∂A·B + A·∂B)`, via `extDerivFun_finset_sum_mul_at`
  (`Bundle/PartialMfderiv/Basic.lean:416` — the ∂ of a Finset sum-of-products, EXACT match for `contrTail`).
  Needs component-wise `MDifferentiableAt` of the two fields (threaded as hyps `hA`/`hB`).
- **Piece 3 `covDerivStepComp_frameExtData_contrTail`** — the field-level single-step Leibniz
  `∇(A∗B)=(∇_U A)∗B + A∗(∇B)`: `covDerivStepCompU_contrTail_leibniz` (DONE) with `hext` = Piece 2. The
  inductive engine of the m-fold.
**NEXT — Piece 4: the m-fold expansion of `∇^m(A_k∗g_k)`.** Two load-bearing findings from scoping it:
- **CRITICAL — `binom` is a NORM-level fact, NOT an identity.** The m derivative indices are DISTINCT, so each
  `∇` (Piece 3) sends the new derivative to A (`∇_U`) OR B (`∇`); after m steps the IDENTITY is a **`2^m` subset
  sum** `∇^m(A∗B) = Σ_{w∈{A,B}^m} contrTail(∇_U^{|wA|}A …)(∇^{|wB|}B …)`, where the `binom(m,c)` words of weight
  `c` are PERMUTATIONS of each other (different which derivative-slots), EQUAL only after `compL2_comp_equiv`
  (permutation-invariant norm). So: do NOT state `∇^m(A∗B)=Σ_c binom(m,c)(∇^cA)∗(∇^{m-c}B)` as an identity (FALSE
  at array level). Isolation works because the all-A word `w=AAA…` is UNIQUE → its term is exactly `(∇^m A_k)∗g_k`;
  `(∇^m A_k)∗g_k = ∇^{m+1}g_k − Σ_{w≠allA}(…)`, and `|Σ_{w≠allA}(…)| ≤ Σ_{c<m} binom(m,c)|∇^cA_k||∇^{m-c}g_k|`
  (triangle + per-word `compL2_contrTail_le` + group-by-weight at the NORM level).
- **BLOCKER DISCHARGED (2026-06-09) — the tower-differentiability API is BUILT, sorry-free, in oleans.**
  Two-layer construction (NOT via the bundled `iterCov` bridge — a direct component-level induction):
  * `Geometry/Connection/Realization/SmoothSectionsLocal.lean` (NEW) — the analytic input:
    `contMDiffOn_dual_apply` (global smooth dual section ⊗ `ContMDiffOn u` vector field → `ContMDiffOn u` scalar;
    local mirror of `contMDiff_dual_apply_section` via `ContMDiffOn.clm_bundle_apply` + `contMDiffWithinAt_section`)
    and **`contMDiffAt_extDerivFun_apply`** (f `C^∞` on open u, V `C^∞` on u ⇒ `y ↦ df_y(V y)` ContMDiffAt on u).
    Proof = `SmoothBumpFunction` localization: bump χ (tsupport ⊆ u via `nhds_basis_tsupport`), f̃ = χ·f globally
    smooth (`contMDiff_of_locally_contMDiffOn`, cover u ∪ (tsupport χ)ᶜ), global `contMDiff_extDerivFun_section`,
    pair, transfer back by germ equality (`extDerivFun_real_eq_mfderiv` + `Filter.EventuallyEq.mfderiv_eq`;
    χ ≡ 1 near x via `eventuallyEq_one`). KEY TRICK: localize ONLY the scalar f — the vector field stays local
    (the pairing lemma handles it), avoiding section-extension machinery.
  * `AkMFold.lean` — `iterCovComp_contMDiffOn` + `iterCovCompU_contMDiffOn` (every tower level `C^∞` on u, by
    induction: step = extDerivFun(prev) along frame − Γ-sums; `∞` loses nothing per derivative) + corollaries
    `iterCovComp_mdiffAt`/`iterCovCompU_mdiffAt` (exactly Piece 3's `hA`/`hB` at every level) + private
    `contMDiffOn_finsetSum`. Hypotheses: frame `ContMDiffOn u` (T%-form), chr components `C^∞` on u, base
    components `C^∞` on u — discharge for the concrete chart frame/gRef-Christoffel/A_k,g_k bases is later wiring.
  GOTCHA (recorded): induction over tower level with the multi-index n must keep `∀ n` INSIDE the motive (n's type
  depends on the level). `iterCovComp_succ`+`rfl` unfolds the step to the explicit extDerivFun/Γ-sum form.
**THEN (all DONE blocks):** norm (`compL2_contrTail_le` + `compL2_add_le` + triangle) → relation `∇g_k=A_k∗g_k`
= `connDiffCompEq` (eq 3.7) → isolate the all-A word → invert `|g_k⁻¹|≤C` (eq 3.3) → (A_N)/(B_N) double induction
→ **Claim 1**.

## PROGRESS 11 (2026-06-09) — Piece 4 DE-RISKED: bottom-pull ⇒ NO explicit `2^m`/permutations; it is TEMPLATED
KEY REALIZATION: do the m-fold induction by pulling the BOTTOM (first-applied) derivative, exactly as the proven
bundled `iterCov_product_sqrtNormSq_le`: `∇^{m+1}(A∗B) = ∇^m(∇(A∗B)) = ∇^m(∇_U A ∗ B) + ∇^m(A ∗ ∇B)`, recurse by
IH on each half (with `A→∇_U A` / `B→∇B`), Pascal. The slot permutations are ABSORBED into the shift's norm
invariance (`compL2_comp_equiv`, DONE) — never materialized. So Piece 4 mirrors `iterCov_product` (already done,
incl. the hard `iterCov_shift` cast) — NOT a fresh combinatorial frontier.
WHY norm-bound alone is insufficient (must prove BOTH): the residual `D_m := ∇^m(A∗g) − (∇^m A_k)∗g` cannot be
bounded by a recursion on `|D_m|` (its `|∇D_m|` is uncontrolled); but the bottom-pull proves
`ISO(m): |D_m| ≤ Σ_{c<m} C(m,c)|∇^c A_k||∇^{m-c}g_k|` directly by recursion `D_{m+1} = −D_m[∇_U A_k] −
∇^m(A_k∗∇g_k)` (IH/ISO on `∇_U A_k` + full norm-bound `P(m)` on `A_k∗∇g_k`; the algebra closes by Pascal with
the `c=m+1` term ABSENT — exactly the isolation). So need `P(m)` (full binom norm bound) AND `ISO(m)` (residual),
both bottom-pull.
LEMMA SEQUENCE (all templated from `iterCov_product`; `compL2_*` + `covDerivStepComp_add/_smul` + tower-diff DONE):
1. `frameExtData_add` (field-level `∂`-linearity) — **DONE (2026-06-09, AkMFold.lean)**, via `mfderiv_add`.
2. `iterCovComp_add` (field-eq on `u`; per-level via `frameExtData_add` germ-congruence + `covDerivStepComp_add`
   + tower-diff `_mdiffAt`). The field single-step (Piece 3) as a field equality on `u`.
3. **`iterCovComp_shift` DONE (2026-06-09, AkMFold.lean)** — the bottom=top tower shift with the
   `(r+1)+m ≃ r+(m+1)` cast (the HARDEST technical lemma; mirror of `iterCov_shift`). Built on NEW
   **`covDerivStepComp_compReindex`** (DONE) = the component `covStep_domDomCongr` (step commutes with a free-slot
   reindex `e`; new derivative slot fixed by `frontExtendEquiv e`, Christoffel sum reindexed by `e` via
   `Equiv.sum_comp` + `Function.update`-precompose) + local `shiftEquivC` (recursive `frontExtendEquiv`). The
   `frameExtData` reindex is DEFINITIONAL (`rfl`). Induction one-shot. **`compL2_iterCovComp_shift` DONE**
   (= `iterCovComp_shift` + `compL2_comp_equiv`, 2 lines). **`iterCovComp_compReindex` DONE** (= the component
   `iterCov_domDomCongr`: `iterCovComp` commutes with a free-slot reindex `e`, via `frontExtendIterC` + same
   induction). **`iterCovComp_add` DONE** (field-level linearity, via `frameExtData_add` germ-congruence +
   `covDerivStepComp_add` + tower-diff). So the (0,s)-tower structural layer is COMPLETE.
   **UPPER-tower shift DONE (2026-06-09):** `iterCovCompU_shift` + `compL2_iterCovCompU_shift`, built on NEW
   `covDerivStepCompU_compReindex` (the `+Γ` upper slot fixed via `extendLastEquiv`, the `−Γ` first-`p` sum
   reindexed) + `extendLastEquiv` (via `finSuccEquivLast`/`optionCongr`) + `extendLast_frontExtend_comm` (the
   commute of front/last extensions — fiddly nested `Fin` casing, DONE) + `extendLastEquiv_refl`. So BOTH tower
   shifts (the A-side `∇_U` upper tower and the B-side `∇` tower) and their norm forms are now COMPLETE — the
   hardest cast/shift obstacles of the whole m-fold are solved.
   **REMAINING for P(m)/ISO(m) and Claim 1:** (i) the field single-step in `compReindex` form
   `∇(contrTail A B) = compReindex e₁ (contrTail (∇_U A) B) + compReindex e₂ (contrTail A (∇B))` — `e₁ = finCongr`
   (the index `[d,a,b]` is the SAME sequence, just regrouped `(rA+1)+rB ↔ (rA+rB)+1`); `e₂` = the rotation
   `[d,a,b]↦[a,d,b]` (move slot 0 to position `rA`) — a fiddly explicit `Fin` permutation (~50 lines, the next piece);
   (ii) `P(m)` bottom-pull (uses both shifts + add + compReindex + the field step + Pascal); (iii) `ISO(m)`;
   (iv) the geometric wiring (`connDiffCompEq` relation, invert `|g_k⁻¹|≤C`, `(A_N)/(B_N)` double induction).
   The remaining is templated/tractable but genuinely MULTI-SESSION (~250 more lines).
4. `P(m)` (full binom `compL2` bound) + `ISO(m)` (residual bound), both bottom-pull inductions (universally
   quantified over the two fields). `pascal_sum` reusable from `ProductMFoldNorm`.
5. relation `∇^m(contrTail A_k g_k) = ∇^{m+1}g_k` (`connDiffCompEq` + tower composition) → isolate + invert
   `|g_k⁻¹|≤C` → (A_N)/(B_N) double induction → **Claim 1**.
Estimate: ~300 lines of TEMPLATED work (no new frontier). Difficulty concentrated in step 3 (the cast), already
solved once for the bundled tower.

## PROGRESS 12 (2026-06-09) — `P(m)` DONE sorry-free; `ISO(m)` scoped (the remaining engine frontier)
**`P(m)` = `compL2_iterCovComp_contrTail_le` (AkMFold.lean, sorry-free, oleans):** the full binomial NORM bound
`|∇^m(A∗B)| ≤ ∑_{c≤m} C(m,c)|∇_U^c A||∇^{m-c}B|`, bottom-pull, ∀ two fields. Built en route (all sorry-free):
`slotId1`/`slotId2` (slot identities for the single-step's A/B terms), `rotEquiv` (`[d,a,b]↦[a,d,b]`),
`covStep_contrTail_field` (field single-step in compReindex form; reindexes are `finCongr`/`rotEquiv` EQUIVS so
`iterCovComp_compReindex` applies), wrappers `compL2_iterCovComp_compReindex`/`iterCovComp_congr_on`/
`contMDiffOn_contrTail`. `pascal_sum` MOVED to shared `Evolution/CovDerivStepCompContrNorm.lean` (namespace
`HCGCompactness`; both bundled+component use it). **GOTCHA: inline calc terms timed out even at 4M heartbeats →
`set HL/HR/LF/RF` to keep every calc step small-term (the fix; no `set_option` bump needed after).**

**`ISO(m)` = the residual bound, NEXT frontier.** Define `D_m[A] := ∇^m(A∗g) − (∇_U^m A)∗g` (pointwise array).
**KEY INSIGHT (de-risks ISO): `∇^m(A∗g)` and `(∇_U^m A)∗g` have the SAME slot layout `[d_m..d_1][a_1..a_p][b_1..b_q]`
(rank `m+p+q`) — NO reindex between them**, because `iterCovComp` prepends each derivative at slot 0, `iterCovCompU`
prepends derivs at 0 and keeps the upper slot LAST, and `contrTail` lists A-free then B-free. So `D_m` is a clean
subtraction. Target: `|D_m[A]| ≤ ∑_{c<m} C(m,c)|∇_U^c A||∇^{m-c}g|` (top term `c=m` ABSENT = the isolation).
- Base `m=0`: `D_0 = A∗g − A∗g = 0`, sum over `range 0` empty ⇒ `0 ≤ 0`.
- Recursion (bottom-pull, the work): `D_{m+1}[A] = reindex(D_m[∇_U A]) + reindex(∇^m(A∗∇g))` after the
  `(∇_U^{m+1}A)∗g` terms CANCEL. The cancellation needs the array identity
  `∇^{m+1}(A∗g) = reindex_L(∇^m((∇_U A)∗g)) + reindex_R(∇^m(A∗∇g))` (= P(m)'s calc steps 1–5 at the IDENTITY
  level, NOT norm — extract as `iterCovComp_contrTail_succ`) PLUS the U-shift-commutes-with-∗g lemma
  `contrTail(∇_U^m(∇_U A))(g) = reindex(contrTail(∇_U^{m+1}A)(g))` (from `iterCovCompU_shift` lifted through
  `contrTail`'s first factor). Then `|D_{m+1}| ≤ |D_m[∇_U A]| + |∇^m(A∗∇g)|` (triangle + compL2 reindex-inv)
  `≤ ISO(m)[∇_U A] + P(m)[A,∇g]` → Pascal with the top term absent ⇒ `ISO(m+1)`.
- THE crux is the array identity + cancellation (P(m) avoided ALL identities — norm-only). ~100 lines, reuses the
  whole P(m) engine. Suggested brick order: (i) `iterCovComp_contrTail_succ` (the L+R array identity), (ii)
  `contrTail_iterCovCompU_shift` (U-shift through ∗g), (iii) `ISO(m)` induction.

**After ISO(m): inversion + wiring → Claim 1.** (a) inversion `|∇_U^m A| ≤ |g⁻¹|·|(∇_U^m A)∗g|` (contract back
with `g⁻¹`; `|g_k⁻¹|≤C` from inverting `∇g_k=A_k∗g_k`); (b) `(∇_U^m A)∗g = ∇^m(A∗g) − R_m`, `|R_m|≤ISO(m)`,
`|∇^m(A∗g)|=|∇^{m+1}g|` (since `∇g=A∗g`); (c) `connDiffCompEq` (eq 3.7) to pin A_k's base; (d) (A_N)/(B_N)
double induction. Still 1–2 sessions.

HONEST %: **Claim 1 theorem = 0% (unstated/unproven in Lean).** Its route-(i) machinery ~70–75% (single-step,
shifts, towers, differentiability, **P(m) binomial bound** all DONE sorry-free; ISO(m) residual + inversion +
wiring + double induction remain). This lemma ~ small fraction of `ric_bound` (P2/eq 3.4), itself ~15-20% of
Lemma 3.11, itself part of the whole HCG compactness project (~15-20% theorem-weighted).

## PROGRESS 13 (2026-06-10) — **ABSTRACT CLAIM 1 PROVEN sorry-free** (`claim1_abstract`, AkMFold.lean)
The full abstract chain is DONE and in oleans: `iterCovComp_contrTail_succ` (bottom-pull ARRAY identity) →
`isoTop` (recursive isolated top — the recursion BUILDS IN the L-reindex, dissolving the reindex-matching) →
**`compL2_isoResidual_le` = ISO(m)** (no-top binomial residual bound; `pascal_sum_notop` added to shared norm
file) → `compL2_isoTop_eq` (`|isoTop| = |(∇_U^m A)∗g|`, via `blockLeftEquiv`+`contrTail_extendLast`) →
`compL2_contrTail_topU_le` (isolated-top ≤ tower + no-top binomial) → `contrTail_contrTail_inv` +
`compL2_le_contrTail_inv` (the invert: pointwise inverse-array property ONLY, `∇g⁻¹` never appears) →
**`claim1_abstract`**: `|∇_U^m A| ≤ C(m,C0,KR,K)·(1+|∇^{m+1}g|)` (strong induction, explicit constant).
MATH CORRECTION caught: `A∗g = ∇g` as a single-contraction EQUALITY is false (A hits BOTH lower slots of g);
the honest input is the KOSZUL norm bound `hrelB : |∇^{m'}(A∗g)| ≤ KR·|∇^{m'+1}g|` (KR = 3/2 geometrically).
**REMAINING for geometric Claim 1** (see AkMFold.md): (1) hrelB discharge = component Koszul identity +
`iterCovComp_smul` (new, mirror `_add`) + compReindex/shift norm bounds; (2) hinv/hGinv/hK wiring from
`InverseMetricComponentsInFrame` + eq-3.3; (3) the (1,2) UPPER tower realization bridge
(`iterCovCompU ↔ tensorRSCovariantDerivative` tower of A_k, upper analogue of `iterCovComp_eq_iterCov`) +
norm bridges compL2 ↔ √normSq. Claim-1 machinery now **~85%**; the geometric statement itself still 0%
(unstated). Whole HCG project theorem-weighted ~15-20%.

## PROGRESS 14 (2026-06-10) — **CLAIMS 1+2 GEOMETRIC, sorry-free** (RicBoundClaims.lean)

DAG items 3 (Claim 1) and 4 (Claim 2) DONE as theorems: `claim1_LC` (= `claim1` +
`hkoszul_of_leviCivita`, the F3 producer reused verbatim — Phase W paid off) and
`claim2_component` (mixed `|nabla^a nabla_k^b T| <= C` for `a+b <= L` from Shi rows +
Claim-1 D-bounds; new `mixed_oneStep_rev` + abstract `claim2Double` with
exists-C-before-forall-W).  Orientation: chrG = moving, chrH = fixed; no sign glue.
See RicBoundClaims.md.  NEXT: R3a `mixed_oneStep_top` (split c=k top term, carries
the `|nabla^N g|` of (A_N)), then R3b (A_N) descent + R3c (B_N) Gronwall (item 5).

## PROGRESS 15 (2026-06-10) — (A_N) component core GREEN + `ric_bound` STATED

RicBoundClaims.lean fully sorry-free: + `mixed_oneStep_top` (top-split one-step,
the `|nabla^N g|`-carrying term isolated) and `mixed_descent` (the (A_N) analytic
core: `|nabla_H^N T| <= C(1+|nabla_HU^{N-1}D|)` pointwise from hDlow/hmix/hShiN by
an N-step constant-cost descent).  NEW FILE RicBound.lean: `theorem ric_bound`
STATED intrinsically (ricCovTower = iterCov of ricciSection; hypotheses = IsCompact
K + eq3.3 + (B_r) r<N + moving Shi <= N; conclusion = the
MetricCovOrderEvolutionInput.ric_bound field shape) with ONE precise sorry.
Remaining discharge: frame covering of K, component<->intrinsic ON-frame bridge
(Parseval EXISTS: normSq0S_identity_eq_sum_sq), moving<->fixed norm via eq3.3,
ricciSection component identification, finite-cover maxima.  See RicBound.md.

## COORDINATION (2026-06-10, ~16:20) — TWO TRACKS CONVERGED; do NOT duplicate Step 4

Two concurrent sessions both closed the Claim-1/2 layer today in different shapes.
MAP (all sorry-free, focused-checked):

- Claim1Wiring.lean (track A): `claim1_geom` (trivialization-frame geometric Claim 1,
  B1-B3 producers discharged, numeric window bounds as inputs) + **B5 `compL2_tower_eq`**
  (component tower = sqrt normSq0S of `iterCov` at pointwise-gRef-ON frame points —
  THE component<->intrinsic bridge).
- Claim2Mixed.lean (track A): `claim2core` (pure-`chrR`-tower bound, field-quantified
  strong induction; mixed wrapper = instantiate at `B := iterCovComp chrK T b`).
- RicBoundClaims.lean (track B): `claim1_LC` (frame-general Claim 1 via
  `hkoszul_of_leviCivita`), `claim2_component` (the MIXED `|∇_H^a ∇_G^b T|` bound
  directly — equivalent to claim2core+wrapper; redundant pair, both settled API),
  **`mixed_oneStep_top`** (top-split one-step, hDbound only `c<k`, conclusion carries
  `r·|∇_U^k D|·|X|`) and **`mixed_descent` = THE (A_N) ANALYTIC CORE**:
  `|∇_H^N T| ≤ C(1 + |∇_{H,U}^{N-1}D|)` pointwise from hDlow (`c+1<N` uniform) +
  hmix (Claim 2 at `L=N-1`) + hShiN.  **Step 4's (A_N) descent is DONE — do not
  rebuild the telescoping.**
- RicBound.lean (track B): **`theorem ric_bound` STATED** (intrinsic (A_N) endpoint:
  `ricCovTower := iterCov gRef 2 (ricciSection (LC g))`; hyps = IsCompact K + eq3.3 +
  (B_r) r<N + moving-Shi ≤ N; conclusion = the MetricCovOrderEvolutionInput.ric_bound
  field shape), ONE sorry.  See RicBound.md for the discharge plan.

CONSOLIDATED REMAINING for the ric_bound sorry (either session; claim the files):
(1) a covering of compact K by frame domains where the descent constants uniformize —
    either gRef-ON frames (then B5 gives norm EQUALITY) or bounded-Gram equivalence;
(2) moving<->fixed norm conversion of the Shi inputs via eq(3.3) (hequiv);
(3) ricciSection component smoothness (`hT` for the descent) — frameComp0S of
    ricciSection is ContMDiffOn (B2-pattern producer);
(4) instantiate `mixed_descent` + `claim1_LC`(or claim1_geom) per domain; finite-cover
    maxima; arity reindex `2+N <-> N+2` for the Gronwall consumption.
ORIENTATION GUARD: both tracks use D = Γ_moving − Γ_fixed lowered/towered in the FIXED
connection (chrG/chrK = moving, chrH/chrR = fixed) — consistent, no sign flips.

## PROGRESS 16 (2026-06-10) — ric_bound POINTWISE CORE green + arity bridge

Four new sorry-free bricks (focus-checked): `aN_component` (RicBoundClaims; component
(A_N) = claim2_component+mixed_descent+compose), `tower_bound_to_intrinsic` +
`aN_intrinsic_point` (RicBoundAssembly.lean; the B5-lift and the per-frame-point
intrinsic (A_N): √normSq0S gRef (∇^N Ric) ≤ Cpp·√normSq0S gRef (∇^N g) + Cppp at a
gRef-ON point — the WHOLE geometric inequality pointwise), and
`metricCovDerivNorm_eq_iterCov` (MetricCovDerivArityBridge.lean; the 2+N↔N+2 cast via
acEquiv + covStep_domDomCongr + normSq0S_domDomCongr — connects to the textbook
metricCovDerivNorm). See RicBoundAssembly.md.
REMAINING for the ric_bound sorry = ONE intertwined analytic brick (R4d+R4e): a good
gRef-ON-centered smooth frame on a small domain with bounded Gram (constant Gram-Schmidt
of the trivialization frame, NOT a global ON frame); convert the intrinsic (B_r)/Shi/
inverse bounds to aN_intrinsic_point's component (compL2) form via normSq0S_le_of_metric_equiv
(Comparison.lean:520, EXISTS) + iterCovComp_eq_iterCov + the bounded Gram; apply per x∈K;
uniformize over a finite subcover; assemble in RicBound.lean (R4f for RHS, ricCovTower defeq
for LHS). This frame-analysis + compactness packaging is the genuine remaining frontier.
