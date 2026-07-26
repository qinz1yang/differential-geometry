# ChristoffelDiffKoszulDeriv — B2 P2.a (differentiated Christoffel-difference Koszul)

Companion for `ChristoffelDiffKoszulDeriv.lean`.  Full mission route: `HCGCompactness/UNIF_ITEM6_RECON.md`
(§4b = the confirmed 6-step plan for this file).

## Goal of this leaf

The differentiated Koszul identity (crux of B2 P2, the ungated a=1 connection-difference-derivative bound):
```
2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y), Z),
```
`A = connDiff g₁ g₂ = difference (LC g₁) (LC g₂)`, `∇₂ = LeviCivita g₂`.  Obtained by differentiating
`connDiff_koszul` covariantly along `W`.

## Landed (verified, sorry-free, axioms = [propext, Classical.choice, Quot.sound])

- `connDiff_koszul_nabla` — the **a=0 differentiation base** in `nabla0SFun` currency:
  ```
  g₁(difference (LC g₁)(LC g₂) x (Y x)(X x), Z x)
    = ½·nabla0SFun 2 (LC g₂) X (metricTensorField g₁) x (Y,Z)
      + ½·nabla0SFun 2 (LC g₂) Y (metricTensorField g₁) x (X,Z)
      − ½·nabla0SFun 2 (LC g₂) Z (metricTensorField g₁) x (X,Y)
  ```
  = `koszul_difference` (`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean`) specialised to the
  Levi-Civita pair.  This is `connDiff_koszul` in the currency whose covariant derivative is
  Tensor-layer differentiable via `nabla0SFun_eval_smooth_slots` — the base the differentiation `rw`-uses.

## Key facts nailed (reuse for the next brick)

- `LeviCivita g = leviCivitaConnectionOfMetric g` **definitionally** (`LeviCivita_eq_leviCivitaConnectionOfMetric := rfl`),
  so `covDerivConnDiff`'s `LeviCivita` currency and `koszul_difference`'s connection are interchangeable.
- LC hypotheses for `koszul_difference`: `hmc := by simpa [LeviCivita] using
  leviCivitaConnectionOfMetric_isMetricCompatible g₁` (`IsMetricCompatible_gen`); `htf/htf' :=
  (leviCivitaConnectionOfMetric_isTorsionFree g) x` (`IsTorsionFreeAt`).
- HOME confirmed FEASIBLE: `Geometry/Connection/LeviCivita/` is entangled with `Curvature/`
  (`LeviCivita/Basic.lean` imports `Curvature.Realized.*`), so this leaf imports `RicciConnDiffPalatini`
  (`covDerivConnDiff`, Curvature) + `KoszulDifference` (Tensor) with no cycle.  The ratified home works.
- Instances: needs `[VectorBundle]` + `[ContMDiffVectorBundle 1]` (added as theorem hyps),
  `[IsManifold I 1]` + `[IsManifold I (∞+1)]` (`haveI ... IsManifold.of_le` / `change`),
  `CompleteSpace E` (`private local instance` from `FiniteDimensional.complete`).  `omit
  [InnerProductSpace] [NeZero] [BoundarylessManifold] in` before the a=0 lemma (they're for the later
  `covDerivConnDiff` bricks).  `omit ... in` must precede the docstring, not follow it.

## NEXT (the differentiation — recon §4b, 6 steps)

`nabla0SFun_eval_smooth_slots` (`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`) is the
differentiability engine:
`(nabla0SFun s cov X α x)(V·x) = extDerivFun (fun p => α p (V·p)) x (X x) − ∑ₐ α x (update (V·x) a (∇_X V_a))`.
Threading cost: re-package `∇₂g₁` as a `Tensor0SField` (`totalNabla0S`) so the 2nd application has `W`
leading and X/Y/Z as slots; the three combo terms differentiate separately (leading dir X,Y,Z differ).
Then LHS metric-compat Leibniz + step-4 `covDerivDiff` unfold + step-5 `connDiff_koszul_nabla`-cancellation
of slot corrections.  Est. 200–400 lines, genuine multi-session.

## Landed session 3 (both differentiation engines, verified, axioms [propext, Classical.choice, Quot.sound])

- `metricField_totalReg` — regularity of `∇₂g₁ = totalNabla0SFun 2 (LC g₂)(metricTensorField g₁)` as a
  `(0,3)`-field (from `totalNabla0S_reg` + `leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally`),
  so it bundles via `totalNabla0S` and differentiates a second time.
- `nablaMetric_combo_extDeriv` — **RHS engine**: `extDerivFun` along `W` of a `∇₂g₁` combo term
  (direction `V 0`, slots `V 1, V 2`) `= nabla0SFun 3 (LC g₂) W (∇₂g₁-field)` (= `∇₂²g₁`) `+ Leibniz
  corrections`.  **V-parameterized ⟹ covers all THREE combo terms** of `connDiff_koszul_nabla`
  (`V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`).
- `metric_leibniz_extDeriv` — **LHS engine**: `extDerivFun` along `W` of `p ↦ metricTensorField g₁ p (V·p)`
  `= nabla0SFun 2 (LC g₂) W (metricTensorField g₁)` (= `(∇₂g₁)(a,b)`) `+ g₁(∇₂_W ·,·)` corrections.

Both engines = one `nabla0SFun_eval_smooth_slots` + `abel`; RHS also uses the slot-0 bridge
`totalNabla0SFun_apply_section` + `Fin.cons_self_tail`.  `extDerivFun` resolves UNQUALIFIED (it is
`DifferentialGeometry.extDerivFun`, not `Tensor0SBundle.extDerivFun`).  Pass section families as a
`V : Fin n → ContMDiffSection` PARAMETER — inlining `Fin.cons X (…)` in a statement fails constant-motive
inference ("Function expected at Fin.cons … a").

## LANDED session 5 (the assembly — P2.a COMPLETE, verified, axioms [propext, Classical.choice, Quot.sound])

- **`connDiff_koszul_deriv`** — the full differentiated Christoffel-difference Koszul identity:
  ```
  2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z x)
    = nabla0SFun 3 (LC g₂) W field x ![X x,Y x,Z x]
      + nabla0SFun 3 (LC g₂) W field x ![Y x,X x,Z x]
      − nabla0SFun 3 (LC g₂) W field x ![Z x,X x,Y x]
      − 2·nabla0SFun 2 (LC g₂) W (mtf g₁) x ![difference (LC g₁)(LC g₂) x (Y x)(X x), Z x]
  ```
  `field = totalNabla0S 2 (LC g₂)(mtf g₁)(metricField_totalReg …)` (= the bundled ∇₂g₁ (0,3)-field);
  the three `nabla0SFun 3` terms are the ∇₂²g₁ combo, the last is `2·(∇₂_W g₁)(A(X,Y),Z)`.
- **`koszul_field`** (private helper) — field-eval form of `connDiff_koszul_nabla`: pairing `A` against `g₁`
  as `½·field(![Q,P,R]) + ½·field(![P,Q,R]) − ½·field(![R,Q,P])`.  Used 3× on the slot corrections.

### How the assembly closed (the cancellation is EXACT — no α-symmetry needed)
- The 9 slot-correction field-evals from the LHS (koszul on `∇₂_W`-slot args) match the 9 from the RHS
  (`nablaMetric_combo_extDeriv` update terms) **term-for-term by pure rearrangement**.  Predecessor recon
  feared an α slot-symmetry step; with the correct Koszul third-term slot order `−½α(w;q,p)` (NOT `−½α(w;p,q)`),
  every term is syntactically identical after normalisation → `linarith` closes.
- Route: `funext` identity from `connDiff_koszul_nabla` → `congrArg (extDerivFun · x (W x))` → LHS via
  `metric_leibniz_extDeriv` (V=![Adiff,Z]) + RHS via `nablaMetric_combo_extDeriv` ×3 (V=![X,Y,Z]/![Y,X,Z]/![Z,X,Y])
  + `extDerivFun_add`/local `extDerivFun_sub'`/`extDerivFun_const_mul` linearity split (3 combo `MDifferentiableAt`
  via `tensor0SField_eval_smooth_slots_contMDiffAt`, NOT the raw `contMDiffAt_section_apply_gen` — that hits the
  NormedSpace-on-Tensor0SModel wall) → normalise slot funcs / `Function.update` / index-2 to explicit `![·,·,·]`
  → `covDerivConnDiff` expansion `hB` (proved by ONE `rfl`-defeq intermediate, then `abel`) → `koszul_field` ×3
  → `g₁.inner` bilinearity (local `map_add`+`ContinuousLinearMap.add_apply` helper) → `linarith`.

### Lessons (session 5)
- `LeviCivita_isContMDiff` (needed by `diffSec_contMDiff`/`covApply_contMDiffOn`) requires the FULL instance set
  incl. `[BoundarylessManifold I M]` (and InnerProductSpace/NeZero).  DO NOT `omit` them on lemmas that build
  covariant-derivative sections — the a=0 base omits them only because it never packages such sections.
- `covApply_contMDiff` is in `TensorThirdOrderWeitzenbock` (NOT imported here); use `covApply_contMDiffOn`
  (`CurvatureOperator/Defs.lean`, imported) + `contMDiffOn_univ`.  `extDerivFun_sub'` lives in a downstream
  RicciLinearization file — re-derive it locally from `extDerivFun_add` (the add/const_mul ARE in scope).
- `extDerivFun_const_mul`'s FIRST explicit arg is `I` (then `c`, then `hf`): `extDerivFun_const_mul I (1/2) hMDcX`.
- `set cX := (fun p => …)` folds the standalone lambda (in `hRX`/`hMDcX`) but NOT applied `cX p` occurrences
  (inside the combined RHS lambda); fold those with `simp only [← hcX_app]` where `hcX_app p : cX p = … := rfl`.
- `congrArg (fun f => extDerivFun f x (W x)) h` leaves a β-redex; `simp only [] at hmaster` β-reduces it before `rw`.
- Coe-of-`ContMDiffSection.mk` is `rfl` (no `coe_mk` lemma exists — `ContMDiffSection` only has `coe_add`/`coe_smul`/…).
  `↑cov` (CovariantDerivative FunLike coe) = `cov.toFun` definitionally; write `(LeviCivita g₂) σ x v` WITHOUT the
  explicit `↑` (explicit `↑` errors "expected type not known").
- Normalise `![a,b,c] 2` with a `fun _ _ _ => rfl` helper (`Matrix.cons_val_zero/one` only cover 0,1).

## DOWNSTREAM UPDATE (2026-07-25, session 6): P2 route pivoted to the dual/eval form of THIS identity

The consumer B2 P2 no longer uses a (1,3)-component engine.  `connDiff_koszul_deriv` (this file, unchanged)
is now consumed in its **lowered-eval form** by the dual route in
`HCGCompactness/ConnDiffDerivBound.lean`: pair it against the output vector `B` (`Z x = B`), Cauchy–Schwarz
each RHS term (`abs_apply_le_sqrt_normSq0S`) in the `metricCovDeriv 2/1` currency (currency bridges
`field_eq_mcd1`/`nabla3_eq_mcd2` = green there), re-expand `|A|` by `connDiffVec_norm_le`+`lcDiff_norm_le`,
divide by `|B|`, convert `g₁↔g₂`.  Yields B3's `hA1` directly with `CA = (3/2)Λ⁴(Λ''+ΛΛ'²)`.  The P2.b/c/d
below are SUPERSEDED; see `ConnDiffDerivBound.md` §"ROUTE DECISION" + §"EXACT NEXT STEPS".  This file's
`.lean` is UNCHANGED this session (still green, `connDiff_koszul_deriv` sorry-free).

## REMAINING (P2.b/c/d) — the a=1 component→norm engine and comparability conversion (SUPERSEDED — see above)

- **P2.b** — a=1 analogue of `diff_le_covOne_basis` (component→norm engine): from `connDiff_koszul_deriv`
  in a g₁-ON basis, bound `√normSqRS(g₂,1,3)(∇₂A) ≤ C·(√normSq0S(∇₂²g₁) + √normSq0S(∇₂g₁)²)`.  The `∇₂²g₁` combo
  is now available as the RHS `nabla0SFun 3 W field` terms; the quadratic `Λ'²` term is `2·(∇₂_W g₁)(A,Z)`.
- **P2.c/P2.d** — order-4 comparability conversion sibling + assembly into the fibre bound (recon §4).
- Then B2 = P1 ∘ P2 (P1 already landed in `ConnDiffDerivBound.lean`).

## Superseded (session 4 recon) — EXECUTABLE RECIPE + tools (kept for provenance)

Session-4 verdict (STOP-CLEANLY): the assembly is NOT pure algebra — it needs `extDerivFun` linearity over
a **sum-form** RHS, which requires `MDifferentiableAt` of each of the 3 combo terms (real analysis), plus a
delicate many-term cancellation.  Stopped at the green boundary (deep context, per planner's red-spill
guidance).  All tools are located; a fresh successor should close it in one pass:

**Tools confirmed present (do not re-recon):**
- `diffSec_contMDiff cov₀ cov₁ hX hZ` (`ConnectionDifferenceCurvature.lean:120`) — needs instances
  `[ContMDiffCovariantDerivative cov₀ ∞]` + `[..cov₁ ∞]`, `hX : ContMDiff … X`, `hZ : ContMDiff …
  ((∞:WithTop ℕ∞)+1) Z` (Z one level higher).  Instance: `LeviCivita_isContMDiff g :
  ContMDiffCovariantDerivative (LeviCivita g) ∞` (`LeviCivita/Defs.lean:393`).
- `extDerivFun_add` (used at `POUReduction.lean:304`) + `extDerivFun_sub'`
  (`RicciLinearizationConnDiffCoefficients.lean:2679`): `MDifferentiableAt f x → MDifferentiableAt g x →
  extDerivFun (f±g) x = extDerivFun f x ± extDerivFun g x`.  (Also `extDerivFun_neg_at`.)  For the `½`
  scalar use the `const_smul`/`smul` extDerivFun lemma or fold `½` in after.
- combo `MDifferentiableAt`: rewrite combo `nabla0SFun 2 (LC g₂) (V 0) (mtf g₁) p (V.succ·p) = α p (V·p)`
  (via `totalNabla0SFun_apply_section.symm` + `totalNabla0S_apply.symm` + `Fin.cons_self_tail`, `α =
  totalNabla0S 2 (LC g₂)(mtf g₁) (metricField_totalReg …)`), then
  `(TensorMultilinear.contMDiffAt_section_apply_gen (T := fun y => α y) (α.contMDiff.contMDiffAt)
  (v := fun a => V a) (hv := fun a => (V a).contMDiff.contMDiffAt)).mdifferentiableAt`
  (`Tensor/Multilinear/BundleSmoothEvalRealized.lean:856`; pattern copied from
  `nabla0SFun_eval_smooth_slots`'s `hpair`).
- `metricTensorField_apply` (`Tensor/RSTensor/MetricCompatibility.lean:53`): `metricTensorField g x
  slots = g.inner x (slots 0)(slots 1)` (s=2) — bridges `connDiff_koszul_nabla`'s LHS `g₁.inner …` to
  `metric_leibniz_extDeriv`'s `metricTensorField g₁ p (V'·p)` form.

**Recipe:**
0. `Adiff := ContMDiffSection.mk (diffSec (LC g₂)(LC g₁) X Y) (diffSec_contMDiff …)`.  Note
   `diffSec (LC g₂)(LC g₁) X Y p = difference (LC g₁)(LC g₂) p (Y p)(X p)` (defeq) = `connDiff_koszul_nabla`'s
   LHS vector.
1. `hfun : (fun p => g₁.inner p (Adiff p)(Z p)) = (fun p => ½cX p + ½cY p − ½cZ p)` by `funext p;
   exact connDiff_koszul_nabla …` (`cX/cY/cZ` = the three `nabla0SFun 2` combo terms).
2. `congrArg (extDerivFun · x (W x)) hfun` (no differentiability needed here).
3. LHS: rewrite `g₁.inner p (Adiff p)(Z p) = metricTensorField g₁ p (![Adiff, Z]·p)`
   (`metricTensorField_apply`), then `metric_leibniz_extDeriv (V := ![Adiff, Z])` ⟹
   `nabla0SFun 2 (LC g₂) W (mtf g₁) x (Adiff x, Z x) + g₁(∇₂_W Adiff, Z x) + g₁(Adiff x, ∇₂_W Z)`.
4. RHS: `extDerivFun_add/_sub'` + `½`-smul (using the 3 combo `MDifferentiableAt`), then
   `nablaMetric_combo_extDeriv` at `V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`.
5. Identify `∇₂_W Adiff = (LC g₂)(Adiff) x (W x)` and unfold `covDerivDiff` def
   (`ConnectionDifferenceCurvature.lean:274`, via `covDerivConnDiff_eq`): `covDerivConnDiff g₂ g₁ W X Y x =
   ∇₂_W(diffSec X Y) − difference(LC g₁)(LC g₂) x (Y x)(∇₂_W X) − difference(LC g₁)(LC g₂) x (∇₂_W Y)(X x)`,
   so `∇₂_W Adiff = covDerivConnDiff g₂ g₁ W X Y x + A(∇₂_W X, Y) + A(X, ∇₂_W Y)`-type terms.
6. **Cancel**: the step-3 `g₁(A(∇₂_W …), Z)` + step-4 slot corrections cancel via `connDiff_koszul_nabla`
   applied to the `∇₂_W`-slot args (each `2 g₁(A(∇₂_W s, ·), ·)` = its ∇₂g₁-combo).  Surviving:
   `2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z x) = [∇₂²g₁ combo from step 4 `nabla0SFun 3`] − 2·nabla0SFun 2
   (LC g₂) W (mtf g₁) x (Adiff x, Z x)` (= `[∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y),Z)`).  Est. ~150–250 lines.

## Status

- 2026-07-25 (B2 session 5): **P2.a COMPLETE.**  `connDiff_koszul_deriv` (the full differentiated
  Christoffel-difference Koszul identity) LANDED in `ChristoffelDiffKoszulDeriv.lean`, sorry-free, verified by
  authoritative `lake build` (✔ 3666/3666), axioms `[propext, Classical.choice, Quot.sound]`.  Also landed the
  `koszul_field` field-eval helper.  ~230 lines added (helper + main).  The cancellation is EXACT (9+9 slot
  corrections match by rearrangement — no α-symmetry).  Next = P2.b (a=1 component→norm engine); NOT started.
- 2026-07-25 (B2 session 4): assembly RECON complete; **clean stop at the green boundary (no new Lean)**.
  Verdict: the assembly needs `extDerivFun` linearity over a sum-form RHS ⟹ `MDifferentiableAt` of 3 combo
  terms (real analysis) + a delicate many-term cancellation — NOT pure algebra.  All tools located and the
  EXECUTABLE RECIPE recorded above (`diffSec_contMDiff`+`LeviCivita_isContMDiff`, `extDerivFun_add/_sub'`,
  `contMDiffAt_section_apply_gen` for combo `MDifferentiableAt`, `metricTensorField_apply`, `covDerivDiff`
  unfold).  Stopped rather than risk a red spill in deep (438k) context (planner-sanctioned); `.lean`
  unchanged = committed green (f1e4b8e38).  A fresh successor executes the recipe in one pass.
- 2026-07-25 (B2 session 3): BOTH differentiation engines LANDED (`metric_leibniz_extDeriv` +
  `nablaMetric_combo_extDeriv`) + `metricField_totalReg`, verified/axiom-clean.  Milestone (slot-0 bridge
  + one combo) EXCEEDED (general combo covers all 3 terms; LHS engine also done).
- 2026-07-25 (B2 session 2): a=0 base `connDiff_koszul_nabla` LANDED (verified, axiom-clean); home + LC
  currency + instances confirmed in real Lean.
