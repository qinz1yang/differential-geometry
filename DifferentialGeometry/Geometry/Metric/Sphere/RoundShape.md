# RoundShape.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, Step 5B (Gauss route), **Step C**: shape operator = Id
(C1) + Gauss curvature value (C2). Then D (capstone) extends `Curvature/Sphere/ConstCurvature.lean`.

## State (2026-06-30)

- **C1 `ambDeriv_inner_normal` DONE** (focused check green; real build pending/confirmed):
  `⟪ambDeriv Y x v, ↑x⟫ = − roundInner x (Y x) v` for MDiffAt Y. Route: the constraint
  `⟪dInclField Y b, ↑b⟫ = 0` (tangent ⊥ normal) is identically zero, differentiate via
  `mfderiv_inner` (Step B product rule); the const-0 LHS derivative kills one side, the coe-factor
  derivative `mfderiv (↑) x v = dIncl x v` (defeq, lemma `hcoeval := rfl`) gives the metric pairing.
- **Gauss formula `ambDeriv_gauss` DONE** (focused check green): for MDiffAt Y,
  `ambDeriv Y x v = dIncl x (projConn Y x v) − roundInner x (Y x) v • ↑x`.  Route: `dIncl_projConn`
  gives the tangential part as `(ℝ∙↑x)ᗮ.starProjection (ambDeriv …)`; split off the normal line via
  `Submodule.starProjection_add_starProjection_orthogonal` + `Submodule.starProjection_singleton`
  (unit `‖↑x‖=1` ⇒ singleton proj `= ⟪↑x,w⟫•↑x`); identify the normal coeff by C1 + `real_inner_comm`;
  finish with `module`.

## ✓✓ STEP C COMPLETE (2026-06-30, real-build sorry-free)

11 verified lemmas here (C1, ambDeriv_gauss, ambDeriv2, FLAT `ambDeriv_bracket_symm`, inner_dIncl_metricCov,
mdiffAt_inner_left, `mfderiv_mul_innerCoordFun_of_inner_eq_zero` [GPT-Pro unblock], inner_ambDeriv_nested,
ambDeriv_section_mdiffAt, **`dIncl_curv_inner` = HEART, the Gauss equation**).  The curvature VALUE lives in
`Curvature/Sphere/ConstCurvature.lean` as `roundMetric_sec_value`: `metricRm04StdAt roundMetric x X Y Y X =
g(X,X)g(Y,Y) − g(X,Y)²` (c=1), via germ-reduction + HEART.  See the "BLOCKER BROKEN" section above for the
durable synonym/coercion lessons.  Remaining for `spaceForm_const_metric`: the trivial `ConstPosSecMetric`
wrapper (in Hamilton) + the quotient descent S³/Γ (the big frontier).

## C2 — the Gauss curvature value (HISTORICAL plan — now DONE, see above)

**Target.** `metricRm04StdAt roundMetric x X Y Y X = roundInner x X X · roundInner x Y Y − (roundInner x X Y)²`.

**Reduction chain (all `@[simp]`/defeq, mechanical):**
`metricRm04StdAt g x X Y Z W = metricRm04At g x (vec4 X Y Z W)` (`metricRm04StdAt_apply`)
`= riemannCurvature04At g (metricCov g) (metricCov_smooth g) x (vec4 …)` (defeq, `metricRm04At`)
`= g.inner x W (riemannCurvatureAux (metricCov g) (constX)(constY)(constZ) x)` (`riemannCurvature04At_apply_const`),
where `const = tangentConstAt x`, and
`riemannCurvatureAux cov X Y Z x = cov(p↦ cov Z p (Y p)) x (X x) − cov(p↦ cov Z p (X p)) x (Y x) − cov Z x [X,Y]`
(Field.lean:376). So target `= roundMetric.inner x X (R)` with `R = riemannCurvatureAux (metricCov g) cX cY cY x`.

**KEY INSIGHT (the cancellation that makes it tractable — worked out, not yet in Lean):**
`roundMetric.inner x X R = ⟪dIncl x R, dIncl x X⟫`. Pair the WHOLE computation against the tangent
vector `w := dIncl x X`. Then **every `↑x`-direction term dies** (`⟪↑x, dIncl x X⟫ = 0`), so:
- the orthogonal-projection corrections `P(u) = u − ⟪↑x,u⟫↑x` collapse: `⟪P(u), w⟫ = ⟪u, w⟫`
  (P self-adjoint, fixes tangent `w`; reuse Step B's `horth`/`horth_right`);
- the Gauss-formula normal terms `−roundInner•↑x` and ALL product-rule scalars `(dφ)•↑x` die —
  **so the scalar `dφ` factors never need to be computed.**

After substituting `metricCov → projConn` (see below) and injecting `dIncl`:
`dIncl x R = P(ambDeriv A x X) − P(ambDeriv B x Y) − P(ambDeriv cZ x br)`,
`A = p↦ projConn cZ p (cY p)`, `B = p↦ projConn cZ p (cX p)`, `br = mlieBracket cX cY x`.
Pairing with `w` and using `dInclField A =ᶠ p↦ ambDeriv cZ p (cY p) + roundInner p (cZ p)(cY p)•↑p`
(this is `ambDeriv_gauss` rearranged), the Leibniz rule `mfderiv(φ•↑·) x v = (dφ)•↑x + φ(x)•dIncl x v`
contributes only `φ(x)•dIncl x v` after pairing (`(dφ)•↑x` dies), giving the two Gram products; and the
pure second-derivative part cancels by **FLAT**:

**FLAT (the keystone — ambient flatness / 2nd-derivative bracket symmetry).** For `f : sphere→E`
smooth and smooth fields `X,Y`:
`mfderiv(p↦ mfderiv f p (Y p)) x (X x) − mfderiv(p↦ mfderiv f p (X p)) x (Y x) = mfderiv f x (mlieBracket I X Y x)`.
Proof route = the SAME functional-test as Step B's `dIncl_mlieBracket`: fix `w∈E`, set scalar field
`g_w := ⟪f ·, w⟫`, apply the PROVEN `embedDeriv_mlieBracket` to `g_w`, bridge each level with
`mfderiv_inner_left` (w fixed); `ext_inner_right` over all `w`. Smoothness of `p↦ mfderiv f p (Y p)`
(needed for `mfderiv_inner_left`) routes through `metricCov_smooth` after `f = dInclField cZ` is
rewritten by `ambDeriv_gauss` to `dIncl(metricCov g cZ ·) + normal` — metricCov sections are smooth.
Net after pairing: `⟪dIncl x R, dIncl x X⟫ = roundInner(Y,Y)roundInner(X,X) − roundInner(X,Y)²`. ✓

**`metricCov → projConn` substitution (the Koszul caveat, the fiddliest bookkeeping):**
`projConn_eq_metricCov` (Step B) equates `.toFun` only on `MDiffAt` sections. Sections needing the
substitution: `cX,cY,cZ` (MDiffAt — Field.lean:363) AND the nested `A,B` and inner `cov cZ` sections.
The nested-section MDiffAt witnesses come from `metricCov_smooth` (ContMDiffCovariantDerivativeLocally),
NOT from projConn (which has no smoothness field). Reuse the MDiffAt-of-`cov σ` witnesses from
`Pointwise.lean` / `MetricLeviCivitaReconcile.lean`.

**DONE (2026-06-30, real-build sorry-free):** `ambDeriv_bracket_symm` (FLAT) + `ambDeriv2`/`ambDeriv2_apply`
helper. FLAT statement uses `ambDeriv2 Z Y x (X x) − ambDeriv2 Z X x (Y x) = ambDeriv Z x [X,Y]`; the
`ambDeriv2` codomain-ascription dodges the `TangentSpace 𝓘(ℝ,E)` per-point synonym in the subtraction
(the same trick `ambDeriv` uses; a bare `(a − b : E)` does NOT work — `binop%` resolves operand types
first). Proof = exact mirror of `dIncl_mlieBracket`, one level deeper: `embedDeriv_mlieBracket` applied
to `gw := embedDeriv Z (innerCoordFun w)` (auto-smooth), bridged by `mfderiv_innerCoordFun` /
`mfderiv_inner_left` at each level. MDiffAt of `p↦ambDeriv Z p (W p)` is the FLAT hypothesis (supplied
at call site). Gotchas: `simpa using DFunLike.congr_fun hbr x` (not `simp only [Pi.sub_apply]`) to split
`(f−g) x`; `exact hbrx.symm` (bracket on goal RHS here, opposite to `dIncl_mlieBracket`).

**DONE (2026-06-30, real-build sorry-free): `inner_dIncl_metricCov`** — the reusable paired tangential
reduction `⟪dIncl x (metricCov g S x v), dIncl x W⟫ = ⟪ambDeriv S x v, dIncl x W⟫` for MDiffAt `S`.
Proof: `← projConn_eq_metricCov`, `dIncl_projConn`, `← Submodule.starProjection_apply`,
`Submodule.starProjection_inner_eq_zero` + `inner_sub_left`+`sub_eq_zero` (the inlined `horth`).
**Also DONE: `mdiffAt_inner_left`** (`p ↦ ⟪w, F p⟫` differentiable, generic `F`).

## ✓ BLOCKER BROKEN (2026-06-30, GPT Pro consult): `mfderiv_mul_innerCoordFun_of_inner_eq_zero` DONE

Pro's escape works and is VERIFIED. The unblocking lemma (scalar form, routed through the bundled
`innerCoordFun`, never a bare `⟪w,↑·⟫` lambda or bare-coercion `mfderiv`):
`mfderiv (fun p => φ p * (innerCoordFun w) p) x v = φ x * ⟪w, dIncl x v⟫` (for `φ` MDiffAt, `⟪w,↑x⟫=0`).
Proof keys that finally worked: ψ smoothness via `(innerCoordFun w).contMDiff.contMDiffAt.mdifferentiableAt`
(the accessor DOES work — earlier failures were from bare-coercion context, not the accessor); `hψx` via
`rw [hψdef]; simpa [innerCoordFun]`; and the CRITICAL final-algebra fix — the `mfderiv ψ x` CLM has the
`TangentSpace 𝓘(ℝ,ℝ)` synonym codomain that POISONS every `smul_apply`/`add_apply`/`*`/`•` (none match),
so first rewrite it to a CLEAN-codomain CLM `hψCLM : mfderiv ψ x = (innerSL ℝ w).comp (dIncl x)`
(via `ext u; show … = ⟪w, dIncl x u⟫; exact mfderiv_innerCoordFun w x u`), THEN
`rw [(…).mfderiv]; simp only [hψx, hψCLM, zero_smul, add_zero]; change φ x • (((innerSL ℝ w).comp (dIncl x)) v) = …; rw [comp_apply, innerSL_apply_apply, smul_eq_mul]`.
**Durable lesson:** for `mfderiv` into `ℝ`, the codomain `TangentSpace 𝓘(ℝ,ℝ) (f x)` synonym blocks ALL
apply/arith simp lemmas — rewrite the derivative CLM to a clean `T_x →L ℝ` form first (or use `change`
to the defeq pointwise-smul form), never fight `smul_apply` on the synonym.

## ⚠ (historical) BLOCKER: bare-coercion `mfderiv` → false `ChartedSpace E` instance

`inner_ambDeriv_nested` + its helper `inner_smul_coe_deriv` (the `roundInner·↑p` Leibniz term) were
fully written and the MATH is correct, but were REVERTED — blocked by a Mathlib elaboration bug:
- **Trigger:** any `mfderiv (𝓡 n) 𝓘(ℝ,E) F x` with `F = (↑) : sphere→E` the *bare coercion* (e.g.
  inside `mfderiv_inner_left w hcoeM v`, whose conclusion is `⟪w, mfderiv (↑) x v⟫`) demands the FALSE
  instance `ChartedSpace (EuclideanSpace ℝ (Fin n)) E` (E has dim n+1, ≠ n). `dIncl x v` (= `mfderiv(↑) x v`
  by def, but PRE-elaborated) is fine; re-deriving `mfderiv(↑)` fresh is what breaks.
- **Second trigger:** writing a *standalone* `(fun p => ⟪dIncl x W, ↑p⟫)` lambda in a TYPE/statement
  position also demands `ChartedSpace E` (but it's FINE as a subterm of a bigger lambda, and FINE with a
  GENERIC `w` binder à la `innerCoordFun`). Dodge by binding `have h := mdiffAt_inner_left …` WITHOUT a
  type annotation (infer it), or pass the concrete vector as a lemma argument.
- **Third trigger:** `ambDeriv2 … + mfderiv(roundInner·↑) x v` — the second mfderiv lands in the
  per-point `TangentSpace 𝓘(ℝ,E)` synonym, `HAdd E (synonym) ?` fails; `(… : E)` and CLM-codomain
  ascription do NOT stick (only a `def` with baked-in codomain does, à la `ambDeriv2`).
- **Vector alternative blocked too:** `mfderiv_smul` / `HasMFDerivAt.smul` are stated through
  `NormedSpace.fromTangentSpace` (heavy boilerplate). No `MDifferentiableAt.inner` in Mathlib.

**The escape route (for next session / GPT Pro):** the generic-`w`-binder trick (mdiffAt_inner_left)
proves the issue is solvable by stating EVERY coercion-touching fact as a lemma with the concrete
vector/coercion passed as an *argument* (never written bare in a type). Build `inner_smul_coe_deriv`
fully generic in `w` and `φ`; for its internal `mfderiv ⟪w, ↑·⟫ = ⟪w, dι v⟫` use `mfderiv_innerCoordFun`
(its conclusion is `⟪w, dIncl x v⟫` — uses `dIncl`, NOT `mfderiv(↑)`, so it dodges the bug) by rewriting
`ψ = ⇑(innerCoordFun w)`; and define a small `def` for the `roundInner·↑` field's derivative to dodge the
synonym `HAdd`. Then `inner_ambDeriv_nested` + HEART (`dIncl_curv_inner`) + capstone follow as derived below.

**FULLY-DERIVED remaining pieces (transcribe + debug; ~80 lines). USE THE SCALAR ROUTE** (mfderiv on
ℝ-valued maps has NO tangent-space synonym; `mfderiv_smul` is phrased with `NormedSpace.fromTangentSpace`
and is painful — avoid it):

`inner_ambDeriv_nested (Z Yf : sections) (x) (v W : tangent) (hD : MDiffAt (p↦ ambDeriv ⇑Z p (Yf p)) x)`:
`⟪ambDeriv (fun p => metricCov g ⇑Z p (Yf p)) x v, dIncl x W⟫ = ⟪dIncl x W, ambDeriv2 Z Yf x v⟫ + roundInner x (Z x)(Yf x) * ⟪dIncl x W, dIncl x v⟫`.
 1. `hAfun : dInclField (fun p => metricCov g ⇑Z p (Yf p)) = fun p => ambDeriv ⇑Z p (Yf p) + roundInner p (Z p)(Yf p)•↑p`
    (funext p; `dInclField_apply`, `← projConn_eq_metricCov hZp (Yf p)` [hZp = Z.contMDiff…mdifferentiableAt],
     `ambDeriv_gauss hZp (Yf p)` rearranged via `rw [this]; module`).
 2. `ambDeriv_apply`, `real_inner_comm` ⇒ `⟪dIncl W, mfderiv (dInclField A) x v⟫`, then `mfderiv_inner_left (dIncl W) hAd v` BACKWARD
    (hAd = `dInclField_mdifferentiableAt` of A's bundle-MDiffAt from `cov_smooth_apply_contMDiffAt`) ⇒ `mfderiv(p↦⟪dIncl W, dInclField A p⟫) x v`.
 3. scalar `have hscal : (p↦⟪dIncl W, dInclField A p⟫) = (p↦ ⟪dIncl W, ambDeriv ⇑Z p (Yf p)⟫ + roundInner p (Z p)(Yf p) * ⟪dIncl W, ↑p⟫)`
    (funext; `rw [hAfun]`; `simp only [inner_add_right, inner_smul_right]`).
 4. `rw [hscal]`, `mfderiv_add hMh1 hMh2`; `mfderiv_inner_left (dIncl W) hD v` ⇒ h1' = `⟪dIncl W, ambDeriv2 Z Yf x v⟫` (= ambDeriv2_apply);
    h2 = `φ·ψ`, `φ = roundInner ·(Z·)(Yf·)`, `ψ = ⟪dIncl W, ↑·⟫` (= `innerCoordFun (dIncl x W)` up to inner-comm) ⇒ `(HasMFDerivAt.mul hφ' hψ').mfderiv`
    gives `φ(x)•(mfderiv ψ) + ψ(x)•(mfderiv φ)`; `ψ(x) = ⟪dIncl W, ↑x⟫ = 0` (perp, `← range_mfderiv_coe_sphere`+orthogonal); `mfderiv ψ x v = ⟪dIncl W, dIncl x v⟫` (mfderiv_inner_left / mfderiv_innerCoordFun + comm) ⇒ `roundInner x (Z x)(Yf x) * ⟪dIncl W, dIncl x v⟫`.
    MDiffAt: `hMh1` from `(mfderiv_inner_left …)`-differentiability of `⟪dIncl W, ambDeriv ⇑Z · (Yf ·)⟫` (needs hD); `φ` MDiffAt = `(dInclField_mdifferentiableAt hZ).inner (dInclField_mdifferentiableAt hYf)`-style — note **NO `MDifferentiableAt.inner` in Mathlib's Calculus.lean**; build via `innerSL`/`isBoundedBilinearMap_inner` HasMFDerivAt like `mfderiv_inner` (RoundProjConnLC), or test-route; `ψ` MDiffAt from `innerCoordFun`'s ContMDiff.

`dIncl_curv_inner` (HEART): expand `riemannCurvatureAux` (def-unfold to `metricCov g A x (X x) − metricCov g B x (Y x) − metricCov g ⇑Z x br`);
`map_sub`(dIncl) + `inner_sub_left` ⇒ 3 inner terms; `inner_dIncl_metricCov` ×3 (MDiffAt: ⇑Z via Z.contMDiff; A,B via `cov_smooth_apply_contMDiffAt g-smooth Y Z x` / `… X Z x`) ⇒ `⟪ambDeriv A x (X x),dIncl W⟫ − ⟪ambDeriv B x (Y x),dIncl W⟫ − ⟪ambDeriv ⇑Z x br,dIncl W⟫`;
`inner_ambDeriv_nested` ×2 ⇒ `⟪dIncl W, ambDeriv2 Z Y x (X x)⟫ − ⟪dIncl W, ambDeriv2 Z X x (Y x)⟫ + (Gram_X − Gram_Y) − ⟪ambDeriv ⇑Z x br, dIncl W⟫`;
the two ambDeriv2 terms − bracket term = 0 by **FLAT** `ambDeriv_bracket_symm` (after `← inner_sub_right` and `real_inner_comm` on the bracket term); Gram terms via `real_inner_comm` ⇒ `roundInner(Z,Y)·⟪dIncl(X x),dIncl W⟫ − roundInner(Z,X)·⟪dIncl(Y x),dIncl W⟫`.

**Capstone** (extend `Curvature/Sphere/ConstCurvature.lean`): germ-reduce the const-section curvature to smooth `Xc Yc` via
`exists_contMDiffSection_eventuallyEq_tangentConstAt`+`connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst`
(mirror MetricLeviCivitaReconcile.lean:107); `metricRm04StdAt_apply`+`riemannCurvature04At_apply_const` reduce LHS to
`roundMetric.inner x X (riemannCurvatureAux …)` = `⟪dIncl(R), dIncl X⟫`; apply HEART (Z:=Yc, W:=X, `Xc x=X` etc.);
`roundMetric_inner`/`roundInner_apply` + comm ⇒ `metricRm04StdAt g x X Y Y X = roundInner X X·roundInner Y Y − (roundInner X Y)²`;
then `roundMetric_constPosSec : ConstPosSecMetric roundMetric := ⟨1, one_pos, fun x X Y => by …; ring⟩`.

**Remaining C2 assembly (est. ~80 lines, all tools located — the HEART lemma + capstone):**
1. **Germ reduction** (~6 lines, mirror `riemannCurvatureAux_tangentConst_eq_riemannOp`,
   MetricLeviCivitaReconcile.lean:107): `exists_contMDiffSection_eventuallyEq_tangentConstAt x X` gives
   `⟨Xc, hXc : ⇑Xc =ᶠ[𝓝 x] tangentConstAt x X, hXcx : Xc x = X⟩`; then
   `connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst` transfers
   `riemannCurvatureAux (metricCov g) (tangentConstAt …) x` to the smooth `Xc Yc Yc`.
2. **HEART lemma** (Gauss equation on smooth sections X Y Z, tangent W) — the ~110-line core:
   `⟪dIncl x (riemannCurvatureAux (metricCov g) ⇑X ⇑Y ⇑Z x), dIncl x W⟫ =
     roundInner x (Z x)(Y x)·⟪dIncl(X x),dIncl W⟫ − roundInner x (Z x)(X x)·⟪dIncl(Y x),dIncl W⟫`.
   Route: expand `riemannCurvatureAux`; nested-section MDiffAt via `cov_smooth_apply_contMDiffAt`
   (Field.lean:171, takes smooth X Y + `metricCov_smooth`); each `dIncl x (metricCov g S x v)` →
   `dIncl x (projConn S x v)` (`projConn_eq_metricCov`) → `P(ambDeriv S x v)` (`dIncl_projConn`);
   pair with `dIncl x W` and use **P self-adjoint + fixes tangent** `⟪P(u),dIncl W⟫=⟪u,dIncl W⟫`
   (Step B `horth`/`horth_right`, from `Submodule.starProjection_inner…`). Then `dInclField A` (A =
   nested cov section) rewrites by `ambDeriv_gauss` to `ambDeriv Z · (Y ·) + roundInner·↑·`; the
   `ambDeriv2` part cancels by **FLAT**, the `roundInner·↑·` part gives the Gram term via the
   **pairing-first Leibniz trick**: `⟪mfderiv(p↦φ(p)•↑p) x v, dIncl W⟫ = mfderiv(p↦φ(p)·⟪↑p,dIncl W⟫) x v`
   (scalar product rule `mfderiv_mul`-style; `⟪↑x,dIncl W⟫=0` kills `dφ`; `mfderiv_inner_left` on `⟪↑·,dIncl W⟫`
   gives `φ(x)·⟪dIncl(X x),dIncl W⟫`) — so the vector Leibniz `mfderiv_smul` is never needed.
3. **C2 endpoint + D capstone** (~15 lines): germ-reduce, apply HEART with Z:=Y, W:=X, `Xc x=X` etc.,
   `roundInner_apply` + `roundMetric.inner` symmetry ⇒ `metricRm04StdAt g x X Y Y X =
   roundInner X X·roundInner Y Y − (roundInner X Y)²`; then `roundMetric_constPosSec := ⟨1, one_pos, …⟩`.

## API gotchas (durable)
- `mfderiv_const` reduces `mfderiv (fun _=>c)` to the zero CLM but `ContinuousLinearMap.zero_apply`
  does NOT fire on `(0) v` when the codomain is the `TangentSpace 𝓘(ℝ,ℝ) 0` synonym; close `0 v = 0`
  by `rfl` (zero CLM applied = 0 definitionally) after `simp only [mfderiv_const]`.
- `mfderiv%` (the notation) and `mfderiv (𝓡 n) 𝓘(ℝ,E)` are different ATOMS to `linarith` — use
  defeq-aware `exact eq_neg_of_add_eq_zero_left …` not `linarith` to finish such goals.
- Projection lemmas live in `namespace Submodule`: `Submodule.starProjection_singleton`,
  `Submodule.coe_orthogonalProjection_apply`, `Submodule.starProjection_add_starProjection_orthogonal`.
- `norm_eq_of_mem_sphere x : ‖(↑x:E)‖ = 1` for `x : sphere 0 1` (@[simp]).
