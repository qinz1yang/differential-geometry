# UNIF item-6 / B2 recon — the UNGATED order-1 connection-difference-derivative norm bound

Status file for the B2 mission (ungated general-Λ pointwise bound on the output vector of
`covDerivConnDiff g₂ g₁ X Y Z x`).  Companion to `UnifCovSumCross.md` §Session 9 (which isolated
`∇₂A = covDerivConnDiff` and flagged the home mismatch).  This note resolves the ROUTE and the HOME
by a clean factorization, and records the single remaining frontier.

## 0. TARGET (exact statement + hypothesis set)

For `g₂` (reference) and `g₁` two `SmoothRiemannianMetric I M`, on a compact boundaryless manifold,
at `x ∈ K`, for tangent vectors `v w u : TangentSpace I x`:
```
√(g₂.inner x (covDerivConnDiff g₂ g₁ (ext v) (ext w) (ext u) x)
             (covDerivConnDiff g₂ g₁ (ext v) (ext w) (ext u) x))
  ≤ CA(Λ, Λ', Λ'') · √(g₂.inner x v v) · √(g₂.inner x w w) · √(g₂.inner x u u)
```
where `ext · = smoothExtensionTangent (I := I) x ·`, and `covDerivConnDiff` is
`RicciConnDiffPalatini.lean:78` (`= covDerivDiff (LC g₂) (LC g₁)`, the eval `(∇₂_v A)(w,u)` of
`A = connDiff g₁ g₂`).

Hypothesis set the proof needs (general Λ, NO δ<1 gate):
- `hEq  : MetricUniformEquivalentOn K g₂ g₁ Λ`     — the comparability sandwich `Λ⁻¹·g₂ ≤ g₁ ≤ Λ·g₂`
  (note arg order: `MetricUniformEquivalentOn K gRef h C` = `C⁻¹·gRef ≤ h ≤ C·gRef`, so `gRef = g₂`,
  `h = g₁`).
- `hJet1 : MetricCovDerivOrderBoundOn K 1 g₁ g₂ Λ'`  — `|∇₂ g₁|_{g₂} ≤ Λ'`  (order-1 metric jet).
- `hJet2 : MetricCovDerivOrderBoundOn K 2 g₁ g₂ Λ''` — `|∇₂² g₁|_{g₂} ≤ Λ''` (order-2 metric jet).
  (`MetricCovDerivOrderBoundOn K a h gRef C = ∀x∈K, metricCovDerivNorm a h gRef x ≤ C`,
  `metricCovDerivNorm a h gRef x = √normSq0S gRef x (a+2) (metricCovDeriv h gRef a x)`, AllTimesBounds.)
- `hx : x ∈ K`.  `[NeZero (finrank ℝ E)]` etc. as in the a=0 sibling.

CA shape (state-before-prove): `CA = poly(Λ)·(Λ'' + Λ'²)` — linear in the order-2 jet plus the SQUARE
of the order-1 jet.  From Koszul `A ~ g₁⁻¹·∇₂g₁` (so `∇₂A ~ g₁⁻¹·∇₂²g₁ + g₁⁻¹·(∇₂g₁)·g₁⁻¹·(∇₂g₁)`).
Expected explicit constant, mirroring the a=0 `(3/2)·√(Λ³)·Λ'`: a fixed-`n` polynomial in `√Λ` times
`(Λ'' + Λ'²)`, with the `√Λ` power one higher than a=0 (order-4 vs order-3 comparability conversion).

## 1. THE GATE — why δ<1 is there and what replaces it at general Λ

The δ<1-gated sibling `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`
(`Curvature/CovDerivConnDiffQuadraticBound.lean:235`) already delivers the TARGET SHAPE, but:
- it is gated on `gFibreOpBound g₂ (ccTensorBilinSymm g₂ P) δ` with `δ ≤ max δ₀ 0 < 1`
  (`P := g₁ − g₂`), and its constant is EXISTENTIAL in the bundled `iteratedCovGrad` jet currency,
  not the HCG `metricCovDerivNorm` currency.
- The gate is genuinely LOAD-BEARING: the ~5000-line `rfns_*_le_of_lt_one` tower
  (`ConnectionDifferenceArmRfnsBound.lean` etc.) controls `g₁⁻¹` relative to `g₂` by a NEUMANN
  series in the perturbation `P`, which needs `‖P‖_{g₂-op} = δ < 1`.  Concretely the gate enters at
  `raisedKoszulVec = sharpFlatRaiseEndo g₂ g₁ (...)` via `inverseMetricSharpFib g₂` ∘ `g0FlatCLM g₁`
  (the g₂-relative inverse of the g₁-flat).
- **At general Λ the gate FAILS**: comparability gives `|P(v,v)| ≤ (Λ−1)·g₂(v,v)`, i.e. `δ = Λ−1 ≥ 1`
  whenever `Λ ≥ 2`.  The gated theorem is unusable outside `Λ ∈ [1,2)`.  So B2 is NOT "apply the gated
  theorem with a bigger δ₀"; it needs a genuinely different inverse control.

**Replacement (the house route, already realized at a=0):** the comparability sandwich gives inverse
control DIRECTLY, realized as "work in a g₁-orthonormal basis where `g₁⁻¹` has identity components."
This is exactly how `lcDiff_norm_le` (a=0, below) achieves inverse control WITHOUT any δ<1 / Neumann
series — via `MetricInverseInBasis h x basis identityInvMetric` (the basis is chosen h-ON so the
inverse-metric components are the identity), then a `sqrt_normSq0S_*_le_of_metricUniformEquivalentOn`
comparability conversion supplies the `√(Λ^k)` factors.  Cf. the committed D1 comparability idiom
`clm_offdiag_le_of_diag` / `metricDiff_diag_le` in `UnifCurvatureJetBound.lean`.

## 2. THE FACTORIZATION — B2 = P1 ∘ P2 (the key recon result)

Read the gated proof `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`
(`CovDerivConnDiffQuadraticBound.lean:235`) as two independent halves:

- **P1 (lines ~302–349, UNGATED, already existing math):** the output-vector g₂-norm is bounded by
  the FIBRE norm of the bundled order-1 covariant derivative of the connection-difference section:
  ```
  √(g₂(covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x, ·))
      ≤ ‖(covGrad g₂ 1 2 (connDiffSection g₁ g₂)).toSection x‖_{fibre,g₂}
          · √(g₂ v v) · √(g₂ w w) · √(g₂ u u).
  ```
  P1 uses ONLY: the flat/eval bridge `connDiffSection_covGrad_eq_covDerivConnDiff`
  (`ConnDiffCovGradBridge.lean:640`, PUBLIC) and the fibre Cauchy–Schwarz
  `abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt` (`CovDerivConnDiffFibreExtraction.lean:50`, PUBLIC),
  plus `metric_inner_self_nonneg` and a divide-by-`NA` step.  **NO δ<1 anywhere.**  The gated file's
  composed bridge `covGrad_connDiffSection_flat_eval_eq_inner` (:177) is `private`, but its body only
  calls the PUBLIC `connDiffSection_covGrad_eq_covDerivConnDiff` + public flat helpers
  (`g0FlatCLM`, `cotangentToDual_*`, `smoothExtensionTangent_*`, `ContMDiffSection.exists_eq_at`),
  so it re-derives cleanly in a downstream HCG leaf.

- **P2 (the gated `hWnorm` = `exists_norm_covGrad_connDiffSection_le_of_jetEnvelope`, :43): the ONLY
  gated part, and the SINGLE remaining B2 frontier.**  Ungated form to prove:
  ```
  ‖(covGrad g₂ 1 2 (connDiffSection g₁ g₂)).toSection x‖_{fibre,g₂}  ≤  CA(Λ, Λ', Λ'')
  ```
  under `hEq + hJet1 + hJet2` at `x∈K`.  This is the **a=1 analogue of `lcDiff_norm_le`** (a=0).

So: **B2 = P1 (bank now, ungated) ∘ P2 (the a=1 Koszul fibre bound, the frontier).**

## 3. THE a=0 BASE ALREADY EXISTS (do not rebuild)

`lcDiff_norm_le` (`HCGCompactness/MetricLapDiff.lean:164`) is the a=0 ungated Koszul fibre bound in the
comparability + metric-jet currency:
```
√normSqRS(g₂,1,2)(connectionDifferenceTensorAt (LC g₁) (LC g₂) x)  ≤  (3/2)·√(Λ³)·|∇₂g₁|_{g₂}
```
under `MetricUniformEquivalentOn K g₂ g₁ Λ`, NO δ<1.  Its route (the P2-at-a=0 template):
1. Koszul COMPONENT identity `connDiffCompEq` (`AllTimesBounds.lean`, from `connDiff_koszul` /
   `ChristoffelDifferenceKoszul.lean:105`): in a g₁-ON basis, `2·A_comp = (∇₂g₁)_comp + (∇₂g₁)_comp −
   (∇₂g₁)_comp`.  Inverse control = the ON basis (g₁⁻¹ = id), NOT Neumann.
2. component→norm engine `diff_le_covOne_basis` (`AllTimesBounds.lean`): `√normSqRS(A) ≤
   (3/2)·√normSq0S(∇₂g₁)`.
3. comparability conversion `sqrt_normSq0S_three_le_of_metricUniformEquivalentOn(_symm)`
   (`AllTimesBounds.lean`): `√normSq0S(g₁,3)(·) ≤ √(Λ³)·√normSq0S(g₂,3)(·)` = the `√(Λ³)` factor.
Assembled in `diff_le_covOne_basis_ref_lc` (`AllTimesBounds.lean:3287`) → `lcDiff_norm_le`.
The bridge `metricDeriv_eq_covDeriv_norm` (`UnifCovSumCross.lean:620`) then equates the `metricDerivNorm`
and `metricCovDerivNorm` order-1 currencies.  The full a=0 output-vector bound is what
`diffStep_jet_one_le` (`UnifCovSumCross.lean:636`) packages (for generic-rank `diffStep`).

## 4. P2 ROUTE (the a=1 frontier) — brick sequence, state-before-prove

Lift the a=0 route (§3) one derivative up.  `covGrad g₂ 1 2 (connDiffSection g₁ g₂)` is the bundled
`(1,3)`-tensor `∇₂A`; its eval is `covDerivConnDiff` (bridge in §2).

- **Brick P2.a — the differentiated Koszul (component or lowered-tensor) identity — THE CRUX.**
  Differentiate `connDiff_koszul` (`2 g₁(A(X,Y),Z) = K(X,Y,Z)`, `K = ∇₂g₁ combination`) covariantly
  under ∇₂.  Lowered-tensor form (cleanest to state):
  ```
  2 g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = (∇₂_W K)(X,Y,Z) − 2·(∇₂_W g₁)(A(X,Y), Z),
  ```
  with `A(X,Y) = connDiff g₁ g₂ x (Y)(X)`, `(∇₂_W K) = ∇₂²g₁ combination`, and
  `(∇₂_W g₁)(·,·) = metricCovDeriv g₁ (LC g₂) W · · x` (ChristoffelDifferenceKoszul currency).
  Derivation: apply the covariant Leibniz for the metric contraction to both sides of `connDiff_koszul`
  (which holds pointwise ∀y for MDiff sections).  Needs: (i) `mfderiv(g₁(a,b)) x (W x) =
  metricCovDeriv g₁ (LC g₂) W a b x + g₁(∇₂_W a,b) + g₁(a,∇₂_W b)` (near-def unfold of `metricCovDeriv`);
  (ii) the SECOND covariant-derivative Leibniz on the RHS `∇₂_W K` to reach `∇₂²g₁ = metricCovDeriv·2`;
  (iii) `mfderiv` congruence from the pointwise `connDiff_koszul` (functions agree in a nbhd for smooth
  X,Y,Z, so directional derivatives agree).  This is the genuine new content; ~150–300 lines, delicate.
  The `A(X,Y)`-slot term `(∇₂_Wg₁)(A(X,Y),·)` is the source of the `Λ'²` piece.
- **Brick P2.b — the a=1 component→norm engine** (analogue of `diff_le_covOne_basis`): from the
  differentiated component identity + the quadratic term, bound `√normSqRS(g₂,1,3)(∇₂A) ≤
  C·(√normSq0S(∇₂²g₁) + √normSq0S(∇₂g₁)²)`.  In the g₁-ON basis the quadratic `g₁⁻¹`-contraction
  becomes `Σ_m (∇₂g₁)_{..m}(∇₂g₁)_{m..}` (identity inverse).
- **Brick P2.c — comparability conversion at order 3 and 4** (`sqrt_normSq0S_{three,four}_le_...`
  siblings; the order-4 sibling may need adding next to the order-3 one in `AllTimesBounds`).
- **Brick P2.d — assemble** into `‖covGrad connDiffSection‖_{fibre} ≤ CA(Λ,Λ',Λ'')` via
  `riemannianFiberNormSq_eq_bundle_norm_sq'` + `metricDeriv_eq_covDeriv_norm` + `hJet1/hJet2`.
Then B2 = compose with P1 (§2).

Alternative to P2.a/P2.b (eval/dual route, no component engine): from the lowered identity take `Z = B`
(`B = covDerivConnDiff`), g₁-Cauchy–Schwarz `2 g₁(B,B) = RHS(B) ≤ |RHS-covector|_{g₁*}·|B|_{g₁}`, divide
to get `|B|_{g₁} ≤ ½|RHS-covector|_{g₁*}`, bound the dual-covector norm by `|∇₂²g₁| + |∇₂g₁|·|A|`, then
convert g₁↔g₂ by comparability.  This mirrors P1's own divide-by-`NA` step and avoids the (1,3)
component engine, at the cost of building g₁-dual-norm estimates.  Either route keeps ONE genuine
frontier (the differentiated identity P2.a).

## 4b. P2.a differentiated Koszul — CONFIRMED ROUTE (Session 2 recon)

Home NOT a blocker: the layering is entangled (`LeviCivita/Basic.lean` imports `Curvature.Realized.*`), so
a new leaf in `Geometry/Connection/LeviCivita/` (the planner-ratified `ChristoffelDiffKoszulDeriv.lean`)
CAN import `covDerivConnDiff` (`RicciConnDiffPalatini`, Curvature) + the Tensor infra below — no cycle.

**Superior base — use `koszul_difference`, NOT the eval-scalar `connDiff_koszul`.**
`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean` proves (Tensor layer, importable):
```
koszul_difference cov cov' g hmc htf htf' X Y Z :          -- cov = LC g₁ (metric-compat w/ g₁), cov' = LC g₂
  g.inner x (difference cov cov' x (Y x)(X x)) (Z x)
    = ½·nabla0SFun 2 cov' X (metricTensorField g) x (Y,Z)
      + ½·nabla0SFun 2 cov' Y (metricTensorField g) x (X,Z)
      − ½·nabla0SFun 2 cov' Z (metricTensorField g) x (X,Y)
```
= `connDiff_koszul` in the **`nabla0SFun (metricTensorField)`** currency (= bundled ∇₂g₁), whose derivative
is Tensor-layer-differentiable via **`nabla0SFun_eval_smooth_slots`**
(`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`):
```
(nabla0SFun s cov X α x₀) (V·x₀) = extDerivFun (fun p => α p (V·p)) x₀ (X x₀)
                                     − ∑ₐ α x₀ (update (V·x₀) a (cov (V a) x₀ (X x₀)))
```
(supplies differentiability internally; `α = metricTensorField g₁`, s=2; for the 2nd derivative
`α = totalNabla0S (metricTensorField g₁)` = ∇₂g₁ field, or bundled `metricCovDeriv g₁ g₂ 1`, giving
`metricCovDeriv g₁ g₂ 2` = ∇₂²g₁ = the `Λ''` currency).

**Proof plan (6 steps), differentiating `koszul_difference` along a smooth `W`:**
1. `F(y) := 2·g₁(A(Y)(X)(y),Z(y)) = ∑±nabla0SFun-2 combos(y) =: G(y)` by `koszul_difference` + `funext`
   (smooth sections ⟹ ∀y), so `extDerivFun F x (Wx) = extDerivFun G x (Wx)`.
2. LHS `extDerivFun F`: metric-compat Leibniz on g₁ along ∇₂ (`metricCovDeriv` def / `IsMetricCompatible`)
   → `2·mcd(W,A(Y)(X),Z) + 2·g₁(∇₂_W(A(Y)(X)),Z) + 2·g₁(A(Y)(X),∇₂_W Z)`.
3. RHS `extDerivFun G`: `nabla0SFun_eval_smooth_slots` per term → `nabla0SFun-3` (∇₂²g₁) combos + slot corr.
4. Identify `∇₂_W(A(Y)(X)) = covDerivConnDiff g₂ g₁ W X Y x + A-slot corrections` (`covDerivDiff` def,
   `ConnectionDifferenceCurvature.lean:274`).
5. Cancel step-2/3/4 slot-correction terms via `koszul_difference` again on the `∇₂_W`-slot args.
6. Assemble ⟹ `2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y),Z)`.

**Threading cost (the real work):** re-packaging `∇₂g₁` (eval `nabla0SFun`) as a `Tensor0SField`
(`totalNabla0S`) so the 2nd `nabla0SFun_eval_smooth_slots` applies with `W` leading while X/Y/Z are slots;
per-term leading direction differs (X,Y,Z) so the three combo terms differentiate separately.  Genuine
multi-brick; est. 200–400 lines.

## 5. HOME decision

- **P1 and B2 (jet-currency endpoint): NEW HCG leaf `HCGCompactness/ConnDiffDerivBound.lean`.**  B2's
  honest statement uses `MetricUniformEquivalentOn` + `MetricCovDerivOrderBoundOn` (HCG-layer predicates,
  `AllTimesBounds`), so it cannot live in the Tensor-layer `ConnectionDifferenceNorm.lean` (upstream of
  Curvature — and P1 consumes `covGrad`/`connDiffSection`, Curvature layer).  HCG is downstream of both.
- **P2.a differentiated Koszul identity: canonical home is UPSTREAM** near `connDiff_koszul`
  (`Geometry/Connection/LeviCivita/ChristoffelDifferenceKoszul.lean` sibling) or Curvature — it is a pure
  differential-geometric identity (no comparability, no jets).  For the first landing it may be proved in
  the HCG leaf and later PROMOTED upstream (record the debt; do not leave a reusable identity trapped in
  the consumer leaf per Mathlib-home discipline).

## 6. CONSUMER confirmation

Both consumers take the OUTPUT-VECTOR g₂-norm bound (the §0 target), which B2 = P1 ∘ P2 delivers:
- **T-B `mixedComm_norm_le` via `hA1`** (`UnifCovSumCross.md` §Session 8/9): needs the `∇₂A` output-vector
  bound to close the base-Leibniz norm layer.  The §0 form (`√(g₂(covDerivConnDiff…,·)) ≤ CA·|v||w||u|`)
  is exactly `hA1`'s content.
- **2a-tel composition (b)**: the same `covDerivConnDiff` telescoping sub-frontier; consumes the §0 form.
The `.md`'s Session-9 `covDerivConnDiff` reframing (do not re-materialise a bundled `∇₂A`; reuse the eval
form) is respected — P1/P2 are stated on the eval `covDerivConnDiff` and the existing bundled
`covGrad connDiffSection`, no parallel `tensorRSCovariantDerivative 1 2` field is built.

## 7. Session log

- 2026-07-25 (B2 session 6 — P2 ROUTE PIVOT + currency/comparability helpers LANDED; STAND-DOWN pause):
  **Chose the dual/eval route (recon §4 alternative), NOT the component P2.b/c/d.**  The dual route pairs
  the LOWERED identity `connDiff_koszul_deriv` against the output vector `B` itself (`Z x = B`), bounds
  each RHS term by the EXISTING multilinear CS `abs_apply_le_sqrt_normSq0S` in the `metricCovDeriv 2/1`
  currency, re-expands `|A|` via the a=0 atoms `connDiffVec_norm_le`+`lcDiff_norm_le`, divides by `|B|`,
  then converts `g₁↔g₂` by comparability — **producing B3's `hA1` (eval form) DIRECTLY, bypassing the
  fibre-norm P2.d and the compose-with-P1 step, and avoiding any new (1,3)-component→l² engine or
  quadratic-l² lemma.**  P1 (`covDerivConnDiff_fibreNorm_le`) is thus an unused-but-kept alternative for
  this consumer.  Pinned **`CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`**.  LANDED green (whole-file `lake build`
  EXIT=0, 9451 jobs) in `ConnDiffDerivBound.lean`: `field_eq_mcd1` + `nabla3_eq_mcd2` (currency bridges
  `field = metricCovDeriv g₁ g₂ 1` and `nabla0SFun 3 W field = metricCovDeriv g₁ g₂ 2`) and
  `sqrt_normSq0S_comp` (general-`s` comparability — subsumes order-3 AND order-4, so **no order-4 sibling
  is needed in AllTimesBounds; that file is UNTOUCHED**).  REMAINING = the dual core + endpoint (two
  lemmas, all ingredients present, no new frontier) — see `ConnDiffDerivBound.md` §"EXACT NEXT STEPS".
  P2.b/c/d as originally scoped are SUPERSEDED by this route.
- 2026-07-25 (B3 consumer LANDED, in `UnifCovSumCross.lean`): the T-B consumer of `hA1`,
  **`covStepDiff_norm_le` + `covStepDiff_jet_le`**, is PROVED sorry-free + axiom-clean (build EXIT=0),
  taking the §0 target as the **abstract hypothesis `hA1`** in the committed **ext-form**
  (`√(g₂(covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x,·)) ≤ CA·|v||w||u|`, = `covDerivConnDiff_
  fibreNorm_le`'s (P1) shape with the fibre norm `‖covGrad connDiffSection‖` folded into `CA`).  So
  **the ONLY thing left for this consumer is B2 = P1 ∘ P2**: apply `covDerivConnDiff_fibreNorm_le`
  (P1, committed here) then bound `‖covGrad g₂ 1 2 (connDiffSection g₁ g₂)‖ ≤ CA(Λ,Λ',Λ'')` (P2, §4,
  still OPEN = the differentiated-Koszul telescoping wall) — one `le_trans` per §2 discharges `hA1`.
  Confirms the §6 consumer shape is exactly what B2 delivers; no `covDerivConnDiff` tensoriality lemma
  is required on either side (B3 chose its frame sections = `mk(smoothExtensionTangent …)`).
- 2026-07-25 (B2 session 5): **P2.a DONE.**  `connDiff_koszul_deriv` — the full differentiated Koszul
  identity `2 g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo = nabla0SFun 3 W field] − 2 (∇₂_W g₁)(A(X,Y),Z)`
  — LANDED in `ChristoffelDiffKoszulDeriv.lean`, sorry-free, authoritative `lake build` ✔ (3666/3666), axioms
  clean `[propext, Classical.choice, Quot.sound]`.  The recon's feared α slot-symmetry step was NOT needed:
  with the correct Koszul third-term slot order the 9 LHS + 9 RHS slot corrections cancel term-for-term by
  rearrangement (`linarith`).  The remaining a=1 frontier is **P2.b** (component→norm engine, analogue of
  `diff_le_covOne_basis`) + P2.c/d (order-4 comparability + assemble into `‖covGrad connDiffSection‖ ≤ CA`);
  see `ChristoffelDiffKoszulDeriv.md` §LANDED session 5 for the route + lessons.  With P1 already landed
  (`ConnDiffDerivBound.lean`), B2 = P1 ∘ (P2.a ∘ P2.b/c/d); one `le_trans` then discharges `hA1` for B3.
- 2026-07-25 (B2 session 4): P2.a assembly RECON complete; **clean stop at the green boundary (no new
  Lean)**.  Located all assembly tools (`diffSec_contMDiff`+`LeviCivita_isContMDiff` instance,
  `extDerivFun_add/_sub'`, `contMDiffAt_section_apply_gen` for the 3 combo `MDifferentiableAt`,
  `metricTensorField_apply`, `covDerivDiff` unfold) and recorded the EXECUTABLE RECIPE in
  `ChristoffelDiffKoszulDeriv.md`.  Verdict: the assembly is NOT pure algebra (sum-form `extDerivFun`
  linearity needs the 3 combo `MDifferentiableAt` + a delicate many-term cancellation, ~150–250 lines);
  stopped rather than risk a red spill in deep (438k) context per planner guidance.  `.lean` = committed
  green (f1e4b8e38).  Fresh successor executes the recipe.
- 2026-07-25 (B2 session 3): **BOTH differentiation engines LANDED** (P2.a RHS + LHS).  In
  `ChristoffelDiffKoszulDeriv.lean`, verified/axiom-clean: `metricField_totalReg` (∇₂g₁-field regularity),
  `nablaMetric_combo_extDeriv` (RHS: `extDerivFun` of a combo term = `∇₂²g₁` + corrections, V-parameterized
  so it covers all 3 combo terms), `metric_leibniz_extDeriv` (LHS: `extDerivFun` of the g₁-contraction =
  `∇₂g₁` + Leibniz corrections).  Both = one `nabla0SFun_eval_smooth_slots` + slot-0 bridge
  `totalNabla0SFun_apply_section` + `abel`.  Milestone (slot-0 + one combo) EXCEEDED.  Remaining P2.a =
  the assembly: differentiate `connDiff_koszul_nabla` (funext ⟹ `extDerivFun LHS = extDerivFun RHS`), apply
  both engines, package `diffSec` as a `ContMDiffSection`, unfold `covDerivDiff` to surface
  `covDerivConnDiff`, cancel slot corrections via `connDiff_koszul_nabla`.  Est. ~100–200 lines algebra.
- 2026-07-25 (B2 session 2): P2.a route CONFIRMED (§4b) + **a=0 differentiation base LANDED**.  Found the
  Tensor-layer `koszul_difference` is the superior differentiation base (`nabla0SFun (metricTensorField)`
  currency, differentiable via `nabla0SFun_eval_smooth_slots`); confirmed the ratified LeviCivita-dir home
  is FEASIBLE (entangled layering — imports `covDerivConnDiff`, no cycle); resolved the
  `LeviCivita = leviCivitaConnectionOfMetric` (`rfl`) currency bridge.  **`connDiff_koszul_nabla`** (a=0
  base) LANDED in the new leaf `Geometry/Connection/LeviCivita/ChristoffelDiffKoszulDeriv.lean`, verified
  by authoritative `lake build`, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`.  Full
  differentiated identity = steps 2–6 (§4b): differentiate via `nabla0SFun_eval_smooth_slots` (the engine
  also gives the LHS metric-compat Leibniz when applied to `metricTensorField g₁`), with the `totalNabla0S`
  RHS-field packaging the remaining threading cost.  Genuine multi-session; verified-boundary stop.  See
  `ChristoffelDiffKoszulDeriv.md`.
- 2026-07-25 (B2 session 1): recon COMPLETE + **P1 LANDED**.  Established the §1 gate analysis (δ<1 =
  Neumann inverse control, unusable at Λ≥2), the §2 factorization **B2 = P1 ∘ P2**, the §3 a0-exists
  finding (`lcDiff_norm_le`), the §4 P2 brick sequence, and the §5 home decision.  **`covDerivConnDiff_
  fibreNorm_le`** (P1, ungated fibre→vector reduction) LANDED in the new leaf `ConnDiffDerivBound.lean`,
  verified by authoritative `lake build`, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`.
  The SINGLE remaining B2 frontier is **P2** = `‖covGrad g₂ 1 2 (connDiffSection g₁ g₂)‖_{fibre} ≤
  CA(Λ,Λ',Λ'')` (a=1 analogue of `lcDiff_norm_le`; crux = the §4 P2.a differentiated Koszul identity;
  genuine multi-session).  Both consumers close by composing P1 with any P2 supply (one `le_trans`).  See
  `ConnDiffDerivBound.md` for the Lean-side status and lessons.
