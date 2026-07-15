# Lemma45Engine.lean — the Lemma 4.5 hOne engine over the Claim-1 machinery

## ✅ F3 PROVEN (2026-06-11): `lemma45_F3`

**The book-facing MSM135 Lemma 4.5 (`lbl370`) endpoint is a verified theorem.**
On a local-frame domain `u`, for the Levi-Civita frame-Christoffels of `g`/`gRef`,
with `hGinv` (`|g⁻¹-array| ≤ C0`) and `hgK` (`|∇_H^j g-comps| ≤ ε`, `1 ≤ j ≤ p`):
`∃ C ≥ 0, ∀ x ∈ u, ∀ 0 < ρ ≤ p, |∇_G^ρ T| ≤ |∇_H^ρ T| + ε·C·Σ_{j<ρ}|∇_H^j T|`
(component `compL2` norms in the frame).  Chain: `hkoszul_of_leviCivita` →
`claim1_eps_koszul` (per-order ε-linear difference-tower bounds, totalized by
`choose`) → `lemma45_component_bdd` → `lemma45DoubleBdd`
(Lemma45CovariantAbstract.lean — the bounded-envelope variant: `hOne` only on
`i + k < P`, matching the book's finitely-many-orders hypotheses) → the endpoint.
`C = lemma45Const B p r₀` with `B` the chosen `claim1_eps` constants.
Remaining presentational upgrades (NOT gating F4): intrinsic-`normSq0S` statement
form via `iterCovComp_eq_iterCov` + the norm lift at a `gRef`-ON frame; smoothness
hypotheses (`hchrG/hchrH/hgsm`) dischargeable from existing producers.

Consumes `AkMFold.lean` (the parallel `ric_bound` track's Claim-1 engine, sorry-free)
WITHOUT modifying it, and discharges the `hOne` interface of `lemma45Double`
(`Lemma45CovariantAbstract.lean`) — the F3 (MSM135 Lemma 4.5, `lbl370`) one-step
estimate that was deliberately left as an interface on 2026-06-09.

## Contents (all sorry-free, verified 2026-06-10/11)

1. **`claim1_eps`** — the ε-homogeneous sibling of `claim1_abstract`:
   `|∇^j g| ≤ ε (1≤j≤m+1)` + Koszul relation + `|Ginv| ≤ C0` ⟹ `|∇_U^m A| ≤ C·ε`
   (same strong induction; the conclusion keeps the ε factor instead of absorbing
   into `(1+|∇^{m+1}g|)` — `claim1_abstract`'s shape loses the ε-homogeneity that
   `hOne`'s correction term needs).  `C = max C0 0·(max KR 0 + Σ binom·Cc)` explicit.
2. **The connection-change one-step**: `chrDiffField` (the difference Christoffel as a
   rank-(2+1) field, upper slot last), `chrCorrField` (per-slot correction),
   `covDerivStepComp_chr_sub` (the `ext` cancels — pure component identity),
   `iterCov_one_chr_change` (field level: `∇_G X = ∇_H X − Σ_s D∗_s X`).
3. **Slot plumbing**: `slotRotEquiv` (move slot `s` last, via `finSuccEquiv'`),
   `corrSlotMap`/`corrSlotEquiv` (the `Fin (2+r') ≃ Fin (r'+2)` threading the per-slot
   correction into `contrTail` form; `Equiv.ofBijective` + injectivity case-bash),
   **`chrCorrField_eq_contrTail`** (the bridge to `P(m)`'s shape).
4. **`compL2_iterCov_chrCorr_le`** — the per-slot tower bound
   `|∇_H^k(D∗_s X)| ≤ Σ_c binom(k,c)·|∇_U^c D|·|∇_H^{k-c} X|`
   (= `P(m)` through the slot reindex, both reindexes killed by
   `compL2_iterCovComp_compReindex`).
5. Linearity/plumbing: `iterCovComp_sub`, `iterCovComp_zero_field`,
   `iterCovComp_finsetSum`, `compL2_finsetSum_le`, `contMDiffOn_chrCorrField`.
6. **`mixed_oneStep_le`** — THE hOne engine:
   `|∇_H^k(∇_G X)| ≤ |∇_H^{k+1}X| + ε·oneStepConst B k r·Σ_{j≤k}|∇_H^j X|`
   from `hDbound : |∇_{H,U}^c(Γ_G−Γ_H)| ≤ B c·ε`.  The slot sum gives the rank
   factor `r` of `oneStepConst B k r = r·Σ_a binom(k,a)·B a` — the constant's shape
   matches the book exactly.
7. **`lemma45_component`** / **`lemma45_component₀`** — MSM135 Lemma 4.5 in
   component-tower form: `lemma45Double` instantiated at
   `W i k := |∇_H^k ∇_G^i T|`, hOne discharged by (6).  The `X_{i+1} = ∇_G X_i`
   identification is definitional (`iterCovComp_succ`).

## Lean lessons

- The rank-dependent summand `fun j => compL2 (iterCovComp … X j x)` defeats
  higher-order unification in `Finset.single_le_sum` (each summand has a different
  implicit rank) — pass `(f := …)` explicitly.
- `0 + ρ` is not defeq to `ρ` (variable ρ): the `i = 0` corollary needs
  `rw [zero_add]`; `r₀ + 0` and `iterCovComp … 0 = id` are defeq (Nat right-recursion).
- Beta-forms in `Fin.snoc` evaluation haves must be written REDUCED (the goal comes
  from instantiated lemma statements, which `instantiateMVars` beta-reduces).
- `contrTail`'s contraction is LAST-slot against LAST-slot; the upper-tower factor
  (`P(m)`'s `A`) must be the connection-difference (its upper slot is the contracted
  one) — the order is forced.

## What consumes this next

- **F3 book form (W4)**: convert `compL2`-towers to `√normSq0S`/`normSqRS` via
  `iterCovComp_eq_iterCov` ((0,s)-side, exists); discharge `hDbound` from
  `claim1_eps` + the geometric Koszul.  **SCOPE CORRECTION (2026-06-11): the
  (1,2)-upper normSqRS bridge is NOT needed** — upper towers appear only in
  internal estimates (compL2 form); both endpoints' statements are (0,s).
- **W4-P1 DONE (2026-06-11, green): `Tensor/RSTensor/NablaOnTensors/
  KoszulDifference.lean`** — the intrinsic Koszul-difference formula:
  `difference_symm_at` (torsion-free difference is symmetric; Lie brackets cancel),
  `nabla_metric_two_term` (`∇'g(X;Y,Z) = g(D(Y)(X),Z) + g(Y,D(Z)(X))`, from
  `nabla0SFun_sub_cov_two` + `nabla_metric_zero`), **`koszul_difference`**
  (`g(D(Y)(X),Z) = ½[∇'g(X;Y,Z)+∇'g(Y;X,Z)−∇'g(Z;X,Y)]`).  All hypotheses
  pointwise (`IsTorsionFreeAt`, `IsMetricCompatible_gen`); statement tensorial in
  the three sections (values only).
- **W4-P2 DONE (2026-06-11, green): `hkoszul_of_leviCivita`** (this file) — in ANY
  local frame on `u`, the `g`-lowered connection-difference array
  `contrTail (chrDiffField chrG chrH y) (frameComp0S (metricTensorField g) frame y)`
  equals the `(½, ½, −½)`-Koszul combination of the level-1 `gRef`-tower of the
  `g`-components, with `P₁ = Equiv.refl`, `P₂ = Equiv.swap 0 1`,
  `P₃ = (finRotate 3).symm` — EXACTLY `claim1`'s `hkoszul` shape.  Proof: the
  contrTail collapses to `g(f_e, D(f_b)(f_a))` (coeff-linearity + `difference_apply`
  + the frame expansion), `koszul_difference` at section-extensions of the frame
  values, and the towers convert to `nabla0SFun` via `iterCovComp_eq_iterCov` +
  `covStep_apply` + `totalNabla0SFun_apply_section`.
  Lean gotchas: `mdifferentiableAt`'s side condition here is `n ≠ 0` (pass `by simp`,
  not `le_rfl`); permutation applications must be REDUCED by explicit
  `show … from by decide` rewrites before `linarith` (defeq atoms are not linarith
  atoms); `Fin.eq_one_of_ne_zero` for the `Fin 2` if-bridge (omega can't do Fin).
- **Remaining glue for `hDbound`** (next, ~40 lines): the `claim1_eps`-from-`hkoszul`
  wrapper — derive `claim1_eps`'s `hrelB` from `hkoszul_of_leviCivita` exactly as
  the parallel track's `claim1` derives it (tower linearity `iterCovComp_smul`/`_add`
  + `compL2_iterCovComp_compReindex` + `compL2_iterCovComp_shift` +
  `compL2_smul`/`_add_le`; mirror AkMFold's claim1 proof block).  Then `hK` from the
  approximate-isometry ε-bounds ⟹ `hDbound` ⟹ F3 book form.  The SAME producer
  instantiates ric_bound's `claim1` `hkoszul` directly (Phase R).
- **W4-P2 original blueprint** (now executed): frame componentization → claim1's `hkoszul` shape.  Blueprint:
  (1) apply `koszul_difference` at section-extensions of frame-vector values
  (`ContMDiffSection.exists_eq_at_gen`, the `nabla_metric_zero`-proof pattern —
  the statement is tensorial so extensions suffice);
  (2) `chrDiffField chrG chrH` (both `christoffelSymbolInFrame` of the two LC
  connections) = `hframe.coeff` of `CovariantDerivative.difference` (linearity of
  `coeff` + `difference_apply`); the contrTail-LHS collapses by the frame
  expansion `Σ_c coeff_c(v)·frame c = v` (IsLocalFrameOn API);
  (3) the RHS ∇'g-terms = level-1 tower values via `iterCovComp_eq_iterCov` (a=1)
  + `covStep = totalNabla0SFun` (rfl, MetricCovDerivLinear:204) + the
  total↔directional slot bridge (`totalNabla0SFun_apply_section`-style — direction
  in slot 0);
  (4) the three slot-permutations P₁,P₂,P₃ (id, swap 0 1, the cycle 0↦2,1↦0,2↦1)
  with c = (½,½,−½), KR = 3/2.
  Then: instantiate `claim1_eps` with A := chrDiffField, g := frameComp0S of the
  moving metric ⟹ `hDbound` ⟹ F3 book form; same hkoszul feeds ric_bound's
  `claim1` instantiation (Phase R).
- **ric_bound Phase R**: Step-4 telescoping needs `iterCov_one_chr_change` (built
  here, general chrG/chrH) — the same one-step identity.

## 2026-07-09: explicit scaled constants

Added and verified the scaled chain `claim1MulConst` / `claim1_eps_mul_bound` /
`claim1_koszul_bound` / `lemma45_F3_bound`.  Component hypotheses may now be
`L * eps` with only the original `eps <= 1`; `L` is absorbed into a pure numeric
constant.  The existential APIs remain compatibility wrappers.  This makes the
F3 constant visibly independent of manifold, metrics, tensor, frame, and
epsilon, which is required by the constant-first F4 endpoint.
