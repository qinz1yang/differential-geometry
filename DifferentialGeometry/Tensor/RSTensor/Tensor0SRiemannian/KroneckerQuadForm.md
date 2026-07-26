# KroneckerQuadForm.lean — brick 2 of `ric_bound` (the non-diagonal norm bound)

Pure linear algebra feeding `coordInner0S` (Comparison.lean) → `aN_intrinsic_point`
(RicBoundAssembly) → `ric_bound`.  Goal: convert an intrinsic `gRef`-norm into the
raw frame-component `ℓ²` when the frame Gram's inverse-eigenvalues are bounded below.

## Verified (2026-06-10, sorry-free, focus-checked)

- **`sum_posSemidef_mul_posSemidef_nonneg`** — PSD-pairing: `0 ≤ ∑ i j, M i j * G i j`
  for real PSD `M, G`.  Proof: spectral decomposition of `M`
  (`M i j = ∑ k λ_k U_ik U_jk`), reorder the triple sum, each term
  `λ_k · (U_·kᵀ G U_·k) ≥ 0`.  Imports: `Mathlib.Analysis.Matrix.Spectrum/.PosDef`
  (the `LinearAlgebra.Matrix.Spectrum` olean is NOT built in this checkout — use the
  `Analysis.Matrix.*` ones, as MaximumPrinciple.lean does).
- (sibling, in Comparison.lean) **`coordInner0S_identity_le_pow_diagonal`** — the
  diagonal case `coordInner0S Id ≤ (1/m)^s coordInner0S (diagInv μ)` for `μ ≥ m`.

## ✅ CAPSTONE DONE (2026-06-11): `quadForm_id_le_pow` verified sorry-free

Built via GPT Pro consult (induction design below was sent; answer integrated with
local hardening) + 3 fix iterations.  Final structure: `sum_fin_succ_fun`/`_₂`
(head-tail reindex via `Fin.consEquiv` + `Equiv.sum_comp` + `rw [Fintype.sum_prod_type]`
— NOT `Finset.sum_bij`, whose goal order is fragile), `prod_fin_succ_Q` (needs
`(Fin.cons k I : Fin (s+1) → Idx)` ascriptions — bare `Fin.cons k I a` fails to
elaborate), `diag_pairing`, `matrix_posSemidef_of_quad_nonneg`
(`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` + `Matrix.IsHermitian.ext`),
`shifted_posSemidef` (`Q - α·Id` PSD), `kron_kernel_posSemidef_of_ih`,
`sandwich_entry` (entries of `Vᴴ*P*V`; over ℝ the first factor-split is DEFEQ —
`congr 1` closes it, do NOT add rw steps after), Gram-PSD via
`PosSemidef.conjTranspose_mul_mul_same` (the matrix-sandwich idiom — far more
robust than proving bilinearity `∑∑ aₖaₗB(vₖ,vₗ) = B(Σav,Σav)` directly).
GOTCHAS: `Fintype.sum_prod_type`/`Finset.sum_sub_distrib` have explicit function
args — use `rw`, not term-mode `exact`; `Mathlib.LinearAlgebra.Matrix.Spectrum`
olean is NOT built in this checkout — import `Mathlib.Analysis.Matrix.Spectrum`
(as MaximumPrinciple.lean does); `omit ... in` must precede the docstring.

## ✅ ADAPTERS DONE (Comparison.lean, 2026-06-11, sorry-free)

- `coordInner0S_identity_le_pow_quad`: `coordInner0S Id A A ≤ C^s · coordInner0S Q A A`
  for symmetric `Q` with quad form ≥ (1/C)·Id (one `mul_assoc` reassociation —
  `coordInner0S` is left-assoc `(∏)*cA*cB`).
- **`sum_comp_sq_le_pow_normSq0S`** — THE pointwise brick-2 inequality:
  `∑_slots comp² ≤ C^s · normSq0S g x s A` given `MetricInverseInBasis_gen g x basis Q`
  + `Q` symmetric + quad-form lower bound.  Via `normSq0S_eq_coord`.

## ✅ hQlb PRODUCER DONE (2026-06-11): `quad_lb_of_near_id` sorry-free

`|Q i j − δᵢⱼ| ≤ ε` entrywise + `card·ε ≤ 1/2` ⟹ quad form of `Q` ≥ `(1/2)·Id`.
ELEMENTARY (identity-split + `Finset.abs_sum_le_sum_abs` + `Finset.sum_mul_sum` +
Chebyshev `sq_sum_le_card_mul_sum_sq` — needs `import Mathlib.Algebra.Order.Chebyshev`,
root-level name).  This REPLACES the planned eigenvalue route entirely: near the
keystone gRef-ON point the inverse Gram is entrywise near Id by continuity, so
C := 2 suffices in `quadForm_id_le_pow`/`sum_comp_sq_le_pow_normSq0S`.

## REMAINING to consume brick 2 (not this file)

1. ~~hQlb producer~~ DONE (`quad_lb_of_near_id`; consumer must also check `Q` symm —
   inverse Gram of symmetric Gram, available from the gramE machinery).
2. Entrywise-continuity producer (geometry layer): for the keystone frame, an open
   `u' ∋ x` on which the inverse-Gram entries `Q z i j` are within `ε := 1/(2n)` of
   `δᵢⱼ` (the entries are continuous on the trivialization domain — gramE entries
   smooth, inverse via det/adjugate or `ginvCompField` regularity — and equal `δ` at
   `x` by ON-ness), plus `MetricInverseInBasis_gen gRef z basis(z) (Q z)` per z.
3. Tower application: `compL2(iterCovComp …) ≤ √(CG^{2+j})·√normSq0S(iterCov …)` via
   `iterCovComp_eq_iterCov` + `sum_comp_sq_le_pow_normSq0S` (+ component0S ↔
   tensor0SComponent bridge).
4. Shi moving→fixed (`normSq0S_le_of_metric_equiv`), Ricci-component smoothness,
   finite-subcover uniformization, RicBound.lean assembly.

## ORIGINAL design notes — `quadForm_id_le_pow` (the induction)

`(1/C)^s · ∑_I c_I² ≤ ∑_{I,J} (∏_a Q(I_a,J_a)) c_I c_J` for symmetric `Q ≥ (1/C)Id`,
any `c : (Fin s→Idx)→ℝ`.  Induction on `s`:
- base `s=0`: `Fin 0→Idx` is `Unique`; `∏` over `Fin 0` = 1; both sides = `c(∅)²`.
- step: peel index 0 via `Fin (s+1)→Idx ≃ Idx × (Fin s→Idx)` (`Fin.cons`/`Fin.tail`);
  `∏_{Fin(s+1)} = Q(k,l)·∏_{Fin s}` (`Fin.prod_univ_succ`).  Set `v_k := c(cons k ·)`,
  `B_s(u,w) := ∑ (∏Q) u w` (the `s`-form).  Then RHS = `∑_{k,l} Q(k,l) B_s(v_k,v_l)`.
  - `M := Q - (1/C)Id` is PSD (from the quadratic-form lower bound + `hQsymm`).
  - `Gmat k l := B_s(v_k,v_l)` is PSD: `∑_{k,l} a_k a_l B_s(v_k,v_l) = B_s(Σ a v, Σ a v)
    ≥ 0` by IH (bilinearity of `B_s` + IH gives `B_s(w,w) ≥ (1/C)^s Σw² ≥ 0`).
  - `sum_posSemidef_mul_posSemidef_nonneg M Gmat`: `∑ M_kl Gmat_kl ≥ 0`
    ⟹ `∑ Q_kl B_s(v_k,v_l) ≥ (1/C) ∑_k B_s(v_k,v_k) ≥ (1/C)·(1/C)^s ∑ c² = (1/C)^{s+1}∑c²`.

Then apply to `coordInner0S` (Comparison.lean): `coordInner0S` unfolds to exactly the
`∑_{I,J}(∏Q) c c` form with `c = tensor0SComponent`, giving the non-diagonal
`coordInner0S_identity_le_pow` that brick 2 consumes.

ASSESSMENT: ~100 lines, fiddly `Fin.cons` reindex + the Gram-PSD-from-IH bilinearity
expansion + the `M`-PSD bridge.  Self-contained pure linear algebra → ideal Pro-consult
candidate (full design above), or a multi-iteration solo grind (Comparison/this-file
checks are ~30–50s each).
