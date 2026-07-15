# `StarRouting` — Brick 4 P2 toolkit (Session γ, 2026-06-12, Opus)

Scope: the generic `(k,q)`-σ routing for the CURVACT shape (dite-val pattern, per the PLANNER
REVIEW directive) + val-eval lemmas + the end-to-end identity `base (k+1)(k+1) 0 0 σ_q comps =
update-form q-term`, both `q=0` and `q≥1`.

## ✅ GREEN so far (q ≥ 1 branch)
- **`sigmaCurvPos k q hq : Fin (k+9) ≃ Fin (k+9)`** — the `q≥1` routing.  Built via
  `Equiv.ofBijective (tfPos k q) (injective→bijective)`.  **The dite-val recipe that works:**
  - `tfPos` = explicit val-dite (`if a.val = 0 then ⟨0,_⟩ else …`); use **dite (`if h : …`)** for
    the `≤ k+4` branch so the bound `4+a.val < k+9` is in scope; `by have := q.isLt; omega` for the
    `q`-dependent bounds (omega does NOT auto-add `q.isLt` here).
  - bijectivity = `Fintype.bijective_iff_injective_and_card`; card goal closes by
    `simp only [Fintype.card_fin]` (the two rank expressions are defeq — do NOT add `; omega`,
    it errors "No goals").
  - injectivity: `simp only [tfPos] at hab; split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega`.
    **KEY TRAP**: omega treats `(⟨c,_⟩ : Fin n).val` as an OPAQUE ATOM — after `split_ifs`, `hab`
    is `⟨c_a,_⟩ = ⟨c_b,_⟩`; you MUST `simp only [Fin.mk.injEq]` to extract `c_a = c_b` before omega.
- **`sigmaCurvPos_cast_val`** / **`sigmaCurvPos_nat_val`** — val-form eval of `σ_q` on the
  `∇^{k+1}Rm` block (`castAdd`, `0↦0,q↦2,else↦4+p`) and `Rm04` block (`natAdd`,
  `k+5↦1,k+6↦4,k+7↦4+q,k+8↦3`).  Proof: `simp only [sigmaCurvPos, Equiv.ofBijective_apply, tfPos,
  Fin.val_castAdd/Fin.val_natAdd]; split_ifs <;> first | rfl | omega`.  (`(⟨c,_⟩).val = c` is `rfl`;
  contradiction branches close by omega with `p.isLt`/`q.isLt`.)

## Routing tables (val 0..k+8; W = [bᵢ,bᵢ,bⱼ,bⱼ,m₀,…,m_{k+4}], j=bp)
- `q≥1`: ∇-block `0↦0, q↦2, (1≤v≤k+4,≠q)↦4+v`; Rm04-block `k+5↦1, k+6↦4, k+7↦4+q, k+8↦3`. (bijection ✓)
- `q=0`: ∇-block `0↦2, (1≤v≤k+4)↦4+v`; Rm04-block `k+5↦0, k+6↦4, k+7↦1, k+8↦3`. (factor2 = Rm04(bᵢ,X,bᵢ,bp): bᵢ twice; bijection ✓)

## ✅ DONE (GREEN, 0 sorry, symbolic k, BOTH branches) — the done-criterion is met

The full toolkit + end-to-end identity for the CURVACT q-term:
- **`sigmaCurvPos` / `sigmaCurv0`** (q≥1 / q=0 σ-Equivs, dite-val + `Equiv.ofBijective`).
- **`sigmaCurvPos_cast_val` / `_nat_val`** and **`sigmaCurv0_cast_val` / `_nat_val`** (val-eval).
- **`wRoute_val`** (the `W = [bᵢ,bᵢ,bⱼ,bⱼ,m…]` evaluation bridge).
- **`curvactStarPos` / `curvactStar0`**:
  `base (k+1)(k+1) 0 0 σ_q comps = ∑ⱼ∑ᵢ ∇^{k+1}Rm(update (cons (basis i) tail') q (basis j)) ·
  Rm04(vec4 (basis i)(basis m₀) (q-slot) (basis j))` (q≥1: q-slot = `(cons (basis i) tail') q`;
  q=0: q-slot = `basis i`, with `update … 0`).

### The proof recipe that worked (reuse for Session δ's `∂ₜΓ∗∇ᵏRm`)
`rw [starBaseProd_eq]` + per-`(j,i)` two funext (`hL` ∇-input, `hR` Rm04-input):
`rw [wRoute_val, Function.update_apply / vec4]`; `rcases eq_or_ne p.val …`; per case a
`hcv` (`rw [eval_lemma]; split_ifs <;> omega`); resolve the if-chains with `if_pos hcv` /
`if_neg (by rw [hcv]; omega)`; the `m`-index match by `congr 2; simp only [hcv, Nat.add_sub_cancel_left, Fin.eta]`.

### Lean traps solved (apply, don't rediscover)
- **omega treats `(0:Fin (4+(k+1))).val` and `(⟨c,_⟩).val` as OPAQUE atoms** (the `+1` is nested,
  so `Fin.val_zero`/simp won't fire).  FIX: pass the val-hypothesis DIRECTLY —
  `Fin.ne_of_val_ne h0` (for `p ≠ 0`, h0 : `p.val ≠ 0`), `Fin.ext h0` (for `p = 0`) — Lean's defeq
  bridges `(0:Fin).val ≡ 0`.  Use `(by omega)` ONLY for pure-nat goals (`p ≠ q` with no literal).
- **Dependent-motive `Fin.cons`**: `Fin.cons (basis i) f q` infers a dependent motive `?m q` →
  type mismatch.  FIX: `@Fin.cons (4+k) (fun _ => TangentSpace I x) (basis i) f`.
- **`Fintype.bijective_iff_injective_and_card`** for the Equiv; card closes by
  `simp only [Fintype.card_fin]` (NO `; omega`); inj by `split_ifs at hab <;>
  (try simp only [Fin.mk.injEq] at hab) <;> omega`.
- Focused verification passed for `StarRouting.lean` after adding a file-local
  `linter.unnecessarySeqFocus` setting.  The `<;>` proof shape is intentionally kept in the
  `split_ifs` branches because replacing it by `;` leaves open goals in the first `curvactStarPos`
  funext block.

### For Session δ (P2 completion)
CURVACT = `−∑_{q : Fin (4+(k+1))} (q-term)`.  Use `curvactStar0` (q=0) + `curvactStarPos` (q≥1)
under a `Fin.cases`/`q.val=0` split, sum via `starSum2_sum`, then the `∑ᵢⱼδᵢⱼ→∑ᵢ` δ-collapse.
The `σ`-Equivs need `StarSum2`'s olean current (rebuild StarSum2 first — it was stale this session).

## 2026-06-13 Codex pass: SLOTDIFF routes added

Added and verified the generic SLOTDIFF routing toolkit:
- `(a,b)=(1,k)`: `tfDiffA`, `sigmaDiffA`, `sigmaDiffA_cast_val`,
  `sigmaDiffA_nat_val`, and the end-to-end base identity `slotdiffStarA`.
- `(a,b)=(0,k+1)`: `tfDiffB`, `sigmaDiffB`, `sigmaDiffB_cast_val`,
  `sigmaDiffB_nat_val`, and the end-to-end base identity `slotdiffStarB`.

The route layout is still the same `W = [bᵢ,bᵢ,bₑ,bₑ,m…]` double-trace convention:
- `slotdiffStarA` evaluates the `∇Rm04 * ∇ᵏRm` sharp-expanded term with the updated frozen slot.
- `slotdiffStarB` evaluates the `Rm04 * ∇^{k+1}Rm` sharp-expanded term with the derivative slot
  consed at the front.

Verification status: focused verification passed, and the `StarRouting` module built.  No existing
declarations in `StarRouting.lean` were changed; the new declarations were appended.

## 2026-06-13 Planner review: Ricci-trace gamma routes accepted

The gamma-correction routing bank described in `TimeRecursion.md` is now present in
`StarRouting.lean`:

- `tfRic1/2/3` and `sigmaRic1/2/3`;
- `sigmaRic1/2/3_cast_val` and `sigmaRic1/2/3_nat_val`;
- `slotRic1/2/3`.

These are the `(1,4)` Ricci-trace variants of the `(a,b) = (1,k)` route. The `nabla^k Rm`
factor uses the same update-shape routing as `slotdiffStarA`; only the `nabla^1 Rm` input routing
changes to match the three `hchrId` terms consumed by `gammaStepStar`.

Planner source inspection accepted the route/sign alignment:

- route 1 evaluates `nabla^1 Rm(m0, i, m_{q+1}, e, i)`;
- route 2 evaluates `nabla^1 Rm(m_{q+1}, i, m0, e, i)`;
- route 3 evaluates `nabla^1 Rm(e, i, m0, m_{q+1}, i)`;
- `gammaStepStar` combines them as `-slotRic1 - slotRic2 + slotRic3`.

No further StarRouting work is currently planned for P3 unless the final `residualStarSumLF` succ
assembly exposes a new component-order mismatch.

## 2026-06-14 — component-eval transparency sweep (item 4): 7 → 0 blocks

Removed the `set_option backward.isDefEq.respectTransparency false in` from **all 7** theorems
(`curvactStarPos`, `curvactStar0`, `slotdiffStarA`, `slotdiffStarB`, `slotRic1`, `slotRic2`, `slotRic3`).
All were **STALE** — the `set_option maxHeartbeats 1000000 in` was kept; only the transparency line was
unnecessary. These are pure pointwise star-base/component evaluations (`starBaseProd_eq` + `wRoute_val` +
`Function.update`/`Fin.cons` slot routing + `split_ifs`/`omega`), with no `ContMDiffAt`/`letI bundle_topology`/
section ext, so the transparency option was not load-bearing. Full-file focused check **green** (465s — heavy
but passes; the 7 `maxHeartbeats 1000000` proofs dominate). Statement-preserving; no consumer affected.
See `Tensor/RSTensor/ComponentEvalApiPlan.md` (7th pass).
