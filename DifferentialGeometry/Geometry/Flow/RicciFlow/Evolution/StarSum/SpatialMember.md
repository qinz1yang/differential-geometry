# `SpatialMember` — Brick 4 Phase P2 (spatial commutator is a star sum)

## 2026-07-22 fixed global commutator field

`commStarField S t k` is now selected before any point, basis, or local frame.
`commStarField_cost` gives its exact certificate and `commStarField_spec`
realizes the spatial commutator in every supplied orthonormal basis.  The old
`spatialCommStarSum` remains a compatibility wrapper.  Focused verification is
GREEN and the exact target is current (`3784/3784`); this is the fixed witness
consumed by `resStarNext`.

## 2026-07-14 exact spatial-commutator cost

Added `commStarCost` and strengthened `spatialCommStarSum` to return a
`StarSum2Cost` certificate with that cost. The coefficient is uniform in the
spacetime point and frame. Focused verification and the module refresh passed.

# ═══ EXECUTION LOG (2026-06-12, Opus) — CURVACT half GREEN; SLOTDIFF fully de-risked ═══

## ✅ `curvactReduce` DONE (GREEN, 0 sorry) — the CURVACT half
`SpatialMember.lean`, private lemma before `spatialCommStarSum`.  Conclusion:
`∑ᵢ curvatureAction0SAt rm13 (∇^{k+1}Rm x) bᵢ (b(I0 0)) (cons bᵢ (b∘I0∘succ))
  = −∑_q ∑_p ∑ᵢ ∇^{k+1}Rm(update (cons bᵢ (b∘I0∘succ)) q (bp)) · ∇⁰Rm(vec4 bᵢ (b(I0 0)) (cons bᵢ …)_q (bp))`.
Proof: per-`i` `curvatureAction0SAt_eq_rm04` at `gInv = identityInvMetric` (the `∑_r δ` collapse via
`Finset.sum_eq_single`), then `Finset.sum_neg_distrib` + `Finset.sum_comm`×2.  This RHS is EXACTLY
`−∑_q (curvactStar_q RHS)` (peel q via `Fin.sum_univ_succ`: q=0→`curvactStar0`, q.succ→`curvactStarPos`).
**Lean traps solved:** (1) `vec4 … (Fin.cons … q) …` and `Function.update (Fin.cons …) …` need the
EXPLICIT `@Fin.cons (4+k) (fun _ => TangentSpace I x) …` form (bare `Fin.cons` motive uninferred) — and
must match `curvactStarPos`/`curvactStar0`'s spelling for the downstream `rw`.  (2) `Finset.sum_neg_distrib`
is FORWARD (`∑ -f = -∑ f`), not `←`.  (3) **`CurvatureActionLower` was imported by NOTHING** — added
`import DifferentialGeometry.Geometry.Curvature.CurvatureActionLower` to SpatialMember.lean.

## ✅ WALL 2 FULLY DISSOLVED — the B-term bridge is `allBut0SFreezeNabla`
The δ session feared the `nablaKRmNablaFrozenSlotField` evaluation (∇-of-frozen → frozen-∇^{k+1}) was
unbuilt.  IT IS BUILT: **`allBut0SFreezeNabla`** (`StarSum/FrozenSlotAllK.lean:181`):
`totalNabla0SFun 1 cov (freezeAllBut0SField A q Y) x (vec2 (X x) U)
   = totalNabla0SFun s cov A x (cons (X x) (update (Y·x) q U))`  (hyp `hYzero : ∀ i≠q, ∇_{Xx}(Y i)=0`).
With `A := ∇ᵏRm`, this is exactly the B-term identification.  So EVERY lemma for SLOTDIFF exists.

## REMAINING: `slotdiffReduce` (long but 100% banked) + final assembly

### `slotdiffBasisEq` (per-`i` SLOTDIFF identity → basis-vector star summands)
For `a b c : Idx`, `m : Fin (4+k) → Idx`:
`∇^{k+3}Rm(cons (ba)(mTI bb bc (b∘m))) − ∇^{k+3}Rm(cons (ba)(mTI bc bb (b∘m)))
  = −∑_q [ ∑_e ∇ᵏRm(update (b∘m) q (be)) · ∇¹Rm(vec5 (ba)(bb)(bc)(b(m q))(be))
         + ∑_e ∇^{k+1}Rm(cons (ba)(update (b∘m) q (be))) · ∇⁰Rm(vec4 (bb)(bc)(b(m q))(be)) ]`
Proof recipe (mirror `abs_nablaK_antisym_basis_le` lines 876-891 BUT keep equality):
1. `obtain Xa/Vb/Vc` + `choose Vm` via `TensorLieDeriv.exists_cov_zero_at_apply`; rewrite `ba = Xa x₀`
   etc. (`rw [show … from h.symm]`).  Reshape SLOTDIFF via rfl: `mTI ba bb (cons …)` ↦
   `cons ba (mTI bb bc …)` (defeq, the `abs_spatialBracket` hAB1/hAB2 `congrArg rfl` trick).
2. `rw [nablaK_antisym_eq_rm04_raise_leibniz S hS t k x₀ Xa Vb Vc Vm (hVbcov Xa)(hVccov Xa)(fun i => hVmcov i Xa)]`.
3. Per q, A-term: `cotangentSharp_ortho_expand` (sharp = ∑_e β(be)•be) + `tensor05_vec5_sum_last_idx`
   (pull ∑_e out) + `nablaKRmFrozenSlotField_apply_vec` (β(be) = ∇ᵏRm(update (Vm·x₀) q be)) + rewrite
   `Vm i x₀ = b(m i)` and `Xa/Vb/Vc x₀ = ba/bb/bc`.  `nablaRm04Field = nablaKRm04Field 1` (check rfl/bridge).
4. Per q, B-term: same sharp+`tensor04_vec4_sum_last_idx`, then `tensor0S_curry`+`totalNabla0S_apply`
   to expose `totalNabla0SFun 1 cov (nablaKRmFrozenSlotField k q Vm) x₀ (vec2 (Xa x₀) be)`, then
   `allBut0SFreezeNabla` (A=∇ᵏRm) → `totalNabla0SFun (4+k) cov (∇ᵏRm) x₀ (cons (Xa x₀)(update (Vm·x₀) q be))`,
   then `nablaKRm04Field_succ`+`totalNabla0S_apply` → `nablaKRm04Field (k+1) x₀ (cons ba (update (b∘m) q be))`.

### `slotdiffReduce` then `spatialCommStarSum`
- `slotdiffReduce`: `∑ᵢ slotdiffBasisEq(i; i, I0 0, fun q => I0 q.succ)` + `Finset.sum_comm`/`sum_neg_distrib`
  ⟹ `∑ᵢ SLOTDIFF(i,i) = −∑_q (slotdiffStarA q + slotdiffStarB q at I0)` (the `∑ᵢ`,`∑_e` swap into the
  starLemmas' double sums; mul_comm).
- assembly: `T := −(∑_{q:Fin(4+k)} base_A_q + ∑_{q:Fin(4+k)} base_B_q + ∑_{q:Fin(4+(k+1))} base_curv_q)`
  (`curv_q` σ = `if q=0 then sigmaCurv0 else sigmaCurvPos`, peel via `Fin.sum_univ_succ`).  Membership:
  `starSum2_sum` + `.smul (−1)` + `.add` + `.base`.  Component identity: `tensor0SComponent (T x) basis I0`
  unfolds (rfl, `tensor0SComponent_apply`) to the routing-lemma sums = `curvactReduce` + `slotdiffReduce` = LHS
  (after `spatialComm_nablaKRm_split` at `gInv=identityInvMetric` + `sumIdentityDiag` δ-collapse, with
  `X := basis (I0 0)`, `tail := fun p => basis (I0 p.succ)`, `Fin.cons_self` to match `basis∘I0`).

# ═══ PLANNER REVIEW (2026-06-12, Fable) — wall verdicts + re-scope ═══

Stop was correct per the rules; recon below is excellent and fully reusable.  Verdicts:

## WALL 2 (frozen-slot bridge): **DISSOLVED — the bridge EXISTS, do not build infra**
- The "tangent vector ↦ covariant-constant-at-x section" extension is
  **`TensorLieDeriv.exists_cov_zero_at_apply (cov) (hcov) (x) (v)`** — used ×12 across
  `MetricTrace/NablaTraceGen.lean` (215, 217, 530) and `MetricTrace/Higher.lean` (51, 53,
  190, 370, …), always via the `choose Vtail hVtailx hVtailcov using fun b => …` idiom.
- Decisive precedent: **`abs_spatialComm_nablaKRm_ortho_le`** (`NablaReactionAllK.lean:976`)
  is STATED at pointwise basis vectors and was PROVED from the same frozen-slot lemmas —
  its proof body contains the exact bridging choreography (choose extensions, apply the
  frozen-slot identity, evaluate at the centre).  **MINE THAT PROOF**; the identity-level
  intermediate steps you need exist inside it (before it takes `|·|`).
- So P2b = pattern-following assembly, not new infrastructure.

## WALL 1 (generic `(k,q)`-σ): **CONFIRMED — build it, with this design directive**
- Do NOT use `Equiv.ofBijective ![…]` (concrete-only) and do NOT compose
  `cycleRange`/`succAbove` combinator chains (their eval lemmas rw-rematch poorly at
  symbolic `k`).  Use the **dite-val pattern** (the proven `mtInputBasis` /
  `traceNablaShuffle_val` / `metricTraceInput_apply` recipe): define `toFun`/`invFun` as
  explicit val-arithmetic dites, `left_inv`/`right_inv` by `Fin.ext` + `omega`
  case-splits, eval lemmas = the dite specs (`split_ifs`).  All three precedents are
  generic-rank and robust.
- The `q = 0` branch is a DIFFERENT routing (factor2 takes the `i`-trace var twice:
  `Rm04(bᵢ, X, bᵢ, b_p)`, factor1 loses `i`) — expose the toolkit as a `q = 0` instance +
  a `q ≥ 1` family (or one dite-on-`q`), per the recon's split.
- Factor assignment: `∇^{k+1}Rm` = the `a := k+1` factor, `Rm04` = `b := 0`;
  `base (k+1) (k+1) 0 0 σ_q` ✓ (`starBaseProd_eq` is already generic in `a, b`).

## Re-scope (accepted): two sessions
- **Session γ — `StarRouting.lean`** (NEW file, claim only it; import StarSum2):
  the generic σ-family for the CURVACT shape + val-eval lemmas + ONE end-to-end validated
  generic-`k` instance: `base (k+1) (k+1) 0 0 (σ_q)`-comps = the `update`-form q-term of
  the recon (line ~38).  Done-criterion: that identity GREEN at symbolic `k`, both
  `q = 0` and `q ≥ 1` branches.
- **Session δ — P2 completion** (in `SpatialMember.lean`, imports StarRouting):
  CURVACT assembly (γ's lemma + `starSum2_sum` + δ-collapse `∑ᵢⱼδᵢⱼ→∑ᵢ`) + SLOTDIFF via
  the mined `abs_spatialComm…ortho_le` bridging pattern + final assembly of
  `spatialCommStarSum`.  Also: promote `starSum2_sum` into `StarSum2.lean` (claim it; α
  is finished, no conflict).
P3 remains blocked on P2 (and will reuse γ's toolkit for the `∂ₜΓ∗∇ᵏRm` term).


Session β (2026-06-12, Opus). Scope: P2 only. File created + claimed; `StarSum2.lean` NOT edited.

## STATUS: statement FROZEN (GREEN/sorry) + one reusable helper GREEN; proof = a 2-wall frontier

P2 is **substantially larger than the plan's "1 session" estimate**. The banked inputs are NOT in
the clean pointwise-orthonormal form P1.3 enjoyed — they are in a *frozen-slot vector-field*
framework and produce a *per-slot `∑_q`* whose `σ` is `(k,q)`-dependent and generic. Two genuine
infrastructure pieces are missing (details below). Honest recommendation to the planner: re-scope
P2 (build the two infra pieces first, OR carry the recast as a standing structured input).

## ✅ GREEN deliverables in `SpatialMember.lean`
- **`starSum2_sum`** (private, flag for promotion to `StarSum2.lean`): `StarSum2` is closed under
  finite `Finset.sum` (`Finset.induction` + `.zero`/`.add`). P2's curvature-action term is a sum
  over the `4+(k+1)` slots, so this is required. Promote next to `StarSum2.add`.
- **`spatialCommStarSum`** (frozen P2 statement, `sorry`): `∃ T, StarSum2 S t (k+1) T ∧ ∀ x basis
  gInv hinv horth I0, (spatialComm LHS at basis∘I0) = tensor0SComponent (T x) basis I0`. The LHS is
  `metricTraceFirstTwo0STensor g (∇^{k+3}Rm) − totalNabla0SFun (Δ∇ᵏRm)` (the
  `spatialComm_nablaKRm_split` LHS = `[Δ,∇]∇ᵏRm`). Carries `hcov`/`hmc` (spatialComm's analytic
  inputs). This is the interface P3 consumes.

## The structure (fully reconned — all three banked inputs read)

`spatialComm_nablaKRm_split` (`RoughLapNablaK.lean:140`) is an IDENTITY:
```
[Δ,∇]∇ᵏRm (cons X tail)  =  ∑ᵢ ∑ⱼ gInv i j · ( SLOTDIFF(i,j) + CURVACT(i,j) )
  SLOTDIFF(i,j) = ∇^{k+3}Rm(mTI bᵢ bⱼ (cons X tail)) − ∇^{k+3}Rm(mTI bᵢ X (cons bⱼ tail))
  CURVACT(i,j)  = curvatureAction0SAt (rm13) (∇^{k+1}Rm) bᵢ X (cons bⱼ tail)
```
At an orthonormal basis (`gInv = δ`), the `∑ᵢⱼ δᵢⱼ` collapses to `∑ᵢ` (j:=i).

### CURVACT term  → `∑_q base(σ_q)`  [WALL 1: generic `σ`]
`curvatureAction0SAt_eq_rm04` (`CurvatureActionLower.lean:49`), at `gInv=δ`:
```
curvatureAction0SAt Rm13 S X' Y' slots = −∑_q ∑_p  S(update slots q (basis p)) · Rm04(vec4 X' Y' (slots q) (basis p))
```
So `∑ᵢ CURVACT = −∑ᵢ ∑_q ∑_p ∇^{k+1}Rm(update (cons bᵢ tail) q (bp)) · Rm04(bᵢ, X, (cons bᵢ tail) q, bp)`.
The TWO basis-sums `∑ᵢ` (`bᵢ`) and `∑_p` (`bp`) are the **two metric traces** of a
`∇^{k+1}Rm ⊗ Rm04` product ⟹ each `q` gives one `base (k+1) (k+1) 0 0 σ_q` term, and the whole is
`∑_{q : Fin (4+(k+1))} base(σ_q)` (use `starBaseProd_eq` + `starSum2_sum`).
- **WALL 1**: `σ_q : Fin ((4+(k+1))+(4+0)) ≃ Fin ((4+(k+1))+4)` is `(k,q)`-DEPENDENT and GENERIC in
  `k` — the concrete `![…]` `Fin 8` tables of P1.3 do NOT generalize. Needs a generic
  `Equiv`-construction (insertion/`Fin.cycleRange`/`Fin.succAbove`-style routing of the rotated
  slot `q`), with a `q=0` (cons-head) vs `q≠0` split. This is intricate generic Fin-algebra,
  comparable to (harder than) `stNabla_starBase`'s slot algebra. Plus the `update slots q`/`Fin.cons`
  evaluation must be reduced generically (no `fin_cases` — `k` is symbolic).

### SLOTDIFF term  → `∇Rm04∗∇ᵏRm + Rm04∗∇^{k+1}Rm`  [WALL 2: frozen-slot bridge]
`SLOTDIFF` is the antisymmetric 2nd-derivative difference; it does NOT directly reduce (it is still
order-`k+3`). It is reduced by:
- `nablaK_antisym_eq_covDeriv_curvatureAction` (`NablaReactionAllK.lean:397`):
  `SLOTDIFF = extDerivFun (curvatureAction0SAt rm13 (∇ᵏRm) Vb Vc Vm) x₀ (X x₀)` (∇ of the action), and
- `nablaK_antisym_eq_rm04_raise_leibniz` (`:533`): expands that to the explicit
  `∇Rm04 ∗ ∇ᵏRm + Rm04 ∗ ∇^{k+1}Rm` form (with `cotangentSharp_gen` metric raises).
- **WALL 2**: BOTH are stated in the **frozen-slot framework** — slots are vector-field SECTIONS
  `Vb,Vc,Vm` with `(∇_X V)(x₀) = 0` (covariant-constant at the centre, the `#45`/normal-frame
  pattern). To apply them at our pointwise basis `bᵢ, X, tail`, I must EXTEND each basis vector to
  such a section. `nablaKRm04_ricciIdentityAt` (`RmRealizationBridgeAllK.lean:274`) is pointwise but
  is only the LOW-level `Tensor0SRicciIdentityAt`, not the star form. The extension bridge
  (tangent vector ↦ covariant-constant-at-x₀ section) is the missing API — check
  `FrozenSlotAllK.lean` / `RmFrozenSlotField.lean` for a banked normal-frame extension; if absent,
  it is new infrastructure. The `cotangentSharp_gen` raises also need δ-collapse at orthonormal.

## Why this is not a clean single session
- P1.3 worked because k=0 made everything concrete `Fin 8` (`![…]` tables, `fin_cases`). P2 is
  inherently **general-k** (P3's induction uses P2 at every level), so the concrete-table technique
  is unavailable; generic `σ` + generic slot-evaluation are required.
- The antisym half lives in the frozen-slot framework, needing a pointwise extension bridge.
- Net: P2 needs (1) a generic `(k,q)`-`σ` builder + `starBaseProd_eq` at general `a,b`, and (2) the
  frozen-slot↔pointwise extension. Each is its own sub-project.

## Recommendation for the planner
1. Re-scope P2 to ≥2 sessions, OR
2. Split: **P2a** = the CURVACT half (pointwise, no frozen-slot) once a generic-`σ` builder exists;
   **P2b** = the SLOTDIFF half (frozen-slot bridge). P2a is the better first target (cleaner).
3. Consider whether P3 can consume a *weaker* P2 (e.g. just the `StarSum2 (k+1)` MEMBERSHIP of a
   named field `T_spatial` defined from the RHS, with the component identity deferred) — but the
   membership still needs the `base` constructors' `σ`, so the generic-`σ` wall remains.
4. The generic-`σ` builder is the highest-leverage missing piece — it unblocks CURVACT (P2a), the
   `∂ₜΓ∗∇ᵏRm` term of P3, and `StarSum2.nabla`'s general use. Build it as reusable infra first.

## Banked-lemma reference (exact)
- `spatialComm_nablaKRm_split` — `Evolution/StarSum/RoughLapNablaK.lean:140` (the split identity).
- `curvatureAction0SAt_eq_rm04` — `Geometry/Curvature/CurvatureActionLower.lean:49` (action = Rm04 raise).
- `nablaK_antisym_eq_covDeriv_curvatureAction` — `…/StarSum/NablaReactionAllK.lean:397` (frozen-slot).
- `nablaK_antisym_eq_rm04_raise_leibniz` — `…/StarSum/NablaReactionAllK.lean:533` (frozen-slot, raise).
- `nablaKRm04_ricciIdentityAt` — `Evolution/RmRealizationBridgeAllK.lean:274` (pointwise low-level).
- `starBaseProd_eq` / `mtfDiag` / `starBaseField` / `StarSum2` — `StarSum2.lean` (our eval tools).

## 2026-06-13 Codex pass

Verification still fails to close the target theorem: `spatialCommStarSum` remains the active
frontier and still uses its existing `sorry`.

What changed:
- `SpatialMember.lean` now imports `StarRouting` so it sees the CURVACT and SLOTDIFF routing
  identities.
- Added generic-`Idx` exact sharp-expansion helpers in `SpatialMember.lean`:
  `cotangentSharp_ortho_expand`, `tensor05_vec5_sum_last_idx`, and
  `tensor04_vec4_sum_last_idx`.  These generalize the existing `Fin n` reaction-bound exact
  expansion lemmas to the arbitrary finite `Idx` used by `spatialCommStarSum`.
- `StarRouting.lean` now has checked generic SLOTDIFF routes:
  `sigmaDiffA` / `slotdiffStarA` for the `(a,b)=(1,k)` term and
  `sigmaDiffB` / `slotdiffStarB` for the `(a,b)=(0,k+1)` term.
- `StarSum2.starSum2_sum` is promoted next to the constructors in `StarSum2.lean`.

Current blocker:
- The remaining proof is the assembly equality, not the route infrastructure:
  instantiate `spatialComm_nablaKRm_split` with the identity inverse metric from `horth`,
  collapse `∑ᵢⱼ δᵢⱼ` to `∑ᵢ`, rewrite the CURVACT summand by
  `curvatureAction0SAt_eq_rm04` and `curvactStar0/curvactStarPos`, then rewrite the SLOTDIFF
  summand by the frozen-slot choose-idiom plus `nablaK_antisym_eq_rm04_raise_leibniz`,
  `cotangentSharp_ortho_expand`, and `slotdiffStarA/slotdiffStarB`.
- This looks like a routine but long local assembly proof.  I do not see a new mathematical
  obstruction after the generic sharp helpers and SLOTDIFF sigma routes checked.

Verification status:
- `StarRouting.lean` passed focused verification and targeted module build.
- `SpatialMember.lean` passed focused verification only with the existing `spatialCommStarSum`
  `sorry`.

## 2026-06-13 Planner confirmation and executor prompt

Live grep confirmation:
- `curvactReduce` is a proved private lemma in `SpatialMember.lean`; it is not the remaining
  frontier.
- `spatialCommStarSum` is still the P2 `sorry`.
- The needed route bank exists in-tree: `starSum2_sum`, `curvactStar0`, `curvactStarPos`,
  `slotdiffStarA`, `slotdiffStarB`, `cotangentSharp_ortho_expand`,
  `tensor05_vec5_sum_last_idx`, `tensor04_vec4_sum_last_idx`, `allBut0SFreezeNabla`,
  `TensorLieDeriv.exists_cov_zero_at_apply`, `nablaK_antisym_eq_rm04_raise_leibniz`,
  and `spatialComm_nablaKRm_split`.

Refined executor prompt:

```text
Work in `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/SpatialMember.lean`.
Claim that file with `scripts/lake-locked.ps1` before editing. Do not edit `StarRouting.lean`
or `StarSum2.lean` unless a focused check shows a real stale-import/export issue.

Target: close `spatialCommStarSum`.

Read `SpatialMember.md` sections:
- `2026-06-13 Planner confirmation and executor prompt`
- `2026-06-13 Codex pass`
- `REMAINING: slotdiffReduce ...`
- `PLANNER REVIEW`

Plan:
1. First prove the tiny local inverse-metric collapse needed by the current final statement:
   from `_hinv : MetricInverseInBasis_gen ... basis gInv` and `_horth`, derive
   `gInv i j = identityInvMetric i j`. This is just the inverse equation plus
   `Finset.sum_eq_single`; do not search for new geometry.
2. Instantiate `spatialComm_nablaKRm_split` with the original `gInv`, rewrite it to the
   identity inverse using step 1, then collapse the `sum_i sum_j delta_ij` to `sum_i`.
3. Reuse `curvactReduce` for the CURVACT diagonal.
4. Prove a private `slotdiffBasisEq` by mining the pre-absolute-value middle of
   `abs_spatialComm_nablaKRm_ortho_le`: choose cov-zero sections with
   `TensorLieDeriv.exists_cov_zero_at_apply`, apply
   `nablaK_antisym_eq_rm04_raise_leibniz`, expand sharps with
   `cotangentSharp_ortho_expand`, and identify the B-term with `allBut0SFreezeNabla`.
5. Sum `slotdiffBasisEq` over the diagonal index to get `slotdiffReduce`, then rewrite its
   two double sums with `slotdiffStarA` and `slotdiffStarB`.
6. Use the witness
   `T := -(sum_q base_slotdiffA q + sum_q base_slotdiffB q + sum_q base_curv q)`.
   Membership is `starSum2_sum`, `.add`, `.smul (-1)`, and `.base`. The component identity is
   the split identity plus `curvactReduce` plus `slotdiffReduce`.

Stop conditions:
- If `allBut0SFreezeNabla` does not match after the cov-zero choose idiom and exact
  `nablaKRm04Field_succ`/`totalNabla0S_apply` unfolding, report that exact goal.
- If a `StarRouting` lemma has the wrong sign or slot order after the summand is fully
  normalized, report the exact normalized summand and do not add a parallel routing family
  until the mismatch is verified.
- If the arbitrary-`gInv` final statement forces more than the local diagonal-collapse helper,
  report that statement-form problem instead of weakening the theorem silently.

Verification: focused locked check of `SpatialMember.lean`; if it exports a newly closed
`spatialCommStarSum` and a downstream file needs it, then build the `SpatialMember` module once.
Record only pass/fail and the exact blocker in this note.
```

# EXECUTION LOG (2026-06-13, Codex) -- `spatialCommStarSum` GREEN

`spatialCommStarSum` is closed with 0 `sorry` in `SpatialMember.lean`.
The proof follows the Opus recipe:

- Added private `slotdiffBasisEq`: basis-vector equality from
  `nablaK_antisym_eq_rm04_raise_leibniz`, using
  `TensorLieDeriv.exists_cov_zero_at_apply`, sharp expansions, `nablaKRmFrozenSlotField_apply_vec`,
  and `nablaKRmFrozenSlot_eval` (the `allBut0SFreezeNabla` bridge).
- Added private `slotdiffReduce`: sums `slotdiffBasisEq(i; i, I0 0, I0.succ)` and routes exactly through
  `slotdiffStarA` / `slotdiffStarB`.
- Added private `curvRoute` and `sumDiag`: wraps the existing `curvactReduce` with
  `curvactStar0` / `curvactStarPos`, then the final assembly uses
  `spatialComm_nablaKRm_split` at `identityInvMetric`.
- Final witness is `T = (-1) • (TA + TB + TC)`, with membership by `starSum2_sum`, `.base`, `.add`,
  and `.smul`.

New traps recorded:
- `rw [hslots]` does not reliably rewrite both normalized slot arities; use a raw split equality plus
  two explicit slot equalities for `Fin (4 + (k + 1))` and `Fin (4 + k + 1)`.
- Generic pointwise `Tensor0SField` finite-sum application creates brittle bundle-instance/universe
  obligations. Keep it local at the concrete rank and prove the three finite-sum applications by
  direct `Finset.induction_on`.
- For the `TC` dependent-if sum, the insert step needs section/tensor `add_apply` before using the
  induction hypothesis, then split on `a.val = 0`.

Verification passed.

## 2026-06-13 Planner review -- P2 accepted

Live review confirmed the executor report:

- `rg "sorry|admit" SpatialMember.lean` is clean.
- `spatialCommStarSum` is proved at the frozen P2 signature.
- The private helpers are present in the same file: `slotdiffBasisEq`, `slotdiffReduce`, `sumDiag`,
  and `curvRoute`.
- The SLOTDIFF proof uses the banked producer chain
  `nablaK_antisym_eq_rm04_raise_leibniz` + cov-zero section choices + sharp expansion +
  `nablaKRmFrozenSlotField_apply_vec` / `nablaKRmFrozenSlot_eval`.
- The final assembly uses `spatialComm_nablaKRm_split` at `identityInvMetric`; this is justified by
  the orthonormal-basis hypothesis and does not introduce a new arbitrary-`gInv` frontier.

Sign sanity:

- `slotdiffReduce` routes the diagonal SLOTDIFF sum to `-(sum_q (DiffA_q + DiffB_q))`.
- `curvRoute` routes the CURVACT diagonal sum to `-(sum_q Curv_q)`.
- The final witness `T = (-1) • (TA + TB + TC)` matches those two negative reductions.

Planner decision: P2 is accepted as closed.  The next plan-of-record step is P3 in `StarSum2.md`:
refreeze the all-`k` residual target with honest dim-3/base/time-side inputs, then isolate the
`gammaStepStar` producer before attempting full induction.

## 2026-06-14 hcov/hmc cleanup

`spatialCommStarSum` no longer carries the old analytic witnesses from
`spatialComm_nablaKRm_split`.  The split now derives solution connection
smoothness and metric compatibility internally, so the star-sum membership
statement is cleaner.

Verification passed for the edited file and module refresh.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
spatial star-sum membership file.  The proof remains under the standard smooth
manifold context.

Verification passed for the edited file.

## 2026-06-14 — component-eval transparency sweep (item 4): 2 → 1 blocks

Removed the `set_option backward.isDefEq.respectTransparency false` from **`curvactReduce`** (the private
CURVACT helper) — it was **STALE**.  The proof is pure pointwise component reduction
(`curvatureAction0SAt_eq_rm04` at `identityInvMetric` + `Finset.sum_eq_single`/`sum_neg_distrib`/`sum_comm`
+ `Fin.cons`/`Function.update`/`vec4` slot algebra), no `StarSum2` structure / `ContMDiffAt` / section ext.

**Kept `spatialCommStarSum`** (the P2 deliverable): tested removal → `synthInstanceFailed` at the `StarSum2`
membership proofs (`starSum2_sum`/`StarSum2.base`, lines ~521–533).  The transparency option is **load-bearing**
for the `StarSum2` structure instance synthesis — this is the bundle/structural class, not pure component-eval.
Restored.  Focused-check **green** (55.4s).  See `Tensor/RSTensor/ComponentEvalApiPlan.md` (8th pass).

## 2026-07-12 short-time-existence branch alignment

The merge made `Tensor0SSpace` point evaluation opaque at the old underlying
`ContinuousMultilinearMap` representation.  The finite-sum induction in
`spatialCommStarSum` now uses the public `Tensor0SSpace.add_apply` theorem
instead of the representation-level `ContinuousMultilinearMap.add_apply`.
This is a compatibility repair only; it does not change the star-sum witness or
the spatial commutator argument.

Focused verification and the targeted module refresh passed.  `spatialCommStarSum` and its dedicated machinery
remain complete (100%); this compatibility repair is complete (100%).  The
short-time-existence theorem itself remains proved (100%); branch-alignment
verification is about 99% pending the downstream Hamilton replay, and the merge
commit remains 0% until final verification and diff review.  No completion
percentage of the Hamilton positive-Ricci endpoint or wider HCG compactness
theorem changes here.

## 2026-07-22 canonical commutator field

The former existential proof now exposes its actual witness as
`commStarField S t k`.  The field is definitionally the existing
`(-1) • (TA + TB + TC)` expression and depends on neither `IsSolutionOn`, a
component index type, a point, nor a basis.  Its checked projections are:

- `commStarField_cost`, the exact `commStarCost` constructor-tree bound;
- `commStarField_spec`, the orthonormal-basis component identity.

`spatialCommStarSum` retains its original public statement as a compatibility
wrapper around this fixed field.  This removes the witness-choice ambiguity for
the successor residual recursion without changing any sign, routing, cost, or
component equation.

Focused verification passed with no remaining diagnostics.  This canonical
field extraction and P2 remain complete (100%).  The arbitrary-index successor
brick is a separate completed consumer; the dedicated direct-tower machinery is
about 94%, while the final `residualStarCosted` theorem remains unstated/unproved
(0%) and the unconditional compactness endpoint remains 0%.
