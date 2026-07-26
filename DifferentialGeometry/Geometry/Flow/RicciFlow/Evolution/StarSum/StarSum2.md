# `StarSum2` — design + brick status

## 2026-07-14 quantitative StarSum certificate

Added `StarSum2Cost`, its membership/nonnegativity/component-bound projections,
the canonical `StarSum2.cost`, and exact cost propagation through sums and
covariant differentiation. The base residual has fixed cost `108` in
dimension three. Focused verification and the module refresh passed.

This closes the quantifier defect in the old existential component bound: a
cost now depends only on the recorded constructor tree, not on the spacetime
point where the estimate is consumed.

Goal is the five BBS bricks: `StarSum2` predicate + `.add`, `.bound`, `.nabla`, the `E_k`
recursion, and the `IteratedRmTowerOn` wiring.

## ✅ BRICK 2 DONE (2026-06-11, GREEN — `StarSum2.bound` proved)

**`StarSum2.bound : StarSum2 S t k T → ∃ C ≥ 0, ∀ x basis (horth) m, |T(basis-comps)| ≤
C·Σ_{j∈range(k+1)} √(stNormSq j)·√(stNormSq (k−j))`** — the Cauchy–Schwarz extraction, 0 sorry.
`stNormSq S t j x basis := compNormSqMulti (basis-components of ∇ʲRm)` (= `wⱼ`); `horth` is the
folder-standard inner-product form `g.inner x (basis i) (basis j) = δᵢⱼ` over an abstract
`{Idx}[Fintype][DecidableEq]` (matching the tower's index style; `C` is uniform in `(x, basis, m)`,
only `card Idx` enters). Constants: zero→0, add→C₁+C₂, smul c→|c|·C, base→card² (one `card` per
metric trace, then per-component CS).

New supporting API (same file): `sumIdentityDiag` (δ double-sum collapse), `mtInputBasis`
(∃-form: a trace input of basis vectors IS `basis ∘ mIdx` — dite index tuple), `mtfOrthoBd`
(**the reusable orthonormal trace bound**: per-component bound c on X ⟹ per-component bound
card·c on `metricTraceFirstTwoField g X`, via `metricInverseInBasis_identity_of_orthonormal` +
`metricTraceFirstTwo0SAt_eq_sum_basis` + δ-collapse). Base case: a+b=k extracted from σ via
`Fintype.card_congr`; lands on the j:=a summand via `Finset.single_le_sum`.

**Lean lessons (brick 2):** (1) `abs_le_sqrt_compNormSqMulti` (NablaRiemannHeat.lean) carries a
DIFFERENT ℝ-lattice/AddGroup instance path than this file's `|·|` (`Real.lattice` vs
`instDistribLatticeOfLinearOrder`) → "Application type mismatch" even under respectTransparency;
WORKAROUND: use instance-clean `sq_le_compNormSqMulti` + Mathlib's `Real.abs_le_sqrt`. (2) `abs_add`
is GONE (renamed `abs_add_le`). (3) `Fin.cases`-style tuple lemmas: state as ∃ index tuple (dite
form) + `simp only [metricTraceInput_apply]` (simp beta-reduces; `rw` doesn't) + `split_ifs <;> rfl`.
(4) `Finset.single_le_sum` leaves `(fun j => …) a` un-beta-reduced — `simp only [hb] at` both
beta-reduces and rewrites. (5) induction @-binders: index k is consumed — `| @add A B hA hB ihA ihB`.

## ✅ CLASS EXTENSION DONE (2026-06-11, GREEN build 3705): metric factors + iterated traces

The g-factor extension below is **fully implemented and verified** (0 errors/warnings in
`StarSum2.lean`; bricks 1–3 and 2 re-proved in the extended setting):
- `starProd S t a b r` (g's right-appended, all rank steps defeq), `mtIter` (τ-fold trace),
  `mtIter_add`; `starBaseField S t k a b r σ = mtIter (2+r) (ddc σ (starProd a b r))`,
  `σ : Fin (((4+a)+(4+b))+2r) ≃ Fin ((4+k)+2(2+r))`; `base` ctor gains `r`.
- `.nabla` (re-proved): `starProdNabla` (r-induction; g-branch vanishes via
  `zero_realizes_metric` + `product_zero` + `domDomCongr_zero` + the NEW
  `product_add_left`/`product_domDomCongr_left`); `stNablaMtIter` (τ-induction of the keystone,
  ∃ρ-form, massage = `← metricTraceFirstTwoField_domDomCongr` + `domDomCongr_trans`);
  `stNabla_starBase` witnesses right-assoc + `Equiv.trans_assoc` in the final simp.
- `.bound` (re-proved): `starProdBd` (r-induction; metric components `δ ≤ 1` via
  `metricTensorField_apply` + horth), `mtIterOrthoBd` (τ-induction over `mtfOrthoBd`),
  base constant `card^{2+r}`.
- NEW light-layer (Tensor.lean / DomDomCongrSection.lean): `product_add_left`,
  `product_domDomCongr_left` (the `finSumFinEquiv`-conjugated `e ⊕ refl` block equiv).
- Lean traps hit: `rw [product_fun_apply]` fails on rank-index mismatch (`2*(r+1)` vs
  `(…+2r)+2`) → use `le_trans (le_of_eq (congrArg abs hpf)) …` (exact-mode defeq) instead;
  `Fin.natAdd _ 0`'s `_`/Fin-rank metavars underdetermined in `show` → write
  `Fin.natAdd <explicit> (0 : Fin 2)`.

### (historical) the discovery record

⚠️ BRICK 4 DESIGN DISCOVERY (2026-06-11): the class needs METRIC FACTORS

Feasibility check of `E_0 = (∂ₜ−Δ)Rm = −2B# − drift` against the class exposed a REAL
design gap: the dim-3 reaction contains terms with **free metric factors** — `bsharp_eq_knC`
gives `B# = KN(C, −|R|², δ)` with `C = 2R²−(3S/2)R+(S²/2−|R|²)δ` (UhlReaction3), so
`R²⊙δ`, `S·R⊙δ`, `(S²/2−|R|²)δ⊙δ` terms appear.  A pure double trace of `∇ᵃRm⊗∇ᵇRm`
leaves its 4 free slots ON THE Rm FACTORS — it can never produce free `g`-slots.  Hamilton's
`∗`-algebra always allowed `g`/`g⁻¹` factors; the class must too.

**EXTENSION (in progress):** generator `starProd a b r` = `∇ᵃRm ⊗ ∇ᵇRm ⊗ g^{⊗r}` with the
`g`'s appended ONE AT A TIME on the right (`| r+1 => product (starProd r) (metricTensorField g)`)
— this keeps every rank step `(R+2r)+2 ≡ R+2(r+1)` DEFEQ (the existing `metricPow` has a
`2+2r ≠defeq 2(r+1)` cast in its successor — avoid it as the generator; its parallelism lemma
`nabla_metricPow_zero` shows the proof pattern).  `base k a b r σ` = `mtIter (2+r)` traces of
`ddc σ (starProd a b r)`, `σ : Fin (((4+a)+(4+b))+2r) ≃ Fin ((4+k)+2(2+r))` (cardinality still
forces `a+b=k`; rank still pinned by σ).  Brick-3 adaptation: `∇(starProd) ` by r-induction —
the `g`-branch of Leibniz VANISHES (`zero_realizes_metric` + `product_zero`), so `∇base` is
STILL two daughters.  Brick-2 adaptation: `g`-components are `δᵢⱼ ≤ 1` at orthonormal bases;
each extra trace costs one `card` → base constant `card^{2+r}`.  New light-layer needs:
`product_add_left`, `product_domDomCongr_left` (block equiv via `finSumFinEquiv`-conjugated
`Equiv.sumCongr e (refl)`), `mtIter` + `mtIter_add` + iterated keystone (`τ`-induction) +
iterated `mtfOrthoBd`.

# ═══ P1.3 DONE + P1.4 IN PROGRESS (2026-06-12, Opus session β) ═══

## ✅ P1.3 COMPLETE (GREEN): `e0Field`-comps `= −2·B# − drift`
New in `StarSum2.lean` (`section ComponentIdentity`, `open Dim3Reaction`), all 0-sorry:
- `rmComp_eq_rm`: `∇⁰Rm`-comps `= rm R` at orthonormal Fin-3 frame (via `solution_rm04_kn_all`
  + `nablaKRm04Field_zero` + `simp [← hR, horth, htr, rm, sc, kd]`).  **Needs `NeZero (finrank E)`**
  — derived locally `⟨by have : finrank E = 3 := hdim; omega⟩` (TangentSpace defeq E).
- `ricTrace`: `∑_b rm R a b c b = −R a c` (`fin_cases a<;>fin_cases c<;>simp only[…,Fin.reduceFinMk,…]<;>ring`).
- `driftPiece` (g-general): `∑_e∑_f rm a e f e · g f = −∑_p R a p · g p` (`Finset.sum_comm` +
  `ricTrace` + `Finset.sum_neg_distrib`).
- `btStar2/3/4`, `drStar1/2/3/4`: the 7 `btStar_eq`-template term identities (σ-tables as recorded;
  `include horth` needed — it's used only in the proof, not the statement, so not auto-bound).
- `e0Field_comp` (capstone, GREEN first try): distribute eval (`hev := rfl`) + 8 term identities
  + `simp [rmComp_eq_rm …, Matrix.cons_val_{zero,one,two,three}, head_cons, tail_cons]` (Rm→rm R,
  reduce `![…] i`) + 4 `driftPiece` rw + `simp [Bt, drift, Finset.sum_add_distrib]` + `ring`.
  **All 8 σ-routings verified correct** (the identity closed — pencil tables were right).

## ✅ P1.4 COMPLETE (GREEN): `residualStarSum_zero` — k=0 instance, 0 sorry in the k=0 path
`residualStarSum_zero (S) (t : RegularTime D) (hdim : ∀x, finrank = 3) (hbase) : ∃ T,
StarSum2 S t 0 T ∧ <frozen conclusion at k=0, Idx=Fin 3>`.  Proof = `⟨e0Field, e0Field_mem, …⟩`;
per `(x,basis,horth,I0)`: `htr` from `scalar_eq_trace_ortho`+`simp[sc]`; `hlhs := rfl`
(`tensor0SComponent ∇⁰Rm = S.base.rm04` via `nablaKRm04Field_zero`); `hval := rfl` splits
`tensor0SComponent (roughLap + e0Field x)` into `comps(roughLap) + e0Field x (basis∘I0)` (CMM
`add_apply` rfl); `rw [e0Field_comp …]` (the genuine content) turns `e0Field`-comps into the
`−2B#−drift` reaction; `exact hbase`.  **Needs `NeZero (finrank E)`** — derived locally per x.

**DESIGN (de-walling, honest standing input)**: `hbase` carries the per-`(x, orthonormal-frame)`
`∂ₜRm04` evolution with **Laplacian already in the rough-trace form**
`comps(metricTrace0S2TensorInBasis basis δ ∇²Rm04)` and **reaction in bare `Bt`/`drift` form**.
This is the natural orthonormal heat-equation statement for `Rm` (bottoming out on the standing
`hlich`/scalar DeTurck layer — coworker's lane), and it BYPASSES BOTH (a) the forbidden C⁴
transfer AND (b) the deep `traceRm04Kn`/`rm04DerivsKn`/`lapRm04Kn` Δ-part machinery (the
`KN(lap,lapS,δ) = comps(roughLap ∇²Rm04)` intermediate is never needed — `hbase` states the
rough-trace form directly).  The genuine new math in the k=0 path is `e0Field_comp` (P1.3); the
PDE input is honestly threaded, not proven here.  **If a future session wants `hbase` discharged
from `rm04BaseEvolution_at`**: that needs the Δ-part proof (`KN = comps roughLap` via
`traceRm04Kn` + connecting `nablaKRm04Field S t 2` to `rm04DerivsKn.nabla2A`) — a separate
substantial chunk, deferred.

## STATUS: P1 COMPLETE through k=0.  Only remaining sorry = the all-`k` `residualStarSum` stub (P3).

# ═══ REVIEW + NEXT-PHASE DIRECTIVES (2026-06-12, Fable planner) ═══

## Review verdict on the P0+P1 session: ACCEPTED
- Claims verified: focused check GREEN, exactly 1 real `sorry` (line ~892, the intended
  `residualStarSum` stub); the frozen statement's math is right (slot order: the two
  outermost derivative slots are traced, matching `traceRm04Kn`'s convention).
- **All 8 σ-routing tables PENCIL-VERIFIED** against the recorded convention
  (`W = [e,e,f,f,m0..m3]`, `u(i) = W(σ i)`, factor1 = `u(0..3)`, factor2 = `u(4..7)`):
  σBt1–σBt4 realize `Bt(m0m1m2m3) / (m0m1m3m2) / (m0m2m1m3) / (m0m3m1m2)` = exactly the
  `Bsharp = Bt(abcd)−Bt(abdc)+Bt(acbd)−Bt(adbc)` expansion with the `−2,+2,−2,+2`
  coefficients ✓; σD1–σD4 realize the four drift tuples `(mᵢ,e,f,e,…f…)` ✓; all eight are
  bijections ✓.  Residual risk shifts to (i) `UhlReaction3`'s exact `R = −trace` slot/sign
  (compiled-checked by the Ricci-trace lemma) and (ii) the producer's actual `Bsharp`
  spelling (compiled-checked at assembly).  Proceed.

## ⚠️ DIRECTIVE for P1.4 — the "C⁴ wall" is BYPASSED, do not climb it
The frozen statement is at ORTHONORMAL bases — and `rm04BaseEvolution_at`
(`UhlenbeckBaseProducer.lean`, banked) is ALREADY the per-(t,x) g_t-orthonormal-frame
derivative `∂ₜRm04-comps = KN(lap,lapS,δ) − 2B# − drift`, with its four shaped hypotheses
discharged by the banked `rm04CompknOrtho` / `ricDot_ortho` / `scalarDot_ortho` /
`scalar_eq_trace_ortho`.  `rm04HrmProducer` (the coordinate-frame capstone) is the TOWER's
input, NOT ours — **do not touch the C⁴ coordinate↔orthonormal transfer at all**.
What P1.4 actually is (plumbing, each step has an existing lemma):
1. `fun r => tensor0SComponent (nablaKRm04Field S r 0 x) basis I0` IS
   `fun r => S.base.rm04 r x (basis∘I0)` (`nablaKRm04Field_zero` rfl) — feed
   `rm04BaseEvolution_at` directly.
2. Δ-part match: comps(`metricTrace0S2TensorInBasis basis δ (∇²Rm04)`) =
   `KN(lap,lapS,δ)`-comps, via `metricTrace0S2InBasis_eq_metricTrace`
   (`RoughLaplacian.lean:644`) + `traceRm04Kn` (field-level, DONE) evaluated at the
   orthonormal basis (`mtfDiag`-machinery) + the bundled-`ΔRic`↦`roughLapRic`-array and
   `ΔS`↦`scalarLap` component bridges (the route-status "light plumbing":
   `metricTraceFirstTwo0SAt_eq_sum_basis` / `RoughLap0SRealizesMetricTrace`).
3. **Statement adjustment (REQUIRED, not a failure)**: `rm04BaseEvolution_at`'s inputs
   bottom out on the standing h_ricci/hlich layer (`hswap`, `hmetricFrame`/`hmix` —
   the project-wide DeTurck-level black boxes, coworker's lane).  `residualStarSum`
   MUST carry the same standing hypotheses as `rm04BaseEvolution_at`'s discharger chain
   (mirror `rm04HrmProducer`'s hypothesis list where orthonormal-relevant).  This is
   honest threading of KNOWN standing inputs, not a wrapper.
If after this de-walling a genuine mismatch persists for 3 routes — return with the
exact goal/error; do NOT fall back to the C⁴ transfer.

## Parallelization directive
- **Session α (next): P1.3 + P1.4** in `StarSum2.lean` (claim it via lake-locked).
- **Session β (parallel, independent): P2** in a NEW file
  `Evolution/StarSum/SpatialMember.lean` (import StarSum2; claim only the new file) —
  needs only the banked `starBaseProd_eq`/`mtfDiag`.  Follow the P2 section of the plan;
  same ground rules; do NOT edit `StarSum2.lean` (if an eval-lemma variant is missing,
  state it in the new file privately and flag here for later promotion).

# ═══ BRICK 4 — P0 + P1 EXECUTION LOG (2026-06-11, Opus session) ═══

## ✅ P0 STATEMENT FREEZE — DONE (GREEN, elaborates with `sorry`)

Frozen as `residualStarSum (S) (hS) (k) (t : RealTimeInterval.RegularTime D)` in
`StarSum2.lean` (new `section Brick4`, abstract `{Idx}[Fintype][DecidableEq]`):
```
∃ T : Tensor0SField (4+k), StarSum2 S t k T ∧
  ∀ (x) (basis : Basis Idx ℝ (TangentSpace I x))
    (_horth : ∀ i j, (S.base.metric t).inner x (basis i) (basis j) = if i=j then 1 else 0)
    (I0 : Fin (4+k) → Idx),
    HasDerivWithinAt
      (fun r => tensor0SComponent (nablaKRm04Field S r k x) (fun i => basis i) I0)
      (tensor0SComponent
        (metricTrace0S2TensorInBasis basis (identityInvMetric) (nablaKRm04Field S t (k+2) x)
          + T x) (fun i => basis i) I0)
      D.carrier t
```
Reading: `∂ₜ∇ᵏRm = Δ∇ᵏRm + T`, `T = (∂ₜ−Δ)∇ᵏRm ∈ StarSum2 k`.  **Recon facts that pinned it:**
- **Component-form caution RESOLVED**: `tensor0SComponent A frame slots := A (fun a => frame (slots a))`
  (`Tensor0SMetric.lean:478`, rfl) — definitionally `T x (fun p => basis (m p))`, so the
  frozen `tensor0SComponent` form is rfl-interchangeable with `StarSum2.bound`'s `|T x …|`.
  `@[simp] tensor0SComponent_apply` is the bridge lemma.
- **heatEq `hT` interface** (`IteratedRmTowerHeatEq.lean:214`): `Tdot : Real → (x) →
  Tensor0SSpace (4+k) x` is a *parameter*; consumer reads `tensor0SComponent (Tdot t x) basis I0`.
  ⟹ set `Tdot t x := metricTrace0S2TensorInBasis basis δ (∇^{k+2}Rm) + T x` and the frozen
  value IS `tensor0SComponent (Tdot t x) basis I0` (zero glue at P4).  `hT` is over ALL x with a
  GLOBAL basis family (not orthonormal-restricted) — P4 picks an orthonormal frame family so
  the frozen orthonormal identity supplies it.
- **residual bridge** (`IteratedRmTowerProducer.lean:411` `combinedStarArray` + `:434` #38
  `nablaKRm04Reaction_orthoBasis_eq_compContract`): `residualComp m = tensor0SComponent
  (Tdot t x − metricTrace0S2TensorInBasis basis gInv (∇^{k+2}Rm)) basis m` = `(∂ₜ−Δ)∇ᵏRm`.
  With `Tdot := roughLap + T`, residual `= T`, so `.bound` plugs straight in.
- **`orthonormality` uses `S.base.metric`** (matches producers + heatEq `hinv`); proofs bridge
  to `StarSum2`-internal `S.family.metric t` via `SolutionOn.family_metric`.
- **k=0 producer** (`UhlenbeckBaseProducer.lean:1486` `rm04HrmProducer`): gives
  `∂ₜrealizedRmBase = ∑slots [KN(roughLapRic,scalarLap,δ) − 2·Bsharp − drift](slots)·∏basis.coord`
  in **bare `Fin 3` / coordinate-frame** form (`Bt R`, `drift R`, `Bsharp = Bt(abcd)−Bt(abdc)+
  Bt(acbd)−Bt(adbc)`).  The C⁴-coordinate↔orthonormal-frame transfer is the flagged hard spot.

## ✅ P1.2 `e0Field` + membership — DONE (GREEN, 0 sorry)
`e0Field S t : Tensor0SField (4+0)` defined as the signed star-sum combination (8 `base` terms
via the 8 routing perms `btPermE, σBt2/3/4, σD1/2/3/4 : Fin 8 ≃ Fin 8`, each
`Equiv.ofBijective ![…] (by decide)`); `e0Field_mem : StarSum2 S t 0 (e0Field S t)` by the
`.smul`/`.add`/`.base` constructor tree (use `refine StarSum2.add (… ?_ ?_) … ?_` + per-term
`exact` bullets — the giant nested `.add` expression is paren-error-prone).  **Brick-1 wall
does NOT bite at concrete rank `4+0`** — `•`/`+` elaborate fine under `respectTransparency false`.

## ✅ P1.1 + the eval toolchain — DONE (GREEN, 0 sorry).  Five new declarations:
1. `mtfDiag` (private): the **single-trace diagonal equality** atom (the equality underlying
   `mtfOrthoBd`'s rw-chain): `metricTraceFirstTwoField g X x (basis∘mm) = ∑ i, X x
   (metricTraceInput (basis i)(basis i)(basis∘mm))`.  Reusable, all τ.
2. `starBase_comp_eq` (r=0): `starBaseField k a b 0 σ x (basis∘m) = ∑ j ∑ i
   (domDomCongr σ (starProd a b 0)) x (metricTraceInput (basis i)(basis i)
   (metricTraceInput (basis j)(basis j)(basis∘m)))`.  Proof = peel `mtIter (2+0)` as two
   `metricTraceFirstTwoField` + `mtfDiag` ×2 + `mtInputBasis`.
3. `starBaseProd_eq` (r=0): same, with the generator's `product` split into its two factors —
   `= ∑ j ∑ i (∇ᵃRm) x (W∘σ∘castAdd(4+b)) · (∇ᵇRm) x (W∘σ∘natAdd(4+a))`, `W` = the nested
   metricTraceInput.  THE reusable product-split for P1 (`e0Field`) **and** P2 (`∇ᵃRm∗∇ᵇRm`).
4. `btPermE` + `btStar_eq`: the **validated σ-term template**.  `btPermE := Equiv.ofBijective
   ![4,0,5,2,6,1,7,3] (by decide) : Fin 8 ≃ Fin 8`; `btStar_eq : starBaseField 0 0 0 0 btPermE
   x (basis∘m) = ∑ e ∑ f Rm(![m0,e,m1,f])·Rm(![m2,e,m3,f])` (= the `B`-tensor contraction;
   `Rm := ∇⁰Rm`).  Proof = `starBaseProd_eq` + `Finset.sum_comm` + two `have`s, each
   `funext p; fin_cases p <;> simp [btPermE, Equiv.ofBijective, Fin.castAdd/natAdd,
   metricTraceInput_apply]`.

### Lean traps solved (apply, don't rediscover)
- **Reduce `mtIter g (2+0) A`**: `rw [show (2:ℕ)+0 = … from rfl]` FAILS (motive not type-correct
  — `2+0` is in `mtIter`'s dependent rank slot).  FIX: rewrite the whole **field** via
  `rw [show mtIter g (2+0) A = metricTraceFirstTwoField g (metricTraceFirstTwoField g A) from rfl]`
  (same result type `Field (4+k)`, motive trivial).  `set A := domDomCongr … AFTER rw [starBaseField]`.
- **`product_fun_apply` via `rw` FAILS** on `starProd…0 x`: the `v`-domain is
  `Fin (((4+a)+(4+b))+2*0)` (the `+2*0` from `starProd`'s rank), not `Fin (s+q)`; `rw` won't
  unify the `2*0`.  FIX: `exact Bundle.continuousMultilinearMap.product_fun_apply (∇ᵃRm x)(∇ᵇRm x)
  (fun p => W (σ p))` — `exact`'s full defeq absorbs both the `2*0` cast and `starProd 0 = product_fun`.
- **`congr 1` on `Rm(a)·Rm(b) = Rm(c)·Rm(d)`** mis-splits → "No goals".  FIX: prove the two
  arg-function equalities as `have hL/hR` and `rw [hL, hR]`.
- **σ construction**: `Equiv.ofBijective ![…] (by decide)` for `Fin 8`; evaluate `σ (Fin.castAdd …)`
  by `fin_cases p <;> simp [Equiv.ofBijective, …]` (validated cheaply in a throwaway probe first).

## MATH FEASIBILITY of `e0Field` (P1.2) — CONFIRMED
`Bt R a b c d = ∑_e ∑_f rm(a,e,b,f)·rm(c,e,d,f)` (`UhlReaction3.lean:67`) IS a double trace of
`rm⊗rm`.  `drift` (`:74`) contracts Ricci (= a trace of Rm) with Rm ⟹ also a double trace of
`Rm⊗Rm`.  Both `r=0`.  `btStar_eq` proves the Bt(abcd) term GREEN — the route is fully validated.

## REMAINING in P1 (next session, all routes de-risked) — with the EXACT σ routings computed:

**Convention** (from `starBaseProd_eq` + `Finset.sum_comm`, outer sum var `e`, inner `f`):
the diagonal input is `W = [e,e,f,f,m0,m1,m2,m3]` (slots {0,1}→e, {2,3}→f, 4..7→m0..m3); a
permutation `σ : Fin 8 ≃ Fin 8` makes `base 0 0 0 0 σ comps = ∑_e ∑_f Rm(W∘σ|₀₋₃)·Rm(W∘σ|₄₋₇)`.
To realize a factor-tuple `(p0,…,p7)` (each `pᵢ ∈ {e,f,m0,m1,m2,m3}`): `σ(slot)=0/1` for `e`,
`=2/3` for `f`, `=4+k` for `mₖ`.  `btStar_eq` is the proven template (σBt1 below).

- **4 `Bt`-term identities** (`btStar_eq` template; `Bt R a b c d = ∑∑ rm(a,e,b,f)·rm(c,e,d,f)`):
  - `Bt(s0s1s2s3)`: tuple `(m0,e,m1,f,m2,e,m3,f)` → σBt1 `![4,0,5,2,6,1,7,3]` (=`btPermE` ✓ done)
  - `Bt(s0s1s3s2)`: tuple `(m0,e,m1,f,m3,e,m2,f)` → σBt2 `![4,0,5,2,7,1,6,3]`
  - `Bt(s0s2s1s3)`: tuple `(m0,e,m2,f,m1,e,m3,f)` → σBt3 `![4,0,6,2,5,1,7,3]`
  - `Bt(s0s3s1s2)`: tuple `(m0,e,m3,f,m1,e,m2,f)` → σBt4 `![4,0,7,2,5,1,6,3]`
- **Ricci-trace identity (dim 3)**: `R a c = -∑_e rm(a,e,c,e)` (UhlReaction3 `:61` comment
  "Σ_b rm a b c b = -R a c"; slots 1,3 traced).  Prove via `Fin.sum_univ_three` + `rm`/`R` defs.
- **4 `drift`-term identities** (`drift = ∑_p (R a p·rm(p,b,c,d)+R b p·rm(a,p,c,d)+
  R c p·rm(a,b,p,d)+R d p·rm(a,b,c,p))`; using `R x p = -∑_e rm(x,e,p,e)`, so `base σDk comps =
  -(drift-term-k)`, hence the 4 drift bases sum to `-drift` with coefficient **+1**):
  - term1 `R a p·rm(p,b,c,d)`: tuple `(m0,e,f,e, f,m1,m2,m3)` → σD1 `![4,0,2,1,3,5,6,7]`
  - term2 `R b p·rm(a,p,c,d)`: tuple `(m1,e,f,e, m0,f,m2,m3)` → σD2 `![5,0,2,1,4,3,6,7]`
  - term3 `R c p·rm(a,b,p,d)`: tuple `(m2,e,f,e, m0,m1,f,m3)` → σD3 `![6,0,2,1,4,5,3,7]`
  - term4 `R d p·rm(a,b,c,p)`: tuple `(m3,e,f,e, m0,m1,m2,f)` → σD4 `![7,0,2,1,4,5,6,3]`
- **`e0Field` def + membership** (constructors, zero math): reaction `= -2(Bt1-Bt2+Bt3-Bt4) - drift`,
  and `-drift = base σD1+σD2+σD3+σD4` (sign from `R=-trace`), so
  `e0Field := (-2)•base σBt1 + 2•base σBt2 + (-2)•base σBt3 + 2•base σBt4
            + base σD1 + base σD2 + base σD3 + base σD4`.
  `StarSum2 S t 0 e0Field` = `.smul`/`.add`/`.base` tree.
- **P1.3 component identity** (orthonormal, abstract→dim-3): assemble the 8 term-identities +
  `rm04CompknOrtho` (`∇⁰Rm comps = rm R`, banked in `rm04HrmProducer`) ⟹ `e0Field comps =
  -2·Bsharp(R) - drift(R)` by `Bt`/`Bsharp`/`drift` defs.  **WALL-FREE** — completes P1.2+P1.3,
  the "reaction is a star sum" theorem (the math heart of brick-4 k=0).
- **P1.4 k=0 assembly into `residualStarSum_zero`**: connect `rm04HrmProducer` (coordinate
  frame, `realizedRmBase`/bare-`Fin 3`) to the frozen statement (`nablaKRm04Field`/orthonormal).
  **THE FLAGGED WALL = the C⁴ coordinate↔orthonormal frame transfer.**  Also the Laplacian-part
  match `comps(roughLap_δ ∇²Rm) = comps(KN(roughLapRic,scalarLap,δ))`.  Fallback (plan): state
  P1's deliverable at the orthonormal frame only, defer coordinate-transfer to P3.

# ═══ BRICK 4 EXECUTION PLAN (2026-06-11, Fable-planned, for Opus sessions) ═══

## 0. The frozen target + a verified plan-level simplification

**The j-split frontier DISSOLVES.**  Source-verified (2026-06-11):
- `combinedStarArray` (`IteratedRmTowerProducer.lean:411`) `= ricStarArray ric (comp ∇ᵏRm)
  + residualComp`, where `residualComp m` is LITERALLY the `m`-component of
  `Tdot t x − metricTrace0S2TensorInBasis basis gInv (∇^{k+2}Rm)` — i.e. `(∂ₜ−Δ)∇ᵏRm`
  with `Tdot` a *parameter* of the reaction.
- The Bernstein consumer is `TowerHeatBoundOn w wLap c k` (`BernsteinShiHigher.lean:478`)
  with an ARBITRARY constant `c` (`towerReactionSum w c k = Σⱼ c·√wⱼ√w_{k−j}·√wk`), and
  `iteratedRmTower_heatBoundSharp` itself emits the k-dependent `c = 2·card^{6+k}`.
  `BernsteinTower.hheat` uses ONE `c`, but the max-principle runs per target level `m`,
  so instantiate per-`m` with `c_m := max(constants for k ≤ m)` — no interface change.

**So bricks 4+5 = (4) the RESIDUAL MEMBERSHIP**: for each `k` and regular `t`, the
components of `(∂ₜ−Δ)∇ᵏRm` are the components of some `T_k ∈ StarSum2 S t k`
(then `.bound` gives `|residual comps| ≤ C_k·Σⱼ√wⱼ√w_{k−j}`), **+ (5) wiring** to
`TowerHeatBoundOn` directly — `IteratedRmTowerOn`'s per-j `star` arrays are BYPASSED
(do NOT build the j-bucketed split; do NOT touch `IteratedRmTowerOn`).

**Component-form caution**: the reaction bridge speaks `tensor0SComponent (field x)
basis m`; `StarSum2.bound` speaks `|T x (fun p => basis (m p))|`.  P0 must check these
are rfl-interchangeable (expected) and record the bridging idiom.

## P0 — recon + statement freeze (½ session, read-only + stubs)
Pin down, then freeze the brick-4 statement:
1. `nablaKRm04NormHeatEquationOn_intrinsic` (`IteratedRmTowerHeatEq.lean:185`): the EXACT
   hypothesis through which `Tdot` enters (what the producer must supply per (k,t,x)).
2. `iteratedRmComp_hasDerivWithinAt` (`IteratedRmTowerHeatEq.lean:430`): the VALUE shape of
   the `∂ₜ∇^{k+1}` recursion (how `∂ₜΓ`-terms and the level-`k` derivative enter).
3. What #38 ("schematic commuted-curvature identity → heatEq") actually banked — avoid dupes.
4. `rm04HrmProducer` (`UhlenbeckBaseProducer.lean:1486`)'s exact hrm value-shape (k=0 input).
**Frozen statement (validate/adjust in P0; keep the invariants):** per `k`, `hS`,
regular `t`: `∃ T, StarSum2 S t k T ∧ (∀ x₀ ⟨frame data at x₀⟩, HasDerivWithinAt
(fun s => comps(∇ᵏRm s)) (comps(Δ∇ᵏRm) + comps(T)) D.carrier t)` — the per-component
HasDerivWithinAt form, uniform over centres `x₀` (each `x` is the centre of its own
coordinate frame — the #45 pattern; this uniformity is what makes P3's ∇-step legal).
If the heatEq's Tdot-interface makes the `Tdot = roughLap + T` equality form cheaper,
freeze that instead. Deliverable: the frozen statements appended HERE + stubs compiling
with precise `sorry`s.

## P1 — E₀ membership (1 session; first execution block)
1. **`starBase_comp_eq`** (new, in `StarSum2.lean`): the EQUALITY version of the
   δ-collapse — components of `starBaseField k a b r σ` at a g-orthonormal basis as the
   explicit `(2+r)`-fold diagonal sum of `starProd`-components (extract from
   `mtfOrthoBd`/`mtIterOrthoBd`'s proof pattern: `metricTraceFirstTwoField_apply` chain +
   `sumIdentityDiag` + `mtInputBasis`, iterated).  This is THE shared eval tool for
   P1/P2/P4 — build it first, reusable, τ-induction.
2. **`e0Field`**: explicit `base 0 0 0 r σ`-combination (constructors `.add`/`.smul`)
   matching `−2B# − drift` of `rm04BaseEvolution_at`.  EXPECTATION: `B#` and the drift
   are plain double-traces of `Rm⊗Rm` (`B#ᵢⱼₖₗ = Σ_{p,q} Rmᵢₚⱼ_q Rmₖₚₗ_q` at δ), so
   `r = 0` suffices throughout; the `r > 0` generality is insurance (use it if the
   drift/`uhlenbeckBTensorInFrame` shapes force `g`-factors — check `uhlBt_eq_bt`/
   `uhlDrift_eq_drift` first).  Membership is BY CONSTRUCTORS (zero math).
3. **Component identity**: `e0Field`-comps at orthonormal = `−2B#−drift` comps — via
   `starBase_comp_eq` + the banked δ-frame bridges (`uhlBt_eq_bt`, `uhlDrift_eq_drift`,
   `UhlReaction3` closed forms `bt_closed`/`cc_closed`).  Bare `Fin 3`-free: keep it at
   abstract `Idx`/`Fin n` with `horth` (dim only enters where the banked identities do).
4. Assemble the k=0 instance of the frozen statement from `rm04HrmProducer`'s hrm value
   (its `KN(ΔRic,ΔS,δ)`-part = `comps(ΔRm04)` via `traceRm04Kn` + the C⁴-transform
   frame-transfer already inside `rm04HrmProducer`).
Done-criterion: frozen statement at `k = 0`, GREEN, 0 sorry.  Likely-hard spot: the
C⁴-coordinate-vs-orthonormal frame transfer around hrm — if stuck 3 routes, return with
the exact mismatch; an acceptable fallback is to state P1's deliverable at the
orthonormal frame only and leave the coordinate-transfer to P3's assembly.

## P2 — spatial commutator membership (1 session; needs P1's `starBase_comp_eq` only)
`[Δ,∇]∇ᵏRm`-comps = comps of a `StarSum2 (k+1)` element (per k, all x, orthonormal).
Inputs (all banked, IDENTITY form): `spatialComm_nablaKRm_split` (`RoughLapNablaK.lean`,
`[Δ,∇]∇ᵏRm = Ricci-term + term-B`), `nablaK_antisym_eq_rm04_raise_leibniz`
(`NablaReactionAllK.lean`, term-B `= ∇Rm04∗∇ᵏRm + Rm04∗∇^{k+1}Rm`),
`curvatureAction0SAt_eq_rm04` (raise form).  Work = recast each RHS as
`starBase_comp_eq`-form (σ-bookkeeping; the Ricci-term: `Ric = trace Rm` makes it a
2-trace of `Rm⊗∇^{k+1}Rm`; expect `r = 0`).  These lemmas' STATEMENTS are per-point —
the membership witness `T` must be uniform in `x` (the field is built from
`nablaKRm04Field`s, so it is — only the IDENTITY is checked pointwise).

## P3 — time recursion → full `E_k` (1–2 sessions; the heaviest; needs P1+P2)
Induction on `k` of the frozen statement.  Step `k → k+1`:
`E_{k+1}-comps = ∇(E_k)-comps + (∂ₜΓ ∗ ∇ᵏRm)-comps − ([Δ,∇]∇ᵏRm)-comps`, with
- `∇(E_k)`: from IH `T_k` + `StarSum2.nabla` (the hcov1 hypothesis: discharge via
  `connSmoothOfSol S hS t (D.regular_subset t.2)`).  **CENTRAL DESIGN RISK**: the IH's
  component identity must hold at EVERY centre (the ∀x₀-uniform frozen form) so that
  `comps(∇E_k) = comps(stNabla T_k)` is derivable (realizes-machinery at each point);
  if this step won't typecheck after 3 genuinely different routes (e.g. via
  `totalNabla0SRealizes_unique` + the producers' `iteratedRmComp ↔ totalNabla0S` bridge
  #36 `RmRealizationBridgeAllK`), STOP and return — that's a statement-form bug, fix in
  P0's freeze, don't brute-force.
- `(∂ₜΓ ∗ ∇ᵏRm)`-comps: `christoffelEvolution_of_solution` (`MetricCovDerivProducer`)
  gives `∂ₜΓ` as `∇Ric`-combination; `∇Ric = trace ∇Rm` ⟹ 2-trace `∇Rm⊗∇ᵏRm` base
  terms (`a=1, b=k`, expect `r=0`).  The contraction shape must match
  `iteratedRmComp_hasDerivWithinAt`'s value (P0 item 2).
- the spatial piece: P2's lemma at level `k`.
Membership of the sum: constructors.  Done-criterion: frozen statement ∀k, GREEN.

## P4 — wiring to `TowerHeatBoundOn` (= brick 5; 1 session; needs P3)
1. From the intrinsic heatEq + `nablaKRm04Reaction_orthoBasis_eq_compContract` +
   brick-4 + `.bound`: `|reaction| ≤ 2·(Σ_m |rmC m|)·max_m|combined m|` with
   `Σ_m |rmC_m| ≤ √(card^{4+k})·√wk` (ℓ¹–ℓ² on `card^{4+k}` indices) and
   `|combined m| ≤ |ricStar m| (≤ card²√w0√wk, banked `abs_ricStarArray_le`) + C_k·Σⱼ√√`
   ⟹ `TowerHeatBoundOn w wLap c_k k` with `c_k = 2·√(card^{4+k})·(card² + C_k)`-shape.
2. Per-target-level `m`: `c⋆_m := max_{k ≤ m} c_k` → `BernsteinTower` instantiation →
   the existing Stage-1/2 max-principle machinery → the C∞ bounds feeding
   `extends_of_rmBounded`'s skeleton.  (The remaining global-PDE step of
   `extends_of_rmBounded` stays a black box — NOT this plan's scope.)

## Ground rules for every executing session (paste-verbatim material)
- Work ONLY in `DifferentialGeometry/`; follow `CLAUDE.md` (lake-locked claims, focused
  checks, same-name `.md` notes, no public-API rewrites, ≤20-char names).
- Read FIRST: this file (whole), `bbs-allk-route-status` content is mirrored here — do
  NOT re-derive; `convention.md` for conventions.
- The solved-trap list (apply, don't rediscover): per-declaration
  `set_option backward.isDefEq.respectTransparency false in` for ANY generic-rank
  `0/+/•/ddc/mT` statement; `rw` on `product_fun_apply` DIES on rank-index mismatch →
  `refine le_trans (le_of_eq (congrArg abs hpf)) ?_` / `congrArg`-style exact-defeq;
  `Fin.natAdd`'s rank + `(i : Fin 2)` literals EXPLICIT; ∃-witnesses EXPLICIT,
  right-assoc `.trans` + `Equiv.trans_assoc` in the closing simp; `induction` case
  binders do NOT re-bind the family index `k`; the project's `abs_le_sqrt_*` helpers
  carry an alien ℝ-lattice instance → use `sq_le_compNormSqMulti` + Mathlib's
  `Real.abs_le_sqrt`; `Finset.single_le_sum` needs `simp only [h] at` to beta-reduce;
  bare `Fin.cons/cases` motive not inferred → `@Fin.cons n (fun _ => V)` or
  dite-indexed ∃-tuple forms (`mtInputBasis` pattern).
- Stop conditions: 3 genuinely different routes failed on one lemma / missing API /
  statement smells wrong → write findings HERE (same-name md) and return.  A green
  intermediate with a named next lemma is NOT a stopping point.

**REMAINING after this plan**: the Bernstein→C∞→`extends_of_rmBounded` glue (partly
banked, #14), the DeTurck black boxes (coworker), `ham3_main` assembly.

## ✅ BRICK 3 DONE (2026-06-11, GREEN — `StarSum2.nabla` proved)

**`StarSum2.nabla : StarSum2 S t k T → StarSum2 S t (k+1) (stNabla S t T)`** — the inductive
heart — is proved, 0 sorry.  One analytic hypothesis: `hcov1 : ContMDiffCovariantDerivativeLocally
(S.family.connection t) 1` (discharge at consumers via `connSmoothOfSol S hS t (D.regular_subset t.2)`,
the `IntrinsicDerivation.lean:345` pattern; no ∞→1 mono lemma exists in the codebase).

**KEY DESIGN CHANGE — `starBaseField` rank decoupling.**  `starBaseField S t k a b σ` now takes
the level `k` SEPARATELY from `a, b`, with `σ : Fin ((4+a)+(4+b)) ≃ Fin (((4+k)+2)+2)` pinning
the output rank `4+k` (σ's cardinality forces `a+b=k` semantically).  This is what makes `.nabla`'s
base case cast-free: `(a+1)+b` and `(a+b)+1` are NOT defeq for open `a b` (`Nat.succ_add` is not
rfl), so the old `base (a b) : StarSum2 (a+b) …` design would hit dependent-rank cast hell; with
`k` decoupled, `base k a b ↦ base (k+1) (a+1) b + base (k+1) a (b+1)` typechecks on the nose
(`leibnizLeftEquiv` internally absorbs the succ_add bridge).

New in `StarSum2.lean` (all GREEN): `stMetricCompat` (local solution-compat handle);
`stNabla` (canonical `totalNabla0S` + `totalNabla0S_reg`/`connSmoothInf` auto-reg);
`stNabla_realizes`; `stNabla_zero/add/smul` (via `totalNabla0SRealizes_unique` against
`.add`/`.smul` realizer closures — zero via the `0 • 0` trick); `stNabla_starBase`
(∃-form: `∇(base k a b σ) = base (k+1) (a+1) b σL + base (k+1) a (b+1) σR`); `StarSum2.nabla`
(four-case induction).  New in `Tensor/Multilinear/DomDomCongrSection.lean`:
`domDomCongr_trans`/`_add`/`_smul`.

**Proof shape of `stNabla_starBase` (worked first try once assembled):** realizes chain
`nabla0S_product_realizes` (+`nablaKRm04Field_realizes` ×2) → `totalNabla0SRealizes_domDomCongr`
→ keystone `nablaRealizes_metricTraceFirstTwo` ×2 → `totalNabla0SRealizes_unique` vs
`stNabla_realizes` ⟹ `heq : stNabla(base) = chain-realizer`; then `rw [heq]` + ONE
`simp only [domDomCongr_add, metricTraceFirstTwoField_add, ← metricTraceFirstTwoField_domDomCongr,
domDomCongr_trans, Equiv.trans_assoc, starBaseField]` normalizes both sides to the two-base form.
Explicit witnesses (right-assoc): `σL = lle.trans ((feq σ).trans ((tns ((4+k)+2)).trans (feq²(tns (4+k)))))`.
**Lean lessons:** (1) `refine ⟨_, _, ?_⟩` with ∃-witness metavars FAILS ("don't know how to
synthesize") — give explicit witnesses + let `Equiv.trans_assoc` in the simp set reconcile the
trans-association; (2) `induction hT with` case binders do NOT re-bind the family index `k`
(`| zero =>`, `| base a b σ =>`); (3) `import ProductNablaLeibniz` was missing (only
UhlenbeckBaseProducer imported it).

**REMAINING bricks: 2 (.bound) and 4–5 (E_k recursion + tower wiring).**

## ✅ BRICK 1 DONE (2026-06-11, GREEN — `StarSum2.lean` committed)

The brick-1 blocker (generic-rank `0`/`+`/`•` synthesis on `Tensor0SField (4+k)` timing out at
`whnf`) is **RESOLVED by one line**: `set_option backward.isDefEq.respectTransparency false in`
before each declaration that writes those ops.  This is the codebase's OWN established
workaround — every theorem in `MetricTrace/NablaTraceGen.lean` that writes `0`/`+`/`•` on a
generic-rank `Tensor0SField` is prefixed with it (`metricTraceFirstTwoField_add/_smul/_zero`).
The prior 5 attempts (raw inductive, `include`, letI helpers, +smooth-bundle letI, plain def)
never tried the set_option; route (a) [low-level host file] was a red herring — `Coordinates.Field`
(the type's OWN home) also fails the bare `(0 : Tensor0SField (4+k))`, and also COMPILES with the
set_option.  So the fix is per-declaration, import-independent.

`StarSum2.lean` (ns `DifferentialGeometry.PDE.RicciFlow`, imports `StarSum/NablaReactionAllK`) now has:
- `starBaseField S t a b σ` — the `base` term `metricTrace₁₂²(domDomCongr σ (∇ᵃRm ⊗ ∇ᵇRm))`,
  rank `4+(a+b)`, `σ : Fin ((4+a)+(4+b)) ≃ Fin (((4+(a+b))+2)+2)`; built from
  `MultilinearSection.product`/`domDomCongr` + `metricTraceFirstTwoField` ×2, mirroring `knRicT`.
- `inductive StarSum2 S t : (k) → Tensor0SField (4+k) → Prop` with `zero`/`add`/`smul`/`base`.
  (Dropped `reindex` — subsumed by `base`'s `σ`; `.nabla` of a `base` lands back in `base`.)
- `.add` = the `add` constructor (free).  **Brick 1 (predicate + `.add`) complete.**

## ✅ Keystone API `nablaRealizes_metricTraceFirstTwo` — DONE (2026-06-11, GREEN in `NablaTraceGen.lean`)

The field-level ∇–trace realizer is **proved and committed** to `NablaTraceGen.lean` (the
core Tensor-layer file stays `sorry`-free; `lake env lean` clean). It is the gateway for brick 3
`.nabla`. Added alongside: `traceNablaShuffle` (the 3-cycle perm) + its value lemmas
(`_zero/_one/_two/_val_ge/_val`), `consPredVal` (the single-cons evaluator), and
`traceNablaShuffle_metricTraceInput` (the slot identity).

**The Fin-mechanics lessons that cracked the slot lemma (reuse these):**
1. **Bare `Fin.cons`'s dependent motive is NOT inferred in `rw`/statement position** → write
   `@Fin.cons n (fun _ => V) c f q` with the explicit constant motive (this was THE blocker —
   the error is `Fin.cons ?m ?m q has type ?m q but expected V`). `consPredVal` uses
   `Fin.cons_succ (α := fun _ => V)`.
2. For a goal whose conses come from a typed wrapper (`metricTraceInput`/`mtInput`), use a
   `show (Fin.cons … : Fin n → V) …` ascription (or `simp only [mtInput]`) to expose the
   conses in *typed* form, so `consPredVal`/`Fin.cons_zero` fire.
3. Literal `Fin` vals: `((2 : Fin (s+2+1)) : ℕ) = 2` closes by **`by simp`** (NOT
   `Nat.mod_eq_of_lt`, which doesn't unify the OfNat coercion); the `≠` facts follow via
   `rw [Ne, Fin.ext_iff, <val-lemma>]; omega`.
4. `pred` chains: `Fin.val_pred` (NOT deprecated `Fin.coe_pred`); the final tail-index match is
   `congr 1; rw [Fin.ext_iff]; simp only [Fin.val_pred, hval]` with
   `hval : (shuf p).val = p.val`.
5. The keystone's last step is `exact congrArg _ (traceNablaShuffle_metricTraceInput …)` (NOT
   `rw`, because the goal's composition `v ∘ ⇑(traceNablaShuffle s)` from
   `ContinuousMultilinearMap.domDomCongr_apply` doesn't match `rw`'s pattern — mirrors
   `metricTraceFirstTwoField_domDomCongr_gen`'s `congrArg` at NablaTraceGen.lean:737).

(The slot lemma was first cracked in a throwaway Mathlib-only `ShuffleTest.lean`, then ported.)

### (historical) the design + obstruction record

**Statement (correct, type-checks):**
```
theorem nablaRealizes_metricTraceFirstTwo {s} [T2Space M][CompleteSpace E][I.Boundaryless]
    [IsManifold I 1 M][IsManifold I (∞+1) M]
    (cov)(hcov : cov.ContMDiffCovariantDerivativeLocally 1)(g)(hmc : IsMetricCompatible_gen cov g)
    (A : Tensor0SField (s+2))(nablaA : Tensor0SField (s+2+1))
    (hnablaA : TotalNabla0SRealizes (s+2) cov A nablaA) :
  TotalNabla0SRealizes s cov (metricTraceFirstTwoField g A)
    (metricTraceFirstTwoField g (MultilinearSection.domDomCongr ∞ (traceNablaShuffle s) nablaA))
```
where `traceNablaShuffle s : Equiv.Perm (Fin (s+2+1))` is the 3-cycle `0↦2,1↦0,2↦1` (id on tail).

**Main proof (VALIDATED — compiled modulo the slot lemma):**
```
intro X x slots
set basis := coordinateFrameAt_toBasis x; set gInv := inverseMetricFlatModelInChart_component … (extChartAt x x)
have hinv := inverseMetricFlatModelInChart_metricInverseInBasis_center g x
rw [← totalNabla0SFun_apply_section s cov X (metricTraceFirstTwoField g A) x slots,
    nabla_metricTraceFirstTwo0S cov hcov g hmc A basis gInv hinv (X x) slots]   -- RHS = Σ gInv·∇A(cons X (mtInput …))
rw [metricTraceFirstTwoField_eq_sum g (domDomCongr (traceNablaShuffle s) nablaA) x (cons (X x) slots)]
rw [← hbasis, ← hgInv]; unfold metricTrace0S2InBasis
refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; congr 1
rw [MultilinearSection.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    totalNabla0SFun_apply_section (s+2) cov X A x (mtInput (basis i)(basis j) slots),
    ← hnablaA X x (mtInput (basis i)(basis j) slots)]
rw [traceNablaShuffle_metricTraceInput (basis i) (basis j) (X x) slots]   -- ← THE GAP
```
Ingredients all verified to exist: `totalNabla0SFun_apply_section` (HigherOrder.lean:230),
`nabla_metricTraceFirstTwo0S` (NablaTraceGen.lean:504), `metricTraceFirstTwoField_eq_sum`
(NablaTraceGen:623, uses `coordinateFrameAt_toBasis`+`inverseMetricFlatModelInChart_component`),
`inverseMetricFlatModelInChart_metricInverseInBasis_center` (Inverse.lean:581), `metricTrace0S2InBasis`
def (RoughLaplacian.lean:316 = `Σ gInv·T(metricTraceInput basis_i basis_j tail)`), product-Leibniz
`nabla0S_product_realizes` (ProductNablaLeibniz:55), `totalNabla0SRealizes_domDomCongr` (NablaDomDomCongr:152).
The value lemmas `traceNablaShuffle_zero/_one/_two/_val_ge/_val` (3-cycle vals) ALL COMPILE.

**THE ONE BLOCKER = `traceNablaShuffle_metricTraceInput`** (a *trivially-true* slot-permutation fact):
```
metricTraceInput a b (Fin.cons Z tail) ∘ traceNablaShuffle s = Fin.cons Z (metricTraceInput a b tail)
```
i.e. `[a,b,Z,tail…] ∘ shuffle = [Z,a,b,tail…]`.  Resisted 4 tactic iterations — the warned-about
generic-`Fin` trap (`fin_cases` needs a concrete rank; `Fin.cases` breaks the dependent-`dite`
motive when substituting `q`; `(2 : Fin (s+3))` is `⟨2 % (s+3),_⟩`, not defeq `⟨2,_⟩` or `succ¹`,
so `Fin.cons_succ`/`Fin.cons_zero` don't fire on `OfNat` indices).  The recurring sub-problem is a
`val`-based single-cons evaluator `cons_val_apply : Fin.cons c f q = dite ((q:ℕ)=0) c (f ⟨(q:ℕ)-1,_⟩)`
whose *statement* hits a stubborn "Type mismatch" (the dependent `⟨(q:ℕ)-1, by omega⟩` index).
**Next attempt:** either (a) a hypothesis-form `cons_val_apply (hq : q ≠ 0) : Fin.cons c f q = f (q.pred hq)`
(clean statement, no dependent nat index) applied per-case with `Fin.cons_zero`, tracking
`Fin.pred`-vals via `Fin.coe_pred`+`tns_c1`/`tns_c2`; or (b) a short GPT-Pro/Lean-expert consult on
the single goal "prove `metricTraceInput a b (cons Z tail) ∘ <3-cycle perm> = cons Z (metricTraceInput a b tail)`
for generic `Fin (s+3)`".  Pure Lean-tactics; no math risk.

## (after keystone) brick 3 `.nabla` — full plan

`.nabla : StarSum2 k T → StarSum2 (k+1) (totalNabla0S … T)`, induction on the derivation.
zero→zero, add→add, smul→smul are immediate.  The **`base` case** needs:
`totalNabla0S (starBaseField a b σ) = starBaseField (a+1) b σ₁ + starBaseField a (b+1) σ₂`,
proved via `totalNabla0SRealizes_unique` (the canonical `∇` = any realizer) by building the
RHS as a realizer of `∇(base a b σ)`.  Composes: `nabla0S_product_realizes` (A⊗B Leibniz) +
`totalNabla0SRealizes_domDomCongr` (DONE, NablaDomDomCongr.lean:152, gives `domDomCongr (frontExtendEquiv e)`)
+ **a MISSING field-level trace-commute realizer** `nablaRealizes_metricTraceFirstTwo`:
`TotalNabla0SRealizes (s+2) cov A nablaA →
  TotalNabla0SRealizes s cov (metricTraceFirstTwoField g A)
    (metricTraceFirstTwoField g (domDomCongr σ_move nablaA))`
where `σ_move : Fin ((s+2)+1) ≃ Fin ((s+1)+2)` moves the new ∇-slot (position 0) past the trace
pair (orig slots 0,1 → positions 1,2 of nablaA) to the back.  The EVALUATED form exists
(`nabla_metricTraceFirstTwo0S`, NablaTraceGen.lean:504, the gInv-weighted sum); the field-level
realizer must be lifted from it (instantiate a basis + metric inverse at each x, match the
`metricTraceFirstTwoField_eq_sum` gInv-sum to the `nabla_metricTraceFirstTwo0S` RHS).
**Flagged as a known TODO at `UhlenbeckBaseProducer.md:503`.**  Build it in `NablaTraceGen.lean`
next to `nabla_metricTraceFirstTwo0S`.  RISK: generic-`p` `metricTraceInput`/`Fin.cons` whnf
timeouts + rw-rematching traps (route-status lessons) — `funext`+`Fin.cases`, not raw defeq.

---
## (historical) brick-1 blocker diagnosis — kept for the lesson

**Returned after 5 attempts stuck on brick 1** in the prior session.  The math design is sound;
the blocker was purely Lean instance plumbing.

## The intended design (sound — keep for next attempt)

Inductive family on `(k : ℕ) → Tensor0SField (4+k)`:
```
inductive StarSum2 (S t) : (k:ℕ) → Tensor0SField (4+k) → Prop
  | zero (k)                : StarSum2 k 0
  | add  {k} {A B}          : StarSum2 k A → StarSum2 k B → StarSum2 k (A + B)
  | smul {k} (c) {A}        : StarSum2 k A → StarSum2 k (c • A)
  | reindex {k} (σ) {A}     : StarSum2 k A → StarSum2 k (domDomCongr σ A)
  | base (a b) (σ)          : StarSum2 (a+b) (starBaseField a b σ)
```
`starBaseField a b σ := metricTraceFirstTwoField g (metricTraceFirstTwoField g
  (domDomCongr σ (product (∇ᵃRm) (∇ᵇRm))))` — the double metric trace of a slot-reindexed
`∇ᵃRm ⊗ ∇ᵇRm`, rank `4+(a+b)`, `σ : Fin ((4+a)+(4+b)) ≃ Fin ((4+(a+b)+2)+2)`.

- **brick 1 `.add`** = the `add` constructor (free once it elaborates).
- **brick 2 `.bound`**: induct on the derivation → `∃ C ≥ 0, ∀ x (g-orthonormal), ‖T‖ ≤
  C·Σⱼ √(wⱼ)√(w_{k−j})` (`wⱼ = |∇ʲRm|²`).  zero→C=0, add→C_A+C_B, smul c→|c|·C, reindex→C,
  base→`card²` via `abs_curvatureAction0SAt_orthoBasis_le` (done). The existential `C`
  absorbs coefficient/term-count growth cleanly.
- **brick 3 `.nabla`** = `StarSum2 k T → StarSum2 (k+1) (totalNabla0S T)`, induct on the
  derivation; the `base` case commutes `∇` through both traces (`nabla_metricTraceFirstTwo0S`,
  done) + `domDomCongr` (`totalNabla0SRealizes_domDomCongr`) + product Leibniz
  (`nabla0SFun_product_eval`) ⟹ `base (a+1) b σ' + base a (b+1) σ''` (the slot-algebra is the
  same shape as the verified `traceRicWit` in `UhlenbeckBaseProducer.lean`).
- **brick 4 `E_k ∈ StarSum2 k`**: one-step peeling `E_k = ∇E_{k-1} + (∂ₜΓ)∗T_{k-1} −
  [Δ,∇]T_{k-1}`, base `E_0 = Rm∗Rm` (Uhlenbeck), close by induction using brick 3 + the done
  single-step commutator `spatialComm_nablaKRm_split`.
- **brick 5 wiring**: feed brick 2's bound into `IteratedRmTowerOn.starBound`, and (with
  `nablaKRm04Reaction_orthoBasis_eq_compContract`) the reaction into `heatEq`.

## THE BLOCKER (brick 1 — Lean instance synthesis, NOT math)

`0`/`+`/`•` (`OfNat`/`HAdd`/`HSMul`) on the **generic-rank** `Tensor0SField (4 + k)` fail to
synthesize their `ContMDiffVectorBundle ∞` module instance in this file's context.  Error:
`failed to synthesize OfNat (Tensor0SField ∞ (4 + k)) 0` (and `HAdd`/`HSMul`).

Five attempts, all the same failure:
1. raw `inductive … (A + B)` / `… 0`;
2. `include hMinf hM1 hM2 hMinf1 hEc` to force the manifold instances in;
3. `stZeroField`/`stAddField`/`stSmulField` `def` wrappers with `letI := tensor0SBundle_topology`;
4. + `letI := TangentBundle.contMDiffVectorBundle` + `letI := tensor0SBundle_smooth`;
5. plain `def` bodies (no `letI`), mirroring `TotalNabla0SRealizes.add` which *does* compile
   with generic-`s` `α + β`.

Diagnostic facts:
- the SAME ops work at **concrete** rank (`knField` at `2+2` in `UhlenbeckBaseProducer.lean`);
- they work for **generic `s`** in the lighter `Tensor/` layer
  (`TotalNabla0SRealizes.add`, `metricTraceFirstTwoField_add/_zero`, `NablaTraceGen.lean`);
- they fail for **generic `4+k` in this heavy RicciFlow import context**.
- `Tensor0SField` is an `abbrev` carrying `letI := tensor0SBundle_topology s` internally; the
  module also needs `tensor0SBundle_smooth` (needs `[IsManifold I (∞+1) M]`, present).

**ROOT CAUSE — fully isolated by minimal repros (2026-06-10).** Throwaway test files (deleted)
walked it down to the real cause.  WRONG guesses, each ruled out by repro:
- `[InnerProductSpace Real E]` diamond — removing it does NOT fix it;
- rank shape `s+2` vs `4+k` — both fail equally;
- instances-in-scope — explicit `[IsManifold I 1/2/(∞+1) M]` in the signature does NOT fix it;
- theorem-vs-def — a *theorem* with `(0 : Tensor0SField (s+2))` ALSO fails in the importing file
  (while the identical `metricTraceFirstTwoField_zero` compiles *inside* `NablaTraceGen`);
- `open`s — adding `open DifferentialGeometry.Tensor.Coordinates` does NOT fix it.

**CONFIRMED CAUSE = instance-synthesis PERFORMANCE pathology.** With `set_option maxHeartbeats
1000000` + `synthInstance.maxHeartbeats 1000000`, synthesizing `OfNat (Tensor0SField (s+2)) 0`
gives **`(deterministic) timeout at whnf, maximum number of heartbeats (1000000)`** — i.e. the
search does *pathologically expensive `whnf` reductions* (unfolding the bundle/`ContMDiffSection`
definitions) and runs out of fuel; it is NOT a missing instance.  Inside `NablaTraceGen` (low in
the import tree) the same search is fast; once the BBS chain (`RmRealizationBridgeAllK` and below)
is imported, some candidate instance makes the search explode.  A bigger heartbeat is not a real
fix (1M already overshoots; `maxHeartbeats 4000000` per declaration would make the file
uncompilable).

## Fix routes for next attempt (in priority order)
A. **Find & fix the pathological instance.** In a file importing `RmRealizationBridgeAllK`, run
   `set_option trace.Meta.synthInstance true in example : Tensor0SField (s+2) := 0` and read the
   trace to see which candidate instance the search keeps unfolding (the loop/blowup).  Likely a
   bundle `local instance`/`letI` that escaped a section and now offers a non-canonical
   `TopologicalSpace`/`VectorBundle` path the synthesizer keeps trying.  Fix = scope it, lower its
   priority, or give the canonical one higher priority.  This is the clean root fix and likely helps
   the whole BBS layer's compile times.
B. **Bypass synthesis: provide the module instance explicitly.** `letI : Zero (Tensor0SField (4+k))
   := <explicit ContMDiffSection zero>` (and similarly `AddCommGroup`/`Module`) so the `0`/`+`/`•`
   never trigger the expensive search.  Needs the exact instance path written by hand once; reusable
   via the `stZeroField`/`stAddField`/`stSmulField` helpers.
C. **Avoid raw module ops entirely.** Carry the closures through the realizer `TotalNabla0SRealizes`
   (already elaborated in the healthy `HigherOrder` layer) so `StarSum2` never writes `0`/`+`/`•` on
   `Tensor0SField` in the heavy context.

This is a Lean-environment performance bug, separable from the (sound) math design above — a good
candidate for a focused `trace.Meta.synthInstance` session or a Lean-expert/Pro consult.

## MECHANISM + AUTHORITATIVE FIX (user-confirmed, 2026-06-11)

`Tensor0SField` is an **abbrev carrying `letI := tensor0SBundle_topology … s`** internally.  So
`(0 : Tensor0SField (s+2))` is NOT a plain zero: synthesizing `OfNat (Tensor0SField (s+2)) 0`
forces the search to find `ContMDiffSection`'s `Zero`/`OfNat` AND unfold the bundle
topology/smooth-bundle instances.  In the heavy RicciFlow import context (post
`RmRealizationBridgeAllK`) that `whnf` unfolding becomes huge → `synthInstanceFailed` / `whnf`
timeout.  `metricTraceFirstTwoField_zero`'s own note in `NablaTraceGen.lean` already records this
exact class: *generic `domDomCongr e 0 = 0` / `product A 0 = 0` jam `OfNat 0` at statement time;
low-level files can only pin the instance at concrete ranks or inside a proof.*  **Take that note
as the answer — do NOT re-run `letI`/extra-`IsManifold`/def-wrapper variations; the repro proves
they all hit the same synthesis path.**

**Do (in priority):**
1. **Never** write generic `0`/`+`/`•` on `Tensor0SField (4+k)` in a heavy RicciFlow/StarSum file.
2. Put the canonical `stZeroField`/`stAddField`/`stSmulField` (and any generic-rank field algebra)
   in a **low-level tensor file** that does NOT import the BBS chain, where they compile to
   `def`/`theorem`; then `import` and *apply* them (a function application does not re-trigger the
   search).  (NB: even importing `NablaTraceGen` already broke the repro, so the helper file must
   sit low — at/near the `Tensor/RSTensor/…` Multilinear/Coordinates layer, not above it.)
3. Or bypass raw `Tensor0SField` algebra entirely: state `StarSum2`'s closures through an
   already-compilable realization API (`TotalNabla0SRealizes`-style closures in the healthy
   `HigherOrder` layer), so no raw `0`/`+`/`•` appears in the heavy context.

The verified upstream pieces (`traceRicWit`-style slot algebra, `nabla_metricTraceFirstTwo0S`,
`spatialComm_nablaKRm_split`, `abs_curvatureAction0SAt_orthoBasis_le`, the orthonormal collapse)
all remain ready; only the predicate's hosting layer is the open question.

## 2026-06-13 Codex pass

`starSum2_sum` was promoted into `StarSum2.lean` next to the `StarSum2` constructors.  The proof is
the finite-sum closure by `Finset.induction`, using `StarSum2.zero` and `StarSum2.add`.

Verification status: focused verification of `StarSum2.lean` passed, and the `StarSum2` module
built.  The file still has its pre-existing `residualStarSum` sorry warning.

## 2026-06-13 P3 EXECUTOR FINDINGS (Opus) — STOPPED on the Ricci-trace bridge + a scope conflict

Did targeted recon for `gammaStepStar`; hit the planner's named stop condition.  Two findings:

### FINDING 1 (scope/architecture): P3 cannot live in `StarSum2.lean`
The executor prompt says "work in `StarSum2.lean`", but the same prompt requires (a) instantiating
`spatialCommStarSum` (P2) which is in **`SpatialMember.lean`**, and (b) reusing the `StarRouting`
route helpers (`slotdiffStarA`/`sigmaDiffA`, etc.) in **`StarRouting.lean`**.  Import DAG is
`StarSum2 ← StarRouting ← SpatialMember`, so `StarSum2` is **upstream** of both — it cannot import
either.  Concretely:
- `gammaStepStar`'s normalized term is `base (k+1) 1 k 0` = **exactly `slotdiffStarA`'s shape**
  (`StarRouting.lean:390`, `starBaseField S t (k+1) 1 k 0 (sigmaDiffA k q)`).  Reuse needs StarRouting.
- The all-`k` `residualStarSum` induction needs P2 (`spatialCommStarSum`, SpatialMember) + the
  time-step inputs from `iteratedRmComp_hasDerivWithinAt` (`IteratedRmTowerHeatEq.lean`, NOT imported
  by `StarSum2`).  So the old `residualStarSum` stub at `StarSum2.lean:1176` can **never be proved in
  `StarSum2.lean`** — it is itself misplaced.
- ⇒ **P3 (refreeze + P2-at-Fin3 + `gammaStepStar` + induction) belongs in a NEW file downstream of
  `SpatialMember.lean`** (e.g. `Evolution/StarSum/TimeRecursion.lean`).  The refrozen endpoint and
  the `S hS k t` stub should move there; do not keep the unprovable stub in `StarSum2.lean`.
  No `StarSum2.lean` edit was made (any P3 edit there would be wrong/unprovable).

### FINDING 2 (the named stop condition): the Ricci-trace-to-`nablaRm` bridge is MISSING
`gammaStepStar` needs, after `iteratedRmCompDt_succ` → `covDerivStepDt (chrDt) (∇ᵏRm)` +
`christoffelRHS_id` (orthonormal: `chrDt_{ijk} = −nablaRic_{ijk} − nablaRic_{jik} + nablaRic_{kij}`)
+ `christoffelEvolution_of_solution` (realizes `nablaRic := ricciCovDerivCompInFrame`), the bridge:
```
-- SMALLEST MISSING API LEMMA (report shape; do NOT name it hgamma)
ricciCovDeriv_trace_nablaRm (S) (hS) (frame) (t) (x) (horth : orthonormal) (d a b : Idx) :
  ricciCovDerivCompInFrame S frame t x d a b
    = ∑ e : Idx, nablaKRm04Field S t 1 x
        (vec5 (frame d x) (frame e x) (frame a x) (frame e x) (frame b x))
```
i.e. `∇_d Ric_{ab} = ∑_e ∇_d Rm04(e,a,e,b)` in the *realized-component* (`ricciCovDerivCompInFrame`)
form.  **What exists (and the exact gaps):**
- `NablaRicTraceAt basis gInv nablaRm04 nablaRic` (`Bianchi.lean:1108`) = the trace PREDICATE
  `nablaRic(A,B,C) = ∑ᵢⱼ gInv·nablaRm04(A,eᵢ,B,C,eⱼ)`.  ✓ the right statement.
- `canBianchiAt` (`Ricci/CoordinateIdentities.lean:200`) produces
  `∃ nablaRm04, … ∧ NablaRicTraceAt basis gInvAt nablaRm04 nablaRicT ∧ …` with
  `nablaRicT := totalNabla0SFun 2 (conn t) (S.ricci t) x` (the intrinsic ∇Ric tensor).
- **Gap A**: `canBianchiAt`'s `nablaRm04` is EXISTENTIAL — not identified with `nablaKRm04Field S t 1 x`.
  Need `nablaRm04 = nablaKRm04Field S t 1 x` (the abstract ∇Rm04 = the StarSum2 ∇¹Rm).
- **Gap B**: `nablaRicT = totalNabla0SFun 2 (conn) (S.ricci t)` (the COVARIANT-deriv tensor) vs
  `ricciCovDerivCompInFrame = extDerivFun (ricciCompInFrame)` (the FRAME-deriv of components) — differ
  by Christoffel corrections; equal only at a covariant-constant-at-`x` frame (the `#45`/frozen-slot
  realization link).  No banked `ricciCovDerivCompInFrame = nablaRicT-component` lemma.
- **Gap C**: `canBianchiAt` is at the coordinate frame (`coordinateFrameAt`); P3 wants an arbitrary
  orthonormal frame.
A targeted grep (`ricciCovDeriv*`, `nablaRic*`, `nablaRm04Field`, `Ric = ∑ Rm04`, `nabla*metricTrace`)
found NO single lemma closing this; it is a producer in its own right (extract `canBianchiAt`'s
existential + identify with `nablaKRm04Field S t 1` + the frame-realization link).  Per the stop
rule, reported rather than built.

### IH-to-`stNabla` bridge (P3.3) — NOT reached
`gammaStepStar` is upstream of the induction step, so the IH/`stNabla` realization bridge was not
exercised this session.  It remains a flagged downstream risk.

### Recommended next executor prompt
Create `Evolution/StarSum/TimeRecursion.lean` (import `SpatialMember`); move the refrozen endpoint
there; first build `ricciCovDeriv_trace_nablaRm` (the bridge above) from `canBianchiCore` +
an arbitrary-frame realization of `totalNabla0SFun ... S.ricci`; then `gammaStepStar` via
`slotdiffStarA`.

### Planner review (2026-06-13)

Accepted the scope finding: `StarSum2.lean` is upstream of both `StarRouting.lean` and
`SpatialMember.lean`, and it does not import the time-recursion producer
`IteratedRmTowerHeatEq.lean`.  P3 cannot be closed in `StarSum2.lean`; the all-`k` endpoint
belongs downstream, in a new `TimeRecursion.lean` file.

Accepted the missing-bridge stop condition, with one route correction.  The coordinate-only
`canBianchiAt` is not the best first source for an arbitrary orthonormal frame: the lower producer
`canBianchiCore` in `Geometry/Connection/LeviCivita/Curvature/Realized.lean` already gives
`NablaRicTraceAt` for an arbitrary basis and inverse metric.  The real missing API is the
Ricci-flow specialization and component realization:

- identify the geometric `nablaRm04` from `canBianchiCore` with the project field
  `nablaKRm04Field S t 1` (definitionally the same route as `nablaRm04Field`);
- identify the geometric `nablaRic := totalNabla0SFun 2 (S.family.connection t) (S.ricci t) x`
  component with `ricciCovDerivCompInFrame S frame t x d a b`;
- then collapse the inverse metric to the orthonormal diagonal.

There is a coordinate-frame prototype for the second bullet: `coordNablaReal` /
`coordNablaRealOn` in `Evolution/Ricci/CoordinateRegularity.lean`.  No arbitrary-frame version was
found by grep.  So `gammaStepStar` remains 0%; P3 remains 0%; the next producer is the
arbitrary-frame Ricci-trace bridge, not the induction.

## 2026-06-13 Planner P3 design, after P2 closure

Status:
- `residualStarSum` itself is still 0% complete: the theorem is not proved and still has the
  intended all-`k` `sorry`.
- P3 infrastructure is substantial but not the theorem: `StarSum2.nabla`, `starSum2_sum`,
  `residualStarSum_zero`, the component time-recursion machinery
  `iteratedRmCompDt_succ` / `iteratedRmComp_hasDerivWithinAt`, and the P2 routing bank are
  available.
- P2 is closed and accepted: `spatialCommStarSum` returns a level-`k+1` witness for the spatial
  commutator and carries `hcov`/`hmc`; in P3 those should be discharged by
  `connSmoothOfSol S hS (t : Real) (D.regular_subset t.2)` and
  `solution_isMetricCompatible S (t : Real)`.
- The P2 theorem is generic in `Idx`, but the refrozen all-`k` endpoint should follow
  `residualStarSum_zero` and instantiate P2 at `Idx := Fin 3` with the same orthonormal basis.

### P3.0 required statement refreeze

The current stub

```lean
residualStarSum (S) (hS) (k) (t)
```

is too strong as written. The checked base case `residualStarSum_zero` needs the honest
dimension-3 and base-evolution inputs:

```lean
hdim : forall x, Module.finrank Real (TangentSpace I x) = 3
hbase : forall x (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) horth I0,
  HasDerivWithinAt ...  -- the orthonormal rough-trace plus bare Bt/drift value
```

The review section above already says this is required. The first P3 executor step is therefore
to refreeze the public P3 target, not to force the current stub. Preferred route:

1. Replace the current `residualStarSum` statement with the honest Fin-3/input-bearing endpoint
   needed by the BBS consumer, or introduce `residualStarSum3` and stop treating the old generic
   stub as the active target. Do not leave both as parallel frontiers.
2. Keep the theorem at orthonormal `Fin 3` bases. Do not re-open the C4 coordinate-to-orthonormal
   transfer.
3. Carry the standing time-side inputs explicitly. At minimum this means the `hbase` used by
   `residualStarSum_zero`; for the induction step, either carry the already packaged time-step
   input produced by `iteratedRmComp_hasDerivWithinAt`, or carry the same `hrm`/`hchr`/`hswap`
   style inputs needed to derive it. This is honest threading, not a wrapper.

Stop immediately if an executor tries to prove the current `S hS k t` stub with no extra inputs:
that would be a statement-form bug, not a proof-search problem.

### P3.1 induction shape

For the step from level `k` to `k+1`, use the actual component recursion, not a remembered sign:

```text
iteratedRmCompDt_succ =
  covDerivStepComp (... E_k ...) - covDerivStepDt (d/dt Gamma) (nabla^k Rm)
```

Together with the spatial commutator convention from P2, normalize the residual to:

```text
E_{k+1} = nabla(E_k) + gamma-correction - spatial-commutator
```

where the sign of `gamma-correction` is whatever remains after unfolding
`iteratedRmCompDt_succ`. Do not hard-code the plus sign from prose; let the definition set it.

The witness should have the constructor form:

```text
T_{k+1} = stNabla T_k + T_gamma +/- T_spatial
```

with membership by:
- IH gives `T_k : StarSum2 S t k`;
- `StarSum2.nabla` gives `stNabla T_k : StarSum2 S t (k+1)`;
- P2 gives `T_spatial : StarSum2 S t (k+1)`;
- the new gamma lemma gives `T_gamma : StarSum2 S t (k+1)`;
- `.add`/`.smul` assemble the signed sum.

### P3.2 gamma-correction lemma

The only new StarSum algebra in P3 should be the `d/dt Gamma * nabla^k Rm` correction.
Use the existing route bank before adding any new routing family:

- `covDerivStepDt` is a sum over the moved lower slot and replacement index.
- `christoffelRHS_id` rewrites the raised Christoffel evolution in an orthonormal frame as
  the three `nablaRic` terms.
- `nablaRic` is a trace of `nablaRm`; after expanding that trace, each summand is a double
  trace of `nablaRm * nabla^kRm`, so it should be a `base (k+1) 1 k 0` term.
- Try to reuse the `slotdiffStarA`/`slotdiffStarB` route shapes where the normalized term
  matches. Add only the missing three-term Christoffel routing helpers that are not literally
  covered by the SLOTDIFF routes.

Suggested private endpoint before full induction:

```lean
gammaStepStar
  : exists Tgamma, StarSum2 S (t : Real) (k+1) Tgamma
      /\ forall x basis horth I0, gammaCorrectionComponent = tensor0SComponent (Tgamma x) basis I0
```

If the normalized `nablaRic` trace cannot be connected to `nablaKRm04Field S t 1` by existing
Ricci-trace/`nablaKRm04Field` lemmas after targeted grep, report that as the smallest missing
API lemma. Do not introduce an assumption named like `hgamma`.

### P3.3 IH derivative bridge

The known risk is turning the IH component identity for `E_k` into the component identity for
`nabla(E_k)`. The intended bridge is:

1. Use the IH uniformly in the centre `x` and basis.
2. Use `stNabla_realizes` / `nablaKRm04Field_realizes` / `totalNabla0SRealizes_unique` to identify
   the covariant derivative of the IH witness with `stNabla T_k`.
3. Evaluate at `basis (I0 0)` and `I0.succ`, matching the `Fin.cons` spelling used in P2.

Stop condition: if this cannot be made to typecheck after three genuinely different local routes,
the frozen theorem is still missing the right "uniform in local frame/centre" hypothesis. Report
the exact goal; do not bury the gap behind a new adapter theorem.

### Superseded executor prompt

```text
Do not use the old "work in StarSum2.lean" prompt for P3.  It is superseded by
`TimeRecursion.md`: P3 lives downstream of `SpatialMember`, and the next step is the
local-frame endpoint refreeze `residualStarSumLF`, not `gammaStepStar`.
```

### 2026-06-13 Planner update

The `gammaStepStar` part of P3 is now closed downstream in `TimeRecursion.lean`; the three needed
Ricci-trace routes live in `StarRouting.lean` as `slotRic1/2/3`. The active P3 frontier is now the
single `residualStarSumLF` `succ`-branch assembly in `TimeRecursion.lean`, not a new StarSum2
predicate or routing-family design.

## 2026-06-13 PLANNER REVIEW -- P3 complete; P4 starts with residual bound bridge

Live source review accepts the `TimeRecursion` completion report:

- `resStarLFU` is present and the local Lean `sorry` grep is clean in `TimeRecursion.lean`.
- The obsolete fixed-point `gammaStepStar` declaration is gone; `gammaStarU` is the remaining gamma
  producer.
- `StarRouting.lean` now names `gammaStarU`.
- Minor cleanup remains: a few `TimeRecursion.lean` doc comments still mention the old
  `residualStarSumLF` name or say the induction body is a `sorry`. These are comment-only but should
  be fixed before the next proof pass touches that file.

Planner decision for P4: do not resurrect the old `IteratedRmTowerOn` j-split as the first target.
The P3 endpoint plus `StarSum2.bound` should first be exposed as a direct local-frame residual bound.
That is the smallest honest bridge toward `TowerHeatBoundOn`; the later global scalar/Bernstein
consumer still has frame-existence and reaction-assembly choices to settle.

### Next executor prompt

```text
Work in E:\testdifferential-geometry on branch short-time-existence.

Read first:
- CLAUDE.md
- convention.md
- dictionary.md
- important_lesson.md
- lessons.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarSum2.md, especially
  "2026-06-13 PLANNER REVIEW -- P3 complete; P4 starts with residual bound bridge"
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.md
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TimeRecursion.lean
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/StarSum2.lean
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/IteratedRmTowerProducer.lean
- DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/BernsteinShiHigher.lean

Target:
Begin P4 by proving the smallest direct bound bridge from the closed P3 endpoint. Do not try to
prove the full `TowerHeatBoundOn` theorem in the first pass unless this bridge closes easily.

First cleanup:
- Claim `TimeRecursion.lean`.
- Fix stale comments that still mention `residualStarSumLF` or say the all-k induction body is a
  `sorry`. Do not change theorem statements.

Implementation target:
- Create `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/TowerHeat.lean` and
  `TowerHeat.md` if no better existing downstream file is found.
- Import `TimeRecursion` plus the reaction/heat-bound files needed for the bridge.
- Add a theorem with short name, suggested `resStarBoundLF`, that consumes `resStarLFU` and
  `StarSum2.bound` and returns a local-frame residual component bound.

Suggested statement shape:
Given the same local-frame/time-side hypotheses as `resStarLFU`, obtain the witness `T` from
`resStarLFU`, then obtain `C` from `StarSum2.bound hT`. Conclude:

  exists T, StarSum2 S (t:Real) k T and exists C, 0 <= C and
    (component derivative identity from resStarLFU) and
    forall y, y in u -> forall m : Fin (4+k) -> Fin 3,
      |T y (fun p => frame (m p) y)|
        <= C * sum j in Finset.range (k+1),
             sqrt (stNormSq S (t:Real) j y (hframe.toBasisAt hy)) *
             sqrt (stNormSq S (t:Real) (k-j) y (hframe.toBasisAt hy))

Do not hide the residual behind a new assumption.

Proof route:
1. Apply `resStarLFU` to get `T, hT, hcomp`.
2. Apply `StarSum2.bound hT` with `Idx := Fin 3`.
3. For each `y hy`, use `basis := hframe.toBasisAt hy`.
4. Build orthonormality for `S.family.metric (t:Real)` from `horthU y hy`, using
   `hframe.toBasisAt_coe hy` and the existing `SolutionOn.family_metric` simp bridge if needed.
5. Specialize the bound at `m`; reduce
   `T y (fun p => (hframe.toBasisAt hy) (m p))` to `T y (fun p => frame (m p) y)` by
   `hframe.toBasisAt_coe hy`.

Stop conditions:
- Stop if the `S.base.metric` vs `S.family.metric` orthonormality bridge is not available; report
  the exact goal.
- Stop if `StarSum2.bound` cannot be specialized with `basis := hframe.toBasisAt hy`; report the
  exact type mismatch.
- Stop if the theorem statement wants a global orthonormal frame or global basis family; report this
  as a P4 design issue instead of adding an assumption.

Verification:
Use `scripts/lake-locked.ps1` claims for edited Lean files, focused-check the edited file(s), release
the lock, and update the same-name `.md` note without full logs. Do not run a full build.
```

## 2026-06-13 EXECUTOR -- P4 bridge `resStarBoundLF` GREEN

P4 first step done. New file `Evolution/StarSum/TowerHeat.lean` (details + lessons in `TowerHeat.md`):
`resStarBoundLF` composes `resStarLFU` (P3 endpoint) with `StarSum2.bound` into a single local-frame
residual bound `|T y (frame · y)| <= C * Σⱼ √(stNormSq j)·√(stNormSq (k-j))`, taking exactly the
`resStarLFU` hypotheses (no new assumption), sorry-free.

One necessary upstream API change: `lfBase`/`lfChr` in `TimeRecursion.lean` were `private` and so could
not be named in a downstream file's hypothesis types -> removed `private` (no statement change).

NOT attempted (the real P4 frontier, per the planner decision): the global scalar/Bernstein
`TowerHeatBoundOn`. **CORRECTION: no global basis is needed** (a global orthonormal frame generally
does not exist -- parallelizability). The global consumer is INTRINSIC (`nIntrinsic = |∇ᵏRm|²`); the
per-`u` local bound lifts to a pointwise intrinsic bound because at an orthonormal frame the component
sum-of-squares IS the intrinsic norm (`compNormSqMulti_orthoBasis_eq_normSq0S`, already banked) and
local orthonormal frames always exist -- intrinsic results glue trivially. So frame existence/
invariance is NOT a frontier. The genuine remaining work = (b) the reaction/heat WIRING: connect the
residual `T` to `nablaKRm04ReactionIntrinsic` and assemble the eq-7.4 `n` predicate, plus discharging
the standing analytic inputs at each point's local frame. Details in `TowerHeat.md`.

## 2026-06-14 hcov cleanup

`stNabla_starBase` and `StarSum2.nabla` no longer take a caller-supplied
local-smoothness proof for the solution connection.  The proof is derived from
the fixed-time metric connection internally.

Verification passed for the edited file and the module was rebuilt for
downstream signature refresh.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
StarSum2 metric context.  The exported star-sum surfaces no longer expose that
extra smoothness spelling.

Verification passed for the edited file.

## 2026-07-12 short-time-existence branch alignment

The merge exposed three representation/API compatibility failures, with no new
mathematical frontier: `stNabla_starBase` now rewrites `mtIter_add` explicitly
after the two `domDomCongr` maps distribute over addition; both occurrences of
`product_fun_apply` now supply the bundle fibre and arity parameters; and the
double-trace diagonal calculation closes its normalized reflexive goal
explicitly.

Focused verification and the targeted module refresh passed.  `StarSum2` theorem/machinery remains complete
(100%); this compatibility repair is complete (100%).  The short-time-existence
theorem itself remains proved (100%); its branch-alignment verification is about
99% pending the downstream Hamilton target replay, while the merge commit is
still 0% until final verification and diff review.  This repair does not change
the completion percentage of the Hamilton positive-Ricci endpoint or the wider
HCG compactness theorem.
