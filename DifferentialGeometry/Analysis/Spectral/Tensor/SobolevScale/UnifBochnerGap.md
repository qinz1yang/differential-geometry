# UnifBochnerGap — item-6 spine S1, stage α note

Session 4 (Opus 4.8, LANE C), branch `codex/analytic-producers-e87b`.
Ratified route: item-6 packet S1 (`UNIF_ITEM6_RECON.md §S1, §7`), curvature taken
ABSTRACTLY (Finding C, `HCGCompactness/UnifCurvatureJetBound.md`).

## S1 CONSUMER VERDICT (session 10, read-and-verdict — NO build, NO commit)

**VERDICT: S1-abstract COMPLETE — STEP 2.2 (`:1439` mode-mass) / 2.3 (`cc_dirichlet_gap`
coefficient-one-gap) are UNNECESSARY.  No consumer needs the sharper-constant form; the S1 lane
closes.**  Two DOWNSTREAM packaging/discharge deltas remain (neither is 2.2/2.3, both outside
`UnifBochnerGap`'s spectral core).

Evidence (read the CONSUMERS, not built):
- **What consumers need = the two-sided equivalence pair.**  `UNIF_ITEM6_RECON.md §2` states S1 =
  "**exactly `exists_{…}_general` (§1.1) but with the choose-constant bounded by explicit
  `F(Λ,n)`**" — i.e. the covsum↔`Hs` pair `covsum_hs_unif`/`hs_covsum_unif`, which the landed
  `covsum_hs_unif`/`hsCovsum_unif` (generic rank, abstract `hcurv`/`Fc`) provide.  §3 route table:
  S2 = `covsum_hs_unif` at `s=a+1` + Morrey; S3 = the pair + Sobolev-mult + item-2; S4 =
  `hs_covsum_unif` at `s=a` + curvature-jet→L²; S1b = `S1∘S0∘Gårding(gBase)`.  "**The whole packet
  has ONE hard level, reached by S1; S2–S4, S1b inherit it.**"  `UnifClassBounds.md §2/§5`
  confirms every (N)-time constant (`Csym1/Csym2`, `R₀`, `K`, `‖Nfun 0‖`) transfers through this
  pair; `UNIF_EXISTENCE_PLAN.md` Stage-3 = "apply Stage 2 + Stage 1 to produce `τ₀`" (Stage-1 =
  the S2–S4 uniform constants).
- **The `:1439`/gap forms are NOT consumer-facing.**  Per `RECON §7.1–7.3` they are INTERNAL steps
  of an ALTERNATIVE per-metric derivation (route 2, `DirichletSpectralBochnerGap.lean`
  `…succ_le_…:1220` → mode-mass `:1439` → `cc_dirichlet_gap:1539`); `cc_dirichlet_gap` is
  explicitly "a coefficient-one Gårding inequality, **not a spectral gap**" (§7.1).  The landed
  pair reaches the SAME equivalence endpoints via route 1 (elliptic `elliptic_lapSum_unif` →
  `jetEven_unif`/`jetOdd_unif` = uniform `hsJet_le`), so route 2's internal `:1439`/gap steps are
  never needed.

Downstream deltas (report-only; do NOT build this session):
1. **Rank-2 `smoothCcToTensorHs` face.**  S1 spec writes `smoothCcToTensorHs g₀ s T`
   (`T : SmoothCcTensor g₀ 0 2`); the landed pair uses generic `ccTensorToHs g₀ s (n:ℝ)`.  Bridged
   by the existing identity `ccTensorToHs g₀ 2 (n:ℝ) = smoothCcToTensorHs g₀ (n:ℝ)`
   (`IteratedCovGradHsJetBound.lean:1029`, `tensorHs.ext`; precedent adapter `:1021`) — a thin
   rank-2 wrapper, downstream (Stage-1 `UnifClassBounds.lean` or a one-line specialization).
2. **The `C ≤ F(Λ,n)` clause** (the S1 spec's `∃C, 0≤C ∧ C ≤ F(Λ,n) ∧ …`).  The landed pair gives
   `∃C ≥ 0 ∧ ∀…` with `C` built from the ABSTRACT `Fc`(+dim/order + internally-`.choose`d
   metric-contraction constants); the `≤ F(Λ,n)` bound is the DOWNSTREAM discharge 2a/2b/2c
   (`RECON §7.5`: bound `sup‖∇^a Riemann‖`, `ccR/ccdR`, `K_lap` by `Λ` from
   `MetricCovDerivOrderBoundOn`) — Finding C explicitly puts this in `HCGCompactness`
   (`UnifCurvatureJetBound.lean`, the concurrently-active lane), NOT in S1.  **CAVEAT for the
   planner (distinct from 2.2/2.3):** for 2c to prove the AGGREGATE `C ≤ F(Λ,n)`, the top-level
   endpoints' `∃C` may need restating to EXPOSE `C` as an explicit monotone function of
   (`Fc`, the metric-contraction/dimension constants) — the per-STEP blocks
   (`bochner_step_hcurv`, `baseAddLower_unif`) already expose `Fc`-explicit constants; only the
   aggregates (`elliptic_lapSum_unif`/`covsum_hs_unif`/`hsCovsum_unif`) are `∃`-wrapped.  This is
   an "expose-aggregate-constant" refinement to scope when 2a/2c compose, NOT the mode-mass/gap
   form.

Net: the spectral gate (the one HARD level, S1) is mathematically DONE at the abstract-`hcurv`
interface the plan mandates; remaining item-6 work is the downstream 2a/2b/2c curvature-jet
discharge (other lane) + Stage-1 packaging (rank-2 face; expose-constant if 2c needs it) + S0/S1b
covariant cross-metric + S2–S4.  STEP 2.2/2.3 dropped from the plan as unnecessary.

## What landed (stage α) — GREEN, axiom-clean

`bochner_step_unif` — the `Λ`-uniform single Bochner step, the uniform sibling of
the private `iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1220`).  EXPLICIT constant `Cbase + Fc 0`
(no `Classical.choose`).

Statement (rank `s`, inner order `k`):
`∀ u, ‖∇^{k+2}u‖²_{L²} ≤ ‖∇^{k}(Δ_∇u)‖²_{L²} + (Cbase + Fc 0)·(∑_{a≤k+1}‖∇^a u‖)²`.

Abstract hypotheses (both discharged downstream — NOT `Classical.choose`):
- `hcurv` : `∀ r p (S : SmoothCcTensor g₀ 0 r), ‖∇^p(pointwiseTensorCurv g₀ r S)‖ ≤
  Fc p · ∑_{a≤p+1} ‖∇^a S‖` — the uniform Weitzenböck-defect bound, order/rank-generic,
  with explicit `Fc : ℕ → ℝ` (`hFc : ∀ p, 0 ≤ Fc p`).  This is the conclusion of
  `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` (`AllOrderGardingConstant.lean:193`)
  with `Fc` in place of the choose-witness `K`.  It is the "curvature-jet sup in
  consumable currency"; brick 2a discharges it from `sup_x‖∇^{g₀,a}Riemann(g₀)‖ ≤ F(Λ,n)`.
- `hbase` (constant `Cbase`) : the uniform commutator base+lower bound, uniform sibling of
  `rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`
  (`:1085`).  Expressing `Cbase` through `Fc` is stage β (see below).

`0 ≤ Cbase` was DROPPED (weakest-hypotheses rule): the `nlinarith` certificate does
not use it — `hbase` already carries `+Cbase·SUM²` on the correct side.  (Callers get
`0 ≤ Cbase + Fc 0` from their own `hbase`/`hFc` when needed.)

Proof = structural mirror of `:1220`: `weitzenbock_integrated_covGrad_l2_normSq`
(`IntegratedOrder2Weitzenbock.lean:196`, PUBLIC) + Cauchy–Schwarz on the curvature
pairing.  Only the two curvature-dependent `obtain`s of the private original are
replaced by `hcurv`/`hbase`.  Uses PUBLIC API only (the leaf imports just
`DirichletSpectralBochnerGap`; no private symbol referenced).

## Verification
Whole-file `lake env lean` (`buildDir = C:/dgb2/e87b`; new file ⟹ genuine
elaboration, not cached-stale): **EXIT 0, zero errors/warnings.**  Axiom audit
(`#print axioms bochner_step_unif`, then stripped): exactly
`[propext, Classical.choice, Quot.sound]`.  Verified in a quiet Lean window
(lanes A/B active; wait-poll protocol).

## Stage β step 1 (session 5) — commutator LANDED; `:1085` BLOCKED on covDivergence tower

**`roughLapComm_unif` — GREEN, axiom-clean.**  The class-uniform `m`-fold
rough-Laplacian/covGrad commutator, uniform sibling of the `private`
`iteratedRoughLapGrad_commutator_l2Norm_le_local` (`DirichletSpectralBochnerGap.lean:616`).
Structural mirror of the original induction on `m`, with `hcurv` (the same stage-α
hypothesis) in place of its `Classical.choose` witness `K`; constant family built by the
recursion `Cfun p = Fc p + Cfun_{m-1}(p+1)` — EXPRESSED THROUGH `Fc`, no choose.  The one
private dep, the reindex `norm_iteratedCovGrad_comp_local` (`:443`, ~25 lines), was inlined
verbatim as `private norm_iterCovGrad_comp` (pointwise input `rfns_iteratedCovGrad_comp`,
public).

**`:1085` (base+lower) is BLOCKED — STOP-and-request per the session-5 mandate.**  Turning
`roughLapComm_unif` into `bochner_step_unif`'s `hbase` requires the uniform sibling of
`rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower` (`:1085`),
whose IBP cross-term uses `covDivergence_l2Norm_le_covGrad_local` (`:599`).  Unlike the
reindex helper, this is NOT a ≤40-line inline: it sits atop a **~130-line `private` tower**
(`:479–597`: `contract_eq_covGradBundleEquiv_symm_local`,
`riemannianFiberNormSq_eq_sum_contract_orthoFrame_local`,
`riemannianFiberNormSq_contract_le_succ_local`,
`covDivergenceRaw_eq_sum_contract_covDeriv_local`,
`riemannianFiberNormSq_covGrad_eq_sum_frame_local`,
`riemannianFiberNormSq_covDivergence_le_local`).  No PUBLIC `covDivergence ≤ covGrad` bound
exists anywhere in the tree.  The IBP identity itself
(`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`, `TensorCovDivergence.lean:1095`)
and `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` (`:537`) ARE public.

**Requested ruling:** publicize `covDivergence_l2Norm_le_covGrad_local` and its `:479–597`
support tower in `DirichletSpectralBochnerGap.lean` (drop `private`; a benign,
`covDivergence`-standard, foundational-file change), OR authorize a >130-line inline copy
in this leaf (forbidden-parallel-API territory — not recommended).  With the publicize,
`:1085` → `hbase` is a short assembly (commutator `roughLapComm_unif` + `:759`-analog +
public IBP + public rawConnLap≤2ndCovGrad + the now-public covDivergence bound).

## Stage β step 1 CLOSED (session 6) — `hbase` assembled; publicize granted

Planner GRANTED the publicize (minimal form): `private` dropped from
`covDivergence_l2Norm_le_covGrad_local` (`DirichletSpectralBochnerGap.lean:599`) ONLY (the
`:479–597` support tower stays `private` — a public theorem freely uses same-file privates).
This is the sole one-token edit in that foundational file.

Three theorems added to this leaf (verification: authoritative `lake build +…UnifBochnerGap`,
which refreshes the edited DirichletSpectralBochnerGap olean — status recorded in Status log):
- `rawConnLapIter_unif` — uniform `:759` (`∇^a∘Δ_∇` bound): public dimension-only
  `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` + `roughLapComm_unif`.
- `baseAddLower_unif` — uniform `:1085`, **the `hbase` provider**: its conclusion is EXACTLY
  `bochner_step_unif`'s `hbase`; explicit constant `(Cfun 0)² + 2·Crc·√finrank·Cfun 1`
  (`Fc`-explicit heads + dimension), IBP via public
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence` + the now-public covDivergence bound.
- `bochner_step_hcurv` — **`hbase` DISCHARGED**: combines `baseAddLower_unif` +
  `bochner_step_unif` so the only remaining hypothesis is the abstract `hcurv` (with explicit
  `Fc`).  Induction-ready form for step 2.

## `hsJet_le` audit (session 6, for step 2) — PASSES, no non-Λ quantity

`hsJet_le` (`IteratedCovGradHsJetBound.lean:834`) → `jet_even:603` / `jet_odd:667`:
- `jet_even` constant `= (2k+1)·Cg·(k+1)` — order factors × `Cg` from
  `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter` (the SAME Bochner elliptic recursion
  `∇^j ≤ ∑ Δ^i` this file uniformizes).
- `mode_le_jet:438` constant `= (Cfun 0)²`, `Cfun` from
  `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le` (iterated Δ = curvature commutator + dim).
**Verdict: entirely curvature-commutator + dimension + order factors — NO spectral gap,
injectivity radius, or `λ₁`.  Λ-controllable via the same `hcurv`/`Fc` mechanism.** (Its
UNIFORM version is not free — it requires re-deriving `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`
through `bochner_step_hcurv`, which is step-2 work — but the audit finds no blocker.)

## STEP-2 route MAPPED (session 7) — fully specified for a mechanical write

**KEY finding:** the endpoints `covsum_hs_unif`/`hs_covsum_unif` ARE uniform
`hsJet_le`/`hs_le_jet` (`IteratedCovGradHsJetBound.lean:834/855`).  The hard one routes
through the elliptic `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`
(`AllOrderGardingConstant.lean:918`, `∑‖∇^j‖ ≤ C·∑‖Δ^i‖`).  Its ORIGINAL proof peels a
DEEPER curvature atom `exists_integrated_curvatureCrossBound` (via the order-2 step
`exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen:122`, constant `2+2·Ccross`) that my
`hcurv` (the `pointwiseTensorCurv` defect) does NOT capture.  **The planner's route sidesteps
it:** re-derive `:918`'s CONTENT via `bochner_step_hcurv` (whose curvature is already
`hcurv`-packaged), NOT by uniformizing `:918`'s subs.  All pieces are now identified.

### STEP 2.1 — uniform elliptic `elliptic_lapSum_unif` (`∀ j, ‖∇^j S‖ ≤ C_j·∑_{i≤j}‖Δ^i S‖`)
STRONG induction on the jet order `j` (rank `s` fixed; `hcurv` rank-generic ⇒ reusable):
- **`j=0`:** `‖S‖ = ‖Δ^0 S‖`, `C_0 = 1`.
- **`j=1` (base, curvature-FREE):** `‖∇S‖² ≤ ‖ΔS‖·‖S‖` — the Dirichlet-energy IBP
  `covGrad_norm_sq_le_rawConnLap_mul_self` (`AllOrderGardingConstant.lean:843`, private,
  ~9 lines — INLINE; atom `covGrad_l2NormSq_le_rawConnLap_mul_self_gen`).  ⇒ `‖∇S‖ ≤
  ‖S‖+‖ΔS‖ = ∑_{i≤1}‖Δ^i S‖`, `C_1 = 1`.  No `Fc` (curvature-free, Λ-independent).
- **`j≥2` (either parity):** `bochner_step_hcurv` at `k=j-2`:
  `‖∇^j S‖² ≤ ‖∇^{j-2}(ΔS)‖² + C·(∑_{a≤j-1}‖∇^a S‖)²`.  Bound `‖∇^{j-2}(ΔS)‖` by strong-IH
  at `j-2` applied to `ΔS`, reindex `Δ^i(ΔS)=Δ^{i+1}S` (inline the private
  `rawTensorConnLapIter_rawTensorConnLapSmooth:520`, ~6 lines; `Δ^i,Δ^{i+1}` public
  `rawTensorConnLapIter_zero/_succ`); bound each `‖∇^a S‖` (`a≤j-1`) by strong-IH.  Take
  `√`: `C_j = C_{j-2} + √C·∑_{a≤j-1}C_a`, `Fc`-explicit.
- Then wrap to `hsJet_le` shape: even orders `jet_even`-style
  (`∑_{j≤2k}‖∇^j‖ ≤ C·‖Hs^{2k}‖`) via `elliptic_lapSum_unif` + the curvature-FREE
  `rawIter_even`(`‖Δ^i S‖ ≤ ‖Hs^{2i}‖`)/`ccToHs_norm_mono` (both consumable); odd via `jet_odd`.
  ⟹ `covsum_hs_unif`.  Easy direction `hs_covsum_unif` mirrors `hs_le_jet:855`/`mode_le_jet:438`
  (curvature via `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le` — iterate `roughLapComm_unif`).
- Effort: `elliptic_lapSum_unif` ~100–130 lines (+ 2 inlined helpers ~15); wrappers ~120.
  Genuinely a multi-lemma brick; NOT one clean landing under the wait cadence.

### STEP 2.2 — uniform strong induction (mirror `:1439`)
Once uniform `hsJet_le` (2.1) exists: iterate `bochner_step_hcurv`, fold the uniform
Sobolev-jet constant (as `:1439` does at `:1465`).  Prereq = 2.1.

### STEP 2.3 — coefficient-one gap + endpoints
Mirror `cc_dirichlet_gap:1539` (uses 2.2) → `covsum_hs_unif`; easy → `hs_covsum_unif`.

## STEP 2.1 LANDED (session 8) — `elliptic_lapSum_unif` GREEN; wrappers BLOCKED on private spectral bridges

**`elliptic_lapSum_unif` — GREEN, axiom-clean (public).**  The `Λ`-uniform sibling of
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter` (`AllOrderGardingConstant.lean:918`):
```
(g₀) (Fc) (hFc) (hcurv) (s k) :
  ∃ C ≥ 0, ∀ j ≤ 2*k, ∀ S, ‖∇^j S‖ ≤ C · ∑_{i ∈ range (k+1)} ‖Δ_∇^i S‖
```
`Fc`-explicit constant (no `Classical.choose`), same abstract `hcurv`/`Fc` interface as the rest
of the file.  Built on three private helpers added to this leaf:
- `rawIter_lap_reindex` — `Δ_∇^i(Δ_∇ S) = Δ_∇^{i+1} S` (inline of the private
  `AllOrderGardingConstant.rawTensorConnLapIter_rawTensorConnLapSmooth:520`, induction on `i`).
- `lap_shift_le` — `∑_{i<m}‖Δ_∇^{i+1}S‖ ≤ ∑_{i<n}‖Δ_∇^i S‖` for `m+1≤n` (curvature-free; via
  `Finset.sum_range_succ'` + range monotonicity).  Needed `omit [CompactSpace M] [I.Boundaryless]`.
- `elliptic_engine` (strong form) — `∀ J, ∃ C ≥ 0, ∀ a ≤ J, ∀ S,
  ‖∇^a S‖ ≤ C·∑_{i ∈ range ((a+1)/2+1)} ‖Δ_∇^i S‖`.  **Ordinary** induction on `J` (single `C`
  covers all `a ≤ J`; NOT strong recursion): `a=0` trivial; top order `a=1` = curvature-free
  order-1 Dirichlet-energy IBP (`covGrad_l2NormSq_le_rawConnLap_mul_self_gen`, inlined ~8 lines);
  top order `a=J'+2 ≥ 2` = `bochner_step_hcurv` at `k=J'`, term-1 bounded by IH at `a=J'` applied
  to `Δ_∇ S` (reindexed + `lap_shift_le`), the gradient-jet sum bounded by IH at each `a'≤J'+1`,
  then `√` with constant `C_{J+1}=max(C_J, C_J·√(1+Cb·(J'+2)²))`.

**KEY REFINEMENT of the session-7 map:** the map's stated RHS `∑_{i≤j}‖Δ^i S‖` (Laplacian order
up to `j`) is **too loose for the `jet_even` wrapper**, which needs `‖Δ^i S‖ ≤ ‖Hs^{2i}‖ ≤
‖Hs^{2k}‖` i.e. `i ≤ k = j/2`.  A loose `i ≤ j` would force `‖Hs^{4k}‖` (wrong Sobolev exponent).
The engine therefore carries the **tight** per-order budget `(a+1)/2 = ⌈a/2⌉` (order-1 needs
`Lap_1`, so it is `⌈a/2⌉` not `⌊a/2⌋`), which the ordinary-`J` induction still closes because
both Bochner terms land in `range(⌈a/2⌉+1)`.  This is not a route gap; it is the correct shape,
and it collapses to the `:918` `∑_{i≤k}` via `range_mono` (`(j+1)/2+1 ≤ k+1` from `j≤2k`).

**WRAPPERS BLOCKED (not from math — from `private`).**  Both `Hs`-form deliverables the mission
lists (uniform `hsJet_le`/`covsum_hs_unif` and the easy-direction uniform `mode_le_jet`) require
curvature-free spectral bridges that are `private` in `IteratedCovGradHsJetBound.lean` and hence
**not importable** into this leaf (editable set = `UnifBochnerGap.lean` only):
- Hard (uniform `jet_even`/`jet_odd`): needs `rawIter_even` (`:386`, PRIVATE) —
  `‖Δ_∇^i S‖ ≤ ‖ccTensorToHs (2i) S‖` — to bridge the `∑‖Δ^i S‖` of `elliptic_lapSum_unif` to
  `‖Hs^{2k}‖`.  `ccToHs_norm_mono` (`:183`) is already public; `rawIter_even` is the missing one.
- Easy (uniform `mode_le_jet`): needs `rawIter_tsum` (`:227`), `covIter_tsum` (`:248`),
  `covIter_odd` (`:315`) — all PRIVATE — the spectral `tsum = ‖Δ^i S‖²`/`‖∇(Δ^i S)‖²` identities.
  (The curvature side, uniform `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le`, is buildable
  here by iterating `roughLapComm_unif`; the SPECTRAL side is what is blocked.)
There is **no public `rawTensorConnLapIter → ccTensorToHs` bridge anywhere in the tree** (grep
confirmed).  The session-7 map called `rawIter_even` "consumable"; it is not (it is `private`).

**Requested ruling (mirrors the session-6 covDivergence publicize):** drop `private` from
`rawIter_even`, `rawIter_tsum`, `covIter_tsum`, `covIter_odd` in
`IteratedCovGradHsJetBound.lean` (four one-token edits; all curvature-free spectral bridges, a
benign foundational-file change).  With those public, uniform `jet_even`/`jet_odd`/`hsJet_le`
(hard) and uniform `mode_le_jet` (easy) are near-verbatim copies of `:603/:667/:834/:438` with
`elliptic_lapSum_unif` swapped for `:918` and `roughLapComm_unif` for the commutator — an
estimated ~200-line follow-up dispatch once the publicize lands.  Distance to STEP 2.2/2.3
endpoints (`covsum_hs_unif`/`hs_covsum_unif`) is exactly this wrapper layer + the 2.2 strong
induction; STEP 2.1's hard mathematical content (the Bochner elliptic recursion) is now DONE.

## Status
- 2026-07-24 (session 9): STEP 2.1 WRAPPER LAYER COMPLETE — BOTH `Hs`↔covsum endpoints LANDED +
  VERIFIED + AUDITED.  Publicize GRANTED + applied (four one-token edits in
  `IteratedCovGradHsJetBound.lean`: `private` dropped from `rawIter_tsum`, `covIter_tsum`,
  `covIter_odd`, `rawIter_even`; module rebuilt GREEN, 58s, no downstream breakage).  Eight new
  public theorems in `UnifBochnerGap.lean` (all axiom-clean `[propext, Classical.choice,
  Quot.sound]`; authoritative `lake build +…UnifBochnerGap` GREEN):
  - HARD direction (covsum ≤ `Hs`): `jetEven_unif` (even, via `elliptic_lapSum_unif` +
    `rawIter_even` + `ccToHs_norm_mono`); `jetOdd_unif` (odd, via `elliptic_lapSum_unif` at rank
    `s+1` + `covIter_odd` + the `Fc`-explicit commutator); **`covsum_hs_unif`** = uniform
    `hsJet_le` (`:834` shape), the endpoint.
  - Commutator layer: `iterLapGradComm_unif` (`‖∇^p([Δ^i,∇]S)‖ ≤ Cfun(p)·∑_{a<2i+p}‖∇^a S‖`,
    `Fc`+dim-explicit, mirror of the private aux `:673`) + `rawConnLapCovComm_unif` (`p=0` face).
  - EASY direction (`Hs` ≤ covsum): `iterRawLap_unif` (`‖∇^p(Δ^i S)‖ ≤ Cfun(p)·∑_{b≤2i+p}‖∇^b S‖`,
    mirror `:609`, iterates `rawConnLapIter_unif`); `modeLeJet_unif` (per-mode, via
    `rawIter_tsum`/`covIter_tsum`); **`hsCovsum_unif`** = uniform `hs_le_jet` (`:855` shape),
    the endpoint.
  - Two more inlined private helpers (curvature-free, deps all public): `mode_summable_inl`
    (mode-series summability, inline of private `mode_summable:533`) and `norm_icg_order_eq`
    (jet-order reindex, inline of private `norm_iteratedCovGrad_order_eq:596`).  These + the
    session-8 `rawIter_lap_reindex`/`lap_shift_le` are the only `private` inlines.
  Constant chains are all `Fc`(+dimension/order)-explicit; the only `Classical.choose` calls are
  of `rawConnLapIter_unif`'s `Fc`+dim constant (never a curvature sup), matching the original's
  choose pattern but with the curvature already `hcurv`-packaged.  Distance to STEP 2.2/2.3: the
  two endpoints ARE the `covsum_hs_unif`/`hs_covsum_unif` shapes (`hsJet_le`/`hs_le_jet` with
  explicit `Fc` constants); STEP 2.2 (uniform strong induction, mirror `:1439`) can now iterate
  `bochner_step_hcurv` and fold these jet constants, and STEP 2.3 (coefficient-one gap, mirror
  `cc_dirichlet_gap:1539`) assembles the final gap.  No commit.
- 2026-07-24 (session 8): STEP 2.1 CORE LANDED + VERIFIED + AUDITED.  `elliptic_lapSum_unif`
  (public, `:918`-shape, `Fc`-explicit) + 3 private helpers (`rawIter_lap_reindex`,
  `lap_shift_le`, `elliptic_engine`).  Authoritative `lake build +…UnifBochnerGap`: "Build
  completed successfully (9342 jobs)", UnifBochnerGap built 69s, zero errors, zero NEW warnings
  (lone `unusedSectionVars` on `lap_shift_le` fixed via `omit [CompactSpace M] [I.Boundaryless]`).
  Axiom audit (direct `lean`, full package `LEAN_PATH`): exactly
  `[propext, Classical.choice, Quot.sound]`; audit line stripped after green.  The two `Hs`-form
  wrappers are BLOCKED on four PRIVATE spectral bridges in `IteratedCovGradHsJetBound.lean`
  (`rawIter_even:386`, `rawIter_tsum:227`, `covIter_tsum:248`, `covIter_odd:315`) — publicize
  requested (see the STEP 2.1 LANDED section).  Map refinement: engine RHS is TIGHT `⌈a/2⌉`
  (map's `≤j` was too
  loose for `jet_even`).  No plan edits; no commit.
- 2026-07-24 (session 7): STEP-2 route fully MAPPED (no Lean landed — a deep mapping of the
  elliptic chain).  KEY: `bochner_step_hcurv` route sidesteps the deeper
  `curvatureCrossBound` atom `:918` uses; the `j=1` base is curvature-FREE
  (`covGrad_norm_sq_le_rawConnLap_mul_self:843`); every sub-lemma + inline identified above.
  STEP 2.1 (uniform elliptic `elliptic_lapSum_unif` → uniform `hsJet_le`) is a specified
  ~250-line multi-lemma write; recommended as the next focused dispatch.  No plan edits; no
  commit.
- 2026-07-24 (session 6): publicize GRANTED + applied (one token: `private` dropped from
  `covDivergence_l2Norm_le_covGrad_local:599`; DirichletSpectralBochnerGap rebuilt GREEN,
  63s — NO downstream breakage).  `hbase` ASSEMBLED + DISCHARGED: `rawConnLapIter_unif`,
  `baseAddLower_unif` (the `hbase` provider), `bochner_step_hcurv` (only `hcurv`/`Fc` remain)
  — all three axiom-clean `[propext, Classical.choice, Quot.sound]`; authoritative
  `lake build +…UnifBochnerGap` GREEN ("Build completed successfully (9342 jobs)", 46s).
  One fix en route: `baseAddLower_unif` needed `set_option maxHeartbeats 1600000 in` (default
  200000 timed out at the IBP `nlinarith`).  `hsJet_le` audit for step 2: PASSES (no non-Λ
  quantity).  STEP 2 (strong induction) is next.  No plan edits; no commit.
- 2026-07-24 (session 5): STEP 0 authoritative build of `UnifBochnerGap` GREEN ("Build
  completed successfully (9342 jobs)").  STEP 1: `roughLapComm_unif` + inlined
  `norm_iterCovGrad_comp` LANDED, both public theorems (`bochner_step_unif`,
  `roughLapComm_unif`) axiom-clean `[propext, Classical.choice, Quot.sound]`; full-file
  authoritative rebuild GREEN.  `:1085`→`hbase` BLOCKED on the ~130-line private
  covDivergence tower — STOP-and-request the publicize ruling (above).  STEP 2 (induction)
  awaits `hbase`.  No plan edits; no commit.
- 2026-07-24 (session 4): stage α `bochner_step_unif` GREEN + axiom-clean.  Curvature
  abstracted as `hcurv` (consumable currency); commutator base abstracted as `hbase`.
