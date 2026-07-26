# RicBound.lean — THE `ric_bound` endpoint (MSM135 Lemma 3.11, Step 4 (A_N))

## Route A explicit witnesses (2026-07-22)

The constants-first noncompact producer layer is source focused-green and
sorry-free:

- `RicTowerCoeffs` packages the explicit affine slope and offset.
- `perDomain_bound` consumes the fixed numeric Claim 1/Claim 2/descent
  witnesses.
- `ric_tower_on` chooses a good frame pointwise; no compact finite subcover is
  used to choose its constants.
- `ric_bound_field_on` and `covOrderBound_stage_on` export the sequence/window
  forms needed by `SourceCovLip`.

The old compact `ric_bound` route is retained as compatibility API. The new
declarations are focused-green and exact-current. Their consumer
`SourceCovLip.srcCovLip_of_soln` is now sorry-free, focused-green, and
exact-green (`4067/4067`).

Progress accounting: the explicit RicBound producer and the dedicated
constants-first `srcCovLip_of_soln` machinery are both 100%. This does not
close the independent solution-generated `ShiCutoffData` frontier. The whole
HCG compactness project remains about 60% complete.

## ✅✅ PROVED SORRY-FREE (2026-06-11, commit c35998f4; targeted build green, 3850 jobs)

`theorem ric_bound` is fully discharged.  STATEMENT CHANGES vs the original
sorry'd version (downstream consumers must adapt):
- hypotheses now live on an OPEN `U ⊇ K` (`hU : IsOpen U`, `hKU : K ⊆ U`) —
  the book's nested-set shape; the engine needs bounds on open frame domains.
- eq-3.3 needs a window-uniform majorant: `(Bmax) (hBmax1 : 1 ≤ Bmax)
  (hBmax : ∀ t ∈ Icc β ψ, B t ≤ Bmax)`.
- added `hKShi0 : 0 ≤ KShi`; variable block gained `[I.Boundaryless]`,
  `[IsManifold I 1/2/(∞+1) M]`, `[VectorBundle ℝ E (TangentSpace I)]`,
  `[ContMDiffVectorBundle 1 E (TangentSpace I) I]`.
## ✅ P2 GRÖNWALL WIRING DONE (2026-06-11, post-ric_bound, commit 90001ab2; all sorry-free)

- `nablaRicReal` (ricCovTower reindexed to the `p+2` Grönwall arity via `acEquiv`)
  + `nablaRicReal_normSq` + **`ric_bound_field`** (the exact
  `MetricCovOrderEvolutionInput.ric_bound` field shape).
- **`normsq_evol_of_comp`**: the `normsq_evol` field from POINTWISE-EVALUATED
  evolution data (`∀ v, HasDerivAt (r ↦ ∇ᵖg_r(x)(v)) ((-2•nablaRic)(v))`, ℝ-valued).
  DESIGN NOTE: Mathlib's CLM-composition (`comp_hasDerivAt`/`clm_apply`/slope) is
  normed-only while the Tensor0SSpace `HasDerivAt` elaborates on the TVS instance
  path — do NOT try to consume the tensor-valued `HasDerivAt`; take the evaluated
  family as the input form (the flow-side producer naturally emits it).
- **`covOrderBound_stage`**: the full stage-`N` `(B_N)` assembly — ric_bound
  inputs + `hevol` + evaluated evolution + init bound + window data ⟹
  `MetricCovDerivOrderBoundOnWindow K β ψ gSeq gRef N (Grönwall constant)`,
  by constructing the `MetricCovOrderEvolutionInput` record and applying
  `metricCovOrderWindow_of_evolution`.

## ✅ P2 STRUCTURE COMPLETE (2026-06-11, commits 8a145c45 → 0f42ac11; all sorry-free)

The whole eq.(3.4) assembly is now ONE capstone theorem:

* **`covOrderBound_of_soln`** (end of RicBound.lean) — from a sequence of
  Ricci-flow solutions `S i` (with `gSeq i = (S i).family.metric`, window in
  regular times), the eq.(3.3) equivalence (P1), the moving Shi bounds, the
  tower regularity, and initial-time bounds: **every exact order `1 ≤ r ≤ N`
  has a `(B_r)` window bound on `K`**.
* Internal chain (all sorry-free, this session):
  - `totalNabla0SFun_hasDerivWithinAt_pt` (engine, pointwise swap;
    TotalNabla0STimeDeriv.lean) — the all-t swap predicate is undischargeable
    at carrier endpoints, and the engine only consumes the swap at the working t.
  - `covDerivOfField_eval_hasDerivWithinAt` — chain in the flow two-set shape
    (within `D.carrier`, at `D.regular`; `regular_mem_nhds` yields
    `carrier ∈ 𝓝 t`, forcing the within-set to be the carrier).
  - `solnMetricDeriv` / `solnTower_hasDerivAt` (flow wrapper, W-a) and
    `covDerivOfField_swapReg` / `solnTowerSwap_of_smooth` (swap from joint
    regularity, W-b structural part; hTime at level p = the chain at level p,
    strong induction).  All in MetricCovDerivTimeDeriv.lean (see its .md for
    the smul-elaboration and `show`-pattern gotchas).
  - `hevComp_of_solutions` (RicBound.lean) — sequence adapter into
    `covOrderBound_stage`'s `hevComp` shape (value bridge:
    `covDerivOfField_smul` + `covDerivOfField_eq_iterCov` + `show`-cast to
    `ContinuousMultilinearMap.domDomCongr`, rfl with `ricCovTower`).
  - `covOrderBound_tower` (RicBound.lean) — all stages by strong induction on
    the order; per stage `exists_compact_between` interpolation
    `K' ⊆ interior L ⊆ L ⊆ U'` (local compactness:
    `I.locallyCompactSpace` + `ChartedSpace.locallyCompactSpace`), lower-order
    constants chosen on the compact `L` via `metricCovOrderWindow_mono` /
    `metricUniformEquivalentOnWindow_mono` (added in AllTimesBounds.lean).

## REMAINING for P2 (the honest frontier list — now = hypotheses of `covOrderBound_of_soln`)

A. **Tower regularity** (`hSmoothT`/`hFdiffT`/`hFtdiffT`): joint `(t,x)` C² of
   `(t,x) ↦ (∇ᵖ_gRef g_t)(x)(V·x)` for `p < N`, + spatial differentiability of
   the metric and `-2Ric` towers.  Source: `IsSolutionOn.smoothMetric`
   (`MetricFamilySmoothOn`) + a joint-smoothness calculus for the tower step —
   missing-API track, induction over p in charts; order-0 precedent
   `metricInner_mdiffAt`.  Likely the next concrete brick.
B. **Moving Shi bounds** (`hShi`): `√normSq0S (g_{i,t}) (ricCovTower g g s) ≤ KShi`
   on the window.  `bernsteinShi_solution_estimate`
   (Evolution/BernsteinShiSolution.lean) gives the COMPONENT-interface
   Rm-tower bound `w m ≤ C/tᵐ` on `(0,T]`; realizing `hShi` needs the
   Rm-tower realization layer (`IteratedRmTowerOn` ↔ intrinsic norms — the
   BBS "norm bound + StarSum2 scaffolding" frontier), the Rc-from-Rm trace
   bound, and the `(0,T] → [β,ψ], β>0` window conversion.  The BIG remaining
   frontier; it is a separate track (see bbs-allk-route-status memory).
C. **Initial bounds** (`hinit`) + window data (`timeRadius`, `ht0`): supplied at
   the 3.10/3.11 application site (P4 assembly) from the time-0 CG convergence.

Historical detail of the W-a/W-b design (superseded by the above):

1. **`hevol` producer — ✅ INDUCTION CORE DONE (2026-06-11, commit 145b75d7,
   sorry-free): `covDerivOfField_eval_hasDerivWithinAt`**
   (`HCGCompactness/MetricCovDerivTimeDeriv.lean`): for a `(0,2)` time-family
   `A` with pointwise-evaluated derivative `B` (`hbase`) and per-level scalar
   swaps (`hswap`, ∀ slot-section tuples — the regularity input), every tower
   level `covDerivOfField gRef (A r) p` has evaluated derivative the `B`-tower.
   Engine: `totalNabla0SFun_hasDerivWithinAt` with the ∀-slot-tuple IH filling
   the frozen-vector inputs; slots extended via
   `ContMDiffSection.exists_eq_at_gen`; `Fin.cons`-tuple identified by
   `Fin.cases` + the extension equations.
   **REMAINING for hevol (two well-scoped pieces):**
   (W-a) the FLOW WRAPPER: instantiate `A r := metricTensorField (S.family.metric r)`,
   `B t := (-2) • ricciSection-field`; hbase = `hS.equation` (BILINEAR `v w` ✓,
   within `D.carrier`) + `metricTensorField_apply` + the ricciSection ↔
   `S.ricciAt` canonical-Ricci bridge (P1 used it; locate the exact lemma) +
   smul-eval; upgrade Within→At via `D.regular_mem_nhds` (the
   `ricciFlow_metric_hasDerivAt` pattern, AllTimesBoundsFlow:41); land in
   `covOrderBound_stage`'s `hevComp` shape via `metricCovDeriv_eq_covDerivOfField`
   (rfl) + `covDerivOfField_smul` + `covDerivOfField_eq_iterCov` +
   domDomCongr-eval (= `nablaRicReal`); the `hevol` (tensor-valued TVS) field:
   construct FORWARD from the evaluated family (finite basis sum) or check
   whether the Grönwall consumer can take the evaluated form instead.
   (W-b) the REGULARITY discharge of `hswap`: joint `(t,x)` `C²`-smoothness of
   the evaluated tower at each level, from `IsSolutionOn.smoothMetric`
   (`MetricFamilySmoothOn`) via
   `fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff`
   (FixedBase.lean:327) — a joint-regularity induction over `p` (the `(a')`
   track; the level-0 case is `metricFrameComp_fixedBaseSwap_of_solution`'s
   `hSmooth` input pattern).
   Background (the engines found, user remembered right):
   - `Bundle/PartialMfderiv/FixedBase.lean`: `FixedBaseExtDerivTimeDerivativeOn`
     (the swap predicate: `∂ₛ(extDerivFun (F s) x V) = extDerivFun (Ft t) x V`).
   - `Evolution/Connection/MetricCovDerivProducer.lean`:
     `metricFrameComp_fixedBaseSwap_of_solution` — the swap PROVED for the
     metric frame components from the solution's joint `C²` smoothness
     (`hSmooth : ContMDiffAt (𝓘(ℝ).prod I) 2 (fun (t,x) => g_t(e_a,e_b)(x))`),
     and `metricCovDerivDeriv_of_solution` — the ORDER-1 producer
     `∂ₛ(∇g)-components = −2·(∇Ric)-components`
     (`MetricCovDerivDerivativeComponentsInFrameOnLocal`), plus the packaged
     `connectionVariationBlackBox_of_solution`.
   - `Tensor/RSTensor/NablaOnTensors/TotalNabla0STimeDeriv.lean`:
     `nabla0SFun_hasDerivWithinAt` / `totalNabla0SFun_hasDerivWithinAt` — the
     ARBITRARY-RANK single-step parametric Clairaut (time derivative through one
     covariant-derivative step), taking the swap predicate + per-slot
     frozen-vector derivatives as inputs.  Since `covStep = totalNabla0SFun`
     (ArityBridge `metricCovDerivStep_eq_covStep`), the `p`-fold `hevol` is a
     `p`-INDUCTION over this engine — assembly, NOT open math.
   REMAINING gap (the actual work): (i) the `p`-induction wrapper
   (each step: `totalNabla0SFun_hasDerivWithinAt` with the IH as `hpt`-input and
   a tower-component swap discharged à la `metricFrameComp_fixedBaseSwap`);
   (ii) the format bridge: solution-track components/`HasDerivWithinAt`/
   `D.carrier` ↔ HCG `metricCovDeriv` tower/`HasDerivAt`/`Icc β ψ`/`gSeq`-
   sequence, ending in `hevol` + `hevComp` shapes of `covOrderBound_stage`.
2. Stage-`N` induction wrapper: thread nested opens `K ⊂ U_N ⊂ … ⊂ U₀` (locally
   compact `M`), feed each stage's `(B_r)` output into the next `hBprev`; init
   bounds from the `t0`-time data; equivalence majorant from eq 3.3.
3. Base stages `(B_0)`/`(B_1)` and the Shi-input realization from the flow's
   curvature bounds (`bernsteinShi_solution_estimate` realization layer).

Architecture: `perDomain` (constants-first per-good-frame-domain engine:
uniform `claim1_LC` → `aN_component` + `compL2_tower_le` + `movingGinv_le` +
moving-Shi conversion + smoothness producers w/ `chrInFrame_mono`), then finite
subcover of `K`, per-centre constants, two-sided conversions at each `x`
(`sqrt_tower_le_compL2` LHS / `compL2_tower_le`+`mcdNorm_eq_at` RHS), constants
= nonneg sums over the cover.  NEXT (separate task): feed this into
`MetricCovOrderEvolutionInput.ric_bound` (the `2+N ↔ N+2` reindex via R4f) +
the hevol/normsq_evol producer track → `metricCovOrderWindow_of_evolution`
(B_N) → stage-N induction (threading the nested `U`).

## ⚡ ASSEMBLY DESIGN (2026-06-11, ACTIVE — the /goal "finish ric_bound" run)

**Uniformization wave DONE (commit af9eeb83, all green):** claim1_abstract/claim1
(AkMFold), claim1_LC/claim2_component/mixed_descent/aN_component (RicBoundClaims)
are now CONSTANTS-FIRST (∃C before the varying field data: metric, moving
Christoffels, T, gComp, Ginv + their bound hypotheses; frame/chrH(gRef)/numerics
stay before ∃).  This was REQUIRED: ric_bound's Cpp/Cppp must be uniform over
(i,t), and the old per-invocation ∃ hid the (numeric-only) constant formulas.
claim1_geom call site updated.  Each proof = same script, intros moved past the
refine ⟨formula,…⟩.

**Route change: BYPASS aN_intrinsic_point (U7 skipped).** Its hinvON-at-the-
eval-point only holds at cover centers.  Instead assemble at COMPONENT level
with aN_component-uniform per cover domain, converting both sides with the
TWO-SIDED goodFrame bounds valid at EVERY z ∈ u′:
- forward (done): `exists_goodFrame_compBound` + `compL2_tower_le`
  (compL2 tower ≤ 2^{r+j}·√normSq0S).
- reverse (W1–W3 below): √normSq0S ≤ ((1+ε)·card)^{s}-ish · compL2.

**Statement fix: hypotheses on open U ⊇ K** (book's nested sets).  The engine
needs bounds on open frame domains; hBprev/hequiv/hShi only on K is not enough
when K has empty interior.  Change ric_bound: add (U : Set M) (hU : IsOpen U)
(hKU : K ⊆ U), state hequiv/hBprev/hShi over U, conclude on K.  Stage-N
induction wrapper will thread U (record in AllTimesBounds consumer later).

**PROGRESS (2026-06-11, commits af9eeb83 + 0ddfb145, ALL GREEN):** U-wave done
(constants-first chain); W1 `quad_ub_of_near_id`, W2 `normSq0S_le_pow_sum_comp_sq`,
W3 `gramInv_near_id` (now also Gram-entry closeness), `exists_goodFrame_compBound`
(BOTH directions: `∑comp² ≤ 2^s·normSq0S` and `normSq0S ≤ ((3/2)(card+1))^s·∑comp²`),
`sqrt_tower_le_compL2` (reverse tower, abstract `Cu ≥ 1`) — all sorry-free.
KEY SIGNATURES (verified): `MetricCovDerivOrderBoundOn K a h gRef C = ∀ x ∈ K,
metricCovDerivNorm a h gRef x ≤ C` (pointwise-on-K); R4f
`metricCovDerivNorm_eq_iterCov h gRef N basis (hinv : MetricInverseInBasis_gen gRef
x basis identityInvMetric) : metricCovDerivNorm N h gRef x = √normSq0S gRef x (2+N)
(iterCov gRef 2 (metricTensorField h) N x)` — needs pointwise ON basis; producer
pattern = RicciOperatorNormBound.lean:204-209 (`exists_gOrthonormalBasis` +
`metricInverseInBasis_of_orthonormal` + simpa to identityInvMetric).
Lean gotchas this wave: `abs_add` → `abs_add_le`; `pow_le_pow_left` →
`pow_le_pow_left₀`; stale-olean errors whenever a downstream check follows an
upstream edit (targeted build first).

**G1+G2 DONE (sorry-free): `ricCompField_mdiffOn` (Ricci comps smooth, B2
engine) + `movingGinv_le` (moving inverse-Gram ≤ √card·2Beq from eq3.3 pointwise
lower + gRef-Gram near Id, via `gramE_dotVec` + `quad_lb_of_near_id` + B4).**

**W6 ASSEMBLY BLUEPRINT (exact; remaining gaps marked ⊙):**
ric_bound NEW statement: add `(U : Set M) (hU : IsOpen U) (hKU : K ⊆ U)`;
hequiv/hBprev/hShi over U; ⊙ add `(Bmax : Real) (hBmax1 : 1 ≤ Bmax)
(hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)` (the per-t equivalence constants need a
window-uniform majorant; MetricUniformEquivalentOn C = ⟨1 ≤ C, pointwise
two-sided⟩).  Proof skeleton:
1. `choose` per-point goodFrame data from `exists_goodFrame_compBound gRef x`
   (⊙ FIRST extend it with a 4th output: the ε with 0 ≤ ε, card·ε ≤ 1/2, and
   ∀ z hz∈u', ∀ i j, |gramE gRef z i j − δ| ≤ ε — needed by movingGinv_le; the
   data is already inside its proof (hnear .2), just expose it).
2. Finite subcover: `hKc.elim_finite_subcover (fun x => u' x ∩ U)` (open ✓,
   covers via hxu' + hKU) → centers `t : Finset M`; domains w_k := u' x_k ∩ U.
3. Per center k numerics: C0 := √card·(2·Bmax); Kg := ∑_{j<N} 2^{2+j+2}·max (Cg (j+1)) 0
   -style nonneg sum ≥ each 2^{2+j}·Cg j (1≤j≤N−1); KShi′ := 2^{2+N}·Bmax^{2+N}·max KShi 0-ish.
4. Per center k, data-free constants: CL c from claim1_LC-uniform (u := w_k;
   ⊙ needs IsLocalFrameOn restriction to w_k ⊆ baseSet — check `IsLocalFrameOn.mono`
   exists, else add 5-line restriction lemma; ContMDiffOn.mono ✓ standard);
   B c := CL c·(1+Kg); Ctop := CL (N−1); then ⟨Cpp_k, Cppp_k⟩ :=
   aN_component-uniform (chrH := gRef-LC-frame-Christoffels on w_k).
5. Cpp := max over k (Finset.sup'), similarly Cppp, times the conversion factors:
   final chain at (i,t,x∈K): pick k with x ∈ w_k; instantiate aN's ∀-data with
   g := gSeq i t: chrG := lcChrist (g) [lcChrist_e_mdiffOn], T := Ricci comps
   [ricCompField_mdiffOn], gComp := metric comps [gCompField_mdiffOn], Ginv :=
   ginvCompField [ginv_hinv, movingGinv_le], hDlow/hDtop := claim1_LC-uniform
   applied to g + hgB, hgB := per-z: ⊙ `compL2_movingTower_le` (generalize
   compL2_tower_le to decouple the tower metric gM from the norm metric gRef —
   its proof already separates them; gM := gRef here) + R4f at z (pointwise ON
   basis producer: RicciOperatorNormBound:204 pattern) + hBprev z; hShi-comp :=
   per-z: moving-tower version (gM := g) + goodFrame fwd + swapped
   `normSq0S_le_of_metric_equiv` (gRef ≤ Bt·g from hequiv inverted) + hShi z.
6. Conclusion at x: component (A_N) from aN_component; LHS:
   √normSq0S gRef x (2+N) (ricCovTower g gRef N x) — ricCovTower g gRef N =
   iterCov gRef 2 (ricciSection (LC g)) N DEFEQ — ≤ Cu^{2+N}·compL2(Ric tower)
   [sqrt_tower_le_compL2, Cu := (3/2)(card+1), hub := goodFrame rev at x] ≤
   Cu^{2+N}·(Cpp_k·compL2(g tower N) + Cppp_k) ≤ Cu^{2+N}·(Cpp_k·2^{2+N}·
   metricCovDerivNorm N g gRef x [compL2_tower_le + R4f at x] + Cppp_k) — final
   constants Cpp := max_k Cu^{2+N}·Cpp_k·2^{2+N}, Cppp := max_k Cu^{2+N}·Cppp_k.

**Remaining work list:**
- W1 `quad_ub_of_near_id` (KroneckerQuadForm): |Q−δ|≤ε entrywise ⟹
  ∑∑(∏Q)c_Ic_J ≤ ((1+ε)·card)^s·∑c² (abs-triangle + ∏|Q| ≤ (1+ε)^s +
  (∑|c|)² ≤ card^s·∑c² via sq_sum_le_card_mul_sum_sq over (Fin s → Idx)).
- W2 Comparison upper adapter: normSq0S g x s A = coordInner0S Q ≤ … ∑comp²
  (via normSq0S_eq_coord + W1).
- W3 RicBoundGoodFrame: (a) extend `gramInv_near_id` to also return Gram-entry
  closeness |gramE z i j − δ| ≤ ε (same hentry continuity, trivial); (b) reverse
  tower bound √normSq0S(iterCov tower) ≤ Cu^{r+j}·compL2(tower) at goodFrame
  points (mirror of compL2_tower_le via W2); (c) extend exists_goodFrame_compBound
  to return BOTH directions + the Gram closeness; (d) moving-metric C0 bound:
  vᵀGram_{g}v = g(W,W) ≥ Beq⁻¹·gRef(W,W) = Beq⁻¹·vᵀGramRef v ≥ (1/(2Beq))‖v‖²
  (quad_lb_of_near_id on GramRef-entries + hequiv pointwise) → B4
  `ginv_compL2_le` ⟹ compL2(ginvCompField e₀ g basisE) ≤ √card·2Beq on u′.
- W4 hgB producer: hBprev (MetricCovDerivOrderBoundOn U) + R4f
  `metricCovDerivNorm_eq_iterCov` (check signature; needs pointwise ON basis —
  available pointwise everywhere) + `compL2_tower_le` ⟹ compL2(gRef-tower of
  g-comps, j ≤ N−1) ≤ Kg uniform.
- W5 hShi producer: hShi (moving norm of ricCovTower g g s) +
  `normSq0S_le_of_metric_equiv` (Comparison:614, pointwise hequiv from
  MetricUniformEquivalentOn) + moving-Christoffel `iterCovComp_eq_iterCov` +
  goodFrame forward bound ⟹ compL2(moving Ricci tower) ≤ KShi uniform.
  ALSO Ricci-component smoothness producer (B2 pattern for ricciSection (LC g))
  — check for a generic frameComp0S-smoothness lemma first.
- W6 assembly in RicBound.lean: per x ∈ K goodFrame u′_x ∩ U; finite subcover;
  per domain aN_component-uniform constants; max over the cover; per (i,t,x)
  apply component conclusion + reverse bound (LHS) + compL2_tower_le + R4f (RHS).
  LHS defeq: ricCovTower g gRef N = iterCov gRef 2 (ricciSection (LC g)) N.

## Status (2026-06-10): STATED, verified to elaborate; proof = ONE precise `sorry`

`theorem ric_bound` is the intrinsic (A_N) endpoint, stated per the user's
"state ric_bound first" directive.  Focused check passes (single expected
`sorry` warning).

## Statement design (load-bearing choices)

- **Conclusion** matches the `MetricCovOrderEvolutionInput.ric_bound` field
  (AllTimesBounds.lean:4365) verbatim in shape, with the abstract `nablaRic`
  data REALIZED by the genuine geometric object
  `ricCovTower g gRef s := iterCov gRef 2 (ricciSection (LC g) …) s`
  (defined in this file): `√(normSq0S gRef x (2+N) (ricCovTower (gSeq i t) gRef N x))
  ≤ Cpp · metricCovDerivNorm N (gSeq i t) gRef x + Cppp`.
  NOTE the arity is `2 + N` (iterCov-native), not `N + 2` (the Grönwall field's
  `p + 2`); the consumption adapter will need a slot-arity cast/reindex
  (norm-invariant).
- **Hypotheses** are the honest stage-`N` inputs of the book's induction:
  `hKc : IsCompact K` (the frame-covering/uniformization needs it),
  `hequiv` = eq (3.3) (`MetricUniformEquivalentOnWindow`),
  `hBprev` = (B_r) for `1 ≤ r < N` (`MetricCovDerivOrderBoundOnWindow`),
  `hShi` = moving-metric Shi bounds on the Ricci towers up to order `N`
  (`ricCovTower (gSeq i t) (gSeq i t) s`, moving norm).  (A_r) for `r < N` is
  NOT needed (the book uses it only to produce (B_r)).
- Namespace/variables mirror AllTimesBounds' FixedDomain section (no
  `I.Boundaryless`, no extra IsManifold instances — instances derived in
  bodies where needed, as in `metricCovDeriv`).

## Discharge chain (what the `sorry` stands for)

Component core PROVEN in RicBoundClaims.lean (all sorry-free, checked):
`claim1_LC` → `hDlow` + the pointwise top factor; `claim2_component` → `hmix`;
`mixed_descent` → `|∇_H^N T| ≤ C(1+|∇_{H,U}^{N-1}D|)` pointwise per frame
domain.  Remaining assembly bricks:
1. smooth local-frame covering of compact `K` + per-domain frame constants;
2. component ↔ intrinsic bridge (`iterCovComp_eq_iterCov` +
   `normSq0S_identity_eq_sum_sq` at a `gRef`-ON frame — Parseval EXISTS at
   `Tensor0SRiemannian/Comparison.lean:220` — or bounded-gram equivalence);
3. moving ↔ fixed norm conversion of the Shi inputs through `hequiv`;
4. Ricci-component identification (`iterCovComp_eq_iterCov` at
   `ricciSection`), giving the `hT` smoothness and the tower match;
5. instantiate `mixed_descent` + `claim1_LC` per domain, take maxima over the
   finite cover.

The missing-API frontier list: a smooth `gRef`-orthonormal local-frame
producer (Gram–Schmidt on a trivialization; pointwise `OrthonormalBasisAt`
exists but carries no smoothness), and the slot-arity reindex adapter
`2 + N ↔ N + 2` for the Grönwall consumption.

## Why this file (and not RicBoundClaims/AllTimesBounds)

Final assembly above all producers: AllTimesBounds is the (huge) predicate +
Grönwall skeleton, RicBoundClaims is the component engine; this file imports
the former for vocabulary and will import the latter when the discharge
begins.  Keeping the endpoint in its own small file avoids coupling the
engine layer to the 4.7k-line skeleton.

## KEYSTONE FOUND — the smooth gRef-ON frame producer already exists (2026-06-10)

The "missing-API frontier" (a *smooth* `gRef`-orthonormal local frame) is NOT
missing.  **`exists_trivFrame_orthonormal_basis`** (`ApproximateIsometry.lean:4846`,
sorry-free) delivers exactly it: `∃ basisE`, with `frame := e₀.localFrame basisE`
on `u := e₀.baseSet`, `hframe : IsLocalFrameOn I E ∞ frame u`, `x ∈ u`, and
`∀ i j, gRef.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) = δᵢⱼ`
(gRef-ON AT the centre `x`).  (`exists_orthoFrameAt`/`exists_orthoBasisFrameAt` in
Evolution are pointwise-only — constant `fun i _x => e i`, no smoothness — do NOT
use them here.)  Downgrade `∞→1` for `aN_intrinsic_point` (mono).  The instances
it needs (`VectorBundle`, `ContMDiffVectorBundle 1`) are already in
RicBoundAssembly's variable block.

## Refined remaining decomposition (3 bricks; the frontier is brick 2)

`aN_intrinsic_point` (RicBoundAssembly.lean, DONE) consumes, over a frame domain
`u`: smoothness inputs (frame/Christoffel/metric/Ricci — Claim1Wiring patterns),
`Ginv`/`hinv`/`hGinv` (Claim1Wiring `gramE`/`ginvCompField`), and the COMPONENT
(`compL2`) bounds `hgB` (= (B_r), `1≤j≤N-1`) and `hShi` (Shi, `s≤N`) over all of
`u`, plus `hinvON` at the eval point.  From the keystone + `exists_trivFrame`,
the gap to ric_bound's intrinsic-over-K hypotheses is:

1. **`boundedGram`** (standard continuity): from the keystone frame, shrink to a
   small open `u' ∋ x ⊆ baseSet` with the frame Gram `G(z)=gRef.inner z(frame i z)
   (frame j z)` and its inverse bounded by a constant `CG≥1` on `u'` (continuity,
   `G(x)=Id`).  Feeds both the `Ginv`/`hGinv` data and brick 2's factor.
2. **`towerBridge`** (THE analytic frontier): generalize B5's *equality*
   `compL2_tower_eq` (which holds only at ON points) to a bounded-Gram *inequality*
   over `u'`: `compL2 (iterCovComp frame chr (frameComp0S T) j z) ≤ CG^? ·
   √normSq0S gRef z (iterCov gRef 2 T j z)` (+ reverse).  Apply with `T :=
   metricTensorField g` (intrinsic (B_r) → `hgB`) and `T := ricciSection (LC g)`
   (intrinsic moving Shi → `hShi`, routed through `normSq0S_le_of_metric_equiv`
   (Comparison.lean:520) for the moving↔fixed norm via eq 3.3 + `iterCovComp_eq_iterCov`).
3. **`uniformize`** (compactness bookkeeping): apply `aN_intrinsic_point` at each
   `x∈K` on its `u'_x`; finite subcover of compact `K`; `max` the `Cpp/Cppp`;
   assemble in RicBound.lean — RHS via `metricCovDerivNorm_eq_iterCov` (R4f), LHS
   via the `ricCovTower g gRef N = iterCov gRef 2 (ricciSection (LC g)) N` defeq.

Brick 1 = continuity; brick 2 = the genuine remaining math (component↔intrinsic
tower norm under a varying Gram); brick 3 = finite-cover maxima.  Build order:
1 → 2 → 3, each a named lemma (likely a new `RicBoundGoodFrame.lean` between
RicBoundAssembly and RicBound).

### Brick 2 is NOT from scratch — MSM135 Lemma 3.13 machinery exists

`Tensor0SRiemannian/Comparison.lean` already has the bounded-inverse-metric norm
comparison: `coordInner0S_diagonal_le_pow_identity` (`coordInner0S(diagInv μ) ≤
C^s·coordInner0S(Id)` for `μ ≤ C`), `normSq0S_diag_le` (the invariant form
`normSq0S h ≤ C^s·normSq0S g` given `g`-ON basis + `h`-diagonal-inverse `≤ C` =
Lemma 3.13), and `exists_diagInv_of_equiv` (from two-sided `C⁻¹g ≤ h ≤ Cg`, a
`g`-ON eigenbasis with `h`-inverse diagonal and `≤ C`).  For brick 2: `compL2²` in
the fixed frame `= coordInner0S identityInvMetric (tower)`, and `normSq0S gRef =
coordInner0S (Gram⁻¹) (tower)` (via `normSq0S_eq_coord`); so the bound is
`coordInner0S(Id) ≤ (λ_max Gram)^s · coordInner0S(Gram⁻¹)`, i.e. the same
quadratic-form-power estimate in the direction `Id ≤ C^s·Q` for symmetric posdef
`Q = Gram⁻¹` with `λ_min Q ≥ 1/CG`.  Route: either generalize
`coordInner0S_diagonal_le_pow_identity` to non-diagonal `Q` (operator-norm bound),
or diagonalize `Gram(z)` per `z` (its eigenbasis) and reuse the diagonal lemma —
the diagonal lemma + `exists_diagInv_of_equiv` are the templates.  This shrinks
brick 2 from "new analytic frontier" to "adapt Lemma 3.13 to the compL2 tower."

### Progress 2026-06-10 (verified)

- **`coordInner0S_identity_le_pow_diagonal`** (Comparison.lean, sorry-free, focus-
  checked): the REVERSE of `coordInner0S_diagonal_le_pow_identity` — raw
  component-ℓ² `coordInner0S Id A A ≤ (1/m)^s · coordInner0S (diagInv μ) A A` when
  `μ ≥ m > 0`.  First brick-2 building block (the diagonal case).
- Brick-2 general-`Q` (non-diagonal) core route CONFIRMED: slot-peel induction on
  `s`, peeling the last index via `Fin (s+1) → Idx ≃ Idx × (Fin s → Idx)`; the
  per-step PSD-pairing `Σ (Q-(1/C)Id)_{kl} B(v_k,v_l) ≥ 0` reuses the existing
  **`sum_posSemidef_mul_neg_semidef_le_zero`** (Analysis/Heat/MaximumPrinciple.lean)
  + `Matrix.PosSemidef.eigenvalues_nonneg`.  Fiddly part = the `tensor0SComponent`
  slice reindex under `Fin.cons`/`Fin.snoc`.  Alternative: bridge `coordInner0S` to
  a `Matrix` Kronecker-power quadratic form and use Mathlib PSD-Kronecker (if it
  exists) — heavier bridge, maybe shorter proof.  ~150 lines, slow (1–2 min) checks.
- HONEST: ric_bound theorem 0% proved (sorry); machinery ~75%; this lemma is a
  small slice of brick 2 (one of ~5 remaining pieces: general-Q core, brick 1
  continuity, brick 3 uniformize, Ricci-smoothness producer, final assembly).
  Multi-session.
