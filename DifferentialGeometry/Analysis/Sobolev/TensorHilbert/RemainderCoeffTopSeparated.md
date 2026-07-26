# RemainderCoeffTopSeparated.lean — construction roadmap (verified, not yet built)

## 2026-07-22 — planner CORRECTION verified; task is FEASIBLE, no missing frontier

This note is the executor's verified roadmap for the leaf file
`RemainderCoeffTopSeparated.lean` (not yet written).  It targets the three
per-field `_perOrder_topSeparated` producers requested in
`Geometry/Flow/RicciFlow/ShortTime/UNIF_EXISTENCE_PLAN.md` "CORRECTION
(2026-07-22, planner verification)":

- trace-Hessian field  (`traceHessianCoeff` / `ricciCometricFourTraceCastG0`, `(4,2)`)
- connection-difference field (`connDiffContrInsertionField`, `(3,4)`)
- Lie field (`linearizedRicciConnDiffOrder1KernelField`, `(3,4)`)

### Headline finding — the previous "WAIT-ON-CODEX" was WRONG (as the CORRECTION says)

The third executor's `ArmBaseCoeffJetL2Summed.md` (§ "remaining 3 fields …
WAIT-ON-CODEX") concluded the three fields had only R-DEPENDENT clean producers
(via `antidiagonalTupleGrid_integral_ballUniform_tameWindow`, `~R^{7k}`), and
that the R-independent engines lived only in a dirty file.  **Both premises are
false at HEAD `922dbc4ac`:**

1. All FOUR R-independent `_topSeparated_le` engines are COMMITTED-CLEAN in
   `Analysis/Spectral/Tensor/CovGrad/CurvatureCoefficientDifferenceJetTower.lean`:
   - `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`  (:1823) — the
     `connDiffSection` `(1,2)` engine.  Head
     `Hd_sec = appCcRS (∇^j raisedKoszul) (sharpFlatEndoCc)`,
     `rfns(Hd_sec) ≤ (10·S 0)·rfns(∇^{j+1}T)` (**Ktop R-independent**, `S` from
     `exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid`, depends only on
     `g₀,hδ₀`); remainder `≤ Kc j · ∑_{k<j} b(j-k)·antidiagTupleGrid b (k+1)`
     (Kc R-independent).
   - `rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le`
     (:10570) — `(0,4)`, a **COMPLETE ~250-line `∃Hd` TEMPLATE** built on the
     `connDiffSection` engine; head R-independent, remainder as
     `boundedFactorGridWindow b (i+1)(i+3)`.
   - `rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le`
     (:11114 HEAD / :11141 worktree) — `(0,4)`.
   - `rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le`
     (:11668 HEAD / :11695 worktree) — `(0,4)`.
2. The file's dirty state is the 64 unrelated inserted lines
   (`pureTrace` / `koszul_l2_succ`, hunks ~6455/~15078); the four engines are
   untouched and elaborate.

### Discipline clarification (why the arm0/arm1 lane is R-"independent")

"R-independent constants" means the **top-split coefficient `Ktop`** is
R-independent (built from `(g₀,hδ₀)` data only — the engine head).  The
low/remainder `Kc` is the DATA-WEIGHTED tame part and IS threaded through a
`…_ballUniform_tameWindow` converter exactly as arm0 does — verified: the arm0
L2 generic `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic`
(`CurvatureCoefficientDifferenceJetTower.lean:14447`) sets
`Ktop = 2·KtCr + 2·KtCu` (R-independent) and
`Kc i = (2·cbg i + 4·KcCr i + 4·KcCu i)·KI i` with `KI` from
`boundedFactorGridWindow_integral_ballUniform_tameWindow`.  So the ruling's
stop-signal is about the coefficient on the TOP difference `‖U−V‖_{a+2}`
(= `Ktop`), which the engine head keeps R-independent.  The previous executor
conflated "the field's only clean producer is the fully-R-dependent
`tameEnvelope_generic` (NO top-split)" with "no R-independent split exists" —
the engines provide the split the tame-envelope producers throw away.

## Target shapes (mirror `RemainderCoeffL2JetMoser.lean:1398/1532`)

Per field, a GENERIC (`g₁,P,htie`) producer + a realizedFam wrapper.  The
realizedFam wrapper is a verbatim clone of
`linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_topSeparated`
(`RemainderCoeffL2JetMoser.lean:1532`) — swap the coefficient/valence, keep the
`convexPerturbation`/`realizedFam`/`htie`/`hPball` plumbing and the
`tsmConvex_*` transfer lemmas unchanged.  Offset `p = 1` for connDiff/Lie
(top order `i+1`, low `i`), like arm1.

GENERIC conclusion (connDiff, `(3,4)`; Lie identical valence):
```
∃ Ktop ≥ 0, ∃ Kc : ℕ→ℝ (≥0), ∀ g₁ P {δ} (hδ_le) (hδ) (htie) (hPball : ∀ j≤a+2, ‖∇^jP‖≤R),
  ∀ i ≤ a, ∃ Hd : SmoothCcTensor g₀ 3 (4+i),
    (∀ x, rfns(Hd) ≤ Ktop·rfns(∇^{i+1}P)) ∧
    ‖Hd‖² ≤ Ktop·‖∇^{i+1}P‖² ∧
    ‖∇^i(connDiffContrInsertionField g₀ g₁) - Hd‖² ≤ Kc i·(1 + ∑_{j<i+1} ‖∇^jP‖²)
```

## Construction recipe (all lemmas CONFIRMED to exist committed-clean)

### connDiff — most tractable; NO background (`connDiff(g₀,g₀)=0`)

Field identity: `connDiffContrInsertionField g₀ g₁ =
reindexCoeffGen (slotExtend 2 3 (slotExtend 1 2 (connDiffSection g₁ g₀))) coreInPerm201`
— `connDiffContrInsertionField_eq_reindex_slotExtend_two`
(`RicciConnDiffOrder1TameEnvelope.lean:893`).

Section→field jet transfer (rfns, factor `fr²`, `fr = finrank`), copy the
`hcore_pt` chain from the existing tameEnvelope
(`RicciConnDiffOrder1TameEnvelope.lean:1044–1111`):
- `rfns_iteratedCovGrad_reindexCoeffGen_eq` (rfns-invariant reindex),
- `rfns_iteratedCovGrad_slotExtend_le` twice (`OperatorFieldFibreNormJet.lean:713`, each ≤ `fr`).

`∃Hd` field-level construction (the one genuinely intricate part; template =
`:10570` HeadCore/HPA/Hd):
- Section head `Hd_sec := appCcRS (∇^i raisedKoszul) (sharpFlatEndoCc)` (engine
  `.1`, order `i`).  Tensor commute for the split transfer:
  `iteratedCovGrad_reindexCoeffGen` (`SymmAbsorbedCoeffInputReindexBounds.lean:211`,
  clean `∇^i(reindex X ρ)=reindex(∇^iX)ρ`) + `exists_iteratedCovGrad_slotExtend_rsDomDomCongr`
  (`OperatorFieldFibreNormJet.lean:618`) TWICE (obtain σ₁ for `slotExtend 1 2 section`,
  σ₂ for `slotExtend 2 3 (slotExtend 1 2 section)`).  Define
  `Hd := reindexCoeffGen (rsDomDomCongrSection σ₂ (castRankCc_db (slotExtend 2 3
     (rsDomDomCongrSection σ₁ (castRankCc_db (slotExtend 1 2 Hd_sec)))))) coreInPerm201`.
- Difference identity `∇^i(field) - Hd = [same op](∇^i(section) - Hd_sec)` by
  linearity: `slotExtend_sub`, `reindexCoeffGen_sub_fw`
  (`DeTurckRemainderTameLipschitz.lean:35519`; if private, add public
  `reindexCoeffGen_sub` / `rsDomDomCongrSection_sub` / `castRankCc_db_sub` at the
  `TensorSpectral` layer), `tsRsDomDomCongr_sub`, `SmoothCcTensor.toSection_sub`.
- rfns transfer of head and of the difference: same `fr²` chain +
  `riemannianFiberNormSq_domDomCongr_covariant`, `tsRfns_castRankCc_db_zero`,
  `rfns_slotExtend_eq` (`OperatorFieldFibreNormJet.lean:227`).

Remainder reshape+integrate (CONFIRMED clean):
- engine `.2` gives `∑_{k<i} b(i-k)·antidiagTupleGrid b (k+1)`;
- `tsResSum_le_boundedWindow` (`CurvatureCoefficientDifferenceJetTower.lean:10312`,
  PRIVATE): `∑_{k<j} b(j-k)·antidiagTupleGrid b (k+1) ≤ j·boundedFactorGridWindow b j (j+2)`.
  **It is a 14-line PURE-combinatorial lemma whose only deps are PUBLIC
  `Combinatorics.*` (`antidiagonalTupleGrid_eq_boundedFactorGrid`,
  `single_factor_mul_boundedFactorGrid_le`, `boundedFactorGrid_le_boundedFactorGridWindow`)
  → COPY it (and `tsTgridSum_le_boundedWindow` :10296, `tsRfns_sub_le` :10328)
  verbatim as `private` helpers into the new file.**  Not a blocker.
- `boundedFactorGridWindow_integral_ballUniform_tameWindow`
  (`:13180`, PUBLIC) → `K i·(1 + ∑_{j<i+2}‖∇^jP‖²)`; window-match via
  `Combinatorics.boundedFactorGridWindow_mono`.
- L2 lift: `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` (as arm0 :14555+).

### RECOMMENDED cheaper route for the SUMMED "second half" — skip the `∃Hd`

The `jetL2_sum_of_perOrder` engine (`ArmBaseCoeffJetL2Summed.lean:84`) only needs
the SCALAR per-order `‖∇^i F‖² ≤ 2(Kc i·(1+∑low)) + 2(Ktop·top)`, NOT the `Hd`
witness (the arm summed proofs DERIVE that scalar from their `∃Hd` via
`norm_sq_le_two_sub`).  So a DIRECT per-order bound
```
‖∇^i(connDiffContrInsertionField g₀ g₁)‖² ≤ Ktop·‖∇^{i+1}P‖²  +  Kc i·(1+∑_{j<i+2}‖∇^jP‖²)
```
(R-independent `Ktop = 2·fr²·(10·S 0)`; `Kc i` R-dependent tame, via the converter)
FEEDS `jetL2_sum_of_perOrder` directly and yields the connDiff SUMMED bound — the
5th-of-5 constituent the data-weighted threeArm precursor needs (arm0/arm1 done;
`ArmBaseCoeffJetL2Summed.md`).  It AVOIDS the intricate field-level `Hd`/DDC
construction entirely:
1. engine (:1823) at order `i`: `rfns(∇^i section) = rfns(Hd_sec + rem_sec)`
   `≤ 2·rfns(Hd_sec) + 2·rfns(rem_sec)` (`riemannianFiberNormSq_add_le`, rewriting
   `∇^i section = Hd_sec + (∇^i section − Hd_sec)`);
2. `≤ 2·(10·S 0)·rfns(∇^{i+1}T) + 2·Kc0 i·(∑_k b(i-k)·antidiagTupleGrid(k+1))`
   (engine `.1`, `.2`);
3. field transfer `rfns(∇^i field) ≤ fr²·rfns(∇^i section)` — COPY tameEnvelope
   `hcore_pt` h0/h1/h2 (`RicciConnDiffOrder1TameEnvelope.lean:1053–1096`);
4. integrate: top → `‖∇^{i+1}T‖²`; remainder → copied `tsResSum_le_boundedWindow`
   + `boundedFactorGridWindow_integral_ballUniform_tameWindow`.
Then realizedFam wrapper (clone arm1 :1532) + `jetL2_sum_of_perOrder` (offset `p=1`).
This is ~180–220 lines and has NO uncertain step.  Deliver the SUMMED bounds this
way first; the `∃Hd` per-order form (needed only if a downstream DIFFERENCE
estimate must pair the individual field tops) is the recipe in the previous
section, done later.

### Lie — combination of connDiff

`linearizedRicciConnDiffOrder1KernelField` (`(3,4)`,
`RicciConnDiffOrder1TameEnvelope.lean:89`) `= -(5 reindex/appCcRS/slotPerm-permuted
copies of connDiffContrInsertionField)` — `kernelField_eq_neg_arm_combination`
(:738).  Each permuted copy has the SAME `rfns∘∇^i` as connDiff
(`armOuter_rfns_eq`/`armFull_rfns_eq`, :760/:783; `armFull_norm_eq` :852).  So the
Lie producer is the connDiff producer + a `5·`-triangle assembly (`c3_norm_five_le`
:879).  Build connDiff FIRST, reuse.

### traceHessian — combines the three curvature `(0,4)` engines

`traceHessianCoeff` / `(4,2)` form `ricciCometricFourTraceCastG0`
(`RicciConnDiffOrder1TameEnvelope.lean:~85`) is the cometric-trace field (via
`ricciCometricFourTraceCLM g₁`, involves `g₁⁻¹`), NOT a slotExtend of
connDiffSection.  Its R-independent split must be assembled from
`riemannLoweredBackgroundDifference` (:10570), `…ricEndoBackgroundDifferenceField`
(:11141), `…riemannG1LoweringDifference` (:11695), plus the C₂-deviation sup
`traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns`
(`RemainderCoeffL2JetMoser.lean:345`).  This is the hardest of the three; the
exact `traceHessianCoeff = f(the three engine fields)` decomposition must be read
off the `ricciCometricFourTrace…` definitions first.  Do LAST.

## Verification environment (validated 2026-07-22)

`lake build` is blocked by the pre-existing `.olean.hash` split (see
ArmBaseCoeffJetL2Summed.md).  Direct `lean` typecheck WORKS (EXIT 0 on a heavy
import test).  Recipe (git-bash):
```
WROOT="$(pwd -W)"   # C:/Users/liao9/.codex/worktrees/e87b/testdifferential-geometry
LP="C:/dgbuild/e87b/lib/lean"
for p in mathlib batteries aesop Qq importGraph proofwidgets plausible LeanSearchClient Cli; do
  LP="$LP;$WROOT/.lake/packages/$p/.lake/build/lib/lean"; done
LEAN_PATH="$LP" LEAN_NUM_THREADS=4 lean <file.lean>      # ~2–4 min for a heavy import
```
File header: `set_option autoImplicit false` + `relaxedAutoImplicit false` +
`maxSynthPendingDepth 3` (matches lakefile).  Import
`…RemainderCoeffL2JetMoser` (brings in the JetTower engines transitively).
`#print axioms` on every new theorem must be `[propext, Classical.choice,
Quot.sound]`.  One `lean` process at a time.

## Guardrails standing

Never commit; never edit the dirty `CurvatureCoefficientDifferenceJetTower.lean`
(its 64 dirty lines at ~6455/~15078 compile on any build; if `pureTrace` /
`koszul_l2_succ` FAIL to elaborate, THAT is the genuine wait-on-Codex condition).
Import + use its committed engines freely.

## Honest scope / status

Feasible, no missing mathematical frontier — every lemma above is committed and
named.  BUT each field is a ~250–350-line intricate tensor-transfer assembly
mirroring the :10570 template, with ~3-min focused-check cycles.  This executor
VERIFIED feasibility + full recipe + environment but did NOT land compiled Lean
(scope exceeds one careful-iteration session).  Recommended order: connDiff
(has NO background, cleanest transfer) → Lie (reuse) → traceHessian (hardest).
Black box (N) `ricci_flow_unif_existence` remains **0%**; these producers are
constituents of the threeArm precursor (ruling item 2 of the R1τ frontier) and
sit far below it.

## 2026-07-22 — connDiff DIRECT summed route LANDED (this roadmap worked as written)

The connDiff field is DONE, in the new leaf
`Analysis/Sobolev/TensorHilbert/ConnDiffJetL2Summed.lean` (+`.md`), namespace
`DifferentialGeometry.Integral.Connection`.  Three GREEN sorry-free theorems (generic
per-order → realizedFam per-order → realizedFam summed);
`connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` is the deliverable, both
windows at order `a+2`, `Ktop = 2·finrank²·Kt0` R-independent, `#print axioms` = standard three.
The DIRECT route above is accurate; two refinements for the next (Lie / traceHessian) executor:

- The remainder low window lands at `i+2` (converter `boundedFactorGridWindow …(i+1)(i+3)`) while
  the top point is order `i+1` — mismatched offsets.  The arm `jetL2_sum_of_perOrder` (single
  offset `p`) does NOT apply; use the new `jetL2_sum_lowShift` (independent top offset `p`, low
  offset `q`; connDiff = `p=1,q=2`) copied/adaptable from `ConnDiffJetL2Summed.lean`.
- Fold the engine head via `set Hd := appCcRS …` AFTER obtaining `heng`.  The `∇^i sec = Hd +
  (∇^i sec − Hd)` split is `riemannianFiberNormSq_add_le` + `simp only [SmoothCcTensor.toSection_sub,
  ContMDiffSection.coe_sub, Pi.sub_apply]; abel` (the `toSection_add/sub` lemmas are section-level
  `rfl`, so `rw [← toSection_add]` on a pointwise `…x + …x` FAILS).
- `iteratedCovGrad_smul_real` is `private` to `RemainderCoeffL2JetMoser`; copy it (Lie reuses the
  connDiff producer directly, so may not even need it).

Lie next: `linearizedRicciConnDiffOrder1KernelField = neg 5-permuted-copy combination of
connDiffContrInsertionField` (`kernelField_eq_neg_arm_combination`), each copy same `rfns∘∇^i`;
so its summed bound = the connDiff summed producer + a `5·`-triangle assembly.

## 2026-07-22 — traceHessian LANDED, but the "three curvature engines" section above is WRONG

CORRECTION to the "traceHessian — combines the three curvature `(0,4)` engines" section: that
premise is a **misclassification** and does not hold for this field.  Verified at HEAD `922dbc4ac`
while building `TraceHessJetL2Summed.lean` (both public theorems GREEN / axioms standard three,
imports only committed-clean `RemainderCoeffL2JetMoser`).

- `traceHessianCoeff g₀ g₁` is a **purely algebraic coefficient in the cometric `g₁⁻¹`**
  (`traceHessianFib = cometricDoubleTraceFib ∘ domDomCongrFib`,
  `RicciLinearizationArmFields.lean:149/221`) — the low-order coefficient in
  `linearizedRicciConnDiffOrder1CoeffField = appCcRS(traceHessianCoeff)(kernelField)`
  (`RicciConnDiffOrder1TameEnvelope.lean:116`).  It carries **no derivative gain**; the gain is in
  the kernelField (= Lie field).
- The three `(0,4)` engines bound curvature-**difference** fields (top at order `i+2`).  There is
  **no committed identity** relating `traceHessianCoeff`/`ricciCometricFourTraceCastG0` to them —
  the engine names appear only in `CurvatureCoefficientDifferenceJetTower.lean`.  The two committed
  trace-Hessian decompositions both route to the metric-inverse difference
  (`deTurckPrincipalCometricCoeff`/`gInvDiffSlotCoeff`, `RemainderCoeffL2JetMoser.lean:328`; or
  `ricciArmPrincipalCoeffPure`/`gInvDiffRaisedEndoField`, `RicciConnDiffOrder1TameEnvelope.lean:137/171`).
  The full `topSeparated` engine inventory has NONE for any metric-inverse field.
- The metric-inverse jet `∇^i gInvDiffSlotCoeff` is controlled by order-`≤ i` data
  (`gInvDiffSlotCoeff_perOrder_l2_tame`, `AppCcJetWindowTame.lean:718`: `≤ K i·(1+‖∇^i P‖²)`).  So
  the field reaches nothing at the protected `a+1`/`a+2` top window ⇒ **`Ktop = 0` is the correct
  value** (not a mask; discipline vacuously satisfied at the top).

Delivered: `TraceHessJetL2Summed.lean` with `Ktop = 0` and a UNIFORM-CONSTANT `Kc` (reshape of the
public ball-uniform `traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform`, `:446`), summed via
the copied `jetL2_sum_lowShift`.  Data-weighting `Kc` (the loose part) is the identified follow-up —
it needs the metric-inverse tame machinery (private `gInvDiffSlotCoeff_perOrder_l2_tame` + its
`productGridTerm_integral_le_topOrderJetSq` dep ≈ 660-line copy, or the public Hs-norm
`deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic` `:1008` with a fragile Hs→jet-L2 bridge);
`Ktop` stays `0` regardless.  See `TraceHessJetL2Summed.md`.  All five constituents now carry a
uniform-shape summed producer.
