# SobolevNonlinearityExistence.lean — notes

## 2026-07-22 — R1τ route test (UNIF_N ruling item 2): second-order TAME difference estimate

Task: prove a smooth-core SECOND-ORDER TAME difference estimate for the symmetric
Ricci–DeTurck remainder, sibling of `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm`,
WITHOUT an `H^{a+2}`-ball hypothesis. Target shape (both high–low orientations retained):

```
‖N(T) − N(T')‖_{H^a} ≤ K · ( (1 + max ‖T‖_{a+1} ‖T'‖_{a+1}) · ‖T−T'‖_{a+2}
                           + max ‖T‖_{a+2} ‖T'‖_{a+2} · ‖T−T'‖_{a+1} )
```

Stop signal (from `UNIF_N_PRO_RULING.md`): a forced pointwise `H^{a+2}` radius, or a term
`‖T‖_{a+2} · ‖T−T'‖_{a+2}`.

### VERDICT: (a) FEASIBLE — the stop signal is NOT hit.

Both orientations close with **R-independent** constants. No `‖T‖_{a+2}·‖T−T'‖_{a+2}` product,
no pointwise `H^{a+2}` radius. Verified by tracing the existing decomposition, not by a new
Lean lemma (see "Implementation status").

### Where the reference proof hides `‖T‖_{a+2}` inside `R`

Chain, all in this file unless noted:
- `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm` (1924): `hball_conv` turns
  `‖ι_{a+2}T‖ ≤ R` into `∀ j≤a+2, ‖∇^j T‖ ≤ Cb·R`, fed to →
- `deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm` (1810), on →
- `deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm` (1421), which
  splits `N(T)−N(T') = A₀+A₁+A₂`, `Aₘ = appCc g₀ (2+m) 2 Cₘ (∇^m(T−T'))`, via →
- `deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_dataWeighted_ballUniform_of_symm` (1353) →
  `..._fibreWeighted_...` (`DeTurckRemainderTameLipschitz.lean:36054`).

The `R` enters the coefficient bounds `ΛC, Γ` (sup / jet-L2 of `C₀,C₁,C₂`), which are
`ballUniform` (opaque constant per fixed `R`). Because `1421` LUMPS everything into a single
`base ~ Γ²+ΛC² ~ R²`, its output `Ccov ~ √base ~ R` multiplies BOTH the `‖T−T'‖_{a+2}` and
`‖T−T'‖_{a+1}` terms — so the reference's `‖T−T'‖_{a+2}` coefficient is `~R·Dm`
(the forbidden shape, hidden inside `K`).

### Why it is nonetheless feasible (the two facts that matter)

1. **Top arm `A₂` (coefficient of `∇²(T−T')`) is R-independent.** The `fibreWeighted` proof
   (36054) builds `C₂ = deTurckPhiTotPathIntegral(…) − deTurckPhiMetTotal(g₀)` (the top-cometric
   path-integral DEVIATION) and gives `rfns(C₂) ≤ (c·max βT βT')²` from
   `deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform`
   (`DeTurckRemainderTameLipschitz.lean:35645`, line 35700):
   `c = √(8·CTH 0 + 8·CR 0)·(dim/(1−δ₀))`, where `CTH, CR` come from
   `traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns` and
   `ricciArmPrincipalCoeff_sub_background_...` (`RemainderCoeffL2JetMoser.md`/
   `Analysis/Sobolev/TensorHilbert/RemainderCoeffL2JetMoser.lean:345`), **called with only `g₀`
   — no `a`, no `R`.** So `c` is R-INDEPENDENT and `βT ~ ‖T‖_{a+1}` is LOW order. The tame
   product (`appCcTwoArmQUniform`, this file 1222) then gives `A₂`'s dangerous piece as
   `(C₂ sup)·‖T−T'‖_{a+2} ~ c·Dm·‖T−T'‖_{a+2}` = orientation 1. **No `‖T‖_{a+2}·‖T−T'‖_{a+2}`.**
   The `fibreWeighted`/`dataWeighted` lemmas WEAKEN this tight `c` to `ΛC ~ R` (36161–36165,
   1414–1417); the un-weakened `c` is what the route needs.

2. **Low arms `A₀,A₁` are data-weightable with R-independent constants.** `C₀,C₁` (linearized
   Ricci arm0/arm1 + connection-difference/Lie fields) genuinely carry `∂²(path)` content, so
   their bounds scale like `‖T‖_{a+2}`. The exposed `ballUniform` bounds
   (`ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform`,
   `RicciThreeArmAppCc.lean:3345`; `linearizedRicciArm0BaseCoeff_..._ballUniform`) are opaque-in-R
   and CANNOT expose that factor — BUT the **top-separated / tame-envelope** layer does:
   `linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_topSeparated`
   (`RemainderCoeffL2JetMoser.lean:1398`) splits `∇^i(C₀) = Hd + rem` with
   `‖Hd‖² ≤ Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²)` (the `‖T‖_{a+2}` data-weight, → orientation 2) and
   `‖rem‖² ≤ Kc i·(1 + ∑_{j≤i+1}(‖∇^jT‖²+‖∇^jT'‖²))` (order ≤ a+1, → orientation 1). The
   constants `Ktop, Kc` are **R-INDEPENDENT**: their generic producer
   `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic`
   (`CurvatureCoefficientDifferenceJetTower.lean:14447`) builds them from
   `rfns_iteratedCovGrad_ricciArmOrder0{Riemann,Curv}Coeff_backgroundDifference_topSeparated_le`
   (called with only `g₀, hδ₀`). Analogues exist for arm1
   (`ricciArmOrder1KoszulCoeff_..._topSeparated`, `RicciArmOrder1KoszulTameEnvelope.lean`) and the
   DeTurck connection-difference/Lie fields (`RicciConnDiffOrder1TameEnvelope.lean`:
   `connDiffContrInsertionField_...tameEnvelope`, `linearizedRicciConnDiffOrder1KernelField_...`).

### Provenance of each high–low term (for the report)

- Orientation 1 `(1+Dm)·‖T−T'‖_{a+2}`  ← top-arm deviation sup (`c`, R-indep, from
  `deTurckPhiTotPathIntegral_deviation_...`) + low-arm top-separated REMAINDERS (`Kc`, order ≤ a+1).
- Orientation 2 `max‖T‖_{a+2}‖T'‖_{a+2}·‖T−T'‖_{a+1}`  ← low-arm top-separated HIGH parts `Hd`
  (`Ktop`, R-indep, data-weighted by `‖∇^{i+2}(T,T')‖`) + top-arm jet-L2 (`Γd`).
- Difference factors `‖ι_{a+2}(T−T')‖`, `‖ι_{a+1}(T−T')‖` and the smooth-core ↔ iteratedCovGrad
  bridge: `exists_{smoothCcToTensorHs_le_iteratedCovGrad_sum,iteratedCovGrad_sum_le_smoothCcToTensorHs}_general`
  (as in the reference 1924/1810).

### Implementation status: NOT a compiling lemma this session (multi-lemma assembly)

No Lean lemma was added. The smooth-core tame theorem is NOT a "one theorem + one precursor"
task: it requires assembling a full **data-weighted (top-separated) threeArm coefficient bound**
(re-deriving the `canonicalTop`+`curvatureFold`+`deviation` decomposition of `36054` with the
top-separated per-field bounds instead of the ballUniform ones), then a **covariant tame
estimate** (analogue of `1421` keeping the top arm's `c` and the low arms' `Hd/rem` split), then
the **smooth-core lift** (analogue of `1924/1810`). Much of the threeArm re-derivation would land
in the frozen `DeTurckRemainderTameLipschitz.lean`, and its deepest generic producers
(`CurvatureCoefficientDifferenceJetTower.lean`) are in-flight Codex work (`M` in git status), so
building on them now risks churn. Adding a partial covariant/threeArm skeleton in this file would
not reach the theorem and would be orphaned machinery, so none was added.

Smallest next brick (in the tame-envelope layer, not this file): sum the per-order
`linearizedRicciArm{0,1}BaseCoeff_..._topSeparated` bounds over `i ≤ a` into a single R-independent
data-weighted jet-L2 bound `∑_{i≤a}‖∇^i C‖² ≤ Ktop·(‖T‖²_{a+2}+‖T'‖²_{a+2}) + Kc'·(1+‖T‖²_{a+1}+‖T'‖²_{a+1})`
per coefficient field, then combine the fields into a data-weighted threeArm coefficient bound
(the topSeparated analogue of `36054`). That bound is the single input a covariant tame estimate
needs; everything above it mirrors `1421 → 1810 → 1924`.

Do NOT re-introduce an `H^{a+2}`-ball or a new `Classical.choose` to hide the low-arm `‖T‖_{a+2}`
— it must stay the explicit orientation-2 factor (the ruling's time integration
`‖A·B‖_{L²_t} ≤ ‖A‖_{L^∞_t H^{a+1}}‖B‖_{L²_t H^{a+2}}` consumes exactly that).
