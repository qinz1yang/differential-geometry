# ArmBaseCoeffJetL2Summed.lean — notes

## 2026-07-22 — R1τ item-(2) machinery: summed data-weighted jet-L2 arm bounds

New leaf file in the tame-envelope layer (`Analysis/Sobolev/TensorHilbert/`, namespace
`DifferentialGeometry.Integral.Connection`).  It is the ratified "smallest next brick" of the
R1τ lane (see `Geometry/Flow/RicciFlow/ShortTime/UNIF_EXISTENCE_PLAN.md` "Planner acceptance"
and `Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.md`).

### What it proves (both GREEN, sorry-free)

For each arm field `F ∈ {arm0, arm1}`, sum the per-order top-separated bound over `i ≤ a` into
one `R`-independent data-weighted jet-L2 bound:

- `linearizedRicciArm0BaseCoeff_realizedFam_jetL2_summed_topSeparated`
  `∑_{i≤a} ‖∇^i (arm0coeff)‖² ≤ Ktop·(∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²)) + Kc·(1 + ∑_{j<a+2}(…))`
  (top window order `a+2`, low window order `a+1`).

- `linearizedRicciArm1BaseCoeff_realizedFam_jetL2_summed_topSeparated`
  `∑_{i≤a} ‖∇^i (arm1coeff)‖² ≤ Ktop·(∑_{j<a+2}(…)) + Kc·(1 + ∑_{j<a+1}(…))`
  (natural windows one order below arm0: top `a+1`, low `a` — arm1 is the
  first-covariant-derivative arm.  Kept at natural/weakest form; a consumer wanting the uniform
  `a+2 / a+1` shape weakens by monotonicity).

Provenance of the constants (the discipline point): `Ktop = 2·Ktop_perOrder`,
`Kc = 2·∑_{i≤a} Kc_perOrder i`, both built ONLY from the per-order constants of
`linearizedRicciArm{0,1}BaseCoeff_realizedFam_jetL2_perOrder_topSeparated`
(`RemainderCoeffL2JetMoser.lean:1398/1532`, committed-clean).  **No ball radius `R`, no
pointwise `H^{a+2}` bound enters the constants** — the ruling's stop signal is NOT hit.  The `R`
hypothesis is still threaded (it feeds the per-order lemma to obtain the split `Hd`), but the
lumped constants do not scale with `R`.  `#print axioms` on both theorems = `[propext,
Classical.choice, Quot.sound]` (no `sorryAx`); this also confirms the consumed committed exports
have NOT drifted.

### Proof structure

Three generic helpers (pure real/`Finset`, no geometry, `private`):
- `norm_sq_le_two_sub` : `‖x‖² ≤ 2‖x−y‖² + 2‖y‖²`.  **Must use `[SeminormedAddCommGroup X]`,
  not `NormedAddCommGroup`** — `SmoothCcTensor g r s` carries only the L² *seminorm*
  (`SeminormedAddCommGroup` + `InnerProductSpace ℝ`, `SmoothSections/PreHilbert.lean:111/118`);
  there is NO `NormedAddCommGroup` instance.  `norm_sub_norm_le`/`norm_nonneg` hold at seminorm
  level, so the split goes through.
- `sum_shift_le` : `∑_{i<m} g(i+c) ≤ ∑_{j<m+c} g j` for nonneg `g` (embedding `i↦i+c` + subset).
- `jetL2_sum_of_perOrder` : the actual summation.  Per-order split
  `f i ≤ 2·(Kc i·(1+low_{i+p})) + 2·(Ktop·w(i+p))` summed to top-window `range(a+1+p)` and
  low-window `range(a+p)`.  Parameterized by the offset `p` (2 for arm0, 1 for arm1) so both arms
  reuse it.

Each arm theorem: `obtain` the per-order `∃ Ktop, Kc, hbound`; build `hper i` from `hbound`'s
`Hd`-split via `norm_sq_le_two_sub` + `linarith`; then `exact jetL2_sum_of_perOrder …` (closes by
defeq: `a+1+p = a+3`/`a+2`, and the passed lambdas β-reduce to the goal's explicit sums).

### Lessons / traps hit

- `SmoothCcTensor` is only `SeminormedAddCommGroup`, never `NormedAddCommGroup`.  Any generic
  norm lemma applied to `‖iteratedCovGrad …‖` must ask for the seminormed class.
- `Finset.range_subset`'s iff direction is not the assumed `(m≤n) → (range m ⊆ range n)` shape in
  a way that let `.mpr (h : m≤n)` typecheck here; the subset goal stayed unfolded as
  `∀ x < i+p, x ∈ range(a+p)` and a bare `omega` choked on the Finset membership (mystery `x` in
  the counterexample).  Robust fix: prove the subset element-wise
  `intro x hx; rw [Finset.mem_range] at hx ⊢; omega`.
- Keeping the per-order RHS shape as `2·(Kc i·(…)) + 2·(Ktop·…)` (explicit `2·(·)`) makes the
  `hper` step close by plain `linarith` against `hbound`'s `hres`/`hL2h` atoms, and lets
  `jetL2_sum_of_perOrder` factor the `2` cleanly.
- Stating arm1 in its natural tight window (rather than weakening to the uniform `a+2/a+1` shape
  inside the theorem) avoids a `β`-redex atom-mismatch that `linarith` cannot bridge across the
  instantiated abstract `w`.  Weaken downstream if needed, not here.

### Verification status

Focused check: **GREEN, sorry-free** via a direct `lean` typecheck against the redirected olean
tree `C:/dgbuild/e87b/lib/lean` (the same valid oleans the project build replays), with the
lakefile's correctness-relevant options replicated in-file (`autoImplicit false`,
`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).  `#print axioms` = standard three.

Authoritative `lake build +…ArmBaseCoeffJetL2Summed` is BLOCKED by a **pre-existing worktree
build-cache inconsistency unrelated to this file and unrelated to the dirty JetTower**: lake's
"Replaying" step aborts on a missing `.olean.hash` for
`…Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHSEigenvalueBounds.
EigenvectorChartRHSDiffNumeratorWkpNormSharp` sought in the worktree `.lake/build/lib/lean`,
while that module's `.olean`+`.olean.hash` DO exist in the redirected `C:/dgbuild/e87b/lib/lean`.
The intended entry point `scripts/lake-locked.ps1` is absent from this worktree, so the
build-dir/hash split cannot be reconciled here.  This should be run once the environment's
build-dir redirection is repaired (or via the intended `lake-locked` wrapper).

### Scope note: threeArm combination NOT attempted (does not compose cleanly)

The route-test note's "data-weighted threeArm coefficient bound" needs `∑‖∇^i C₀‖² , ∑‖∇^i C₁‖²,
∑‖∇^i C₂‖²` for the ASSEMBLED total coefficients `C₀:(2,2), C₁:(3,2), C₂:(4,2)` of
`deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm`
(`DeTurckRemainderTameLipschitz.lean:36054`).  `C₀`/`C₁` are SUMS of several fields
(arm0/arm1 + trace-Hessian + connection-difference + Lie), and `C₂` is the top cometric
path-integral deviation.  arm0/arm1 (this file) are only TWO of those constituent fields; the
`C₀=…+arm0+…` / `C₁=…+arm1+…` decomposition itself lives in the FROZEN
`DeTurckRemainderTameLipschitz.lean` (the `canonicalTop+curvatureFold+deviation` structure) and
its deepest producers are the IN-FLIGHT dirty `CurvatureCoefficientDifferenceJetTower.lean`.
So the combination is not cleanly composable from arm0+arm1 alone — it requires (a) summed
data-weighted bounds for the remaining fields (trace-Hessian, connDiff, Lie, deviation) and
(b) the frozen-file decomposition re-derivation.  Per the route-test note and ruling stop-signal
discipline, STOPPED at the two arm bounds; no orphan skeleton added.

### Honest accounting

Black box (N) `ricci_flow_unif_existence` remains **0%** (its `sorry` is untouched).  This is
item-(2) machinery of the R1τ six-item frontier; within item (2), the summed per-field arm
bounds are 2 of the ~5 constituent per-field bounds the data-weighted threeArm precursor needs,
and the precursor is itself one of several lemmas below the smooth-core tame theorem.  Realistic
whole-(N) fraction: still ~0% (a couple of low-level tame-envelope helpers on a multi-week
frontier).

## 2026-07-22 — remaining 3 fields (traceHessian / connDiff / Lie): WAIT-ON-CODEX, none buildable

Follow-up brick: extend the summed pattern to the other ~3 constituent fields of the threeArm
`C₀,C₁` (trace-Hessian, connection-difference, Lie).  **Result: no new Lean was added — none of
the three has a committed-clean per-order producer with R-independent constants, so a
discipline-compliant (no-`R`-in-constants) summed bound cannot be built from clean inputs.**  All
three are wait-on-Codex.  The blocker is a *constant-provenance* wall, not a summation-engine gap:
`jetL2_sum_of_perOrder` is already field-agnostic and covers all 5 fields; the missing pieces are
purely the three R-independent per-order producers.

### Why arm0/arm1 succeed but these three do not

arm0/arm1's `_realizedFam_jetL2_perOrder_topSeparated` (`RemainderCoeffL2JetMoser.lean:1398/1532`)
split `∇^i C = Hd + rem`, with `‖Hd‖² ≤ Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²)` and
`‖rem‖² ≤ Kc i·(1+low)`, and `Ktop,Kc` **R-independent** because their engine
`rfns_iteratedCovGrad_ricciArmOrder0{Riemann,Curv}Coeff_backgroundDifference_topSeparated_le`
separates the genuinely-top *linear* `∇^{i+2}(path)` piece (background `g₀`-coefficient) from a
*background-subtracted* remainder whose products are bounded WITHOUT the ball radius.

The clean producers for the other three fields instead collapse a genuine **nonlinear jet
product** (from the `g₁⁻¹ = (g₀+P)⁻¹` Neumann expansion) via
`antidiagonalTupleGrid_integral_ballUniform_tameWindow`
(`CurvatureCoefficientDifferenceJetTower.lean:8556`, **DIRTY**), whose constant
`K k = (∑card)·Gfun k + vol`, `Gfun k = k·(max Lam (max (Cgn k) 1))^{7k}`,
`Lam = Cemb·√(a+2)·R` — i.e. **`K k` grows like `R^{7k}`, R-DEPENDENT**.  Summing an
`R`-dependent per-order bound puts `R` in the lumped constant ⟹ the coefficient later multiplies
`‖∇^m(T−T')‖`, producing the ruling's forbidden `C(R₂)·‖U−V‖_{H^{a+2}}` shape.  Stop-signal.

### Per-field status (exact producers + constant provenance)

- **connection-difference** `connDiffContrInsertionField` (`(3,4)`).  Clean producer
  `connDiffContrInsertionField_order0sup_perOrder_l2_tameEnvelope_generic`
  (`RicciConnDiffOrder1TameEnvelope.lean:982`): *tame-envelope* shape
  `‖∇^l F‖² ≤ K l·(1+∑_{j<l+2}‖∇^j P‖²)` (no `Hd` split, generic in `g₁/P` not realizedFam),
  `K l = fr²·CA l·∑_{k<l+2} K_t k` with `K_t` = the R-dependent `antidiagonalTupleGrid` constant
  above (used at `:1004`).  **R-DEPENDENT.**
- **Lie kernel** `linearizedRicciConnDiffOrder1KernelField` (`(3,4)`).  Clean producer
  `linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`
  (`RicciConnDiffOrder1TameEnvelope.lean:1240`) is built *directly* from the connDiff producer
  (`:1259`, `K l = 25·Kc l`; Lie = fixed reindex combination of connDiff insertions via
  `kernelField_eq_neg_arm_combination`).  Inherits the R-dependence.  **R-DEPENDENT.**
- **trace-Hessian** `traceHessianCoeff` / `(4,2)` form `ricciCometricFourTraceCastG0`.  Clean
  realizedFam producer `traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform`
  (`RemainderCoeffL2JetMoser.lean:446`) is even weaker — a *pure* opaque bound
  `‖∇^i(traceHessianCoeff realizedFam)‖² ≤ P i`, `P i = 2‖∇^i(traceHessian g₀ g₀)‖² + 2·D i`,
  `D` from the ballUniform `_sub_background_..._ballUniform` (`:408`).  **R-DEPENDENT**, and not
  even data-weighted.  The `(4,2)` route
  `ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic`
  (`RicciConnDiffOrder1TameEnvelope.lean:226`) also routes through `antidiagonalTupleGrid`
  (`:250`).  The only R-independent trace-Hessian fact is the C₂-*deviation* sup
  `traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns` (`:345`) — that is
  fact-1 (the top-arm deviation `c`), a different role, not a data-weighted jetL2 constituent.

### What is missing / where it comes from (the wait-on-Codex items)

For each field a **clean** per-order jetL2 top-separated producer (`∃ Hd`, R-independent
`Ktop,Kc`) is needed, built on the R-independent `..._topSeparated_le` engines that currently
exist ONLY in the DIRTY `CurvatureCoefficientDifferenceJetTower.lean`:
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (`:1823`, connDiff),
`rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le` (`:10570`),
`rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le`
(`:11141`), `rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le` (`:11695`).
Once those engines land committed-clean and a clean per-order `_perOrder_topSeparated` producer
is written per field, each summed bound is a ~40-line application of the EXISTING
`jetL2_sum_of_perOrder` (connDiff/Lie at offset `p=1`, like arm1; trace-Hessian at its natural
offset) — nothing here needs pre-building.

### Guardrail hit (why STOP was correct, not a shortcut)

The needed R-independent exports exist only in the dirty in-flight
`CurvatureCoefficientDifferenceJetTower.lean`; consuming it is forbidden, and building the
R-dependent tame-envelope versions is forbidden by the ruling's stop-signal (route-test note
`SobolevNonlinearityExistence.md:106–108`: do NOT hide the low-arm `‖T‖_{a+2}` behind an
`R`-ball/`Classical.choose`).  So STOP-and-report is the dispatched action, per the brick's own
guardrail ("STOP and report if a needed export exists only there").  No new theorem ⟹ no new
`#print axioms`; the arm0/arm1 file is unchanged and its consumed exports have not drifted.

### Honest accounting (unchanged)

Black box (N) still **0%**.  Item-(2) machinery: 2 of ~5 constituent per-field summed bounds
exist (arm0/arm1); the remaining 3 are blocked on the Codex JetTower lane.  Whole-(N) fraction
still ~0%.

## 2026-07-22 — CORRECTION: the above WAIT-ON-CODEX call was WRONG (superseded)

Planner-verified and executor-confirmed against HEAD `922dbc4ac`: the remaining 3
fields are NOT Codex-blocked.  The four `_topSeparated_le` engines this note lists
as "dirty-only" are all COMMITTED-CLEAN
(`CurvatureCoefficientDifferenceJetTower.lean:1823/10570/11141/11695`; the dirty
state is 64 unrelated `pureTrace`/`koszul_l2_succ` lines).  The error above was
demanding "no `R` in ANY constant": in fact arm0/arm1's OWN accepted `Kc` IS
R-dependent (threaded through `boundedFactorGridWindow_integral_ballUniform_tameWindow`
in the L2 generic `:14447`) — the discipline is only that the TOP-split `Ktop`
(engine head) is R-independent.  This note looked at the fields'
`tameEnvelope_generic` producers (which discard the top-split, lumping the top
into `R`) instead of the engines (which keep it).  Full verified build roadmap +
the cheaper direct-summed route are in the sibling
`RemainderCoeffTopSeparated.md`; plan status log updated.  No Lean landed here
this session (scope: ~180–350 lines/field intricate transfer assembly); (N) 0%.
