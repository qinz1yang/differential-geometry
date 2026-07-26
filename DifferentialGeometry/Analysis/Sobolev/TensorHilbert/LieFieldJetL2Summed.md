# LieFieldJetL2Summed.lean — notes

## 2026-07-22 — Lie DIRECT summed top-separated bound (constituent 4-of-5)

New leaf file (`Analysis/Sobolev/TensorHilbert/`, namespace
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral`, imports
`ConnDiffJetL2Summed`).  Delivers the Lie field's data-weighted summed jet-L2 bound by REUSING the
just-landed connDiff summed producer as a black box and supplying a per-order structural bridge.
All GREEN, sorry-free, warning-free; `#print axioms` on all public theorems + the private bridge =
`[propext, Classical.choice, Quot.sound]`.

### What it proves

- `lie_normSq_le_25` (private, `g₁`-generic per-order structural bridge):
  `‖∇^i (linearizedRicciConnDiffOrder1KernelField g₀ g₁)‖² ≤ 25·‖∇^i (connDiffContrInsertionField g₀ g₁)‖²`.
- `linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_perOrder_topSeparated` — realizedFam
  per-order (top window `i+1`, low window `i+2`; `w j = ‖∇^jT‖²+‖∇^jT'‖²`), `Ktop = 25·Ktop_connDiff`,
  `Kc i = 25·Kc_connDiff i`.
- `linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_summed_topSeparated` — the deliverable
  summed bound, both windows at order `a+2`:
  `∑_{i≤a} ‖∇^i (LieField g₀ (realizedFam …))‖²
     ≤ Ktop·(∑_{j<a+2}(‖∇^jT‖²+‖∇^jT'‖²)) + Kc·(1+∑_{j<a+2}(‖∇^jT‖²+‖∇^jT'‖²))`
  with `Ktop = 25·Ktop_connDiff`, `Kc = 25·Kc_connDiff`.

### Constant discipline (stop-signal NOT hit)

`Ktop = 25·Ktop_connDiff` is `(g₀,hδ₀)`-only: `25` is a pure combinatorial factor (the `5·`-triangle
squared, from `c3_norm_five_le` over the five arm copies), and `Ktop_connDiff = 2·finrank²·(10·S 0)`
is the `(g₀,hδ₀)`-only connDiff engine head — no `R`.  `R` enters ONLY the lumped low
`Kc = 25·Kc_connDiff` (through the connDiff producer's `KI` converter), the accepted house pattern.
No forbidden `‖T‖_{a+2}·‖T−T'‖_{a+2}` product; the bound is `Ktop·(top data) + Kc·(1+low data)`.
Matches "Planner acceptance №4/№5" calibration.

### Route (REUSE, per the roadmap "Lie — combination of connDiff")

1. Structural identity `LieField g₀ g₁ = -(A+B+C+D+E)`, a negation of five slot-permuted /
   reindexed copies of `connDiffContrInsertionField g₀ g₁` (`kernelField_eq_neg_arm_combination`,
   `rfl`).  A/B/D/E are `armFull` (reindexCoeffGen∘appCcRS∘slotPermCc); C is `armOuter` (bare
   appCcRS∘slotPermCc, no reindex).
2. Each copy has the SAME `iteratedCovGrad`-L2 norm as connDiff (permutation/reindex are fibrewise
   isometries): `armFull_norm_eq`, `armOuter_norm_eq` (via pointwise rfns equalities
   `armFull_rfns_eq`/`armOuter_rfns_eq` and the L2-integral norm identity).
3. Per-order bridge `‖∇^i LieField‖ ≤ 5·‖∇^i connDiff‖` via
   `iteratedCovGrad_neg`+`iteratedCovGrad_add`×4 (distribute ∇^i over the neg-sum) then
   `c3_norm_five_le`.  Square → `‖∇^i LieField‖² ≤ 25·‖∇^i connDiff‖²` (`lie_normSq_le_25`).
4. Per-order realizedFam: compose the bridge with the connDiff realizedFam per-order producer.
5. Summed: sum the bridge over `i≤a` (`Finset.mul_sum`+`Finset.sum_le_sum`) and reuse
   `connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` as a black box; final
   `mul_le_mul_of_nonneg_left` (×25) + `ring`.  The connDiff SUMMED producer is used unopened —
   no re-derivation of the connDiff summation machinery.

### Copied private helpers (all verbatim from committed-clean `RicciConnDiffOrder1TameEnvelope.lean`)

The arm-combination stack there is `private` (not importable), so copied verbatim into this file
(provenance comment in the source): the seven perms (`kOutPerm0312/0213/2301/1302/1203`,
`kInPerm102/120`), `slotPermCcFib_contMDiff`, `slotPermCc`, `kernelField_eq_neg_arm_combination`,
`armOuter_rfns_eq`, `armFull_rfns_eq`, `c3_norm_eq_of_sq_eq`, `armOuter_norm_eq`, `armFull_norm_eq`,
`c3_norm_five_le`.  They use only PUBLIC sub-lemmas (`slotPermCLM`, `slotPermCLM_apply`,
`slotPermCLM_field_contMDiff`, `rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr`,
`rfns_iteratedCovGrad_reindexCoeffGen_eq`, `Tensor0SSpace.toModel_ofModel`, `SmoothCcTensor.norm_def`,
`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs`, `iteratedCovGrad_neg`,
`iteratedCovGrad_add`).  Same copy pattern the connDiff file used for its own private helpers.
The order-0-sup helpers `armOuter_rfns0_eq`/`armFull_rfns0_eq`/`fourTrace_rfns_smul` were NOT needed
(the norm route skips the order-0 sup part).

### Lessons / traps

- The risky step was re-deriving `kernelField_eq_neg_arm_combination` by `rfl` with COPIED perms +
  `slotPermCc`.  It WORKS: the copied defs are byte-identical to the originals (and the `by decide`
  perm proofs are proof-irrelevant), so `slotPermCc g₀ myPerm` is defeq to the original, and the
  definitional unfolding of `linearizedRicciConnDiffOrder1CLM` reproduces the same normal form.
  `set_option backward.isDefEq.respectTransparency false` (present in the source header) is
  replicated here so the defeq check behaves identically.
- Namespace: put the whole file in `DifferentialGeometry.Analysis.Parabolic.TensorSpectral` with
  the EXACT opens of `RicciConnDiffOrder1TameEnvelope.lean` (so the copied bodies typecheck
  verbatim).  That namespace already `open`s `DifferentialGeometry.Integral.Connection`, so the
  connDiff producers resolve unqualified.
- `positivity` does NOT prove `0 ≤ 25*Ktop` for an opaque `Ktop` with only a local `hKtop_nn` in
  context (it ignores such hypotheses) — use `mul_nonneg (by norm_num) hKtop_nn`.
- The statement binders `hδ_le`/`hδ'_le` (used in the PROOF but absent from the conclusion TYPE)
  trip `linter.unusedVariables`; suppress with `set_option linter.unusedVariables false in` on the
  public theorems (same as the connDiff file).

### Verification status / environment

Focused direct-`lean` typecheck against the redirected olean tree (`C:/dgbuild/e87b/lib/lean` +
package build dirs): **GREEN, sorry-free, no warnings**; `#print axioms` = standard three on the
private bridge and both public theorems.  Authoritative `lake build` not run (the worktree's
pre-existing `.olean.hash` split blocks `lake`, unrelated to this file; same limitation recorded in
`ConnDiffJetL2Summed.md`).

MULTI-FILE CHECK RECIPE (import `ConnDiffJetL2Summed` has no olean in the redirected tree — it is
untracked-new): (1) emit its olean with `lean -o <path>/DifferentialGeometry/Analysis/Sobolev/
TensorHilbert/ConnDiffJetL2Summed.olean <src>` under `LEAN_PATH=<redirected tree + packages>`;
(2) COPY that olean into the redirected tree at the matching module path, then check this file with
the plain single-root recipe.  NOTE: adding the local dir as a SECOND `LEAN_PATH` root did NOT work
(Lean did not fall through roots for the transitive `DifferentialGeometry.*` deps — it must all live
in one root); co-locating the olean in the redirected tree is the reliable path.  A gitignored
`.localolean/` scratch dir was used for the emit and then removed; `ConnDiffJetL2Summed.olean` was
left in the redirected tree so downstream checks (e.g. the traceHessian executor) can import it.

Imports only committed-clean engines (transitively via `ConnDiffJetL2Summed` →
`RicciConnDiffOrder1TameEnvelope` / `RemainderCoeffL2JetMoser`) plus the untracked-new
`ConnDiffJetL2Summed`.  The 64 dirty lines of `CurvatureCoefficientDifferenceJetTower.lean`
(`pureTrace`/`koszul_l2_succ`) were not touched and elaboration inside them was not triggered.

### Honest accounting

Black box (N) `ricci_flow_unif_existence` remains **0%** (its `sorry` untouched).  This is item-(2)
machinery of the R1τ frontier: Lie is constituent **4-of-5** of the data-weighted threeArm
precursor (arm0/arm1/connDiff done; only **traceHessian** remains).  The precursor is itself one of
several lemmas below the smooth-core tame theorem.  Realistic whole-(N) fraction: still ~0%.
Next per the roadmap: **traceHessian** field (`traceHessianCoeff` / `ricciCometricFourTraceCastG0`,
`(4,2)`; the hardest — must assemble the R-independent split from the three curvature `(0,4)`
engines `riemannLoweredBackgroundDifference` / `ricEndoBackgroundDifferenceField` /
`riemannG1LoweringDifference`; NOT a slotExtend of connDiffSection).  See
`RemainderCoeffTopSeparated.md` "traceHessian" section.
