# ConnDiffJetL2Summed.lean — notes

## 2026-07-22 — connDiff DIRECT summed top-separated bound (constituent 3-of-5)

New leaf file (`Analysis/Sobolev/TensorHilbert/`, namespace
`DifferentialGeometry.Integral.Connection`, sibling of `ArmBaseCoeffJetL2Summed.lean`).
Delivers the connection-difference field's data-weighted summed jet-L2 bound via the DIRECT
route of `RemainderCoeffTopSeparated.md` (skips the field-level `∃Hd` witness).  All GREEN,
sorry-free; `#print axioms` on all three public theorems = `[propext, Classical.choice,
Quot.sound]`.

### What it proves

Three public theorems (all `R`-independent `Ktop`):

- `connDiffContrInsertionField_perOrder_l2_topSeparated_generic` — generic `(g₁,P,htie,hPball)`
  per-order bound
  `‖∇^i (connDiffContrInsertionField g₀ g₁)‖² ≤ Ktop·‖∇^{i+1}P‖² + Kc i·(1+∑_{j<i+2}‖∇^jP‖²)`
  for `i ≤ a`, with `Ktop = 2·finrank²·Kt0` and `Kc i = 2·finrank²·Kc0 i·i·KI i`.
- `connDiffContrInsertionField_realizedFam_jetL2_perOrder_topSeparated` — realizedFam per-order
  (top window `i+1`, low window `i+2`; `w j = ‖∇^jT‖²+‖∇^jT'‖²`).
- `connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` — the deliverable summed
  bound, both windows at order `a+2`:
  `∑_{i≤a} ‖∇^i (connDiffContrInsertionField g₀ (realizedFam …))‖²
     ≤ Ktop·(∑_{j<a+2}(‖∇^jT‖²+‖∇^jT'‖²)) + Kc·(1+∑_{j<a+2}(‖∇^jT‖²+‖∇^jT'‖²))`.

### Constant discipline (stop-signal NOT hit)

`Ktop` is `(g₀,hδ₀)`-only: `Kt0` is the engine head `10·S 0` from
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (its `S` is
`exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid`, no `R`); `finrank²` is dimensional.  `R`
enters ONLY the lumped low `Kc` (through `KI` = the converter
`boundedFactorGridWindow_integral_ballUniform_tameWindow`), which is the accepted house pattern
(arm0's own generic `…:14447` also has R-dependent `Kc`).  No forbidden
`‖T‖_{a+2}·‖T−T'‖_{a+2}`-shaped product; the bound is `Ktop·(top data) + Kc·(1+low data)`.

### Route (DIRECT, per the roadmap)

Per order `i` (nonempty `M`; empty branch: jet L² seminorm = 0):
1. field↔section transfer `rfns(∇^i field) ≤ finrank²·rfns(∇^i connDiffSection)` via
   `connDiffContrInsertionField_eq_reindex_slotExtend_two` +
   `rfns_iteratedCovGrad_reindexCoeffGen_eq` + `rfns_iteratedCovGrad_slotExtend_le` ×2.
2. engine split `rfns(∇^i section) ≤ 2·rfns(head) + 2·rfns(remainder)` via
   `riemannianFiberNormSq_add_le`, then engine `.1` (head ≤ `Kt0·rfns(∇^{i+1}P)`) and `.2`
   (remainder ≤ `Kc0 i·∑ b(i-k)·antidiagTupleGrid`).
3. reshape remainder `∑ b(i-k)·antidiagTupleGrid b (k+1) ≤ i·boundedFactorGridWindow b i (i+2)
   ≤ i·boundedFactorGridWindow b (i+1)(i+3)` via the copied private `tsResSum_le_boundedWindow`
   + `Combinatorics.boundedFactorGridWindow_mono`.
4. integrate: top → `‖∇^{i+1}P‖²` via `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` +
   `tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs`; remainder → the converter
   (`integral_add`/`integral_const_mul`, `integrable_riemannianFiberNormSq_toSection`).
Then realizedFam wrapper (clone of the arm0 tameEnvelope wrapper's `convexPerturbation`/`htie`/
`hPball`/`hwin` plumbing) and summation via `jetL2_sum_lowShift`.

### Private helpers (copied / new, all pure)

- `tsResSum_le_boundedWindow` — copied verbatim from the private JetTower lemma (pure
  combinatorial, only `Combinatorics.*`); provenance comment in file.
- `sum_shift_le` — copied from `ArmBaseCoeffJetL2Summed`.
- `jetL2_sum_lowShift` — new generalization of `ArmBaseCoeffJetL2Summed`'s
  `jetL2_sum_of_perOrder` with **independent** top offset `p` and low-window offset `q` (connDiff
  needs `p=1`, `q=2`; the arm single-offset version does not apply).
- `iteratedCovGrad_smul_real` — copied (it is `private` to `RemainderCoeffL2JetMoser`, so not
  importable); needed for the `convexPerturbation` jet expansion.

### Lessons / traps hit

- `SmoothCcTensor.toSection_add`/`toSection_sub` are **section-level** `rfl` lemmas
  (`(S+T).toSection = S.toSection + T.toSection`, no `x`).  To fold a pointwise
  `A.toSection x + B.toSection x`, the bridge is `simp only [SmoothCcTensor.toSection_sub,
  ContMDiffSection.coe_sub, Pi.sub_apply]; abel`, NOT `rw [← toSection_add]`.
- The engine head folds cleanly if `set Hd := appCcRS …` runs AFTER `have heng := hbot …` (so
  `set` rewrites `heng`'s occurrences).
- The connDiff remainder low window is `i+2` while the top point is order `i+1` — mismatched
  offsets, which is why `jetL2_sum_lowShift` (two offsets) is required over the arm helper.
- Unfold `set`-defined integrands with `simp only [hFun_def]` (beta-reduces), not `rw` (leaves a
  redex that blocks `integral_const_mul`).
- Reused the `perOrder ∃Hd`-free scalar bound directly: `jetL2_sum_lowShift` needs only the
  scalar per-order inequality, so the intricate field-level `∃Hd`/DDC construction of the
  `:10570` template is entirely avoided.

### Verification status

Focused direct-`lean` typecheck against the redirected olean tree: **GREEN, sorry-free, no
warnings**; `#print axioms` = standard three on all three public theorems.  Authoritative
`lake build` not run (the worktree's pre-existing `.olean.hash` split blocks `lake`, unrelated to
this file; same limitation recorded in `ArmBaseCoeffJetL2Summed.md`).  Imports only committed-clean
engines from the (Codex-dirty) `CurvatureCoefficientDifferenceJetTower.lean`; its 64 dirty lines
were not touched and elaboration inside them was not triggered.

### Honest accounting

Black box (N) `ricci_flow_unif_existence` remains **0%** (its `sorry` untouched).  This is
item-(2) machinery of the R1τ frontier: connDiff is constituent **3-of-5** of the data-weighted
threeArm precursor (arm0/arm1 done in `ArmBaseCoeffJetL2Summed`; remaining = Lie + traceHessian).
The precursor is itself one of several lemmas below the smooth-core tame theorem.  Realistic
whole-(N) fraction: still ~0%.  Next per the roadmap: **Lie** field
(`linearizedRicciConnDiffOrder1KernelField`, reuses this connDiff producer via
`kernelField_eq_neg_arm_combination` + a `5·`-triangle assembly), then **traceHessian** (hardest;
three curvature `(0,4)` engines).
