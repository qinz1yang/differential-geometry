# TraceHessJetL2Summed.lean — notes

## 2026-07-22 — trace-Hessian summed top-separated bound (constituent 5-of-5) LANDED with `Ktop = 0`

New leaf file (`Analysis/Sobolev/TensorHilbert/`, namespace
`DifferentialGeometry.Integral.Connection`, sibling of `ConnDiffJetL2Summed` / `LieFieldJetL2Summed`).
Delivers the trace-Hessian coefficient field's realizedFam summed jet-L2 bound in the exact
sibling-compatible top-separated shape.  All GREEN, sorry-free, warning-free; `#print axioms` on both
public theorems = `[propext, Classical.choice, Quot.sound]`.

### What it proves

Two public theorems (both with `Ktop = 0`):

- `traceHessianCoeff_realizedFam_jetL2_perOrder_topSeparated` — realizedFam per-order, window shape
  identical to connDiff/Lie (top `i+1`, low `i+2`, `w j = ‖∇^jT‖²+‖∇^jT'‖²`), with `Ktop = 0` and
  `Kc i` = the ball-uniform per-order constant of
  `traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform` (`RemainderCoeffL2JetMoser.lean:446`).
- `traceHessianCoeff_realizedFam_jetL2_summed_topSeparated` — the deliverable summed bound, both
  windows at order `a+2`:
  `∑_{i≤a} ‖∇^i (traceHessianCoeff g₀ (realizedFam …))‖²
     ≤ 0·(∑_{j<a+2} w j) + Kc·(1 + ∑_{j<a+2} w j)` with `Kc = ∑_{i≤a} Kc_perOrder i`.

### The headline FINDING — the roadmap's "three curvature engines" route does NOT apply

The `RemainderCoeffTopSeparated.md` roadmap (and `UNIF_EXISTENCE_PLAN.md` acceptances №4/№5/№6)
dispatched trace-Hessian as "assemble the R-independent split from the THREE committed `(0,4)`
curvature engines `riemannLoweredBackgroundDifference` / `ricEndoBackgroundDifferenceField` /
`riemannG1LoweringDifference`."  **That premise is mathematically wrong for this field**, verified
against HEAD `922dbc4ac`:

1. `traceHessianCoeff g₀ g₁` is a purely **algebraic coefficient in the cometric `g₁⁻¹`**:
   `traceHessianCoeff.toSection x = traceHessianFib g₁ x = cometricDoubleTraceFib g₁ 2 x ∘
   domDomCongrFib x` (`RicciLinearizationArmFields.lean:149/221`).  It carries **no covariant
   derivative** of the metric — it is the low-order coefficient in the linearized Ricci arm
   `linearizedRicciConnDiffOrder1CoeffField = appCcRS (traceHessianCoeff) (kernelField)`
   (`RicciConnDiffOrder1TameEnvelope.lean:116`).  The derivative gain lives in the *kernelField*
   (= the Lie field), not in this coefficient.
2. The three `(0,4)` engines bound curvature-**difference** fields (Riemann / Ricci, top at order
   `i+2`).  Their names appear **only** in `CurvatureCoefficientDifferenceJetTower.lean` — grep
   confirms there is NO file relating them to `traceHessianCoeff`/`ricciCometricFourTraceCastG0`.
3. The two committed decompositions of the trace-Hessian field both route to the **metric-inverse
   difference**, never to the curvature engines:
   - `traceHessianCoeff_sub_eq_reindex_deTurckPrincipalCometricCoeff`
     (`RemainderCoeffL2JetMoser.lean:328`): `traceHessian(g₁) − traceHessian(g₀,g₀) =
     reindexCoeffGen (deTurckPrincipalCometricCoeff g₁) traceHessianSlotPerm`, and
     `deTurckPrincipalCometricCoeff` is bounded by `gInvDiffSlotCoeff`.
   - `ricciCometricFourTraceCastG0_eq_reindex_combination`
     (`RicciConnDiffOrder1TameEnvelope.lean:137`): `= ½·(4 reindexed copies of
     ricciArmPrincipalCoeffPure)`, and `ricciArmPrincipalCoeffPure = cometricDoubleTraceField +
     appCcRS(cometricDoubleTraceField, slotInsertEndoCc (gInvDiffRaisedEndoField))` (`:171`).
4. The `topSeparated` engine inventory in `CurvatureCoefficientDifferenceJetTower.lean` is exactly
   `{connDiffSection (1823), riemannLoweredBackgroundDifference (10570),
   slotInsertEndoCc…ricEndoBackgroundDifferenceField (11141), riemannG1LoweringDifference (11695),
   ricciArmOrder0CurvCoeff_backgroundDifference (12253), ricciArmOrder0RiemannCoeff_backgroundDifference
   (12428), ricciArmOrder0BaseCoeff L2 generics (14447/14771)}` — **none** for
   `gInvDiffSlotCoeff` / `gInvDiffRaisedEndoField` / `ricciArmPrincipalCoeff(Pure)` /
   `deTurckPrincipalCometricCoeff` / `traceHessianCoeff`.

**Consequence — `Ktop = 0` is the correct value, not a mask.**  The metric-inverse jet
`∇^i gInvDiffSlotCoeff` is controlled by order-`≤ i` data (`gInvDiffSlotCoeff_perOrder_l2_tame`,
`AppCcJetWindowTame.lean:718`: `‖∇^i gInvDiffSlotCoeff‖² ≤ K i·(1 + ‖∇^i P‖²)` — same order, no
shift).  Hence the trace-Hessian field produces **no term reaching the protected `a+1`/`a+2` top
window**; its highest-order contribution (`∇^i P`, order `i ≤ a`) sits strictly below and is
legitimately low/`Kc` data.  So `Ktop = 0` (trivially `(g₀,hδ₀)`-only) — there is nothing at the top
for `R` to hide in.  Putting the (constant, `R`-dependent) `Kc` is the accepted house pattern; no
forbidden `‖T‖·‖T−T'‖` product, no `R` in `Ktop`.  Discipline (acceptances №4/№5/№6) satisfied
vacuously at the top.

### Route (DIRECT, robust — public deps only, no copy of heavy tame machinery)

Per order `i`, reshape the public ball-uniform per-order producer
`traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform` (`:446`, which gives
`‖∇^i traceHessian(realizedFam)‖² ≤ P i` for a data-independent constant `P i`) into the target shape
with `Ktop = 0`, `Kc i = P i`: `P i ≤ 0·(top) + P i·(1 + low)` since `low ≥ 0` (`nlinarith`).  Then
sum via the copied `jetL2_sum_lowShift` (offsets `p=1`, `q=2`; the `Ktop=0` makes `p` immaterial but
keeps the window shape a uniform drop-in for connDiff/Lie).

### Copied private helpers (verbatim, provenance comments in source)

- `sum_shift_le`, `jetL2_sum_lowShift` — copied verbatim from `ConnDiffJetL2Summed.lean` (pure
  `Finset` combinatorics, no geometry).  No other copies needed (the intricate geometry is entirely
  inside the imported public `:446` producer).

### Honest limitation — `Kc` is a UNIFORM CONSTANT, not yet data-weighted (identified follow-up)

The delivered `Kc` comes from the ball-uniform producer `:446`, so it is a **constant** (`R`-dependent,
data-independent): the bound is `∑‖∇^i tH‖² ≤ Kc·(1 + low data)` but only the `Kc·1` is exercised.  A
genuinely data-weighted `Kc·(1 + ∑ actual data)` is the natural strengthening; it is available in
principle but requires the metric-inverse **tame** machinery, which is not reachable from public
lemmas without a large copy:
- clean shape (`Kc i·(1 + ∑_{j<i+1}‖∇^jP‖²)`) needs the private
  `gInvDiffSlotCoeff_perOrder_l2_tame` (`AppCcJetWindowTame.lean:718`), whose proof chain pulls in
  the private `productGridTerm_integral_le_topOrderJetSq` (`:340`) — a ~660-line verbatim copy;
- the public `deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic` (`AppCcJetWindowTame.lean:1008`)
  is data-weighted but in the **Hs-embedding norm** `‖smoothCcToTensorHs g₀ i P‖`, and the
  Hs→jet-L2 bridge is fragile (multiple `Hs` constructions; the exact `_norm_sq_eq` is odd-order
  only, `SpectralNormLIterateLadder.lean:76`).
Since `Ktop = 0` regardless of which `Kc` is used, and a constant is a valid (if loose) instance of
the shape that is trivially absorbed by the downstream threeArm sum, the constant `Kc` was delivered
to keep the file robust/green (per "partial-but-compiling beats broken").  Upgrading `Kc` to
data-weighted is the identified next brick for this field.

### Verification status / environment

Focused direct-`lean` typecheck against the redirected olean tree (`C:/dgbuild/e87b/lib/lean` +
package build dirs, `LEAN_NUM_THREADS=4`): **GREEN, sorry-free, no warnings**; `#print axioms` =
standard three on both public theorems.  Imports only the committed-clean `RemainderCoeffL2JetMoser`
(so, unlike the Lie file, **no untracked-olean co-location was needed** — single-root `LEAN_PATH`
recipe worked directly).  Authoritative `lake build` not run (pre-existing `.olean.hash` split blocks
`lake`, unrelated to this file; same limitation recorded in the sibling notes).  The 64 dirty lines
of `CurvatureCoefficientDifferenceJetTower.lean` were not touched and elaboration inside them was not
triggered (this file does not import that module).

### Honest accounting

Black box (N) `ricci_flow_unif_existence` remains **0%** (its `sorry` untouched).  This is item-(2)
machinery of the R1τ frontier: trace-Hessian is constituent **5-of-5** of the data-weighted threeArm
precursor (arm0/arm1/connDiff/Lie done).  With this the constituent set is COMPLETE in the sense that
every field now has a summed top-separated producer of the uniform shape; the next brick is the
data-weighted threeArm decomposition itself (which consumes these five).  Caveat carried forward: this
field's `Kc` is a constant, not data-weighted (see the limitation section) — if the threeArm
decomposition needs genuine data-weighting from the trace-Hessian term, the `Kc` upgrade above must be
done first.  Realistic whole-(N) fraction: still ~0%.
