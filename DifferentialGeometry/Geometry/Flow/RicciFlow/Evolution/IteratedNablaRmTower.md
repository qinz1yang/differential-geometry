# IteratedNablaRmTower higher-order heat equation plan

## Live status

`IteratedNablaRmTower.lean` currently has the algebraic tower bridge:

- `IteratedRmTowerOn` stores `wDef`, exact `heatEq`, and `starBound`.
- `abs_towerReactionMulti_le` proves the schematic star-reaction estimate.
- `iteratedRmTower_heatBound` converts `IteratedRmTowerOn` into
  `TowerHeatBoundOn`.

The unresolved producer is not the reaction estimate.  The hard missing content
is producing `IteratedRmTowerOn.heatEq` from an actual Ricci-flow solution for
all `k`.

Lower-order files show the same pattern:

- `RiemannNorm.lean` defines `Rm04NormHeatEquationOn`.
- `RiemannNormHeatProducer.lean` closes the `k = 0` norm heat equation from raw
  component derivative data and reaction algebra.
- `NablaRiemannHeat.lean` defines `NablaRm04NormHeatEquationOn` for `k = 1`,
  but still takes the assembled `|nabla Rm|^2` heat equation as an input.

So the honest remaining frontier is a higher-order analytic producer, not local
maximum-principle algebra.

## Goal

Close the exact heat-equation producer for the tower:

```lean
HasDerivWithinAt (fun s => w k s x)
  (wLap k t x +
    (-2 * w (k + 1) t x +
      towerReactionMulti (level Â· t x) (star Â· t x) k))
  D.carrier t
```

for `w k = |nabla^k Rm|^2` in the Uhlenbeck orthonormal frame.

## Do not do this route

Do not try to prove the all-`k` result by unfolding `iteratedRmComp` and
expanding frame Christoffel formulas recursively.  That route creates a
dependent multi-index explosion and hides the geometry behind component
bookkeeping.

Do not close the theorem by adding a new assumption that is just `heatEq` under
a different name.  `IteratedRmTowerOn.heatEq` is already the exact assumption;
renaming it does not produce anything.

## Correct mathematical split

The producer should be split into two tensor-level statements plus one
component adapter.

### 1. Commuted curvature evolution

Prove a tensor/component theorem with schematic star output:

```lean
(partial_t - roughLap) (nabla^k Rm)
  = Sum_{j = 0}^k nabla^j Rm * nabla^{k-j} Rm
```

In the current component style this should probably be a predicate first:

```lean
def IteratedRmCommutedHeatOn
    (level : (k : Nat) -> Real -> M -> (Fin (4 + k) -> Idx) -> Real)
    (roughLapLevel : (k : Nat) -> Real -> M -> (Fin (4 + k) -> Idx) -> Real)
    (star : (k : Nat) -> Real -> M -> Nat -> (Fin (4 + k) -> Idx) -> Real) : Prop := ...
```

It should assert, for every regular time, point, and multi-index:

```lean
HasDerivWithinAt (fun s => level k s x m)
  (roughLapLevel k t x m + starSum k t x m)
  D.carrier t
```

where `starSum` is the finite sum over `j <= k`.  The exact contraction should
remain schematic; only the star-bound is needed later.

Prove this by induction on `k`, not by norm-square algebra:

- base `k = 0`: use the Uhlenbeck curvature evolution already present in
  `Uhlenbeck.lean`;
- induction step: commute one covariant derivative past `(partial_t - roughLap)`;
- the commutator terms must be absorbed into the schematic `star` family.

The two required local commutator APIs are:

```lean
partial_t_nabla_eq_nabla_partial_t_plus_connection_variation
laplacian_nabla_commutator
```

In book notation:

```text
partial_t (nabla A) = nabla (partial_t A) + (partial_t Gamma) * A
[Delta, nabla] A = Rm * nabla A + nabla Rm * A
```

Under Ricci flow, `partial_t Gamma = nabla Ric`, which is another
`nabla Rm`-controlled star term after Bianchi/trace realization.

### 2. Norm-square Bochner identity

Prove a rank-uniform norm-square identity for a tensor level `A_k`:

```lean
partial_t |A_k|^2
  = Delta |A_k|^2 - 2 |nabla A_k|^2
    + 2 <(partial_t - Delta) A_k, A_k>
```

In the Uhlenbeck orthonormal frame this should be component-level finite-sum
algebra, generalizing `Rm04NormHeatEquationOn` and
`NablaRm04NormHeatEquationOn`.

Good target interface:

```lean
def MultiNormHeatEquationOn
    (level : Real -> M -> (Fin r -> Idx) -> Real)
    (roughLapLevel : Real -> M -> (Fin r -> Idx) -> Real)
    (nextNormSq normLap reaction : Real -> M -> Real) : Prop := ...
```

Then prove:

```lean
multiNormHeatEquationOn_of_componentHeat
```

from:

- component time derivative for `level`;
- Laplacian split
  `Delta |level|^2 = 2 <roughLap level, level> + 2 |nabla level|^2`;
- reaction defined as the contraction of the component heat residual against
  `level`.

This is the right place to reuse and generalize the finite-sum product-rule
style from `RiemannNorm.lean`.

### 3. Adapter into `IteratedRmTowerOn`

After the two producer layers exist, add the thin assembly theorem:

```lean
theorem iteratedRmTowerOn_of_solution
    (...) :
    IteratedRmTowerOn (D := D) level star w wLap
```

This theorem should be mostly field-by-field:

- `wDef`: orthonormal-frame norm reduction, using
  `multiNormInFrame_eq_compNormSqMulti`;
- `heatEq`: from `IteratedRmCommutedHeatOn` plus
  `MultiNormHeatEquationOn`;
- `starBound`: from the already proved schematic component star estimate, or a
  new solution-facing star-bound wrapper.

## Suggested implementation order

1. Add a finite-rank generic component norm heat equation, independent of
   Ricci flow.  Test it at `r = 4` by recovering the existing `Rm04NormHeat`
   shape.
2. Add a `k = 1` closed producer first.  This should turn the current
   `NablaRm04NormHeatEquationOn` hypothesis into a theorem from connection
   variation plus laplacian commutator.  If this cannot be closed, do not start
   all-`k`.
3. Add the commutator theorem as a schematic star theorem.  Avoid specifying
   exact contractions beyond what is needed for the norm bound.
4. Prove the induction from `k` to `k + 1`.
5. Only then assemble `iteratedRmTowerOn_of_solution`.
6. Replace downstream direct assumptions on `IteratedRmTowerOn` only after the
   producer checks.

## Expected blocker

The hard blocker is the commutator/connection-variation API:

```text
partial_t (nabla T)
[Delta, nabla] T
partial_t Gamma = nabla Ric
```

This is a genuine missing analytic/geometric producer, likely substantial but
well-scoped.  The finite-sum norm-square layer should be routine compared with
that commutator layer.

## Verification status

No Lean code was changed in this planning pass.  Verification was not run.

## 2026-06-06 follow-up audit after k = 1 progress

The k = 1 equation route has moved forward.  The following modules now exist and
focused-check:

- `MultiNormHeat.lean`
- `RmRealizationBridge.lean`
- `NablaRiemannCommutator.lean`
- `NablaRiemannTimeDeriv.lean`
- `NablaRiemannCommutatorBound.lean`
- `IteratedNablaRmTower.lean`
- `BernsteinShiSolution.lean`

The key proved pieces are:

- `rm04_ricciIdentityAt`
- `nablaRm04_ricciIdentityAt`
- `iteratedRmComp_one_eq_nablaRm04Field`
- `covDerivStepComp_frameComp_eq`
- `nablaLapComm_orthonormalTrace`
- `iteratedRmComp_one_hasDerivWithinAt`
- `nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`

`#print axioms` for those declarations showed only the usual
`[propext, Classical.choice, Quot.sound]`.

What is still not closed:

- The k = 1 quantitative bound is not proved.
- `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.
- `NablaRiemannTimeDeriv.lean` still takes the level-0 time derivative,
  Christoffel time derivative, and time/spatial derivative swap as input shapes;
  concrete solution instantiation is deferred.

The precise current wall is recorded in `NablaRiemannCommutatorBound.lean`: the
slot-swap/commutator decomposition is proved, but bounding it in the required
`C(dim) |Rm| |nabla Rm|` shape runs into four missing framework pieces:

1. The inverse metric is currently a component function, not a bundled `(2,0)`
   tensor in the realization framework, so `nabla gInv = 0` is not directly
   statable there.
2. The field-level identity `rm13 = raise(rm04)` is not available as a usable
   theorem in the `SolutionOn`/`totalNabla0S` layer.
3. There is no `nablaRm13Field` or `TotalNablaRSRealizes` for `S.base.rm13`.
4. The current concrete commutator term is hardwired to `coordinateFrameAt x0`,
   while the norm estimates are stated in an orthonormal-frame convention.

## Next Claude plan: close the k = 1 quantitative producer honestly

### Target

Do not start all-`k` induction yet.  First close the k = 1 producer:

```lean
NablaRm04NormHeatEquationOn
  (D := D) (nablaRm04NormSqInFrame ...)
  nablaRmNormLap nabla2RmNormSq reaction
```

and then feed it to:

```lean
nablaRm04NormHeatBoundOn_of_components
```

with a reaction bound of the form

```text
|reaction| <= C(dim) * sqrt(|Rm|^2) * |nabla Rm|^2
```

This is the prototype needed before any general `k` producer.

### Preferred route

Work below the current coordinate-frame commutator term.  Build the missing
metric-raising and orthonormal-frame API first, then return to the k = 1 bound.

1. Add a pointwise lowering/raising bridge for curvature at the
   `DifferentialGeometry` layer.

   Desired theorem shape:

   ```lean
   rm13_comp_eq_raise_rm04_comp
   nablaRm13_comp_eq_raise_nablaRm04_comp
   ```

   These should be stated at a point, in a basis/frame carrying the metric and
   inverse-metric compatibility needed to raise/lower.  Do not use
   `coordinateFrameAt` orthonormality; it is not available.

2. Add the missing covariant-derivative raising bridge.

   Mathematically this is:

   ```text
   nabla(rm13) = raise(nabla rm04)
   ```

   because the Levi-Civita connection is metric compatible.  If the existing
   `loweredCovDerivAt_eq_lower_tensorCovDerivAt` only covers `(0,2)`, generalize
   it at the tensor layer or add the smallest `(1,3)` specialization.  Do not
   fake this with a new `nablaRm13` assumption in the Ricci-flow file.

3. Move the quantitative reaction estimate to an orthonormal-frame component
   theorem.

   Prove a pure finite-dimensional algebra lemma for an orthonormal basis:

   ```text
   |curvatureAction0SAt rm13 A ...| <= C(card) * |Rm04| * |A|
   ```

   and its covariant-derivative version:

   ```text
   |nabla(curvatureAction rm13 rm04)| <= C(card) * |Rm04| * |nablaRm04|
   ```

   The second one should use the raising bridge for `nabla rm13`; this is where
   the old route got stuck.

4. Only after the orthonormal-frame reaction bound exists, adapt the k = 1
   commutator output.

   The existing theorem

   ```lean
   nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction
   ```

   is useful as a decomposition certificate, but it is in the coordinate-frame
   concrete route.  If adapting it to the orthonormal frame is larger than
   expected, stop and state the exact missing frame-change lemma instead of
   forcing a coordinate-frame bound into an orthonormal norm statement.

5. Assemble the k = 1 equation and bound.

   Use:

   - `iteratedRmComp_one_hasDerivWithinAt` for the time derivative side, after
     instantiating its `hrm`, `hchr`, and `hswap` from the concrete solution
     producers;
   - `nablaLapComm_orthonormalTrace` for the spatial commutator;
   - `MultiNormHeat.lean` for the norm-square Bochner algebra;
   - `nablaRm04NormHeatBoundOn_of_components` for the final scalar
     heat-inequality package.

### Stop conditions

Stop and report, without adding assumptions, if any of these is the first
unavailable lemma:

- `(1,3)` lowering/raising parallelism for `rm13`/`rm04`;
- a usable `nabla rm13 = raise(nabla rm04)` bridge;
- an orthonormal-frame component norm comparison for `rm13` vs `rm04`;
- a frame-change theorem from the coordinate-frame commutator term to an
  orthonormal-frame reaction term;
- concrete instantiation of `hrm`, `hchr`, or `hswap` in
  `iteratedRmComp_one_hasDerivWithinAt`.

Classify the failure as a missing tensor API or missing realization bridge, not
as a local k = 1 proof failure.

### Acceptance

- No new `sorry`.
- Focused checks for the touched files pass.
- `#print axioms` on any new public theorem shows only
  `[propext, Classical.choice, Quot.sound]`.
- `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn` until the
  full producer is honestly assembled.

## 2026-06-06 second follow-up: the raising bridge is available; the two walls are isolated

A new file `Evolution/RmRaisingBridge.lean` was added.  It closes step 1 of the
plan (the pointwise `rm13 = raise(rm04)` bridge) and the algebraic core of step 3
(removing `rm13` from the curvature action), and it isolates the two genuine
remaining walls precisely.  All new theorems are sorry-free and `#print axioms`
shows only `[propext, Classical.choice, Quot.sound]`.

### What was proved (`Evolution/RmRaisingBridge.lean`)

* `solution_rm04LowersRm13At` â€” the pointwise lowering relation
  `rm04(X,Y,Z,W) = rm13 (gâ™­ W)(X,Y,Z)` for the **solution** curvatures
  `S.base.rm13`/`S.base.rm04`, at every time and point.  This is
  `rm04LowersRm13At_of_realizes` (`Geometry/Curvature/Components/Lowering.lean`)
  transported through the definitional `S.base.rm13 t = metricRm13 (g t)`,
  `S.base.rm04 t = metricRm04 (g t)`; the two shared connection realizations come
  from `metricCurvData`.
* `rm13_apply_eq_rm04_raise` â€” the **raising bridge**: inverting the lowering with
  the metric sharp map `cotangentSharp_gen` gives, for an *arbitrary* covector `Î²`
  (not only `Î² = gâ™­ W`), `rm13 Î² (X,Y,Z) = rm04 (X,Y,Z, gâ™¯ Î²)`.  Proof: write `Î²`
  as `gâ™­(gâ™¯Î²)` via `cotangentSharp_inner_eval`, then apply the lowering relation.
* `curvatureAction0SAt_eq_rm04_raise` â€” the slotwise curvature action expressed
  purely through the all-lowered `rm04`:
  `curvatureAction0SAt (rm13) Î± X Y slots
     = -Î£_q rm04 (X, Y, slots_q, gâ™¯(freezeSlot Î± slots q))`.
  Every `(1,3)` `rm13` is gone; only `rm04` and the metric raising remain.
* `nablaLapComm_secondTerm_eq_rm04_raise` â€” the **second reaction summand `Tâ‚‚`**
  of `nablaLapCommReactionTerm` (the `(0,5)` curvature action on `âˆ‡Rm`,
  `[âˆ‡_a,âˆ‡_c](âˆ‡_b Rm)`) written as the all-lowered contraction of `S.base.rm04`
  against `nablaRm04Field` (`= âˆ‡rm04`) and the metric raising â€” again with **no**
  `rm13` and, crucially, **no** `âˆ‡rm13`.

### This refutes one of the four footer obstructions of `NablaRiemannCommutatorBound.lean`

Footer obstruction #2 ("`rm13 = raise(rm04)` is not available as a usable
field-level lemma") is **incorrect for the lowering/raising relation itself**: the
pointwise lowering `Rm04LowersRm13At` is proved from the *shared realization of the
connection's curvature* (both `rm13` and `rm04` realize the same
`connectionRiemannCurvatureField`), and inverting it with the metric sharp map is
elementary.  The `lowerAllUpperIndicesEquiv`/`(1,3)`-parallelism formalism named in
the footer is a *different* covariant-derivative formalism and is **not** needed
for the pointwise raise.

### The two genuine remaining walls (precisely localised)

The `k = 1` quantitative reaction bound `|reaction| â‰¤ C(dim)Â·|Rm|Â·|âˆ‡Rm|` is still
not closed.  `nablaLapCommReactionTerm = Tâ‚ + Tâ‚‚` (`NablaRiemannCommutator.lean`),
and the two summands fail for **different**, now-isolated reasons:

1. **Summand `Tâ‚ = âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm)` needs `âˆ‡rm13` â€” the `(1,3)` raising
   parallelism.**  `Tâ‚` is the covariant derivative of the curvature action
   `K = curvatureAction(rm13, rm04)`.  Differentiating the `rm04`-form above
   covariantly gives `âˆ‡(gâ™¯) âˆ— rm04 + gâ™¯ âˆ— âˆ‡rm04`; the `âˆ‡(gâ™¯)` factor is the
   covariant derivative of the metric raising.  The honest statement `âˆ‡(gâ™¯) = 0`
   is the `(1,3)` index-**raising** parallelism, which is **absent**:
   - the proved parallelism `loweredCovDerivAt_eq_lower_tensorCovDerivAt` /
     `..._gen` (`MetricCompatibility/TensorLoweringParallel.lean`,
     `â€¦/TensorConnLapGreenIntertwiner.lean`) is the rank-`(0,s)` **lowering**, and
     its proof carries **no** `âˆ‡g = 0` content (at `r = 0` the lowering map is
     evaluation at the unit `(0,0)`-tensor, whose covariant derivative is `0`);
   - there is **no** `(1,3)` `totalNablaRS` realization for `rm13` (the only
     `totalNabla*` realizations for solution curvature are the lowered
     `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` of
     `RmRealizationBridge.lean`).

   *Exact theorem needed next*, stated at the tensor layer (not the Ricci-flow
   file): a `(1,3)` raising-parallelism

   ```text
   âˆ‡_v (lowerAllUpperIndicesEquiv g 1 3 x).symm (Rm04 x)
     = (lowerAllUpperIndicesEquiv g 1 3 x).symm (âˆ‡_v Rm04 x)
   ```

   i.e. the rank-`(1,3)` analogue of `loweredCovDerivAt_eq_lower_tensorCovDerivAt`,
   which at `r â‰¥ 1` genuinely requires `âˆ‡g = 0` (`nabla_metric_zero`).  It belongs
   in `Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`.  The
   `coordinateFrameAt` centre-orthonormality shortcut is invalid: `coordinateFrameAt`
   is the *chart coordinate frame* (`Geometry/Coordinates/CoordinateFrame.lean`
   states it does not make Christoffel symbols vanish), and its
   `InverseMetricOrthonormalAt` is never discharged â€” so the raising cannot be
   trivialised at the centre.

2. **Summand `Tâ‚‚` is `âˆ‡rm13`-free but needs the coordinateâ†’orthonormal frame
   change to match the producer's component norm.**  `nablaLapComm_secondTerm_eq_rm04_raise`
   already writes `Tâ‚‚` through `rm04`/`âˆ‡rm04` with no `rm13`/`âˆ‡rm13`, so its bound
   by `|Rm|Â·|âˆ‡Rm|` does *not* hit wall 1.  But the producer
   (`NablaRm04NormHeatEquationOn` / `nablaRm04NormHeatBoundOn_of_components`,
   `NablaRiemannHeat.lean`) consumes the reaction as `nablaRmReactionInFrame` in an
   **orthonormal** frame (`InverseMetricOrthonormalAt`, `gáµƒáµ‡ = Î´`), while
   `nablaLapCommReactionTerm` is hardwired to `coordinateFrameAt xâ‚€`, which is not
   orthonormal.  `nablaLapComm_orthonormalTrace`'s `horth : gInv = Î´` hypothesis is
   *unsatisfiable* for the coordinate frame's actual inverse metric, so it cannot
   feed the producer.

   *Exact theorem needed next*: a frame-change bridge carrying the intrinsic
   spatial commutator `[Î”, âˆ‡_c] Rm` (or the reaction array contracted against
   `âˆ‡Rm`) from `coordinateFrameAt xâ‚€` to a genuine orthonormal frame at `xâ‚€`, so
   that the producer's `InverseMetricOrthonormalAt` is satisfiable.  This belongs
   in a new orthonormal-frame adapter beside `NablaRiemannCommutator.lean`, not in
   the producer.

### Net

Step 1 (pointwise raise) and the `rm13`-elimination core of step 3 are done and
reusable.  Step 2 (`âˆ‡rm13 = raise(âˆ‡rm04)`) is the **first** stop condition hit and
is a missing **tensor-layer `(1,3)` raising-parallelism** lemma (a realization/
metric-compatibility bridge, not a `k = 1` proof failure).  Independently, even the
`âˆ‡rm13`-free `Tâ‚‚` half is gated by the missing **coordinateâ†’orthonormal frame
change**.  `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 third follow-up: Step A (the `(1,3)` raising-parallelism) is itself the wall

This pass took the dedicated task of proving the rank-`(1,3)` raising-parallelism
lemma (Step A above) **as a self-contained tensor-layer lemma** in
`Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`, then closing
the `Tâ‚` summand from it.  After a full read of the lowering template, the
`lowerAllUpperIndices` definition, both `nabla_metric_zero` sites, and the two
covariant-derivative formalisms in play, the conclusion is that **Step A hits the
task's first stop condition** ("`nabla_metric_zero` at `r â‰¥ 1` is insufficient â€¦
needs a missing chain/product rule").  No Lean code was changed; fabricating a
renamed/axiomatized parallelism is forbidden by the task's honesty constraints.

### Why Step A is blocked (the precise missing ingredient)

The target is the rank-`(1,3)` lowering intertwiner
`âˆ‡(lower_{1,3} S) = lower_{1,3}(âˆ‡^{RS} S)` (equivalently the `.symm`/raising form
stated in the task), the `r â‰¥ 1` analogue of
`loweredCovDerivAt_eq_lower_tensorCovDerivAt[_gen]`
(`MetricCompatibility/TensorLoweringParallel.lean`,
`â€¦/TensorConnLapGreenIntertwiner.lean`).

* The template proof carries **no** `âˆ‡g = 0` content: at `r = 0` the lowering map is
  *evaluation at the unit `(0,0)`-tensor*, whose `tensor0SCovariantDerivative` is
  `0` (`tensor0SCovariantDerivative_unitZero_eq_zero`).  That is the entire reason
  it generalises in `s` (only a `Nat.zero_add` transport), and it is exactly why it
  does **not** generalise in `r`.
* For `r â‰¥ 1`, `lowerAllUpperIndices g r s x T` contracts `T`'s `r` upper slots
  against `r` metric factors: `lowerAllUpperIndices_apply` gives
  `T (separableFormAt g x r (vâˆ˜castAdd)) (vâˆ˜natAdd)`, and `separableFormAt_apply`
  shows `separableFormAt = âˆáµ¢ g.inner x (váµ¢) (Â·)` â€” a genuine product of `r` Gram
  factors.  Proving `âˆ‡(lower S) = lower(âˆ‡S)` therefore requires differentiating this
  metric contraction and killing the `r` `âˆ‡g`-factor terms via metric compatibility.
* That step needs a **general covariant product/contraction Leibniz rule** for
  `tensor0SCovariantDerivative s` (or `nabla0SFun s`) over the `separableFormAt`
  metric contraction at arbitrary rank.  **No such rule exists in the tree.**  The
  only covariant product rules present are `nabla_smul_metric`
  (`Tensor/RSTensor/MetricCompatibility.lean`, the scalar-multiple `âˆ‡(fÂ·g)=dfâŠ—g`,
  `r = 0`) and `nabla0SFun_one_eval_of_coordFrame_product*`
  (`Geometry/Connection/Chart/NablaComponents/OneForm.lean`, rank-1 one-forms in
  coordinate-frame moving-slot form).  There is no `âˆ‡(tensor product)`, no
  `âˆ‡(separableFormAt) = 0`, no `(0,2r)` "metric-power" section with `âˆ‡ = 0`, and no
  `(r,s)` lowering intertwiner for `r â‰¥ 1` anywhere.
* `nabla_metric_zero` **is** available â€” `Tensor/RSTensor/MetricCompatibility.lean`
  (and `Geometry/.../MetricCompatibility.lean` supplies the underlying
  `IsMetricCompatible_gen`), dischargeable for `LeviCivita g` via
  `LeviCivita_isMetricCompatible` â€” but it lives in the `nabla0SFun` formalism and is
  *insufficient on its own*: there is no rule to thread `âˆ‡g = 0` through the rank-`r`
  metric contraction.  The cross-formalism bridge
  `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative`
  (`ChartTensorNabla/Agreement/Tensor0SRSCovariantDerivativeAgreement.lean`) is
  `(0,s) â†” (r=0,s)` **only**, so it does not transport a lowering Leibniz to
  `r â‰¥ 1`.

### The inner-product route is circular (checked, not assumed)

`TensorRSMetricCompatible.lean` proves the `(r,s)` inner-product compatibility
`âˆ‡âŸ¨W,SâŸ© = âŸ¨âˆ‡W,SâŸ© + âŸ¨W,âˆ‡SâŸ©`, but with `loweredCovDerivAt` (= `âˆ‡` of the *lowered*
section) on **both** sides â€” i.e. it is the lowered-picture statement, not the
genuine `(1,3)` `tensorRSCovariantDerivative`.  Pairing `âˆ‡(lower S)` and
`lower(âˆ‡^{RS} S)` against all `(0,4)` test tensors `lower Y` via the nondegenerate
`(0,4)` inner product reduces Step A to the **genuine `(1,3)` inner-product
compatibility** `âˆ‡âŸ¨S,YâŸ© = âŸ¨âˆ‡^{RS}S,YâŸ© + âŸ¨S,âˆ‡^{RS}YâŸ©` (with
`tensorRSCovariantDerivative`), which is inter-derivable with Step A and is **equally
absent** from the tree (searched: no `tensorRSCovariantDerivative`-based inner-product
compatibility exists).  So every route converges on the same missing ingredient:
the general covariant contraction-Leibniz / `âˆ‡(separableForm)=0`.

### `Tâ‚` (Step B) is independently blocked, and Step A would not unblock it

The `Tâ‚` work the task describes is **already proved**, sorry-free, in
`Evolution/NablaRiemannCommutatorBound.lean`:
`nablaLapComm_T1_eq_covDeriv_curvatureAction` shows
`Tâ‚ = âˆ‡Â³Rm(a,b,c) âˆ’ âˆ‡Â³Rm(a,c,b) = âˆ‡_a K`, the covariant derivative of the
curvature-action field `K = [âˆ‡_b,âˆ‡_c]Rm = curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`, in
explicit `eval_C1_slots` form; and
`nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction` packages
the whole reaction as `âˆ‡(Rmâˆ—Rm) + Rmâˆ—âˆ‡Rm`.  The remaining `|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`
bound is blocked because differentiating `curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`
covariantly needs `âˆ‡rm13 âˆ— Rm04 + rm13 âˆ— âˆ‡Rm04`, and in the **`totalNabla0S`
solution formalism** of `Tâ‚`:
  (a) there is no contraction-Leibniz for `totalNabla0S`;
  (b) `âˆ‡rm13` has **no** `totalNablaRS` realization for `S.base.rm13` (the only
      solution-curvature realizations are the lowered
      `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field`); and
  (c) Step A's parallelism â€” even if proved â€” lives in the *different*
      `tensorRSCovariantDerivative`/`lowerAllUpperIndicesEquiv` formalism, with **no**
      bridge to `totalNabla0S` at `r â‰¥ 1`.
Hence even a completed Step A would not close `Tâ‚`: this is precisely the task's
**second** stop condition ("the covariant Leibniz on the curvature-action
contraction needs an unavailable lemma even with Step A"), and it matches the
four-gap frontier independently reached by three prior agents (see
`DimensionThree/HamiltonPositiveRicci.md`, gaps 2â€“3).

### Exact theorems needed next (unchanged frontier, now localised to a Leibniz)

1. A **general covariant product/contraction Leibniz** for `nabla0SFun s` /
   `tensor0SCovariantDerivative s` (minimally, `âˆ‡(separableFormAt g r) = 0` and a
   contraction rule), from which the `(r,s)` lowering intertwiner
   `âˆ‡(lower_{r,s} S) = lower_{r,s}(âˆ‡^{RS} S)` follows by the same
   `nabla0SFun_eval_smooth_slots` + `nabla_metric_eval` cancellation that proves
   `nabla_metric_zero`/`nabla_smul_metric`.  Belongs at the tensor layer
   (`Tensor/RSTensor/â€¦` or `Connection/MetricCompatibility/â€¦`).
2. A `totalNabla*RS` realization `nablaRm13Field` for `S.base.rm13` (gap 3), plus the
   `nabla0SFun â†” totalNabla0S`/`tensorRSCovariantDerivative` bridge at `r â‰¥ 1`, to
   even *state* the contraction-Leibniz for `curvatureAction0SAt (rm13 Â·)(Rm04 Â·)` on
   the solution side.

Neither is a single lemma; both are framework-scale (the "RmRealizationBridge-style
frontier" already flagged).  Per the task, this precise wall is the deliverable.
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`; no `sorry`,
no axiomatized parallelism, no Lean changes were made this pass.

## 2026-06-06 fourth follow-up: the coordinateâ†’orthonormal frame-change adapter is BUILT (obstruction #4 removed)

This pass took the dedicated task of the **coordinateâ†’orthonormal frame-change
adapter** â€” the *second* of the two isolated walls (the `Tâ‚‚`-half / footer
obstruction #4 / fourth stop condition "no frame-change bridge from
`coordinateFrameAt` to an orthonormal frame").  It is now **closed, sorry-free**, in
a new file `Evolution/NablaRiemannOrthoFrame.lean`.  `#print axioms` on every public
theorem is `[propext, Classical.choice, Quot.sound]`.

### Route decision (the three routes scoped before building)

* **(a) orthonormalise at the centre â€” CHOSEN, viable.**  The spatial commutator
  lemmas of `NablaRiemannCommutator.lean` are derived **purely** from the *frame-free*
  `(0, s)` Ricci identities `rm04_ricciIdentityAt` / `nablaRm04_ricciIdentityAt`
  (arbitrary tangent vectors at a point); `coordinateFrameAt xâ‚€` enters only as the
  *choice* of tangent vectors fed to the bundled `âˆ‡Â³Rm = nabla3Rm04Field`, evaluated
  **only at `xâ‚€`**.  So the whole commutator is frame-generic with **zero** new
  mathematical content and needs only a *basis at `xâ‚€`* (no smooth/global frame).
* **(b) general-`gInv` producer bound â€” NOT cheaper, rejected.**  Removing the
  producer's `horth` and re-deriving `|reaction| â‰¤ C|Rm||âˆ‡Rm|` for a general `gInv`
  needs the fibre-norm â†” component-norm bridge in an orthonormal frame
  (`Curvature/FiberNormParseval/*`, `normSq0S_identity_eq_sum_sq` needs
  `identityInvMetric`); the Cauchyâ€“Schwarz core of `NablaRiemannHeat.lean`
  (`abs_nablaRmReactionDown_le`) is hardwired to `compNormSq*` (plain component sums),
  so general `gInv` requires re-deriving substantial norm machinery â€” exactly footer
  obstruction #4 restated, not a shortcut.
* **(c) normal coordinates â€” not needed.**  Route (a) supersedes it; a normal-coord
  realization with `g(centre)=Î´` is also absent in the solution layer.

### What was proved (`Evolution/NablaRiemannOrthoFrame.lean`, all sorry-free)

* `nablaLapCommF_pointwise` / `nablaLapCommF_trace` / `nablaLapCommF_orthonormalTrace`
  â€” the spatial commutator `[Î”, âˆ‡_c] Rm = reaction` over an **arbitrary** index type
  `Idx` and frame `frame : Idx â†’ (x : M) â†’ TangentSpace I x` (the genuine reusable
  abstraction of the `coordinateFrameAt` lemmas; identical one-line Ricci-identity
  proofs).  Generic defs `nabla3InnerSlotsF`, `nabla3FrameTupleF`,
  `nablaLapCommReactionTermF`, `roughLapNablaRmCompF`, `nablaRoughLapRmCompF`.
* `exists_orthoFrameAt` â€” a pointwise **`g`-orthonormal frame of `T_{xâ‚€}M`** from the
  *fibre* metric `g xâ‚€ = S.family.metric t`, with **no** model `[InnerProductSpace â„ E]`.
  Built by the chart-locality-free `letI â€¦ ofCore` Gramâ€“Schmidt
  (`g.toRiemannianMetric.toCore xâ‚€`, `RiemannianMetric.toCore`/`.continuousAt`/
  `.isVonNBounded` from `Mathlib/Topology/VectorBundle/Riemannian.lean`, which need
  only a normed model fibre) + `stdOrthonormalBasis`.  This is the technique of
  `exists_orthonormal_frame_riemannianFiberNormSq`
  (`Analysis/Elliptic/â€¦/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`), replicated
  directly to avoid that file's *spurious* `[InnerProductSpace â„ E]` section variable.
* `deltaInvMetric_orthonormal` â€” the **honest** `InverseMetricOrthonormalAt` witness:
  the constant Kronecker delta `deltaInvMetric` is the *genuine* inverse metric of the
  `g`-orthonormal frame (for a `g`-orthonormal basis `gáµƒáµ‡ = Î´`), **not** an assumption
  about `coordinateFrameAt`.
* `nablaLapComm_orthoFrame` â€” the **assembled adapter**: at `xâ‚€`, for a solution at a
  regular time, there exist a `g xâ‚€`-orthonormal frame and the delta inverse metric
  such that `InverseMetricOrthonormalAt deltaInvMetric t xâ‚€` holds **honestly** and the
  spatial commutator collapses to the diagonal trace
  `Î”(âˆ‡Rm)(c) âˆ’ âˆ‡(Î”Rm)(c) = Î£_a reaction a a c m` â€” exactly the orthonormal shape the
  producer (`nablaRm04NormHeatBoundOn_of_components`, via `(âˆ‚â‚œ âˆ’ Î”)âˆ‡Rm`) consumes.

### Why this is the honest replacement for `nablaLapComm_orthonormalTrace`

`nablaLapComm_orthonormalTrace` (`NablaRiemannCommutator.lean`) carries `horth :
gInv = Î´` but is hardwired to `coordinateFrameAt xâ‚€`, whose true inverse metric is
**not** `Î´`; so its `roughLapNablaRmComp (coordinateFrameAt) Î´` is *not* the rough
Laplacian and the `horth` is unsatisfiable for the real inverse metric.  The adapter
replaces the chart frame by a **genuinely `g`-orthonormal** frame, where `gáµƒáµ‡ = Î´` is
the *true* inverse metric, so the diagonal trace really is `Î” = gáµƒáµ‡ âˆ‡â‚âˆ‡áµ¦`.  The
producer is **not** weakened: `coordinateFrameAt` is never asserted orthonormal.

### Net (the two walls after this pass)

* **Obstruction #4 (frame change) â€” RESOLVED.**  The `âˆ‡rm13`-free `Tâ‚‚` half, and
  indeed the *whole* spatial commutator, is now available in the producer's
  orthonormal convention with a genuine `gáµƒáµ‡ = Î´`.  This was the precise
  "frame-change bridge â€¦ so that the producer's `InverseMetricOrthonormalAt` is
  satisfiable" the prior follow-up named as the next theorem for `Tâ‚‚`.
* **Obstruction #1 (the `(1,3)` raising-parallelism for `Tâ‚`) â€” UNCHANGED, separate.**
  The quantitative bound `|reaction| â‰¤ C(dim)Â·|Rm|Â·|âˆ‡Rm|` is still gated by the
  `Tâ‚` summand's `âˆ‡(raise rm04) = raise(âˆ‡ rm04)` (Step A above, the general covariant
  contraction-Leibniz / `âˆ‡(separableForm)=0` in
  `Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`), which is
  *orthogonal* to the frame change and remains the genuinely missing tensor API.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.  Files added:
`Evolution/NablaRiemannOrthoFrame.lean` (no existing file edited).  Focused
`lake-locked build` of the new module: EXIT 0.

## 2026-06-06 fifth follow-up: Step A's contraction-Leibniz is BUILT (the prior "Step A is the wall" verdict is refuted); Tâ‚'s bound is the second stop condition

This pass took the dedicated task of **Step A** â€” the general covariant
contraction-Leibniz at the tensor layer â€” and **closed its core**, sorry-free and
axiom-clean, in a new file `Tensor/RSTensor/ContractionLeibniz.lean`.  This directly
**refutes the third follow-up's conclusion** that "Step A is itself the wall": the
`nabla0SFun` tensor-product/contraction Leibniz **is** assemblable from
`nabla0SFun_eval_smooth_slots` + `nabla_metric_zero`, by the same concrete-evaluation
technique that proves `nabla_smul_metric`.

### What was proved (`Tensor/RSTensor/ContractionLeibniz.lean`, all sorry-free)

* `nabla0SFun_product_eval` â€” the **evaluated tensor-product Leibniz**
  `âˆ‡(A âŠ— B)(V) = âˆ‡A(X :: Vâˆ˜castAdd)Â·B(Vâˆ˜natAdd) + A(Vâˆ˜castAdd)Â·âˆ‡B(X :: Vâˆ˜natAdd)`,
  for smooth `(0,s)`/`(0,q)` fields `A`/`B` with realized derivatives, from
  `nabla0SFun_eval_smooth_slots`, `product_fun_apply`, and the scalar product rule.
* `nabla_product_zero_of_zero` â€” the tensor product of two `âˆ‡`-parallel tensors is
  parallel (`âˆ‡(A âŠ— B) = 0` when `âˆ‡A = âˆ‡B = 0`).
* `metricPow g r` â€” the `(0,2r)` metric power `g^{âŠ—r}` (the (0,2r) "metric-power
  section" each upper slot of an `(r,s)`-tensor is lowered against).
* `nabla_metricPow_zero` â€” `âˆ‡(g^{âŠ—r}) = 0` for a metric-compatible connection, by
  induction from `nabla_metric_zero` and `nabla_product_zero_of_zero`.  This is
  **Step A.1**.
* `nabla0SFun_metricPow_contraction_eval` â€” **Step A.2** in the reachable formalism:
  the contraction-against-the-metric-power Leibniz `âˆ‡(A âŠ— g^{âŠ—r}) = âˆ‡A âŠ— g^{âŠ—r}`
  (the metric factor passes through `âˆ‡` untouched).

`#print axioms` on all five (plus the helper `tensor0SField_product_apply`) is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0.

### Why this is the genuine Step A primitive, and where it stops

The prior agent conflated **Step A.1/A.2 in the `nabla0SFun` formalism** (now proved)
with **Step A.3 stated in the `tensorRSCovariantDerivative`/`lowerAllUpperIndicesEquiv`
formalism** (still blocked).  The two are *different covariant-derivative
formalisms*:

* `nabla0SFun` (= `mcovariantDeriv_tensor0SFromConnection`, the concrete eval) â€” where
  `nabla_metric_zero`, `nabla_smul_metric`, the new product-Leibniz, and **all the
  solution curvature fields** `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` (via
  `totalNabla0S`) live;
* `tensor0SCovariantDerivative` (the recursive Hom-bundle, base = `extDerivFun`, succ =
  curry/uncurry) â€” where `loweredCovDerivAt` and hence the **A.3 statement**
  `âˆ‡(lower S) = lower(âˆ‡^{RS} S)` live.

There is **no `nabla0SFun â†” tensor0SCovariantDerivative` agreement at rank `r â‰¥ 1`**
(the only bridge, `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative`, is
`(0,s) â†” (r=0,s)`).  So Step A.1/A.2 in `nabla0SFun` do **not** transport to the A.3
statement in the lowering formalism.  A.3 as literally stated is gated by that
missing rank-`â‰¥1` agreement â€” **not** by the contraction-Leibniz, which is done.

### Tâ‚'s bound is the second stop condition (now sharply localised)

`Tâ‚ = âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm) = âˆ‡_a K`, `K = curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`.  The
reduction `Tâ‚ = âˆ‡_a K` is re-exported as `nablaLapComm_T1_eq_covDerivK`
(`Evolution/NablaRiemannT1Bound.lean`, axiom-clean), thin over
`nablaLapComm_T1_eq_covDeriv_curvatureAction`.  The bound `|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`
needs `âˆ‡K` as a `âˆ‡Rm âˆ— Rm + Rm âˆ— âˆ‡Rm` contraction; after Step A this reduces to a
sharply-isolated residual (recorded in full in the header of
`Evolution/NablaRiemannT1Bound.lean`):

1. **`(1,3)` route:** `âˆ‡rm13` has no `totalNabla*RS` realization for `S.base.rm13`,
   and Step A's `nabla0SFun` product-Leibniz covers `(0,s) âŠ— (0,q)` **products**, not
   the `Hom`-**contraction** of the `(1,3)` `rm13`.  Identifying `âˆ‡rm13 = raise(âˆ‡Rm04)`
   is A.3 â€” gated by the missing `nabla0SFun â†” tensor0SCovariantDerivative` rank-`â‰¥1`
   agreement above.
2. **Raise-form route (avoids `âˆ‡rm13`):** `curvatureAction0SAt_eq_rm04_raise`
   (`RmRaisingBridge.lean`) gives `K = -Î£_q rm04(â€¦, gâ™¯ Î²q)` using **only** the realized
   `Rm04` and the metric raising `gâ™¯`.  Differentiating it via
   `nabla0SFun_eval_smooth_slots` for `nablaRm04Field` needs (a) the **sharp-parallelism**
   `âˆ‡(gâ™¯ Î²) = gâ™¯(âˆ‡Î²)` â€” proved for one-forms in `Tensor0SRiemannian/Smooth.lean`
   (`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`) but **`private`**; and (b) a
   **frozen-slot covariant Leibniz** `âˆ‡(oneFormAtSlot0S Rm04 slots q)` in terms of
   `âˆ‡Rm04` â€” **absent**.  This route is the most promising and needs only (a) exposed +
   (b) built; it does **not** hit the `âˆ‡rm13` wall.
3. **Frame reconciliation:** `Tâ‚ = âˆ‡_a K` is proved at the **smooth** `coordinateFrameAt xâ‚€`
   (differentiation needs a smooth frame), but the bound must be in the
   **`g`-orthonormal** frame of `exists_orthoFrameAt`, which is only *pointwise*
   orthonormal at `xâ‚€` (a constant transport off-centre).  Reconciling the two is a
   third, separate piece.

This is the task's **second stop condition** ("closing Tâ‚ needs a `nabla0SFun â†”
totalNabla0S`/`tensorRS` formalism bridge at `r â‰¥ 1` that is absent"), reached *after*
Step A's contraction-Leibniz, exactly as the task anticipated.  `Tâ‚‚` (the bare
curvature action, no curvature derivative) is unaffected and is closed in
`Evolution/NablaRiemannT2Bound.lean`.

### Net

* **Step A.1/A.2 (the `nabla0SFun` contraction-Leibniz + `âˆ‡(g^{âŠ—r}) = 0`) â€” DONE**,
  refuting the prior "Step A is the wall".  Reusable tensor-layer primitives.
* **Step A.3 (the `(1,3)` raising-parallelism *as stated* in the lowering formalism)
  and Step B (`|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`) â€” second stop condition**, localised to: the
  missing `nabla0SFun â†” tensor0SCovariantDerivative` rank-`â‰¥1` agreement (route 1) /
  a public sharp-parallelism + frozen-slot Leibniz (route 2), plus the smoothâ†”orthonormal
  frame reconciliation (route 3).

Files added: `Tensor/RSTensor/ContractionLeibniz.lean`,
`Evolution/NablaRiemannT1Bound.lean` (no existing file edited).  Focused
`lake-locked build` of both: EXIT 0.  `BernsteinShiSolution.lean` remains parametric
in `IteratedRmTowerOn`.

## 2026-06-06 sixth follow-up: the `Tâ‚‚` quantitative bound is BUILT (`|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|`)

This pass took the dedicated `Tâ‚‚` task â€” the bound on the **second** reaction summand
`Tâ‚‚ = curvatureAction0SAt rm13 (âˆ‡Rm) (frame a)(frame c)(slots)` (the bare `(0,5)`
curvature commutator `[âˆ‡_a,âˆ‡_c](âˆ‡_b Rm)`, **no** curvature derivative).  It is now
**closed, sorry-free, axiom-clean** in a new file `Evolution/NablaRiemannT2Bound.lean`.
`#print axioms` on every public theorem is `[propext, Classical.choice, Quot.sound]`.

### The route (no missing tensor-norm lemma â€” neither stop condition is hit)

The task's two stop conditions were (i) the curvature-action fibre-norm â†”
frame-component-norm bridge needing a missing tensor-norm lemma, and (ii) `|rm13| â‰¤
C|Rm04|` needing a missing raising-norm comparison.  **Both are avoided** by *not*
working in fibre norms at all and *not* comparing `|rm13|` to `|Rm04|` as norms.
Instead the curvature action is rewritten as a **plain frame-index component
contraction** before any norm is taken:

1. `curvatureAction0SAt rm13 Î± (e_a)(e_c)(slots) = -âˆ‘_q rm13 (Î²_q)(vec3 e_a e_c slots_q)`
   (definition), `Î²_q = oneFormAtSlot0S Î± slots q`;
2. the pointwise **raising bridge** `rm13_apply_eq_rm04_raise` (`RmRaisingBridge.lean`)
   rewrites each pairing as `rm13 (Î²_q)(vec3 â€¦) = rm04(e_a, e_c, slots_q, gâ™¯ Î²_q)`;
3. in a `g`-orthonormal **basis**, `cotangentSharp_eq_sum_inv_gen` (specialised to
   `gáµƒáµ‡ = Î´` via `MetricInverseInBasis_gen`, immediate from orthonormality) gives the
   simple orthonormal reconstruction `gâ™¯ Î²_q = âˆ‘_e (Î²_q e_e) â€¢ e_e`, and multilinearity
   of `rm04` in its last slot (`MultilinearMap.map_update_sum`) pushes it through:
   `rm04(e_a,e_c,slots_q, gâ™¯ Î²_q) = âˆ‘_e (Î±(update slots q e_e)) Â· rm04(e_a,e_c,slots_q,e_e)`.

After step 3 **every factor is a plain frame component** â€” `rm04(eáµ¢,eâ±¼,eâ‚–,e_l)` (a
`compNormSq4` entry) and `Î±(eâ€¦)` (a `compNormSqMulti` entry); the metric raising is
gone, so there is **no** raising-norm comparison to supply, refuting stop condition
(ii).  Cauchyâ€“Schwarz over the `(q,e)` index pair (`sÂ·card` terms, here `5Â·card`),
with the per-entry domination `abs_le_sqrt_compNormSq4`/`abs_le_sqrt_compNormSqMulti`,
gives the bound directly in the producer's component norms, refuting stop condition (i).

### What was proved (`Evolution/NablaRiemannT2Bound.lean`, all sorry-free, axiom-clean)

* `curvatureAction0SAt_orthoBasis_eq_sum` â€” the curvature action on basis vectors as
  the plain double sum `-âˆ‘_q âˆ‘_e Î±(update sidx q e) Â· rm04(e_a,e_c,e_{sidx q},e_e)`
  (raising bridge + orthonormal `gâ™¯` reconstruction + last-slot multilinearity).
* `abs_curvatureAction0SAt_orthoBasis_le` â€” **the abstract point-level bound**: for any
  `Module.Basis`, `g`-orthonormality, and lowering relation `Rm04LowersRm13At`,
  `|curvatureAction0SAt rm13 Î± (basis a)(basis c)(basisâˆ˜sidx)|
     â‰¤ s Â· card Â· âˆš(compNormSq4 R) Â· âˆš(compNormSqMulti A)`,
  with `R i j k l = rm04(eáµ¢,eâ±¼,eâ‚–,e_l)`, `A idx = Î±(eâˆ˜idx)`.  The honest constant is
  `s Â· card` (the genuine number of contraction terms), not a forced `cardÂ²`.
* `exists_orthoBasisFrameAt` â€” a `g`-orthonormal frame of `T_{xâ‚€}M` whose **centre
  values are a `Module.Basis`** (the `exists_orthoFrameAt` `letI â€¦ ofCore` Gramâ€“Schmidt,
  additionally exposing `stdOrthonormalBasis.toBasis` and `frame i xâ‚€ = basis i`).
* `compNormSqMulti_eq_compNormSq5` â€” the reindexing `âˆ‘_{idx:Fin 5â†’Idx}(A idx)Â²
  = âˆ‘_{m a b c d}(A ![m,a,b,c,d])Â²` (iterated `Fin.consEquiv`), the bridge from the
  rank-uniform `compNormSqMulti` to the producer's nested `compNormSq5` /
  `nablaRm04NormSqInFrame_eq_compNormSq5`.
* `abs_nablaLapComm_T2_orthoBasis_le` â€” the **solution-facing `Tâ‚‚` bound** in plain
  component norms, instantiating the abstract bound at `S.base.rm13`/`nablaRm04Field`
  with `solution_rm04LowersRm13At`, slot tuple `Fin.cons b m`.
* `abs_nablaLapComm_T2_orthoFrame_le` â€” **the assembled `Tâ‚‚` bound** in the producer's
  convention: at `xâ‚€` there exist a genuine `g`-orthonormal frame and the Kronecker-delta
  inverse metric with `InverseMetricOrthonormalAt` holding **honestly**, such that
  `|Tâ‚‚| â‰¤ 5 Â· card Â· âˆš(rm04NormSqInFrame) Â· âˆš(compNormSqMulti of frame âˆ‡Rm)`,
  i.e. `|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|` with the `Rm`-factor in the producer's
  `rm04NormSqInFrame` (via `rm04NormSqInFrame_eq_compNormSq4`) and the `âˆ‡Rm`-factor in
  the plain `compNormSqMulti` (chainable to `nablaRm04NormSqInFrame` through
  `compNormSqMulti_eq_compNormSq5` + `nablaRm04NormSqInFrame_eq_compNormSq5`).

### Why the `Tâ‚‚` frame issue (route-3 of the fifth follow-up) does not arise

The fifth follow-up's "smoothâ†”orthonormal frame reconciliation" (route 3) is a
**`Tâ‚`-only** problem: `Tâ‚ = âˆ‡_a K` must be *differentiated*, which needs a smooth
frame, clashing with the pointwise-at-`xâ‚€` orthonormal frame.  `Tâ‚‚` is a **bare**
curvature action (no differentiation), evaluated only at `xâ‚€` on basis vectors, so the
*pointwise* `g`-orthonormal basis of `exists_orthoBasisFrameAt` is exactly sufficient â€”
no smooth global frame is needed, and the bound lands directly in the producer's
orthonormal convention.

### Net (the frontier after this pass)

* **`Tâ‚‚` quantitative bound â€” DONE.**  `|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|` in the genuine
  orthonormal frame's component norms, sorry-free and axiom-clean.  Neither task stop
  condition was hit: the fibre-norm/component-norm bridge was *bypassed* (the action is
  a component contraction *before* norming), and the `|rm13|`-vs-`|Rm04|` comparison is
  *unnecessary* (the raising `gâ™¯` is eliminated into the contraction).
* **`Tâ‚` quantitative bound â€” UNCHANGED, separate (fifth follow-up's second stop
  condition).**  Still gated by the missing `nabla0SFun â†” tensor0SCovariantDerivative`
  rank-`â‰¥1` agreement / public sharp-parallelism + frozen-slot Leibniz, plus the
  smoothâ†”orthonormal frame reconciliation â€” all orthogonal to `Tâ‚‚`.

Files added: `Evolution/NablaRiemannT2Bound.lean` (no existing file edited).  Focused
`lake-locked build` of the new module: EXIT 0.  `BernsteinShiSolution.lean` remains
parametric in `IteratedRmTowerOn`.

## 2026-06-06 seventh follow-up: the `Tâ‚` route is UNBLOCKED (prior "frozen-slot Leibniz absent" verdict refuted); sharp-parallelism exposed

This pass took the dedicated `Tâ‚` quantitative-bound task (`|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`,
the **first** reaction summand `âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm) = âˆ‡_a(Rm âˆ— Rm)`).  After tracing
the only `âˆ‡rm13`-free route (route 2, the `gâ™¯` raise form
`curvatureAction0SAt_eq_rm04_raise`) end-to-end against the existing tree, the
finding is that **the route is not blocked** â€” every tool it needs already exists â€”
and the prior follow-ups' verdict that the **frozen-slot covariant Leibniz is
absent** is **incorrect**.  One verified, minimal unblocking change was made; the
full assembly is large and was not completed this pass (it would have required new
`sorry`s, forbidden).

### The route, with every tool now located (correcting the prior reports)

`Tâ‚ = âˆ‡_a K`, `K = curvatureAction0SAt (rm13)(Rm04)` (`nablaLapComm_T1_eq_covDerivK`).
Route 2 writes `K = -Î£_q rm04(X, Y, slots_q, gâ™¯ Î²q)` with `Î²q = oneFormAtSlot0S Rm04
slots q` (`RmRaisingBridge.curvatureAction0SAt_eq_rm04_raise`), **no** `rm13`.
Differentiating it covariantly:

1. **Sharp-parallelism `âˆ‡(gâ™¯ Î²) = gâ™¯(âˆ‡Î²)`** â€” `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
   (`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`).  It was `private`; **this pass
   made it public** (the precise content the fifth follow-up's route-2(a) and the task's
   third stop condition flagged as "private, not citable").  Axiom-clean
   (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), focused build EXIT 0.
2. **Frozen-slot covariant Leibniz `âˆ‡(oneFormAtSlot0S Rm04 slots q)` â†¦ frozen slot of
   `nablaRm04Field`** â€” declared "absent" by the second/third/fifth follow-ups, but its
   exact template is **`middleFreezeNabla`** (`Tensor/RSTensor/MetricTrace/Higher.lean`):
   it differentiates a slot-frozen `(0,4)` field and rewrites the derivative through
   `nablaA` by choosing the frozen-slot sections **covariantly constant at `xâ‚€`** via
   `TensorLieDeriv.exists_cov_zero_at_apply`
   (`Tensor/RSTensor/NablaOnTensors/Connection/OneJet.lean`), so all frozen-slot
   Christoffel corrections vanish.  The frozen one-form field itself is built like
   `freezeMiddle04Field` (`Tensor/RSTensor/MetricTrace/NablaTrace02.lean`).  The
   freeze/`âˆ‡` machinery is present and reusable â€” not absent.
3. **Smoothness of the sharp field `p â†¦ gâ™¯ (Î²q p)`** (the `MDiffAt` hypothesis of
   the sharp-parallelism) â€” `metricSharp_contMDiff_total`
   (`Geometry/Operator/MetricSharpSmooth.lean`), from chart-basis component
   smoothness of `Î²q` (a frozen evaluation of the smooth `Rm04` against smooth frame
   fields).  Needs a `metricSharp â†” cotangentSharp_gen` identification at the
   component level.
4. **Frame reconciliation (smooth `coordinateFrameAt` â†¦ pointwise orthonormal)** â€”
   **not a wall**: `âˆ‡_a K` is a genuine tensor value at `xâ‚€` (`nabla3Rm04Field`
   antisymmetrised), so bounding it on orthonormal-frame vectors realises *those*
   vectors by cov-zero sections (`exists_cov_zero_at_apply`) and applies the same
   Leibniz at `xâ‚€`; no smooth orthonormal field is needed.
5. **Final estimate** â€” the two resulting `Rm04 âˆ— âˆ‡Rm04` raise-contraction summands
   are evaluated in the orthonormal basis at `xâ‚€` (where `gâ™¯ Î² = Î£_e (Î² e_e) e_e`,
   `cotangentSharp_orthoBasis_expand`) and bounded by the **exact Cauchyâ€“Schwarz of
   `NablaRiemannT2Bound.lean`** (`abs_le_sqrt_compNormSq4`/`abs_le_sqrt_compNormSqMulti`),
   landing in the producer's `rm04NormSqInFrame`/`compNormSqMulti` norms.

The fifth follow-up's "second stop condition" (a missing `nabla0SFun â†”
tensor0SCovariantDerivative` rank-`â‰¥1` agreement) applies **only** to the `(1,3)`
route (1) â€” differentiating `rm13` directly â€” which route 2 **sidesteps** by raising
`Rm04` instead.  So that stop condition is *not* on the critical path.

### What was changed this pass (verified)

* `Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`:
  `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` changed from `private` to a public
  theorem (with docstring).  No proof change.  Focused `lake-locked build`: EXIT 0;
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
* `Evolution/NablaRiemannT1Bound.lean`: header docstring corrected to record that
  route 2 is viable and to point at the freeze/`âˆ‡` and sharp-smoothness tools (no code
  change; the re-export theorem is unchanged).  Focused `lake-locked build`: EXIT 0.

### What remains (large but unblocked)

The assembly is genuinely framework-scale and was **not** completed (no `sorry` was
introduced): a bundled freeze-all-but-slot-`q` one-form field for `Rm04` with its
`(0,1)` `TotalNabla0SRealizes` (template `freezeMiddle04Field` + `middleFreezeNabla`,
for `q âˆˆ Fin 4`); the `metricSharp â†” cotangentSharp_gen` component-smoothness bridge
for those one-forms (the highest-risk piece); the assembled covariant Leibniz for `K`
combining (1)+(2)+cov-zero slot sections; and the orthonormal evaluation + the `Tâ‚‚`
Cauchyâ€“Schwarz (5).  Estimated ~600â€“1000 LOC across these layers.  None is blocked by
a missing tensor-API/realization frontier â€” the genuine remaining cost is the size of
this concrete assembly, not an absent lemma.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 eighth follow-up: piece (1) of the `Tâ‚` route-2 assembly is BUILT â€” the frozen-slot one-form field of `Rm04` with its `(0,1)` covariant derivative

This pass took the dedicated **piece (1)** of the (now-unblocked) route-2 `Tâ‚`
assembly named in the seventh follow-up: the bundled **freeze-all-but-slot-`q`
one-form field for `Rm04`** plus its `(0,1)` covariant-derivative realization
(`TotalNabla0SRealizes`).  It is now **closed, sorry-free, axiom-clean**, in a new
file `Evolution/RmFrozenSlotField.lean`.  `#print axioms` on every public
declaration is `[propext, Classical.choice, Quot.sound]`.  Focused
`lake-locked build` of the new module: EXIT 0 (3633/3633 jobs).

### Why this refutes the prior "frozen-slot Leibniz is large/risky" framing

The seventh follow-up correctly identified the templates (`freezeMiddle04Field` +
`middleFreezeNabla`) but estimated the frozen one-form field + its `(0,1)`
realization + the `metricSharp â†” cotangentSharp_gen` smoothness bridge together as
~600â€“1000 LOC and flagged the smoothness bridge as "the highest-risk piece".  In
fact the **frozen one-form field and its `(0,1)` covariant derivative need no
sharp-smoothness bridge at all**: the field is the slot-frozen one-form
`oneFormAtSlot0S (Rm04 p)(frozen slots)(q)` itself (a `dualToCotangent_gen` of an
`Rm04`-evaluation), whose smoothness is the **exact** `freezeMiddle04Field`
coordinate-frame proof at rank `(0,1)` (one slot, `Fin 1`), and whose covariant
derivative is the **exact** `middleFreezeNabla` device at rank `(0,4) â†’ (0,1)`.  The
`metricSharp â†” cotangentSharp_gen` bridge is a *separate* concern of piece (2) (the
`gâ™¯ Î²q` sharp-field smoothness, the `MDiffAt` hypothesis of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`), **not** of piece (1) â€” the
covariant derivative of `Î²q = oneFormAtSlot0S Rm04 slots q` is taken *before* any
sharp is applied.  Piece (1) is â‰ˆ430 LOC and hit **no** wall.

### What was proved (`Evolution/RmFrozenSlotField.lean`, all sorry-free, axiom-clean)

Reusable tensor-layer (namespace `Integral.Connection`, arbitrary `(0,4)` field
`A`, not Ricci-flow-specific):

* `freezeAllBut04Field A q Y` â€” the smooth `(0,1)` field
  `p â†¦ oneFormAtSlot0S (A p)(fun i => Y i p) q` freezing all but slot `q` of a
  smooth `(0,4)` field `A` against a tuple `Y : Fin 4 â†’ section` (slot `q`'s frozen
  value is overwritten, hence irrelevant) â€” uniform in `q` via `Function.update`.
  Smoothness by the `contMDiff_multilinearSection_iff_coord` +
  `contMDiffAt_section_apply_gen` route of `freezeMiddle04Field`.
* `freezeAllBut04Field_apply` / `freezeAllBut04Field_apply_vec` â€” its fibre value
  is `oneFormAtSlot0S (A x)(Y Â· x) q`, i.e.
  `(fun _ : Fin 1 => W) â†¦ A x (update (Y Â· x) q W)` â€” exactly the one-form
  `curvatureAction0SAt_eq_rm04_raise` pairs with `gâ™¯`.
* `allBut04FreezeNabla` (private) â€” the **frozen-slot covariant Leibniz**:
  `totalNabla0SFun 1 cov (freezeAllBut04Field A q Y) x (vec2 (X x) U)
     = totalNabla0SFun 4 cov A x (Fin.cons (X x)(update (Y Â· x) q U))`,
  when the frozen sections `Y i` (`i â‰  q`) are covariantly constant at `x` along
  `X`.  This is `middleFreezeNabla` at `(0,4) â†’ (0,1)`: `nabla0SFun_eval_smooth_slots`
  on both sides, the live `B`-correction matched to the `a = q` `A`-correction, the
  three frozen `A`-corrections killed by `exists_cov_zero_at_apply` +
  `metricTrace_tensor0S_update_zero`.

Solution-facing (namespace `PDE.RicciFlow`):

* `rmFrozenSlotField S t q Y` (+ `_apply`/`_apply_vec`) â€” the frozen one-form field
  of the solution's lowered Riemann tensor `S.base.rm04 t` at slot `q`.
* `nablaRmFrozenSlotField S t q Y` â€” its canonical bundled `(0,1)` covariant
  derivative (rank 2), built through `totalNabla0S` exactly like
  `nablaRm04Field`; `nablaRmFrozenSlotField_realizes` is its `TotalNabla0SRealizes`.
* `nablaRmFrozenSlot_eval` â€” the **solution-facing covariant-derivative identity**
  the K-Leibniz (piece 3) consumes: at any `xâ‚€`, for a regular time, with the
  frozen `Y i` (`i â‰  q`) cov-constant at `xâ‚€` along `X`,
  `nablaRmFrozenSlotField S t q Y xâ‚€ (vec2 (X xâ‚€) U)
     = nablaRm04Field S t xâ‚€ (Fin.cons (X xâ‚€)(update (Y Â· xâ‚€) q U))`,
  i.e. `âˆ‡(oneFormAtSlot0S Rm04 Â· q) = (frozen-slot contraction of) âˆ‡Rm04`.  The RHS
  is the realized `âˆ‡Rm04` (`nablaRm04Field`) with the live slot `q` carrying `U` and
  the derivative slot leading â€” exactly the `âˆ‡Rm04`-with-frozen-slots form that
  chains with `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
  (`Tensor0SRiemannian/Smooth.lean`, now public) and `nabla0SFun_product_eval`
  (`Tensor/RSTensor/ContractionLeibniz.lean`).

### Net (what remains of route 2 after piece (1))

* **Piece (1) (frozen one-form field + its `(0,1)` `TotalNabla0SRealizes`) â€” DONE.**
  No wall: both stop conditions of the piece-(1) task were avoided
  (`middleFreezeNabla`/`exists_cov_zero_at_apply` generalise verbatim to the
  `(0,4) â†’ (0,1)` slot positions, and the field's realization needs **no** missing
  smoothness/realization fact â€” only the canonical `totalNabla0S` producer).
* **Piece (2) (the `metricSharp â†” cotangentSharp_gen` component-smoothness bridge
  for the sharp field `p â†¦ gâ™¯ Î²q`) â€” next, separate.**  Discharges the `MDiffAt`
  hypothesis of `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`; the
  seventh follow-up's "highest-risk piece", orthogonal to piece (1).
* **Piece (3) (the assembled K-Leibniz: `âˆ‡K = âˆ‡Rm04 âˆ— gâ™¯Rm04 + Rm04 âˆ— gâ™¯âˆ‡Rm04`)
  and the final orthonormal Cauchyâ€“Schwarz** â€” combine `nablaRmFrozenSlot_eval` (1)
  + the sharp-parallelism + piece (2) + `nabla0SFun_product_eval`, then the
  `NablaRiemannT2Bound.lean` `abs_le_sqrt_compNormSq*` estimate.

Files added: `Evolution/RmFrozenSlotField.lean` (no existing file edited).
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 ninth follow-up: the `metricSharp ↔ cotangentSharp_gen` component-smoothness bridge is BUILT (route-2 piece (3)'s `MDiffAt` hypothesis is dischargeable)

This pass took the dedicated **highest-risk piece** of the (now-unblocked) route-2
`T₁` assembly named in the seventh/eighth follow-ups: the **component-smoothness
bridge** relating the bundled smooth sharp field `metricSharp_contMDiff_total`
(`Geometry/Operator/MetricSharpSmooth.lean`) to the component sharp
`cotangentSharp_gen`/`cotangentSharp_eq_sum_inv_gen` consumed by B's
`curvatureAction0SAt_orthoBasis_eq_sum` (`Evolution/NablaRiemannT2Bound.lean`,
`Tensor/RSTensor/CotangentRiemannian.lean`), so the sharp applied to a smooth
one-form is `MDiffAt`, discharging the `hSharp` hypothesis of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
(`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`).  It is now **closed,
sorry-free, axiom-clean**, in a new file `Geometry/Operator/CotangentSharpSmooth.lean`
(no existing file edited).  `#print axioms` on every public theorem is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0.

### Route decision: a SHORT real lemma, not `rfl` and not a wall

Neither STOP condition was hit.  The two maps are **not** the same map (so not
`rfl`) but are connected by a one-line Riesz-uniqueness lemma, and the bundled
smoothness **does** yield the needed `MDiffAt` (so no wall):

* The two interfaces have **different domains**: `metricSharp g x` (the one in
  `Gradient.lean`, namespace `…DivergenceTheorem`, used by
  `metricSharp_contMDiff_total`) takes `TangentSpace I x →ₗ[ℝ] ℝ`, while
  `cotangentSharp_gen g x` takes a realized `Tensor0SSpace 1 I x`.  They are **both**
  the Riesz raising of `g`: `inner_metricSharp` gives `g(metricSharp g x α, w) = α w`
  and `cotangentSharp_inner_gen` gives `g(cotangentSharp_gen g x β, w) =
  cotangentToDual_gen β w`.  With `α = cotangentToDual_gen β` these coincide, so by
  `metricFlatLinear_injective` (uniqueness of the representative) they are **equal**:
  `cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β)`
  (`cotangentSharp_gen_eq_metricSharp`).
* `Module.Dual ℝ V` is an `abbrev` for `V →ₗ[ℝ] ℝ` (reducible), so the field
  `cv b := cotangentToDual_gen (β b)` has **exactly** the type
  `Π b, TangentSpace I b →ₗ[ℝ] ℝ` that `metricSharp_contMDiff_total` consumes — no
  coercion plumbing needed.
* `metricSharp_contMDiff_total`'s chart-basis smoothness hypothesis
  `b ↦ cv b (chartBasisVecFiber α j b)` is, for `cv = cotangentToDual_gen ∘ β`,
  definitionally `b ↦ β b (fun _ => chartBasisVecFiber α j b)`
  (`cotangentToDual_apply_gen`) — the smooth chart-basis evaluation of the realized
  one-form field.  So the bundled-`ContMDiff` form **does** yield the `MDiffAt (T% …)`
  the sharp-parallelism needs, via `.contMDiffAt.mdifferentiableAt`.

### What was proved (`Geometry/Operator/CotangentSharpSmooth.lean`, all sorry-free, axiom-clean)

* `cotangentSharp_gen_eq_metricSharp` — the pointwise map identity
  `cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β)` (Riesz
  uniqueness via `metricFlatLinear_injective`, `inner_metricSharp`,
  `cotangentSharp_inner_gen`).
* `cotangentToDual_gen_chartBasis_eval` — the component bridge
  `cotangentToDual_gen (β b) (chartBasisVecFiber α j b)
     = β b (fun _ => chartBasisVecFiber α j b)`.
* `cotangentSharp_gen_contMDiff_total` — on a boundaryless model, the bundled raised
  field `b ↦ TotalSpace.mk' E b (cotangentSharp_gen g b (β b))` is `C^∞`, given
  chart-basis smoothness of `b ↦ β b (fun _ => chartBasisVecFiber α j b)`
  (`metricSharp_contMDiff_total` for `cv = cotangentToDual_gen ∘ β`, transported
  through the map identity).
* `cotangentSharp_gen_mdiffAt` — the **`MDiffAt (T% …)` corollary**, the exact
  predicate `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` needs for `hSharp`.

An end-to-end integration check (throwaway probe, EXIT 0, not committed) confirmed
that `cotangentSharp_gen_mdiffAt g hβ x` discharges the `hSharp` argument of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` verbatim — no renamed/axiomatized
smoothness, the bridge genuinely closes the gap.

### Net (route-2 `T₁` frontier after this pass)

* **Piece (1) (frozen-slot one-form field + `(0,1)` `∇`) — DONE** (eighth follow-up,
  `RmFrozenSlotField.lean`).
* **Sharp-parallelism (route-2(a)) — public** (seventh follow-up).
* **Component-smoothness bridge (this pass, the highest-risk piece) — DONE**
  (`CotangentSharpSmooth.lean`): the sharp of a smooth one-form is `MDiffAt`, and its
  orthonormal-basis component form is exactly B's `cotangentSharp_gen`/
  `cotangentSharp_eq_sum_inv_gen` (the same map, related by the proved map identity).
* **Still remaining (route-2 piece (3)): the assembled `K`-Leibniz**
  `∇K = ∇Rm04 ∗ g♯Rm04 + Rm04 ∗ g♯∇Rm04` combining
  `nablaRmFrozenSlot_eval` (1) + the sharp-parallelism + the frozen-slot Leibniz (2)
  + `nabla0SFun_product_eval`, then the `NablaRiemannT2Bound.lean`
  `abs_le_sqrt_compNormSq*` Cauchy–Schwarz.  Not blocked by a missing tensor API —
  the remaining cost is the size of this concrete assembly.

One downstream note for piece (3): the bridge inherits `[InnerProductSpace ℝ E]`
from `metricSharp_contMDiff_total`; `Evolution/NablaRiemannT2Bound.lean` already
carries it, but `Evolution/NablaRiemannT1Bound.lean` currently does not, so the final
`T₁` assembly file will need to add `[InnerProductSpace ℝ E]` (harmless; the model
fibre carries an inner product everywhere the orthonormal frame is used).

Files added: `Geometry/Operator/CotangentSharpSmooth.lean` (no existing file edited).
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-07 tenth follow-up: route-2 piece (3) is ASSEMBLED — `nablaLapCommReactionTerm` is FULLY bounded `|reaction| ≤ C(card)·|Rm|·|∇Rm|`

This pass took the dedicated **piece (3)** assembly (the K-Leibniz, the `T₁`
quantitative bound, the full `T₁+T₂` reaction bound, and the spatial-commutator
connection).  It is now **closed, sorry-free, axiom-clean**, in a new file
`Evolution/NablaRiemannReactionBound.lean` (no existing file edited).  `#print axioms`
on every public theorem is `[propext, Classical.choice, Quot.sound]`.  Focused
`lake-locked build`: EXIT 0 (3691 jobs).  **`nablaLapCommReactionTerm` is now fully
bounded.**

### One environmental wall found and dissolved (not anticipated by follow-ups 5–9)

The banked pieces were each built in ISOLATION (in files without
`[InnerProductSpace ℝ E]`).  Combining them in one file with `[InnerProductSpace ℝ E]`
(required by `cotangentSharp_gen_mdiffAt`) exposed a `Tensor0SModel` model-fibre
instance diamond: accessing `(Tensor0SField).contMDiff` fails `NormedSpace ℝ
(Tensor0SModel s ℝ E)` synthesis in the downstream file (the bundle's `CMDiff`
notation wants the Defs.lean `instNormedAddCommGroupTensor0SModel`, while the global
`tensor0SModel_normedSpace` provides a non-syntactically-matched one).  **Fix:**
`set_option backward.isDefEq.respectTransparency false` (the same option
`freezeAllBut04Field` uses), which unifies the instances.  This is recorded in
`rmFrozenSlot_chartBasis_contMDiffOn`.

### What was proved (`Evolution/NablaRiemannReactionBound.lean`, all sorry-free, axiom-clean)

* `solution_isMetricCompatible` — `IsMetricCompatible_gen (S.family.connection t)
  (S.base.metric t)` (Levi-Civita), the metric-compat discharge for the sharp
  parallelism and Step A.
* `rmFrozenSlot_chartBasis_contMDiffOn` / `rmFrozenSlotSharp_mdiffAt` /
  `rmFrozenSlotSharpSection` — **piece (2) closed in the solution context**: the
  chart-basis smoothness of the frozen one-form, hence the `MDiffAt` of the raised
  sharp field `y ↦ g♯βq`, discharging `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`'s
  `hSharp` (via `cotangentSharp_gen_mdiffAt`, follow-up 9), and the bundled sharp
  section.
* `rmRaise_summand_covDeriv` — the **per-`q` contraction Leibniz**: the covariant
  derivative of one raise-form summand `Rm04(…, g♯βq)` splits into `(∇Rm04)(…,g♯βq) +
  Rm04(…, g♯(∇βq))`, via `nabla0SFun_eval_smooth_slots` on cov-constant slots + the
  sharp-parallelism + `nablaRmFrozenSlot_eval`.
* `nabla3_antisym_eq_covDeriv_curvatureAction_covConst` — the **generic-frame `T₁`
  reduction on cov-constant sections** (route 3): `∇³Rm(X,b,c) − ∇³Rm(X,c,b) =
  extDerivFun(K)` for the curvature-action field `K`, via `eval_smooth_slots` (cov-const
  ⟹ no Christoffel corrections) + the pointwise `(0,4)` Ricci identity.  This
  reconciles the smooth-frame differentiation with the pointwise orthonormal frame.
* `nablaLapComm_T1_eq_rm04_raise_leibniz` — **the assembled K-Leibniz**:
  `T₁ = -Σ_q [(∇Rm04)(X,b,c,m_q,g♯βq) + Rm04(b,c,m_q,g♯(∇_X βq))]`, the covariant
  Leibniz `∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm` for the curvature action through the
  metric-raising form (**no `∇rm13`** — route 2 sidesteps the `(1,3)` raising
  parallelism entirely).
* `abs_tensor05_sharp_last_le` / `abs_tensor04_sharp_last_le` /
  `sum_sq_update_le_compNormSqMulti` — the orthonormal-basis Cauchy–Schwarz on a
  last-slot raise contraction (mirror of B's `abs_curvatureAction0SAt_orthoBasis_le`).
* `abs_nablaLapComm_T1_covConst_le` / `abs_nablaLapComm_T1_orthoBasis_le` — the **`T₁`
  quantitative bound** `|T₁| ≤ 8·card·√|∇Rm|·√|Rm|` on cov-const sections, then in the
  genuine `g`-orthonormal frame (frame vectors realised by cov-const sections via
  `exists_cov_zero_at_apply`).
* `abs_nablaLapCommReactionTerm_diag_orthoBasis_le` — **the full reaction bound**:
  `|Σ_a reactionF a a c m| ≤ 13·card²·√(rm04 compNormSq4)·√(∇Rm compNormSqMulti)`
  = `C(card)·|Rm|·|∇Rm|`, combining the `T₁` bound with B's
  `abs_nablaLapComm_T2_orthoBasis_le`.
* `abs_spatialCommNablaRm_orthoFrame_le` — **the spatial-commutator bound in the
  producer's convention**: at `x₀`, in a genuine `g`-orthonormal frame with
  `InverseMetricOrthonormalAt` (`gᵃᵇ = δ`) holding honestly,
  `|Δ(∇Rm)(c) − ∇(ΔRm)(c)| ≤ 13·card²·√(rm04NormSqInFrame)·√(nablaRm04NormSqInFrame)`,
  assembling `nablaLapCommF_orthonormalTrace` (the diagonal trace) with the full
  reaction bound, in the producer's `rm04NormSqInFrame`/`nablaRm04NormSqInFrame` norms.

### Net (the `k = 1` frontier after this pass)

* **`T₁` quantitative bound — DONE.**  Route 2 (the `g♯` raise form) assembled
  end-to-end; the `(1,3)` raising-parallelism wall (bound obstruction #1) is
  **sidestepped**, not solved — it is never needed.
* **`nablaLapCommReactionTerm` — FULLY bounded** `|reaction| ≤ C(card)·|Rm|·|∇Rm|`,
  and the **spatial commutator** `[Δ,∇_c]Rm` is bounded in the producer's orthonormal
  component-norm convention (`abs_spatialCommNablaRm_orthoFrame_le`).

### Remaining for the full `k = 1` producer (a SEPARATE frontier — the time-derivative side)

The full `NablaRm04NormHeatEquationOn` / `nablaRm04NormHeatBoundOn_of_components`
(`Evolution/NablaRiemannHeat.lean`) is a `HasDerivWithinAt` (time-derivative)
statement.  Its **spatial** reaction input is now discharged
(`abs_spatialCommNablaRm_orthoFrame_le`).  What remains is the **time-derivative
assembly**: `iteratedRmComp_one_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`)
still takes `hrm`/`hchr`/`hswap` (the level-0 time derivative, the Christoffel time
derivative `∂ₜΓ = ∇Ric`, and the time/spatial derivative swap) as **input shapes**;
their concrete instantiation from the solution, plus the `MultiNormHeat` Bochner
norm-square assembly, is the separate analytic frontier.  This is orthogonal to the
reaction bound and was **not** in scope here.  `BernsteinShiSolution.lean` remains
parametric in `IteratedRmTowerOn`.

Files added: `Evolution/NablaRiemannReactionBound.lean` (no existing file edited).

## 2026-06-07 eleventh follow-up: the time-derivative side mapped — `hchr` is solution-dischargeable, `hrm` is an UNBUILT-but-UNBLOCKED assembly (banked `∂ₜRm13` found), and `hswap` + the frame reconciliation are the two genuine walls

This pass took the dedicated **time-derivative assembly** task: discharge
`NablaRm04NormHeatEquationOn` for a real `SolutionOn` by instantiating
`iteratedRmComp_one_hasDerivWithinAt`'s `hrm`/`hchr`/`hswap`
(`Evolution/NablaRiemannTimeDeriv.lean:249`) from the solution and feeding the
Bochner producer.  After an end-to-end trace of every input against the tree, the
finding **corrects two earlier verdicts** and isolates the genuine walls precisely.
No Lean code was changed (a faithful assembly needs new `sorry`s at the walls,
forbidden); the deliverable is the precise frontier.

### Correction 1 — `hchr` (`∂ₜΓ`) IS dischargeable from the solution (not a black box)

`hchr` needs `∂ₜ(realizedChr) = ∂ₜΓ` in the **time-independent `coordinateFrameAt`**.
This is exactly `ChristoffelEvolutionEquationInFrameOn`, and it is **proved from
`S, hS` alone**:
* `coordMetricDeriv` (`Ricci/CoordinateRegularity.lean:870`) discharges the metric
  fixed-base swap `FixedBaseExtDerivTimeDerivativeOnRegular(metric, −2·Ric)` from
  `IsSolutionOn` via `fixedBaseOnReg_of_timeDerivWithin`, whose `hTime` is the
  genuine `∂ₜg = −2 Ric` (`metricCompInFrame_hasDerivWithinAt`, the realized
  `MetricVariationEquationOn`);
* `coordMetricMix` + `coordGammaEvol` (`…/CoordinateRegularity.lean:906, 937`) then
  give `ChristoffelEvolutionEquationInFrameOn` (= `∂ₜΓ`), all from `S, hS`;
* `coordGammaMix` (`…/CoordinateRegularity.lean:1255`) gives the **mixed** Γ swap
  `ChristoffelVariationMixedDerivativeInFrameOnRegular` (= `∂ₜ∂ₓΓ`) from `S, hS`
  (again `fixedBaseOnRegLocal`, `hTime` = the just-built `∂ₜΓ`).

So the prior follow-ups' framing of `∂ₜΓ`/Lemma 6.2 as a `BlackBox.lean` frontier is
**inaccurate for the coordinate frame**: it is a *closed* producer chain.  The
realized Ricci evolution (Lemma 6.3) is likewise closed: `coordRicciEvol`
(`Ricci/CoordinateIdentities.lean:876`) gives `∂ₜ(ricciCompInFrame)` in
`coordinateFrameAt` from `S, hS` (sorry-free; no `sorry`/`admit` in
`CoordinateRegularity.lean`/`CoordinateIdentities.lean`).

### Correction 2 — `hrm` (`∂ₜRm`) is NOT an Uhlenbeck-shape wall; the `∂ₜRm13` coordinate producer is already BANKED

`hrm` needs `∂ₜ(realizedRmBase) = ∂ₜ(S.base.rm04)` frame components in
`coordinateFrameAt`.  The recipe's Uhlenbeck route does **not** supply this:
`UhlenbeckCurvatureEvolutionInFrameOn` is about the *pulled-back* components, and
`uhlenbeckCurvatureEvolution{InFrameOn_of_ricciFlow,_of_solution_components}`
(`Uhlenbeck.lean:987,1122`) themselves take the standard-slot Riemann evolution
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn` as an **input hypothesis** —
which is *only ever consumed*, never discharged.  So the Uhlenbeck `hrm` route is a
genuine shape mismatch (stop condition 2 *for that route*).

**But there is a second, banked route**, mirroring `coordRicciEvol`: the `(1,3)`
Riemann coordinate coefficient `christoffelCurvCoeffAt` (= `∂Γ − ∂Γ + ΓΓ − ΓΓ`,
`Geometry/Curvature/Components/Christoffel.lean:67`) has its time derivative
**already proved**:
`christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`
(`Ricci/GammaCoord.lean:141`) gives `∂ₜ(Rm13^m_{ikj})` in `coordinateFrameAt` from
`hvar` (`∂ₜΓ`) + `hmix` (`∂ₜ∂ₓΓ`) — both discharged from `S, hS` above.  (Indeed
`coordRicciEvol`'s `∂ₜRic` is *built by summing this exact Riemann-coefficient
derivative*, `GammaCoord.lean:318`.)  Combined with the pointwise realization
`rm13_eval_eq_christoffelCurvCoord` (`Geometry/Curvature/Components/RicciIdentity.lean`)
and lowering `rm04 = g·Rm13` with the metric time derivative
(`metricCompInFrame_hasDerivWithinAt`), `∂ₜ(rm04)` in `coordinateFrameAt` is
**assemblable with no missing primitive** — it is the unbuilt `(0,4)` analogue of the
closed `coordRicciEvol`.  This refutes the tenth follow-up's "the time-derivative side
is a separate analytic frontier [whose `hrm`] is deferred": `hrm` is unblocked, only
unbuilt (a bounded ~Lemma-6.1 assembly).

### The two GENUINE walls (the assembly is not closable as-is)

1. **`hswap` for `rm04` needs an UNBANKED second-order mixed space-time Christoffel
   derivative `∂ₜ∂²ₓΓ`.**  `hswap`
   (`NablaRiemannTimeDeriv.lean:267`) needs
   `∂ₜ(extDerivFun(rm04 component))`, i.e. a
   `FixedBaseExtDerivTimeDerivativeOnRegular` for `rm04`.  Since
   `rm04 ~ ∂ₓΓ + Γ·Γ`, the spatial derivative `∂ₓ(rm04) ~ ∂²ₓΓ + ∂ₓΓ·Γ`, so
   `∂ₜ∂ₓ(rm04) ⊇ ∂ₜ∂²ₓΓ`.  The banked Γ swaps stop at **first** order in `∂ₓ`
   (`coordGammaMix` = `∂ₜ∂ₓΓ`); there is **no** `∂ₜ∂²ₓΓ` /
   `christoffelCoordSecondDeriv` mixed producer in the tree (searched).  *Exact
   theorem needed next*: a second-order mixed space-time Christoffel derivative
   `FixedBaseExtDerivTimeDerivativeOnRegular` for `christoffelCoordDerivAt`
   (i.e. `∂ₜ(∂ₓ ∂ₓΓ)`), the one-order-higher analogue of `coordGammaMix`, in
   `Ricci/CoordinateRegularity.lean`.  This is a bounded but real new producer, not
   currently present.

2. **Frame reconciliation — the KEY SUBTLETY, unresolved.**  The time derivative
   `iteratedRmComp_one_hasDerivWithinAt` is hardwired to the **time-independent
   `coordinateFrameAt`** (so `∂ₜ` does not pick up a moving-frame term), where the
   inverse metric `gInv` is the *actual* `coordInv`, **not** `δ`.  But:
   * the producer `nablaRm04NormHeatBoundOn_of_components`
     (`NablaRiemannHeat.lean:634`) requires `horth : InverseMetricOrthonormalAt gInv`
     (`gInv = δ`) — its reaction bound `abs_nablaRmReactionInFrame_le` is hardwired to
     `compNormSq*` (plain component sums) and genuinely needs `gInv = δ`;
   * the spatial commutator bound `abs_spatialCommNablaRm_orthoFrame_le`
     (`NablaRiemannReactionBound.lean:1326`) is proved **only** in the *time-dependent*
     `g(t)`-orthonormal frame of `exists_orthoBasisFrameAt` (whose frame vectors
     depend on `t`).
   These two frames are incompatible:
   * **Route (a)** (everything in `coordinateFrameAt` with the real `gInv`): the
     spatial commutator identity `nablaLapCommF_trace` *is* frame-generic and holds
     for general `gInv`, but (i) the producer's `horth` is then *unsatisfiable*
     (`coordinateFrameAt` is the chart frame, never `g`-orthonormal at its centre —
     `Geometry/Coordinates/CoordinateFrame.lean`), and (ii) the *quantitative* bound
     `abs_spatialCommNablaRm_orthoFrame_le` exists **only** in the orthonormal frame,
     not for a general `gInv` (the sixth/tenth follow-ups built it via the
     orthonormal-basis Cauchy–Schwarz; a general-`gInv` reaction bound is the absent
     fibre-norm↔component-norm machinery, the previously-rejected route (b) of the
     fourth follow-up).  So route (a) needs **both** a `horth`-free producer variant
     **and** a general-`gInv` reaction bound — neither exists.
   * **Route (b)** (everything in the `g(t)`-orthonormal frame): then the time
     derivative `iteratedRmComp_one_hasDerivWithinAt` picks up an **unbanked
     moving-frame `∂ₜ(frame)` correction term** (the theorem is stated for a
     time-independent frame; `exists_orthoBasisFrameAt`'s frame is `t`-dependent
     through the fibre metric).  No moving-frame covariant-derivative time-derivative
     correction exists in the tree.

   *Exact theorem(s) needed next*: **either** (a) a `horth`-free / general-`gInv`
   restatement of `nablaRm04NormHeatBoundOn_of_components` **plus** a general-`gInv`
   reaction bound (the fibre-norm bridge), **or** (b) a moving-frame correction to
   `iteratedRmComp_one_hasDerivWithinAt` carrying the `∂ₜ(frame)` term for a
   `t`-dependent orthonormal frame.  Both are framework-scale; neither is a one-lemma
   gap.

### Net (the `k = 1` producer frontier after this pass)

* **`hchr` (`∂ₜΓ`, `∂ₜ∂ₓΓ`) — solution-dischargeable, closed** (`coordGammaEvol` /
  `coordGammaMix`, from `S, hS`).  Earlier "black-box" framing corrected.
* **`hrm` (`∂ₜrm04`) — UNBLOCKED, unbuilt.**  Banked `∂ₜRm13`
  (`christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`) + realization +
  metric lowering give it with no missing primitive; it is the `(0,4)` analogue of the
  closed `coordRicciEvol`.  Earlier "Uhlenbeck shape mismatch" is correct only for the
  Uhlenbeck route, which is not the only route.
* **`hswap` (`∂ₜ∂ₓrm04`) — WALL 1**: needs an unbanked second-order mixed space-time
  Christoffel derivative `∂ₜ∂²ₓΓ` (one order above `coordGammaMix`).
* **Frame reconciliation — WALL 2 (the key subtlety)**: the clean-`∂ₜ`
  `coordinateFrameAt` (general `gInv`) and the quantitative orthonormal spatial bound
  (`g(t)`-frame, `gInv = δ`) are incompatible; closing it needs either a
  `horth`-free/general-`gInv` producer+reaction-bound or a moving-frame `∂ₜ(frame)`
  correction.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.  No files
changed this pass (a faithful assembly would require `sorry` at walls 1–2).

## 2026-06-07 twelfth follow-up: the `horth`-free / frame-independent `k = 1` producer is BUILT; WALL 1 (`hswap`) is over-counted (template-confirmed); WALL 2 (frame reconciliation) is the sole genuine remaining frontier

This pass took the dedicated task of closing the full `k = 1` producer
`NablaRm04NormHeatBoundOn` for a real `SolutionOn`, building a `horth`-free /
general-`gInv` variant if the producer's `horth` blocks the time-independent-frame
route.  The **frame-independent producer chain is now built, sorry-free,
axiom-clean**, in a new file `Evolution/NablaRiemannHeatSolution.lean` (no existing
file edited).  `#print axioms` on every public theorem is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0
(3629 jobs).

### What was proved (`Evolution/NablaRiemannHeatSolution.lean`, all sorry-free, axiom-clean)

The `horth`-free *scalar* producer (frame-independent, no `gInv`/`compNormSq`):

* `nablaRm04NormHeatBoundSharp_scalar` / `nablaRm04NormHeatBoundOn_scalar` — from a
  bare scalar heat **equation** `NablaRm04NormHeatEquationOn u uLap nabla2 reaction`,
  a frame-independent reaction bound `reaction ≤ cReact·√v·u`, and `nabla2 ≥ 0`,
  the sharp and dropped scalar heat inequalities, the latter being **exactly**
  `NablaRm04NormHeatBoundOn u uLap v cReact` (the predicate
  `bernstein_first_derivative_estimate` consumes).  This is the `horth`-free analogue
  of `nablaRm04NormHeatBoundOn_of_components`: it mentions no frame, no inverse
  metric, no `compNormSq`.  The orthonormal frame was only ever a *convenience* for
  `compNormSq` and the Cauchy–Schwarz reaction bound; the scalar inequality is
  intrinsic.

The Bochner-splice bridge into the producer's predicate:

* `nablaRm04NormHeatEquationOn_of_multiBochner` — the rank-`r=4` Bochner splice
  `multiNormHeatEquationOn_of_components` (`MultiNormHeat.lean`) produces
  `NablaRm04NormHeatEquationOn` with `reaction = multiReactionDown` (`= 2⟨(∂ₜ−Δ)∇Rm,
  ∇Rm⟩`).  The two `HasDerivWithinAt` shapes are identical; this certifies the
  existing `MultiNormHeat` machinery *is* the `k = 1` heat-equation producer (the
  geometric input being the Bochner Laplacian split `MultiNormLaplacianSplit`, same
  status as the `k = 0` producer's `Rm04NormLaplacianComponentsOn`).
* `nablaRm04NormHeatBoundOn_of_multiBochner_residual` — the assembled
  frame-independent producer from the Bochner-splice data + the schematic residual
  identity `(∂ₜ−Δ)∇Rm = star` (`hres`) + a frame-independent `∗`-bound on
  `2⟨star, ∇Rm⟩` (Cauchy–Schwarz), via `multiReactionDown_eq_of_residual`.

### WALL 1 (`hswap` needs `∂ₜ∂²ₓΓ`) is OVER-COUNTED — refuted by the `coordGammaMix` template

The eleventh follow-up's WALL 1 ("`hswap` for `rm04` needs an unbanked
`∂ₜ∂²ₓΓ`") is **incorrect**.  `hswap` (`NablaRiemannTimeDeriv.lean:267`) is a
`FixedBaseExtDerivTimeDerivativeOnRegular` for the *scalar* `rm04`-frame component,
and `fixedBaseOnRegLocal` / `fixedBaseOnReg_of_timeDerivWithin`
(`Bundle/PartialMfderiv/FixedBase.lean`) build it from just:
`hSmooth` (spacetime `C²` of the scalar component `F`), `hFdiff`/`hFtdiff` (spatial
differentiability of `F`, `Ft`), and `hTime` (the *first-order* `∂ₜF = Ft` fact).
The exterior spatial derivative is swapped *automatically*; **no second-order
spatial Christoffel derivative is required.**  This is exactly how `coordGammaMix`
(`Ricci/CoordinateRegularity.lean:1255`) builds `∂ₜ∂ₓΓ` — its `hSmooth` is plain
Christoffel smoothness (`coordGammaSmoothAt`), its `hTime` is just `∂ₜΓ` (`hGamma`),
**not** any `∂ₜ∂ₓ`-derivative identity.  So `hswap` for `rm04` reduces to `hrm`
(`∂ₜrm04`) + spacetime-`C²` smoothness of the `rm04` frame component (the `(0,4)`
analogue of `coordGammaSmoothAt`), with `Rm04` kept as the *smooth* field (never
unfolded to `∂ₓΓ + Γ²`, which would manufacture the spurious `∂ₜ∂²ₓΓ` need).

### The genuine remaining frontier for the from-bare-`S` producer

The `horth`-free producers reduce `NablaRm04NormHeatBoundOn` to two *frame-independent
scalar* inputs (same status as the `k = 0` producer's hypotheses):
(1) the heat equation `NablaRm04NormHeatEquationOn` (= Bochner-splice data +
residual), and (2) the reaction bound `2⟨(∂ₜ−Δ)∇Rm, ∇Rm⟩ ≤ C·|Rm|·|∇Rm|²`.
Assembling those two scalars *from a bare `SolutionOn` in one frame* still needs:

* **`hrm` (`∂ₜrm04`) — UNBLOCKED, unbuilt** (the `(0,4)` analogue of the banked
  `coordRicciEvol`: banked `∂ₜRm13`
  `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation` + realization +
  metric lowering), plus the `rm04` spacetime-`C²` smoothness for `hswap`
  (analogue of `coordGammaSmoothAt`).  A bounded ~Lemma-6.1 assembly, no missing
  primitive.
* **WALL 2 (frame reconciliation) — the SOLE genuine framework-scale wall,
  grep-confirmed absent.**  The clean-`∂ₜ` time derivative
  (`iteratedRmComp_one_hasDerivWithinAt`) is in the **time-independent**
  `coordinateFrameAt` (actual `gInv`); the quantitative spatial reaction bound
  `abs_spatialCommNablaRm_orthoFrame_le` is **only** in the **`g(t)`-orthonormal**
  frame (`gInv = δ`).  The scalar reaction `2⟨(∂ₜ−Δ)∇Rm, ∇Rm⟩` is intrinsic and
  equal in both frames, but **no** lemma identifies the contracted reaction scalar
  across frames (searched: no `coordinateFrameAt`-with-actual-`gInv` reaction
  bound; no scalar reaction frame-invariance; the only `nablaRmReactionInFrame` /
  `abs_nablaRmReactionInFrame_le` are `horth`-bound), and **no** moving-frame
  `∂ₜ(frame)` correction to `iteratedRmComp_one_hasDerivWithinAt` exists
  (searched: no `frameDt`/moving-frame `∂ₜ` covariant-derivative correction).
  Either closes the gap; both are framework-scale.  *Note:* the new `horth`-free
  producer removes the *producer-side* half of route (a) (a `horth`-free producer
  now exists), but route (a) still needs the **general-`gInv` reaction bound**
  (the absent fibre-norm↔component-norm machinery / scalar frame-invariance), which
  is unchanged.

### Net

* **`horth`-free / frame-independent `k = 1` producer — DONE.**  The producer's
  `InverseMetricOrthonormalAt` is no longer required: `NablaRm04NormHeatBoundOn`
  follows from the intrinsic scalar heat equation + a frame-independent reaction
  bound (`nablaRm04NormHeatBoundOn_scalar` /
  `nablaRm04NormHeatBoundOn_of_multiBochner_residual`).
* **WALL 1 (`hswap`) — over-counted, dissolved** (template-confirmed via
  `coordGammaMix`/`fixedBaseOnRegLocal`: `hswap` = `hrm` + spacetime-`C²`, no
  `∂ₜ∂²ₓΓ`).
* **`hrm` (`∂ₜrm04`) + `rm04` smoothness — unblocked, unbuilt** (bounded
  `coordRicciEvol`-analogue assembly).
* **WALL 2 (frame reconciliation) — the sole genuine framework-scale wall**,
  grep-confirmed absent (general-`gInv` reaction bound / scalar frame-invariance, or
  moving-frame `∂ₜ(frame)` correction).

Files added: `Evolution/NablaRiemannHeatSolution.lean` (no existing file edited).
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn` (it consumes
`IteratedRmTowerOn`, not the `k = 1` producer; the `k = 1` producer feeds the
*parametric* `bernstein_first_derivative_estimate`, which has no solution-level
caller to wire up).

## 2026-06-07 thirteenth follow-up: the norm frame-invariance half of WALL 2 (Route (b)) is BUILT — the proven spatial commutator bound is now stated against frame-independent INTRINSIC fibre norms

This pass took the dedicated WALL-2 task (close the full `k = 1` producer
`NablaRm04NormHeatBoundOn` for a real `SolutionOn`, picking the cleaner of Route (a)
/ Route (b)).  After grep-verifying the building blocks, **Route (b)'s norm
frame-invariance is closed, sorry-free, axiom-clean**, in a new file
`Evolution/NablaRiemannHeatFrameInvariant.lean` (no existing file edited).
`#print axioms` on every public theorem is `[propext, Classical.choice, Quot.sound]`.
Focused `lake-locked build`: EXIT 0 (3694 jobs).  This refutes part of the twelfth
follow-up's "scalar reaction frame-invariance — grep-confirmed absent" framing for
the *spatial* half: the norm frame-invariance **is** assemblable from the intrinsic
fibre norm `normSq0S` and its orthonormal-basis component identity.

### The key infrastructure found (correcting "frame-invariance absent")

The twelfth follow-up listed Route (b) as needing a "`multiNormRaised gInv =
(intrinsic)` frame-independently" fact that was "grep-confirmed absent".  In fact the
intrinsic fibre norm and its orthonormal-component identity **already exist**:

* `normSq0S g x s A` (`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean`) — the
  metric-induced squared fibre norm of a `(0,s)` tensor `A`, mentioning **no** frame.
* `normSq0S_identity_eq_sum_sq` (`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean`)
  — in any basis with `MetricInverseInBasis_gen g x basis identityInvMetric`,
  `normSq0S g x s A = ∑_slots (component0S basis A slots)²`.
* `SmoothRiemannianMetric`/`SmoothMetric`/`SmoothMetric_gen` are the **same** abbrev
  (`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`), so `S.base.metric t`
  feeds all three interfaces with no coercion.

A `g`-orthonormal basis (`g.inner basis i basis j = δ`) trivially satisfies
`MetricInverseInBasis_gen … identityInvMetric` (the inline computation of
`cotangentSharp_orthoBasis_expand'`), so the orthonormal-component squared sum
`compNormSqMulti (basis components)` **is** the intrinsic `normSq0S`, the same for
every `g`-orthonormal basis.

### What was proved (`Evolution/NablaRiemannHeatFrameInvariant.lean`, all sorry-free, axiom-clean)

* `metricInverseInBasis_identity_of_orthonormal` — a `g`-orthonormal basis carries
  the Kronecker-delta inverse metric in the `MetricInverseInBasis_gen` sense.
* `compNormSqMulti_orthoBasis_eq_normSq0S` — **the norm frame-invariance bridge**:
  `compNormSqMulti (fun idx => A (basis ∘ idx)) = normSq0S g x s A` for a
  `g`-orthonormal basis (rank-uniform, any `(0,s)` tensor).  The RHS is frame-free,
  so the orthonormal-component norm is frame-independent.  Combined with
  `multiNormInFrame_eq_compNormSqMulti` (`multiNormRaised δ A = compNormSqMulti A`,
  `IteratedNablaRmTower.lean`) this is exactly the Route (b) condition.
* `rm04NormSqInFrame_orthoBasis_eq_normSq0S` /
  `nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S` — the producer's `δ`-raised frame
  norms equal the intrinsic `normSq0S g 4 (Rm04)` (`= |Rm|²`) /
  `normSq0S g 5 (∇Rm)` (`= |∇Rm|²`), via the orthonormal reductions
  `rm04NormSqInFrame_eq_compNormSq4` / `nablaRm04NormSqInFrame_eq_compNormSq5` + the
  bridge + the existing `compNormSqMulti_eq_compNormSq4_basis`/`_compNormSq5`
  reindexings.
* `abs_spatialCommNablaRm_intrinsic_le` — **the frame-independent restatement of the
  proven spatial commutator bound** `abs_spatialCommNablaRm_orthoFrame_le`:
  `|Δ(∇Rm)(c) − ∇(ΔRm)(c)| ≤ 13·card²·√(normSq0S g Rm)·√(normSq0S g ∇Rm)`, with the
  `Rm`/`∇Rm` factors now the **intrinsic** fibre norms — genuinely frame-independent
  scalars.  This is the `Rm ∗ ∇Rm` shape the `horth`-free scalar producer
  (`nablaRm04NormHeatBoundOn_scalar`) consumes as the *spatial* part of its reaction
  bound `reaction ≤ cReact·√v·u` with `v = |Rm|²`, `u = |∇Rm|²` intrinsic.

### Net (the `k = 1` frontier after this pass)

* **Route (b) norm frame-invariance — DONE.**  The orthonormal-component norm is the
  intrinsic fibre norm, and the proven spatial commutator bound is now stated against
  frame-independent intrinsic scalars (`abs_spatialCommNablaRm_intrinsic_le`).  The
  twelfth follow-up's "scalar frame-invariance grep-confirmed absent" is corrected
  for the **norm** (the `normSq0S` machinery supplies it).
* **WALL 2's remaining genuine half — the intrinsic-norm TIME derivative `∂ₜ|∇Rm|²`.**
  The full scalar heat **equation** `NablaRm04NormHeatEquationOn` still needs `∂ₜu`
  for `u = normSq0S (g(t)) (∇Rm)`, and:
  * `iteratedRmComp_one_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`)
    gives the per-component time derivative in the **time-independent
    `coordinateFrameAt`**, not `∂ₜ(normSq0S (g(t)) ·)`;
  * `normSq0S (g(t)) ·` carries the **moving metric `g(t)`**, so `∂ₜ` picks up a
    `∂ₜg`-contraction term.
  Crucially, this is the **same status as the `k = 0` producer**: `k = 0`'s
  `rm04NormHeatEquationOn_of_solution` (`Evolution/RiemannNormHeatProducer.lean`)
  *also* takes its raw time-derivative identity `Rm04NormRawDerivativeEquationOn`
  (`Evolution/RiemannNorm.lean`) as a **hypothesis**, in a fixed frame with moving
  `gInv` (Route (a)), with the `∂ₜgInv` term explicit
  (`raisedRm04DerivRHSInFrame`/`inverseMetricEvolutionRHSInFrame`); the project's
  `k = 0` baseline **never** closes `∂ₜ|Rm|²` from a bare `SolutionOn` either, and
  there is **no** `Rm04NormHeatBoundOn`/`rm04NormHeatBoundOn_of_solution` (grep:
  absent).  So the time-derivative gap is *not* a `k = 1`-specific wall; it is the
  shared `k = 0`-status analytic input, and the `horth`-free scalar producer already
  abstracts it (input (1), `NablaRm04NormHeatEquationOn`).
* **The temporal residual `(∂ₜΓ) ∗ Rm` + Uhlenbeck `Rm ∗ Rm`** — the residual
  `(∂ₜ − Δ)∇Rm` beyond the (now-frame-independent) spatial commutator also has the
  temporal pieces, not yet assembled into the contracted reaction scalar.

### Honest verdict on closing the full producer from bare `S`

The full `NablaRm04NormHeatBoundOn`-from-`SolutionOn` is **not** closed, and (after
this pass) is reduced to exactly the `k = 0`-status inputs:
(1) the intrinsic-norm heat **equation** `NablaRm04NormHeatEquationOn` (the
hypothesis-status time-derivative/Bochner-split input, identical in status to
`k = 0`'s `Rm04NormRawDerivativeEquationOn` + Bochner split), and
(2) the frame-independent reaction bound — whose **spatial half is now discharged
intrinsically** (`abs_spatialCommNablaRm_intrinsic_le`), with the temporal half
(`∂ₜΓ ∗ Rm` + Uhlenbeck) the only remaining `Rm ∗ ∇Rm`/`Rm ∗ Rm` assembly.  The
genuinely framework-scale residue is the moving-metric time derivative of the
intrinsic norm — the same obstruction the `k = 0` baseline leaves open — not a
missing tensor API.  `BernsteinShiSolution.lean` remains parametric in
`IteratedRmTowerOn`.

Files added: `Evolution/NablaRiemannHeatFrameInvariant.lean` (no existing file
edited).

## 2026-06-07 fourteenth follow-up: the intrinsic moving-metric norm TIME derivative `∂ₜ normSq0S(g(t), T(t))` is BUILT GENERICALLY — WALL 2's remaining half (the thirteenth follow-up's item 1) is closed at the reusable tensor level, modulo the same `∂ₜT` component input the `k = 0` baseline takes

This pass attacked the thirteenth follow-up's named remaining half of WALL 2 — the
**intrinsic-norm time derivative** `∂ₜ|∇Rm|²` for the *moving* metric `g(t)` inside
`normSq0S`, which "picks up a `∂ₜg`-contraction term".  The deliverable is the
**general, frame-free, rank-uniform** Bochner-type time-derivative of a covariant
tensor norm, stated and proved once at the reusable fibre-metric level (it has **no**
Ricci-flow content), so it serves `k = 0`, `k = 1`, and every `k` uniformly.  New
file `Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean` (no existing file
edited), all sorry-free, every public theorem `#print axioms = [propext,
Classical.choice, Quot.sound]`, focused `lake-locked build` EXIT 0.

### Why this sidesteps the frame reconciliation entirely

The thirteenth follow-up's spatial half used the orthonormal-frame route.  The
time-derivative half is done **intrinsically**: the key infrastructure
`normSq0S_eq_coord` / `inner0S_eq_coord`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean`) — which were **already fully
proved, not open** — equate the intrinsic fibre norm/inner product with the
`gInv`-raised coordinate contraction `coordInner0S` in *any* tangent basis with
`MetricInverseInBasis`.  Differentiating that finite sum in `t` by the product rule
is pure real algebra; no orthonormal frame and no coordinate↔frame bridge is
needed.

### What was proved (`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`)

* `hasDerivWithinAt_coordContract` — **the product-rule core** (assumption-free, on
  raw real component arrays): for time-dependent inverse-metric components `gInv t`
  and rank-`s` arrays `cA t`, `cB t` with `HasDerivWithinAt` data `gInvDt`, `cAdt`,
  `cBdt`, the contraction `coordContract (gInv t) (cA t) (cB t) = Σ_{I0,J0} (∏_a gInv
  (I0 a)(J0 a))·cA I0·cB J0` is differentiable with derivative `coordContractDt +
  coordContract gInv cAdt cB + coordContract gInv cA cBdt`.  The `∏ gInv` factor is
  differentiated by Mathlib's `HasDerivWithinAt.fun_finset_prod`; the metric term
  `coordContractDt` is the `∂ₜgInv`-contraction (one `gInv` slot differentiated at a
  time).  This is `MultiNormHeat.lean:158`'s fixed-metric product rule
  (`hasDerivWithinAt_compNormSqMulti`, the `∂ₜgInv = 0` case) generalised to a moving
  metric — same product-rule structure, **plus** the metric term.
* `hasDerivWithinAt_normSq0S_coord` / **`hasDerivWithinAt_normSq0S`** — **the GENERAL
  intrinsic lemma**: for arbitrary time-dependent metric `g(t)` (inverse components
  `gInv t`, genuinely inverse via `MetricInverseInBasis`) and tensor
  `T : Real → Tensor0SSpace s I x`, with `∂ₜgInv` and the component derivatives `∂ₜT`
  supplied as `HasDerivWithinAt` hypotheses,
  `∂ₜ (normSq0S (g t) x s (T t)) = (metric term in ∂ₜgInv) + 2·inner0S (g t) (∂ₜT) (T)`.
  The "2·inner" packaging uses the symmetry of the fibre inner product
  (`MetricFiberData.symm`).  **Completely general in `T` and `g`; no curvature,
  metric-compatibility, or flow hypothesis.**  This is the abstraction that closes
  the standing per-case raw time-derivative hypothesis (`k = 0`'s
  `Rm04NormRawDerivativeEquationOn`, the `k = 1`/all-`k` analogues) in one lemma.
* `coordContractDt_eq_ricReactionContract` + **`hasDerivWithinAt_normSq0S_ricciFlow`**
  — **the flow instantiation**: under the Ricci-flow inverse-metric-derivative
  relation `gInvDt i j = 2·Σ_{p,q} gInv i p·gInv j q·ric p q` (the conclusion of
  `inverseMetric_derivative_solve`, from `∂ₜg = −2 Ric`), the metric term becomes the
  explicit **Ricci reaction** `ricReactionContract`, giving
  `∂ₜ|T|² = (Ric ∗ T²) + 2⟨∂ₜT, T⟩` — the architecture's raw curvature-norm time
  derivative, now **derived** from the product rule rather than assumed, for `T =
  ∇ᵏRm` at any rank `s = 4 + k`.

### Net (what is closed, what remains)

* **WALL 2's intrinsic-norm time-derivative half — DONE generically.**  The
  moving-metric `∂ₜ normSq0S(g(t), T(t))` is derived in closed form; the `∂ₜg`
  contraction is the explicit metric term, and under Ricci flow it is the `Ric ∗ T²`
  reaction.  This was the thirteenth follow-up's item (1)/"genuinely framework-scale
  residue".
* **The remaining input is the bare component time derivative `∂ₜT = ∂ₜ(∇ᵏRm)`** — the
  `Tdt`/`hT`/`hTdot` hypotheses of `hasDerivWithinAt_normSq0S`.  This is the **same
  hypothesis-status data** the `k = 0` producer already takes
  (`Rm04NormRawDerivativeEquationOn`) and the `k = 1` analogues; the general lemma
  *consumes* it and produces the full intrinsic time derivative including the
  previously-missing moving-metric reaction.  So the framework-scale obstruction the
  `k = 0` baseline leaves open (the `∂ₜg` term) is now discharged at the reusable
  tensor level; only the schematic `∂ₜ(∇ᵏRm)` curvature input (and, for the heat
  *equation*, the Bochner Laplacian split — `MultiNormHeat.lean`'s
  `MultiNormLaplacianSplit`) remain, exactly as before.

Files added: `Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean` (no existing
file edited).

## 2026-06-07 fifteenth follow-up: the orthonormal-frame reaction-form bridge is BUILT — the concrete intrinsic reaction collapses to the schematic plain-component form; the residual star decomposition (wall 1) is the isolated remainder

This pass took the dedicated task of bridging the *concrete, derived* all-`k` heat
equation `nablaKRm04NormHeatEquationOn_intrinsic`
(`Evolution/IteratedRmTowerHeatEq.lean`, reaction `= ricReactionContract + 2⟨(∂ₜ −
Δ)∇ᵏRm, ∇ᵏRm⟩`) to the *schematic* tower interface `IteratedRmTowerOn.heatEq`
(reaction `= towerReactionMulti = Σⱼ 2·Σ_m (∇ᵏRm m)·(star j m)`, plain component
contraction).  The **algebraic (orthonormal-collapse) half** is now **closed,
sorry-free, axiom-clean**, in a new file `Evolution/IteratedRmTowerProducer.lean`
(no existing file edited).  `#print axioms` on every public declaration is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0
(3706 jobs).

### The precise mismatch identified, and the collapse that resolves it

The two reaction forms differ **only by the inverse metric**: the concrete
reaction is *metric-contracted* (`inner0S` and `ricReactionContract` carry `gInv`),
while `towerReactionMulti`/`nablaRmReactionMulti` is a *plain* orthonormal-frame
component sum.  In a `g`-orthonormal basis (`gInv = δ`) they coincide — the same
collapse `compNormSqMulti_orthoBasis_eq_normSq0S` (thirteenth follow-up) uses for
the norms, here polarized for the inner product and the Ricci reaction.

### What was proved (`Evolution/IteratedRmTowerProducer.lean`, all sorry-free, axiom-clean)

* `inner0S_orthoBasis_eq_compContract` — the orthonormal collapse of the metric
  inner product: `inner0S g x s A B = Σ_m (comp A m)·(comp B m)` for a
  `g`-orthonormal basis (polarization of `compNormSqMulti_orthoBasis_eq_normSq0S`,
  via `inner0S_eq_coord` + `coordInner0S_identity_eq_sum`).
* `sum_delta_erase_slot_eq` — the slot delta-collapse `Σ_{J0} (∏_{a≠b} δ(I0a,J0a))·G
  J0 = Σ_e G(update I0 b e)` (the engine of the Ricci-reaction collapse;
  `Finset.sum_image` over the injective `e ↦ update I0 b e`, summand vanishing off
  the image).
* `ricStarArray` + `abs_ricStarArray_le` — the genuine `Ric ∗ cB` slot-contraction
  star array `Σ_b Σ_e ric(I0b)e·cB(update I0 b e)`, and its Cauchy–Schwarz bound
  `|ricStarArray ric cB I0| ≤ s·card·Rbnd·√(compNormSqMulti cB)` (with `Rbnd =
  √|Ric|²`, the genuine `j = 0` `starBound` shape — the Ricci half is a *controlled*
  factor, not a vacuous dump).  Mirror of `abs_curvatureAction0SAt_orthoBasis_le`.
* `ricReactionContract_delta_eq_compContract` — the orthonormal collapse of the
  Ricci reaction term: `ricReactionContract δ ric cA cB = 2·Σ_I0 cA I0·ricStarArray
  ric cB I0` (pure finite-sum algebra: the off-slot `δ`s collapse the `J0`-sum, the
  inner `(p,q)`-deltas reduce the Ricci-raised contraction to `ric (I0 b) (J0 b)`).
* `combinedStarArray` + `nablaKRm04Reaction_orthoBasis_eq_compContract` — **the
  assembled reaction-form bridge**: in a `g`-orthonormal basis, the concrete
  reaction equals the *single* plain component contraction `2·Σ_m (∇ᵏRm m)·
  (combinedStarArray m)`, with `combinedStarArray = ricStarArray ric (comp ∇ᵏRm) +
  (comp (∂ₜ − Δ)∇ᵏRm)` — the genuine combined Ricci + residual star.  This is the
  CLAUDE.md crux's *"set the tower's star arrays to these factors so towerReaction
  matches the concrete reaction"* step, at the algebraic level: the `heatEq`
  reaction *shapes* now coincide (plain contraction), with no vacuous discharge and
  no renamed identity.

### The isolated remaining wall (grep-confirmed, matches walls 1–3 of follow-ups 11–14)

`nablaKRm04Reaction_orthoBasis_eq_compContract` writes the reaction as a *single*
contraction `2⟨combinedStar, ∇ᵏRm⟩`.  Populating `IteratedRmTowerOn` needs that star
*split over `j ∈ {0,…,k}`* into genuine `∇ʲRm ∗ ∇^{k−j}Rm` factors with the per-`j`
`starBound`.  The Ricci half (`ricStarArray`, bounded by `abs_ricStarArray_le`) is
the genuine `j = 0` factor; the **residual half `(∂ₜ − Δ)∇ᵏRm`** is the standing
frontier:

1. **The commuted-curvature decomposition `(∂ₜ − Δ)∇ᵏRm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm`.**
   The available all-`k` pieces — the *single*-derivative spatial commutator
   `nablaKRm04_ricciIdentityAt` (`= Rm ∗ ∇ᵏRm`), its rank-uniform Cauchy–Schwarz
   `abs_curvatureAction0SAt_orthoBasis_le` (all-`s`), and the covariant Leibniz
   `inner0S_nabla` — give only the `j = 0`/`j = k` boundary terms; the **iterated**
   spatial commutator `[Δ,∇ᵏ]Rm` (the `0 < j < k` cross terms) is assembled only at
   `k = 1` (the `T₁`/`T₂` machinery of `NablaRiemannReactionBound.lean`).
2. **The component time derivative `∂ₜ∇ᵏRm`** (`Tdot`) — unbuilt Lemma-6.1 assembly
   (eleventh follow-up: banked `∂ₜRm13` + realization + lowering; unblocked,
   unbuilt).
3. **Frame reconciliation (WALL 2)** — the collapse needs the `g(t)`-orthonormal
   basis; the clean-`∂ₜ` `iteratedRmComp_hasDerivWithinAt` is in the
   time-independent `coordinateFrameAt`.

Net: the `heatEq`-reaction-*shape* mismatch is reduced to a single reusable
orthonormal-collapse identity (`nablaKRm04Reaction_orthoBasis_eq_compContract`),
isolating the commuted-curvature residual decomposition (wall 1) as the genuine
remaining content.  `BernsteinShiSolution.lean` remains parametric in
`IteratedRmTowerOn` (it consumes `IteratedRmTowerOn`; the producer is not yet
dischargeable from a bare `SolutionOn` for the reasons above).

Files added: `Evolution/IteratedRmTowerProducer.lean` (no existing file edited).

## Claude prompt

```text
Work in E:\testdifferential-geometry. DifferentialGeometry/ is primary;
RicciFlower/ is reference only.

Goal:
Continue the k = 1 Bernstein-Shi producer behind
DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/IteratedNablaRmTower.lean.
Do not start the all-k induction yet.

Current checked progress:
- MultiNormHeat.lean exists and checks.
- RmRealizationBridge.lean proves rm04_ricciIdentityAt,
  nablaRm04_ricciIdentityAt, iteratedRmComp_one_eq_nablaRm04Field, and
  covDerivStepComp_frameComp_eq.
- NablaRiemannCommutator.lean proves nablaLapComm_orthonormalTrace.
- NablaRiemannTimeDeriv.lean proves iteratedRmComp_one_hasDerivWithinAt, but it
  still takes hrm/hchr/hswap as input shapes.
- NablaRiemannCommutatorBound.lean proves
  nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction.
- Axiom audit for those declarations is clean: only propext, Classical.choice,
  Quot.sound.

Honesty constraints:
- The k = 1 quantitative bound is not closed.
- BernsteinShiSolution.lean must remain parametric in IteratedRmTowerOn until a
  real producer exists.
- Do not solve the bound by adding a renamed starBound/heatEq assumption.
- Do not assume coordinateFrameAt is orthonormal.

Task:
Close the next smallest missing producer for the k = 1 quantitative reaction
bound. Start by building the tensor/metric bridge that the current wall needs:

1. Prove or identify the pointwise raising bridge rm13 = raise(rm04) in a
   metric-compatible basis/frame.
2. Prove or identify the covariant derivative bridge
   nabla(rm13) = raise(nabla rm04), using Levi-Civita metric compatibility.
3. Use those to state an orthonormal-frame component estimate for
   curvatureAction0SAt and nabla(curvatureAction0SAt):
   |curvature action| <= C(card) * |Rm04| * |A|
   and
   |nabla(curvature action)| <= C(card) * |Rm04| * |nablaRm04|.
4. Only then return to NablaRiemannCommutatorBound.lean and connect the proved
   commutator decomposition to the required k = 1 star/reaction bound.

Stop if the first missing item is one of:
- no (1,3) lowering/raising parallelism;
- no nabla rm13 bridge;
- no orthonormal-frame norm comparison rm13 vs rm04;
- no frame-change bridge from coordinateFrameAt to an orthonormal frame;
- no concrete instantiation of hrm/hchr/hswap for iteratedRmComp_one_hasDerivWithinAt.

When stopping, report the exact theorem statement needed next, the file where it
belongs, and why the coordinate-frame shortcut is invalid. Do not add new
assumptions or wrappers that merely rename the frontier.

Verification:
Run focused lake-locked checks for touched files. If adding public theorem(s),
run #print axioms and require only [propext, Classical.choice, Quot.sound].
Update IteratedNablaRmTower.md with what was proved or the exact remaining
blocker.
```

## 2026-06-07 follow-up: the general Bochner Laplacian split of a tensor norm is BUILT (the spatial twin of the time derivative)

This pass built the **rank-uniform, intrinsic Bochner Laplacian split** of a
covariant-tensor norm — the spatial twin of the general moving-metric time
derivative `Tensor0SBundle.hasDerivWithinAt_normSq0S`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`).  New file:
`Tensor/RSTensor/FiberMetric/Tensor0SBochnerSplit.lean`, all sorry-free, every
public theorem `#print axioms = [propext, Classical.choice, Quot.sound]`, focused
`lake-locked build`: EXIT 0.

### What was proved (`Tensor0SBochnerSplit.lean`)

* `sum_trace_coordContract_rough`, `sum_trace_coordContract_nabla` — the
  rank-uniform trace algebra: tracing `g^{ij}` over the `(i,j)`-frozen second
  covariant derivative rebuilds the rough Laplacian contraction `⟨ΔT,T⟩`, and over
  the `i`/`j`-frozen first derivative rebuilds the rank-`s+1` norm `|∇T|²`.  These
  generalise the `(0,2)` `sum_trace_tensor02_rough`/`sum_trace_tensor02_nabla`
  (`Curvature/Bochner/BochnerTensor.lean`) to all ranks.  Helpers `sum_fin_cons`,
  `sum_fin_cons2`, `sum_comm_blocks`.
* `TensorNormHessianProductInBasis` — the pointwise Hessian product rule of the
  norm, in basis component form (the rank-uniform analogue of
  `BochnerTensor.Tensor02NormHessianProductInBasis`).
* `tensorNormBochnerSplit_coord` — the coordinate split
  `tr_g (Hess|T|²) = 2·coordInner0S s gInv (ΔT) T + 2·coordInner0S (s+1) gInv (∇T)(∇T)`,
  valid for **any** `gInv` (no inverse hypothesis).
* `tensorNormBochnerSplit` — the **intrinsic split**
  `Δ|T|² = 2·inner0S g x s (roughLap T) T + 2·normSq0S g x (s+1) (∇T)`,
  where `roughLap T = metricTrace0S2TensorInBasis basis gInv (∇²T)` is the rough
  Laplacian `g^{ab}∇_a∇_b T`.  This is exactly the basis-free formula left as a TODO
  in `Geometry/Operator/RoughLaplacian.lean` (lines ~1037–1060), and the
  `MultiNormLaplacianSplit` half of the BBS norm-square machinery
  (`Evolution/MultiNormHeat.lean:137`), now derived from the pointwise product rule.

### Status of the geometric input

The genuine geometric content — the pointwise Hessian product rule
`Hess|T|²(X,Y) = 2(⟨∇²T(X,Y,·),T⟩ + ⟨∇T(Y,·),∇T(X,·)⟩)` — is taken as a hypothesis
(`TensorNormHessianProductInBasis`), at exactly the same status as
`MultiNormLaplacianSplit` itself and as the `(0,2)` producer's `hess_norm02`
hypothesis chain.  A fully self-contained derivation from `nabla_metric_zero` needs
the **general-rank covariant inner-product Leibniz** `∇⟨T,S⟩ = ⟨∇T,S⟩ + ⟨T,∇S⟩`,
which is grep-confirmed **absent** (only the `(0,2)` `inner0S_two_nabla` /
`inner0S_two_metricCompatible_extDerivFun` exist, in
`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`, ~340 lines of coordinate
Christoffel algebra); building it intrinsically runs into the bundled inverse-metric
parallelism `∇gInv = 0` wall (footer obstruction #1 above — the inverse metric is a
component function, not a bundled `(2,0)` tensor; `ContractionLeibniz.lean`'s
`nabla_metricPow_zero` covers the **lowering** metric power `g^{⊗r}`, not the
**raising** `gInv^{⊗r}` needed for the norm).  So the pointwise rule is the honest
input frontier; the `(0,2)` producer `BochnerTensor.second_norm02_mc` discharges it
for `s = 2`.  Generalising `du_norm02`/`freeze02_deriv`/`hess_norm02` to all ranks
(the four-item TODO in `RoughLaplacian.lean`) remains the route to discharge it for
all `s`, gated by that same missing inner-product Leibniz.

## 2026-06-07 follow-up: the general-rank covariant inner-product Leibniz is BUILT (the "absent" verdict above is refuted)

The general-rank covariant inner-product Leibniz named as the missing frontier in
the section above is now **proved, sorry-free and axiom-clean**, in a new file
`Tensor/RSTensor/FiberMetric/Tensor0SInnerLeibniz.lean`.  `#print axioms` on every
new public theorem is `[propext, Classical.choice, Quot.sound]`.

### What was proved

* `inner0S_nabla` — **the headline primitive**, the rank-uniform directional metric
  compatibility of the induced fibre inner product on covariant `(0,s)` tensors:
  `∇_X ⟨A, B⟩_g = ⟨∇_X A, B⟩_g + ⟨A, ∇_X B⟩_g` for a metric-compatible connection,
  smooth `(0,s)` fields `A`, `B`, and `∇_X = nabla0SFun`.  This is the genuine
  generalisation of the `(0,2)` `inner0S_two_nabla`, for **all** `s`.
* `normSq0S_nabla` — the first-order norm derivative `∇_X ‖T‖² = 2⟨∇_X T, T⟩`,
  directly from `inner0S_nabla` (the rank-uniform `du_norm02`).
* `inner0S_symm` — fibre inner-product symmetry on `(0,s)` tensors.
* `coordContractDt_eq_neg_christoffelCorr` — the **rank-uniform algebraic heart**:
  the metric-derivative term of the coordinate contraction, with the
  metric-compatible `∇gInv = 0` value substituted, equals the negated
  Christoffel-correction contractions.  Pure finite-sum algebra over a per-slot
  index swap (`slotSwap`), generalising the position-hardcoded `(0,2)`
  `inner0S_two_metricCompatible_coord_algebra`.
* `extDerivFun_coordContract` — the directional product rule of the coordinate
  contraction (the rank-uniform spatial analogue of `deriv4sum`), with the
  `extDerivFun` finite-product Leibniz `extDerivFun_finset_prod_real`.

### Route (the `∇gInv = 0` wall is *not* hit for the inner product)

The inner-product Leibniz does **not** need a bundled `(2,0)`/`gInv^{⊗r}`
parallelism.  It is proved in the **coordinate route** mirroring `inner0S_two_nabla`:
expand `⟨A,B⟩ = coordContract gInv (comps A)(comps B)` (`inner0S_eq_coord`),
differentiate along `X` (`extDerivFun_coordContract`), kill the metric-derivative
term with the *component-function* identity `∇gInv = 0` (`gInvCovZeroAt`, the
already-present `inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero` family),
and recognise the Christoffel corrections as the `nabla0SFun` components
(`nabla0S_coordFrame_slots_of_smooth`).  So footer obstruction #1 (the inverse
metric being a component function, not a bundled tensor) is exactly what makes the
component route work — `gInvCovZeroAt` *is* `∇gInv = 0` at the component level.

### What remains for the Bochner Hessian discharge

`tensorNormBochnerSplit`'s hypothesis `TensorNormHessianProductInBasis`
(`Tensor/RSTensor/FiberMetric/Tensor0SBochnerSplit.lean`) is **not yet** discharged
for all `s`.  With `inner0S_nabla` in hand the remaining work is the rank-`s`
generalisation of `freeze02_deriv`'s `hBderiv` — the covariant derivative of the
first-slot-frozen field `y ↦ (∇T)(Y_y, ·)` as `∇²T(X,Y,·) + (∇T)(∇_X Y, ·)` — plus
the `du`/Hessian assembly (`hess_norm02`).  The frozen field's bundled smoothness is
available generically as `tensor0SPartialEval` + `contMDiff_tensor0SPartialEval`
(`Geometry/Connection/TensorNabla/Tensor0SPartialEval.lean`, needs
`[SigmaCompactSpace M]`), and the second Leibniz step is `inner0S_nabla` applied to
`(freezeFirst1Field nablaT Y, T)`.  This is now mechanical realization combinatorics
over the missing-Leibniz frontier, which is closed.

## 2026-06-07 follow-up #2: the Bochner Hessian product rule is DISCHARGED for all `s` (the general Bochner Laplacian split is now hypothesis-free)

The remaining realization combinatorics above are now **carried out, sorry-free and
axiom-clean**, in a new file
`Tensor/RSTensor/FiberMetric/Tensor0SBochnerProduct.lean`.  `#print axioms` on every
new public theorem is `[propext, Classical.choice, Quot.sound]`.  The general
Bochner Laplacian split `tensorNormBochnerSplit` no longer needs the
`TensorNormHessianProductInBasis` hypothesis supplied by callers — it is derived
from metric compatibility.

### What was proved (rank-uniform, namespace `Tensor0SBundle`)

* `partialEval0SField nablaT Y` — the first-slot-frozen field `y ↦ (∇T)(Y_y,·)`
  as a bundled `Tensor0SField s`, smooth via `contMDiff_tensor0SPartialEval`
  (the rank-`s` `freeze02Field`).
* `inner0S_mdiff` — the fibre inner product `y ↦ ⟨A_y,B_y⟩_g` of two smooth
  `(0,s)` fields is `MDifferentiableAt` (the rank-`s` `inner0S_two_mdiff`),
  proved from differentiability of the coordinate contraction.
* `nabla_partialEval0S` — **the only nontrivial realization step**, the rank-`s`
  generalisation of `freeze02_deriv`'s `hBderiv`:
  `∇_X ((∇T)(Y,·)) = ∇²T(X,Y,·) + (∇T)(∇_X Y,·)`, i.e.
  `nabla0SFun s cov X (partialEval0SField nablaT Y) x
    = freezeFirstTwoArgs0S (nabla2T x) (X x) (Y x)
      + tensor0S_curry s x (nablaT x) ((cov Y x) (X x))`.  Proved by the
  `Fin s`-tuple realization (`exists_eq_at_gen` per slot,
  `nabla0SFun_eval_smooth_slots` for the frozen field,
  `TotalNabla0SRealizes.eval_smooth_slots` for `∇²T`), with the `(s+1)`-slot
  correction sum split `Fin.sum_univ_succ` into the `Y`-slot
  (`= (∇T)(∇_X Y,·)`) and the `V`-slots (cancelling against the frozen-field
  corrections via `Fin.cons_update`).
* `freeze0S_deriv` — the rank-`s` `freeze02_deriv`: differentiating
  `2⟨(∇T)(Y,·),T⟩` along `X` gives
  `2(⟨∇²T(X,Y,·),T⟩ + ⟨(∇T)(∇_X Y,·),T⟩ + ⟨(∇T)(Y,·),(∇T)(X,·)⟩)`, by the second
  Leibniz step `inner0S_nabla` + `nabla_partialEval0S`.
* `du_norm0S` — the rank-`s` `du_norm02`: `du(W) = 2⟨(∇T)(W,·),T⟩`, from
  `normSq0S_nabla`.
* `hess_norm0S` — the rank-`s` `hess_norm02`, **discharging
  `TensorNormHessianProductInBasis`** from metric compatibility via the
  `nablaDuAt`/`HessianRealizesNablaDuAt` assembly
  (`Geometry/Operator/HessianTraceRealization.lean`).
* `tensorNormBochnerSplit_mc` — **the hypothesis-free general Bochner Laplacian
  split**: `tensorNormBochnerSplit` with `hprod` removed (derived from `hess_norm0S`),
  `Δ‖T‖² = 2⟨ΔT,T⟩ + 2‖∇T‖²` for all `s`.

### Notes

* The variable-rank `Tensor0SModel` `NormedSpace` instance-resolution diamond (the
  KNOWN PITFALL) is resolved by `set_option backward.isDefEq.respectTransparency
  false` together with file-local `tensor0SModel_normedSpace`/`…AddCommGroup`
  instances, exactly mirroring `Geometry/Metric/TensorInner/Tensor0SRiemannian.lean`.
* Extra instances over `Tensor0SBochnerSplit.lean`:
  `[CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [IsManifold I (∞+1) M]`,
  needed by `tensor0SPartialEval` and the `(0,2)`-template Hessian assembly.
* So the `MultiNormLaplacianSplit` half of the BBS norm-square machinery is now
  derivable from metric compatibility at all ranks; the time-derivative half
  remains `hasDerivWithinAt_compNormSqMulti`.

## 2026-06-07 follow-up #3: the intrinsic `k = 1` heat EQUATION for `|∇Rm|²` is ASSEMBLED from the two general Bochner lemmas — `NablaRm04NormHeatEquationOn` is no longer a raw input

This pass took the dedicated task of instantiating the two now-general Bochner
lemmas (`hasDerivWithinAt_normSq0S_ricciFlow` + `tensorNormBochnerSplit_mc`) at
`T = ∇Rm` (`nablaRm04Field`) and assembling the `k = 1` heat equation, then feeding
the `horth`-free scalar producer `nablaRm04NormHeatBoundOn_scalar`.  It is now
**closed, sorry-free, axiom-clean**, in a new file
`Evolution/NablaRiemannHeatFull.lean` (no existing file edited).  `#print axioms`
on every public theorem is `[propext, Classical.choice, Quot.sound]`.  Focused
`lake-locked build`: EXIT 0 (3702 jobs).

### What was proved (`Evolution/NablaRiemannHeatFull.lean`, all sorry-free, axiom-clean)

Intrinsic scalar fields (frame-free `(t, x)` functions):

* `nablaRm04NormSqIntrinsic` (`= |∇Rm|² = normSq0S g 5 (∇Rm)`),
  `nabla2Rm04NormSqIntrinsic` (`= |∇²Rm|² = normSq0S g 6 (∇²Rm)`), and
* `nablaRm04ReactionIntrinsic` — the **derived** `k = 1` reaction
  `(Ric ∗ ∇Rm²) + 2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`, with `Δ∇Rm = metricTrace0S2TensorInBasis
  basis gInv (∇³Rm)` the rough Laplacian (`nabla3Rm04Field`, rank `7 → 5`) and the
  metric reaction the `ricReactionContract` produced from the moving-metric `∂ₜg`
  term of `hasDerivWithinAt_normSq0S_ricciFlow`.  **Not** a renamed hypothesis.

The assembly:

* `nablaRm04NormHeatEquationOn_intrinsic` — **the headline**: the producer predicate
  `NablaRm04NormHeatEquationOn` (`Evolution/NablaRiemannHeat.lean`)
  `∂ₜ|∇Rm|² = Δ|∇Rm|² + (−2|∇²Rm|² + reaction)` in the intrinsic fibre norms, by
  *subtracting* the two Bochner lemmas instantiated at `∇Rm`:
  - time half `hasDerivWithinAt_normSq0S_ricciFlow` (`s = 5`):
    `∂ₜ|∇Rm|² = ricReaction + 2⟨∂ₜ∇Rm, ∇Rm⟩` (the `∂ₜg` reaction is the explicit
    `ricReactionContract`, derived from `hgInvDt` = the Ricci-flow inverse-metric
    relation `inverseMetric_derivative_solve`, **not** assumed);
  - Laplacian half `tensorNormBochnerSplit_mc` (`s = 5`, with
    `T/∇T/∇²T = ∇Rm/∇²Rm/∇³Rm` realized by
    `nabla2Rm04Field_realizes`/`nabla3Rm04Field_realizes`):
    `Δ|∇Rm|² = 2⟨Δ∇Rm, ∇Rm⟩ + 2|∇²Rm|²`.
  The subtraction cancels the `2⟨Δ∇Rm, ∇Rm⟩` against the residual term, leaving the
  exact reaction `ricReaction + 2⟨∂ₜ∇Rm − Δ∇Rm, ∇Rm⟩` — proved by `inner0S`
  additivity (`map_sub`) + `ring`.
* `nabla2Rm04NormSqIntrinsic_nonneg` — `|∇²Rm|² ≥ 0` (fibre inner-product
  positivity, `MetricFiberData.inner_nonneg`).
* `nablaRm04NormHeatBoundOn_intrinsic` — feeds the heat equation + the nonnegativity
  + a frame-independent reaction bound `reaction ≤ cReact·√(|Rm|²)·|∇Rm|²` into
  `nablaRm04NormHeatBoundOn_scalar`, producing the
  **`NablaRm04NormHeatBoundOn`** predicate consumed by
  `bernstein_first_derivative_estimate`, in the intrinsic norms `|∇Rm|²`/`|Rm|²`.

### The advance, and the honest input status

The advance over the previous `k = 1` status: the assembled heat **equation**
`NablaRm04NormHeatEquationOn` — formerly **always a raw input**
(`Evolution/NablaRiemannHeat.lean` takes it as a hypothesis, the `(0,5)` analogue
of `Rm04NormHeatEquationOn`) — is now **derived** from the two general Bochner
lemmas plus the component time derivative `∂ₜ∇Rm`.  The previously-missing
moving-metric `∂ₜg` reaction term is supplied **intrinsically** by
`hasDerivWithinAt_normSq0S_ricciFlow` (the `Ric ∗ ∇Rm²` reaction), not assumed.

The remaining inputs are taken as hypotheses **at exactly the status the `(0,2)`
producer `ricci_heat_mc` (`Basic/RicciNorm.lean`) takes them** — that producer
likewise takes `DuFieldRealizes`, `HessianRealizesNablaDuAt`,
`SmoothBasisFieldsAt`, the genuine inverse metric `hinv`, the per-component
time-derivative facts (`h_inv`/`h_ricci`), and the reaction term as hypotheses:

* the `∇Rm`/`∇²Rm`/`∇³Rm` covariant-derivative realizations — **banked**
  (`RmRealizationBridge.lean`, `nabla2Rm04Field_realizes`/`nabla3Rm04Field_realizes`),
  discharged inside the theorem with no extra hypothesis;
* `DuFieldRealizes`/`HessianRealizesNablaDuAt` of `|∇Rm|²`, `SmoothBasisFieldsAt`,
  the genuine inverse metric `hinv` — `(0,2)`-parity hypotheses;
* `hgInvDt` — the Ricci-flow inverse-metric-derivative relation
  (`inverseMetric_derivative_solve`'s conclusion), `(0,2)`-parity;
* `hT`/`Tdot` — the component time derivative `∂ₜ∇Rm` (the `(0,5)` analogue of
  `k = 0`'s `Rm04NormRawDerivativeEquationOn`), `(0,2)`-parity;
* `hreact_bound` — the BBS reaction estimate `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩ + Ric ∗ ∇Rm²
  ≤ C·|Rm|·|∇Rm|²`, the same status as the `(0,2)` `ricciNormCurvatureReactionInFrame`.

### What this does NOT close (and why `BernsteinShiSolution.lean` stays parametric)

* `NablaRm04NormHeatBoundOn` is **not** discharged from a *bare* `SolutionOn`
  (without the `(0,2)`-parity hypotheses).  The `∂ₜ∇Rm` component derivative
  (`hT`/`Tdot`), the `DuFieldRealizes`/`HessianRealizesNablaDuAt` of `|∇Rm|²`, and
  the full contracted reaction bound `hreact_bound` are still hypotheses — at the
  same status as the project's `k = 0` baseline (`ricci_heat_mc` / the
  `k = 0` `rm04NormHeatEquationOn_of_solution`, which also never close `∂ₜ|Rm|²`
  from a bare solution).  The intrinsic *spatial* half of the reaction is
  separately discharged (`abs_spatialCommNablaRm_intrinsic_le`, thirteenth
  follow-up); wiring it + the temporal `(∂ₜΓ ∗ Rm + Uhlenbeck)` half into
  `hreact_bound` is the remaining `Rm ∗ ∇Rm`/`Rm ∗ Rm` assembly (frame-invariant
  footer item 2).
* `BernsteinShiSolution.lean` consumes the **all-`k` `IteratedRmTowerOn`**
  interface, not the single `k = 1` `NablaRm04NormHeatBoundOn`; the `k = 1`
  producer feeds the *parametric* `bernstein_first_derivative_estimate`, which has
  no solution-level caller.  So `BernsteinShiSolution.lean` **remains parametric in
  `IteratedRmTowerOn`** (correctly; no edit warranted).

### Net

* **The intrinsic `k = 1` heat EQUATION — DONE**, assembled from the two general
  Bochner lemmas; `NablaRm04NormHeatEquationOn` is no longer a raw input, and the
  `∂ₜg` reaction is derived (not assumed).  The `k = 1` heat-inequality producer
  `NablaRm04NormHeatBoundOn_intrinsic` follows, reducing the `k = 1` frontier to
  exactly the `(0,2)`-parity inputs (`∂ₜ∇Rm` component derivative + the contracted
  reaction bound), the same status as the `k = 0` baseline.
* **Notes:** the variable-rank `Tensor0SModel` `NormedSpace` diamond is resolved by
  `set_option backward.isDefEq.respectTransparency false` + file-local instances
  (mirroring `Tensor0SBochnerProduct.lean`); rank bookkeeping is the subtle point —
  the rough Laplacian of `∇Rm` traces `∇³Rm` (`nabla3Rm04Field`, rank 7), while the
  `2‖∇T‖²` term is `normSq0S g 6 (∇²Rm)` (`nabla2Rm04Field`).

Files added: `Evolution/NablaRiemannHeatFull.lean` (no existing file edited).

## 2026-06-07 follow-up #4: the rank-uniform (all-`k`) `∇ᵏRm` realization bridge is BUILT — the `k=1`/`k=2` `RmRealizationBridge.lean` template is generalized to every `k` by induction

This pass took the dedicated task of generalizing the curvature-derivative
realization bridge of `Evolution/RmRealizationBridge.lean` — proven there only at
the concrete ranks `k = 1` (`iteratedRmComp_one_eq_nablaRm04Field`) and `k = 2`
(`iteratedRmComp_two_eq_nabla2Rm04Field`) — to **all** `k`, by induction.  It is
closed, sorry-free and axiom-clean, in a new file
`Evolution/RmRealizationBridgeAllK.lean`.  `#print axioms` on every public
declaration is `[propext, Classical.choice, Quot.sound]`.

### What was proved (`Evolution/RmRealizationBridgeAllK.lean`, all sorry-free)

The three pieces named in the task, all rank-uniform in `k`:

1. **The bundled iterated field** `nablaKRm04Field S t k : Tensor0SField ∞ (4+k)`
   — `k` iterations of `totalNabla0S` starting from `S.base.rm04 t`
   (`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean`), the rank-uniform
   generalization of `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field`.  Defined
   by recursion on `k`: base `k = 0` is `S.base.rm04 t`, step `k+1` is
   `totalNabla0S (4+k) (S.family.connection t) (nablaKRm04Field S t k) (totalNabla0S_reg …)`.
   The arity step `4 + (k+1) = (4+k) + 1` is definitional (the same `Nat.add`
   reduction the component-level `iteratedRmComp` recursion already relies on), so
   no `Fin (4+k) ↔ Fin ((4+k)+1)` coercion is needed.
   - `nablaKRm04Field_zero`, `nablaKRm04Field_succ` — the definitional unfolding lemmas.
   - `nablaKRm04Field_realizes` — the step `TotalNabla0SRealizes`, read off from
     `totalNabla0S_realizes` at rank `4+k`.  Rank-uniform generalization of
     `nablaRm04Field_realizes`/`nabla2Rm04Field_realizes`/`nabla3Rm04Field_realizes`.

2. **The rank-uniform bridge** `iteratedRmComp_eq_nablaKRm04Field` — for **every**
   `k`, at every point `x` of the coordinate-frame neighbourhood
   `coordinateFrameSet x₀`,

   ```text
   iteratedRmComp (coordinateFrameAt x₀) (realizedChr S x₀) (realizedRmBase S x₀) k t x (frameTuple …)
     = nablaKRm04Field S t k x (frameTuple …)
   ```

   **Proved by induction on `k`.**  The statement is set up in the neighbourhood
   form `∀ k {x}, x ∈ coordinateFrameSet x₀ → ∀ n, …` (universally quantified `k`
   first, then the membership), so the inductive hypothesis is available at *every*
   nearby point — exactly what the step needs.
   - base `k = 0`: `iteratedRmComp_zero` + `nablaKRm04Field_zero` + the definitional
     unfolding of `realizedRmBase`/`frameComp0S` (this is `realizedRmBase`);
   - step `k+1`: rewrite the inner level-`k` array as the frame-component array of the
     bundled `∇ᵏRm` throughout the neighbourhood via the IH (an `=ᶠ[nhds x]`
     eventual equality), push it through `frameExtData` with
     `extDerivFun_eventuallyEq_congr`, then apply the rank-uniform step bridge
     `covDerivStepComp_frameComp_eq` (`RmRealizationBridge.lean`) for the rank-`(4+k)`
     field `∇ᵏRm`.  `realizedChr` is *definitionally* `christoffelSymbolInFrame`, so
     the step bridge's Christoffel data matches with a `simpa [realizedChr]`.

   This is the **exact chaining** of `iteratedRmComp_two_eq_nabla2Rm04Field`
   (rank 5 → 6) lifted to arbitrary `k → k+1`; the `k = 1`/`k = 2` theorems of
   `RmRealizationBridge.lean` are recovered by specialization
   (`iteratedRmComp_one_eq_nablaKRm04Field` is included as the explicit `k = 1`
   corollary).

3. **The rank-uniform `(0,s)` Ricci-identity instances** at `s = 4 + k`:
   - `nablaKRm04_nabla0SSectionRealizes` — the `Nabla0SSectionRealizes` first-derivative
     realization at rank `4+k`;
   - `nablaKRm04_nabla20SRealizesAt` — the discharged `Nabla20SRealizesAt` package
     (the bundled `∇^{k+1}Rm`/`∇^{k+2}Rm` realize the first/second covariant
     derivatives of `∇ᵏRm`), the rank-uniform generalization of
     `rm04_nabla20SRealizesAt` (`k = 0`) / `nablaRm04_nabla20SRealizesAt` (`k = 1`);
   - `nablaKRm04_ricciIdentityAt` — the `(0, 4+k)` Ricci identity for `∇ᵏRm`,
     produced from `tensor0S_ricciIdentity_of_torsionFree`
     (`Tensor/RicciIdentity/Tensor0S/Formula.lean`, rank-uniform in `s`) instantiated
     at `s = 4+k`, with `hcov`/`htor` discharged from `connSmoothOfSol`/`lcAt_regular`
     exactly as `rm04_ricciIdentityAt`/`nablaRm04_ricciIdentityAt` do.

### Building blocks reused (grep-confirmed)

`covDerivStepComp_frameComp_eq` (the rank-uniform step bridge; takes any `s`),
`iteratedRmComp`/`iteratedRmComp_succ`/`iteratedRmComp_zero`, `frameTuple`/`frameComp0S`,
`frameExtData`, `realizedChr`/`realizedRmBase`, `coordinateFrameAt`/
`coordinateFrameSet_open`/`coordinateFrameAt_isLocalFrame_one`/`coordinateFrameAt_mem`,
`totalNabla0S`/`totalNabla0S_realizes`/`totalNabla0S_reg` (all rank-uniform in `s`),
`tensor0S_ricciIdentity_of_torsionFree`/`Nabla20SRealizesAt`/`Nabla0SSectionRealizes`,
`connSmoothOfSol`/`rm13OfSol`/`lcAt_regular`/`torsionFree_of_isLeviCivita`.

### One-line edit to `RmRealizationBridge.lean`

Two genuinely reusable helpers in `RmRealizationBridge.lean` — `connSmoothInf` (the
solution connection is `∞`-smooth) and `extDerivFun_eventuallyEq_congr` (the scalar
ext-derivative respects `=ᶠ[nhds x]`) — were `private`; both are now non-private so the
all-`k` file reuses them rather than duplicating.  No proof body changed.

### The defeq question in the task's STOP CONDITIONS did NOT arise

The task flagged a possible wall: "the induction step needs a dependent-type /
`Fin (4+k) ↔ Fin ((4+k)+1)` coercion that doesn't go through".  It does **not**
arise.  `totalNabla0S` at `s = 4+k` returns `Tensor0SField ((4+k)+1)`, and the
declared `k+1` return type `Tensor0SField (4+(k+1))` is **definitionally equal** to
it (`Nat.add` recurses on its second argument, so `4 + (k+1) ≡ (4+k) + 1` by `rfl`);
`covDerivStepComp_frameComp_eq` is stated for an arbitrary `s` and is applied at
`s = 4+k` with no coercion.  Both flagged stop conditions are therefore vacuous here.

### Net

The all-`k` realization bridge — pieces (1)–(3) of the task — is **DONE** and
reusable: the bundled `∇ᵏRm` field, its rank-uniform realization, the inductive
producer↔bundled bridge on the coordinate-frame neighbourhood, and the `(0, 4+k)`
Ricci identity for every `k`.  This is the foundation for the all-`k` `heatEq`
(instantiate the now-complete general Bochner stack
`hasDerivWithinAt_normSq0S_ricciFlow`/`tensorNormBochnerSplit_mc` at `T = ∇ᵏRm`, add
the all-`k` residual: `∂ₜ∇ᵏRm` + the `(0,s)` commutator `nablaKRm04_ricciIdentityAt`
+ Uhlenbeck), which is the next pass.  Per the task's scope, the all-`k`
residual/`heatEq` assembly was **not** attempted in this pass.

Focused `lake-locked build +…RmRealizationBridgeAllK`: EXIT 0.  Files added:
`Evolution/RmRealizationBridgeAllK.lean`; one-line visibility edit to
`Evolution/RmRealizationBridge.lean` (`private` → public on two reusable helpers).

## 2026-06-07 follow-up #5: the rank-uniform (all-`k`) `|∇ᵏRm|²` heat EQUATION is BUILT — `NablaRiemannHeatFull.lean`'s `k=1` headline is generalized to every `k`

This pass took the parked `Evolution/IteratedRmTowerHeatEq.lean.wip` (the prior
agent's all-`k` heat-equation scaffolding, sorry-free in source but not building),
moved it back to `Evolution/IteratedRmTowerHeatEq.lean`, and made it build.  It is
now **sorry-free, axiom-clean, EXIT 0**.  `#print axioms` on every public
declaration is `[propext, Classical.choice, Quot.sound]`.

### The build fix (Step 1)

The wip's *only* defect was a **missing import**.  The file uses `covDerivStepDt`
and `covDerivStepComp_hasDerivWithinAt`, which live in
`Evolution/NablaRiemannTimeDeriv.lean` (namespace `DifferentialGeometry.PDE.RicciFlow`),
but it imported only `NablaRiemannHeatFull`, `RmRealizationBridgeAllK`,
`IteratedNablaRmTower` — and **no file in the tree transitively imports
`NablaRiemannTimeDeriv`** (grep-confirmed: `import .*NablaRiemannTimeDeriv` had zero
matches).  The exact errors were three `lean.unknownIdentifier`:

```
IteratedRmTowerHeatEq.lean:375:6  Unknown identifier `covDerivStepDt`
IteratedRmTowerHeatEq.lean:400:6  Unknown identifier `covDerivStepDt`
IteratedRmTowerHeatEq.lean:477:12 Unknown identifier `covDerivStepComp_hasDerivWithinAt`
```

(`covDerivStepComp`/`frameExtData`/`iteratedRmComp` resolved fine — they are in the
imported `IteratedNablaRmTower.lean`.)  Fix: add the one line
`import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannTimeDeriv`.
No proof body changed; the scaffolding's mathematics was correct.

### What was proved (`Evolution/IteratedRmTowerHeatEq.lean`, all sorry-free, axiom-clean)

* `nablaKRm04NormSqIntrinsic S k` (`= |∇ᵏRm|² = normSq0S g (4+k) (∇ᵏRm)`), the
  rank-uniform generalization of `nablaRm04NormSqIntrinsic`;
* `nablaKRm04ReactionIntrinsic` — the **derived** all-`k` reaction
  `(Ric ∗ ∇ᵏRm²) + 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`, with `Δ∇ᵏRm = metricTrace0S2TensorInBasis
  basis gInv (∇^{k+2}Rm)` the rough Laplacian and the metric reaction the
  `ricReactionContract` from the moving-metric `∂ₜg` term;
* **`nablaKRm04NormHeatEquationOn_intrinsic`** — **the headline**: the producer
  predicate `NablaRm04NormHeatEquationOn`
  `∂ₜ|∇ᵏRm|² = Δ|∇ᵏRm|² + (−2|∇^{k+1}Rm|² + reaction)` in the intrinsic fibre norms,
  by *subtracting* the two general Bochner lemmas instantiated at `T = ∇ᵏRm`
  (`nablaKRm04Field S t k`, rank `4+k`):
  - time half `hasDerivWithinAt_normSq0S_ricciFlow` (`s = 4+k`):
    `∂ₜ|∇ᵏRm|² = ricReaction + 2⟨∂ₜ∇ᵏRm, ∇ᵏRm⟩` (the `∂ₜg` reaction is the explicit
    `ricReactionContract`, derived from the Ricci-flow inverse-metric relation
    `hgInvDt`, **not** assumed);
  - Laplacian half `tensorNormBochnerSplit_mc` (`s = 4+k`, with `T/∇T/∇²T =
    ∇ᵏRm/∇^{k+1}Rm/∇^{k+2}Rm` discharged by `nablaKRm04Field_realizes` —
    **not** hypotheses):
    `Δ|∇ᵏRm|² = 2⟨Δ∇ᵏRm, ∇ᵏRm⟩ + 2|∇^{k+1}Rm|²`.
  The subtraction cancels `2⟨Δ∇ᵏRm, ∇ᵏRm⟩` against the residual, leaving the exact
  reaction — by `inner0S` additivity (`map_sub`) + `ring`.  At `k = 1` this is
  defeq to the `k=1` headline `nablaRm04NormHeatEquationOn_intrinsic`.
* `iteratedRmComp_hasDerivWithinAt` — **the rank-uniform `∂ₜ∇ᵏRm` producer**: by
  induction on `k` from `covDerivStepComp_hasDerivWithinAt`, the level-`k` component
  tower `s ↦ ∇ᵏRm(s)` is time-differentiable with derivative the explicit
  `iteratedRmCompDt` (`∂ₜ∇ᵏRm = ∇(∂ₜ∇^{k-1}Rm) − (∂ₜΓ)∗∇^{k-1}Rm`).  The three
  geometric inputs (`∂ₜRm`, `∂ₜΓ`, per-level swap) are the cited interface
  hypotheses, exactly as at `k = 1`.
* `iteratedRmCompDt` (+`_zero`/`_succ`), `nablaKRm04NormSqIntrinsic_nonneg`.

### Honest input status (identical to the `k=1` headline)

Exactly the `(0,2)`-parity hypotheses the `k=1` `nablaRm04NormHeatEquationOn_intrinsic`
and the `(0,2)` `ricci_heat_mc` take: `DuFieldRealizes`/`HessianRealizesNablaDuAt`
of `|∇ᵏRm|²`, `SmoothBasisFieldsAt`, the genuine inverse metric `hinv`, the
Ricci-flow inverse-metric-derivative relation `hgInvDt`, and the **component time
derivative `∂ₜ∇ᵏRm`** (`hT`/`Tdot`).  The covariant-derivative realizations
`∇^{k+1}Rm`/`∇^{k+2}Rm` are **discharged** (`nablaKRm04Field_realizes`), not assumed.
The assembled heat **equation** is **derived**, not a renamed input; the `∂ₜg`
reaction is derived intrinsically.

### Step 2 — `IteratedRmTowerOn.heatEq`: NOT dischargeable from the all-`k` heat equation (grep-confirmed wall — the documented `IteratedRmCommutedHeatOn` blocker)

`IteratedRmTowerOn.heatEq` (`IteratedNablaRmTower.lean:309`) requires, for level
fields `w k = compNormSqMulti (level k)` (forced by `wDef`):

```
∂ₜ(w k) = wLap k + (−2·w (k+1) + towerReactionMulti (level·) (star·) k)
```

where `towerReactionMulti = nablaRmReactionMulti (level k) (star k)
= Σⱼ 2·Σ_m (level k m)·(star k j m)` — the **schematic** `∗`-reaction contracting
`∇ᵏRm` against *abstract* star arrays `star k j` (only constrained by `starBound`,
the `√(w j)·√(w (k−j))` Cauchy–Schwarz input).

The all-`k` heat equation produces the derivative
`uLap + (−2·|∇^{k+1}Rm|² + nablaKRm04ReactionIntrinsic)` with the **concrete**
reaction `ricReactionContract(...) + 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`.  The norm-form and
`wLap` halves bridge cleanly:

* `w k = compNormSqMulti (level k) = normSq0S = nablaKRm04NormSqIntrinsic` in a
  `g(t)`-orthonormal basis, via `compNormSqMulti_orthoBasis_eq_normSq0S`
  (`NablaRiemannHeatFrameInvariant.lean`) + `iteratedRmComp_eq_nablaKRm04Field`;
* the `−2·w(k+1)` term matches `−2·|∇^{k+1}Rm|²` the same way;
* `wLap` matches the realized Hessian-trace Laplacian.

**The reaction halves do not bridge.**  To discharge `heatEq` *meaningfully*, the
`star k j` must be genuine `∗`-factors with `towerReactionMulti = ` (the concrete
reaction) **and** satisfying `starBound`.  That is precisely the schematic
commuted-curvature identity

```
(∂ₜ − Δ)∇ᵏRm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm
```

(`IteratedRmCommutedHeatOn` in this md's plan, §1) — a **genuine analytic/geometric
producer that does not exist in Lean** and is flagged here as "the hard blocker".

This is grep-confirmed, not an over-count.  Searching the whole tree
(`nablaRmReactionMulti|towerReactionMulti|nablaRm04ReactionIntrinsic|nablaKRm04ReactionIntrinsic`
over `*.lean`) finds **no theorem** relating the concrete BBS reaction
(`nablaKRm04ReactionIntrinsic`/`nablaRm04ReactionIntrinsic`) to the schematic
`nablaRmReactionMulti`/`towerReactionMulti` — even at `k = 1`.  And
`IteratedRmCommutedHeatOn`/`MultiNormHeatEquationOn`/`iteratedRmTowerOn_of_solution`
exist **only in this md** (planning), never in Lean.  So neither the new all-`k`
heat equation nor the `k=1` headline closes `heatEq`; `BernsteinShiSolution.lean`
correctly stays parametric in `IteratedRmTowerOn`.

A *vacuous* discharge (set `star k 0 :=` the residual components, `star k j := 0`
for `j ≥ 1`, so the schematic sum equals the concrete reaction by definition) is
**rejected**: it is exactly the md's forbidden "close the theorem by adding a new
assumption that is just `heatEq` under a different name", and it makes `starBound`
(the entire analytic point — the `√(w j)·√(w (k−j))` bound) unprovable.

* **`heatEq` status**: a **grep-confirmed wall** — requires `IteratedRmCommutedHeatOn`
  (the schematic curvature commutator/connection-variation producer), absent in
  Lean.  The norm-form (`wDef`) and Laplacian (`wLap`) halves *are* bridgeable from
  the all-`k` heat equation; only the reaction equality is blocked.
* **`starBound` status**: a separate follow-up (the all-`k` generalization of
  `abs_spatialCommNablaRm_intrinsic_le`, currently `k=1`-only); its temporal half
  (`∂ₜΓ ∗ Rm` + Uhlenbeck) is likewise the BBS-assembly frontier.
* **realization predicates** (`DuFieldRealizes`/`HessianRealizesNablaDuAt`): remain
  at standard-interface status, identical to the `(0,2)` `ricci_heat_mc` and the
  `k=1` producer.

### Net

The intrinsic **all-`k` heat EQUATION** — the task's Step 1 — is **DONE**, the
faithful rank-uniform generalization of the `k=1` "DONE" headline, assembled from
the two general Bochner lemmas + the all-`k` `∂ₜ∇ᵏRm` producer; no heat equation,
residual, or reaction is renamed/axiomatized.  Step 2 (`IteratedRmTowerOn.heatEq`)
is **not** dischargeable from these foundations: the missing fact is the schematic
commuted-curvature identity `(∂ₜ − Δ)∇ᵏRm = Σⱼ ∇ʲRm ∗ ∇^{k−j}Rm`
(`IteratedRmCommutedHeatOn`), a documented genuine producer with no Lean
realization.

Focused `lake-locked build +…IteratedRmTowerHeatEq`: EXIT 0 (3705 jobs).
`#print axioms` on `nablaKRm04NormHeatEquationOn_intrinsic`,
`iteratedRmComp_hasDerivWithinAt`, `iteratedRmCompDt_succ`,
`nablaKRm04NormSqIntrinsic_nonneg` = `[propext, Classical.choice, Quot.sound]`.
Files: `Evolution/IteratedRmTowerHeatEq.lean.wip` → `Evolution/IteratedRmTowerHeatEq.lean`
(one import line added; no proof body changed).
