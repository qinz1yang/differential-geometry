# Connection-difference contraction norm

## 2026-07-10

Added `connOut_norm_le`, the scalar-applied specialization of
`sqrt_normSqRS_apply` to `connectionDifferenceTensorAt`.  The proof uses a
cheap scalar `change`; it never asserts equality of whole Hom objects.

Focused verification passed.  This producer is complete; downstream still
has to combine it with the metric C1 modulus and the Hessian/gradient spectral
energy bounds in the geometric `A2` estimate.

## 2026-07-24 — `connDiffVec_norm_le` (vector-output companion, sub-frontier T-A(b))

Added the **vector-output** analogue of `connOut_norm_le`, ratified by the planner as the
public home for HCG brick T's atomic per-slot estimate:
`‖(∇−∇') Y X‖_g ≤ √normSqRS(connectionDifferenceTensorAt cov cov' x) · ‖X‖_g · ‖Y‖_g`
(sharp constant `1`).  Here `(∇−∇') Y X = CovariantDerivative.difference cov cov' x Y X` is the
raw Christoffel-difference vector inserted into one slot by
`HCGCompactness/MetricCovDerivLinear.diffStep_eval`.  Sorry-free, axioms
`[propext, Classical.choice, Quot.sound]`, `lake build +…ConnectionDifferenceNorm` EXIT=0
(3520 jobs, 34s).

Route (unlike the 4-line `connOut_norm_le`, this one needs real work because the OUTPUT is a
tangent vector, not a covector contraction):
1. Flatten `w := (∇−∇') Y X` to the covector `α := dualToCotangent_gen (tangentFlatLinear_gen g x w)`.
   `normSq0S g x 1 α = g.inner x w w` via `normSq0S_eq_inner` + `inner0S_one_eq_cotangent` +
   `cotangentInner_dualToCotangent_tangentFlat_gen` (the sharp∘flat roundtrip; `cotangentInner`
   and `cotangentInner_gen` are defeq, so `exact` closes it).
2. `‖w‖²_g = (connectionDifferenceTensorAt cov cov' x α)(X,Y)` via
   `connectionDifferenceOutput_apply_slots` (`= α(fun _ => (A Y) X)`) + `dualToCotangent_apply_gen`
   + `tangentFlatLinear_apply_gen`.  The `connectionDifferenceTensorAt · α ≡ connectionDifferenceOutput ·`
   step is the same defeq `change` `connOut_norm_le` uses.
3. Bound that `(0,2)` pointwise evaluation by its fibre norm with `abs_apply_le_sqrt_normSq0S`,
   feeding a `g`-orthonormal frame built INTERNALLY (`stdOrthonormalBasis` on
   `(tangentMetricData_gen g x).metric.toCore`, copied verbatim from `sqrt_normSqRS_apply`) — so
   the lemma stays frame-free to callers.  `Fin.prod_univ_two` + `simp` collapses the slot
   product to `√gXX·√gYY`.
4. Compose with the mixed HS estimate `sqrt_normSqRS_apply` (√normSq0S(Tα) ≤ √normSqRS(T)·√normSq0S(α))
   and `√normSq0S(α) = ‖w‖_g` (step 1), giving `‖w‖²_g ≤ (√normSqRS·√gXX·√gYY)·‖w‖_g`; divide by
   `‖w‖_g` (`le_of_mul_le_mul_right` in the `‖w‖_g > 0` branch; trivial when `= 0`).

LESSON: in the assembly calc, do NOT `rw [e1]` a `g.inner x w w = |…|` fact globally — it also
rewrites the `√(g w w)` on the RHS.  Fold the equality into the calc's first step instead.
All bridges reachable through the existing `TensorRSRiemannian` import (which pulls in
`Comparison` for `abs_apply_le_sqrt_normSq0S`); no new import needed.  No cotangent-namespace
qualification needed — the flat/cotangent lemmas live in `namespace Tensor0SBundle`.

### Remaining T-A assembly (next, in `UnifCovSumCross.lean`, per planner)
`diffStep_norm_le` = `√normSq0S gBase x (s+1) (diffStep g₁ g₂ s S x) ≤ s·√normSqRS(connectionDifferenceTensorAt)·√normSq0S(S x)`:
expand `normSq0S(diffStep x)` via `diffStep_eval` + `abs_apply_le_sqrt_normSq0S` on `S x` +
`connDiffVec_norm_le` (this lemma) for the inserted slot, over a gBase-ON frame (sub-frontier (a):
grep for a pointwise ON-frame producer — `hframe.toBasisAt`-style — before building), summed over
`s` slots.  Then compose with `lcDiff_norm_le` (jet side).  T-B base-Leibniz stays multi-session.
