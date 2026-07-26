# ChartWkpQuot

## Status

Source-written only. The active named build is owned elsewhere, so this file
has not yet been elaboration-checked.

## Mathematical content

No class, instance, or notation is introduced. The quotient operations are
ordinary explicit functions:

- `qzero` is the class of the zero genuine tensor section;
- `qadd` and `qsub` use `Quotient.map₂`;
- `qneg` and `qsmul` use `Quotient.map`.

The lemmas `qadd_rel`, `qneg_rel`, `qsmul_rel`, and `qsub_rel` expose the
componentwise a.e. compatibility proving that these maps are well-defined.
The `_mk` theorems record their action on representatives.

The ordinary theorem values `qadd_zero`, `qzero_add`, `qadd_assoc`,
`qadd_comm`, `qneg_zero`, `qneg_neg`, `qadd_neg_self`, and
`qneg_add_self` record the additive group laws without installing an additive
group. The corresponding subtraction identities include `qsub_eq_add_neg`,
`qsub_self`, `qsub_zero`, `qzero_sub`, `qsub_rev`, `qsub_chain`, and
`qsub_eq_zero`.

`qnorm_zero`, `qnorm_add_le`, and `qnorm_smul` prove the norm laws needed by a
future local seminormed structure, while `qnorm_lt_top` permits conversion to
a real-valued norm. `qnorm_eq_zero` proves separation: a class has zero
quotient norm exactly when it is `qzero`. Its forward direction uses the
order-zero `eLpNorm` summand of every chart component, so it proves actual
componentwise a.e. equality rather than assuming norm separation.

`qnorm_neg`, `qnorm_sub_symm`, `qnorm_sub_triangle`, and `qnorm_sub_sep`
supply the translation-invariant metric prerequisites. The plain real-valued
function `qdist` is `ENNReal.toReal` of the q-norm of `qsub`; the theorem
values `qdist_nonneg`, `qdist_symm`, `qdist_eq_zero`, `qdist_self`, and
`qdist_triangle` prove its metric laws. Finiteness from `qnorm_lt_top` is used
explicitly in the `toReal` separation and triangle arguments.

`qrep` chooses a genuine Sobolev representative and `qmk_qrep` proves that it
maps back to the original class. `qCauchy_limit` is the direct theorem-valued
completeness bridge at arbitrary finite order `k`: a
sequence Cauchy for `wkpTensorQNorm (qsub _ _)` has a quotient limit with
q-norm differences tending to zero. It uses no metric or completeness
instance.

`qdist_limit` is the arbitrary-order consumer-facing form of this completeness
result. Taking `k = 3` supplies the spatial quotient completeness required by
the low-regularity contraction route. Its hypothesis is the ordinary real epsilon definition of a
`qdist`-Cauchy sequence, and its conclusion is convergence to a quotient class
in `qdist`.  The proof converts between the finite `ENNReal` quotient norm and
its `toReal`, then invokes `qCauchy_limit`.  This is the smallest instance-free
bridge from the tensor quotient construction to a Picard iteration or other
limit-transfer argument.

The current Ricci--DeTurck maximal-regularity files do not yet call any
`WkpTensorQuot` declaration.  They contract on spectral Hilbert-valued
Bochner `L²` spaces.  Likewise, `WkpForcingBridge.lean` concerns the scalar
`WkpChartQuot`, not this tensor quotient.  Therefore `qdist_limit` closes the
spatial explicit-completeness API, but it does not manufacture the missing
tensor-valued time carrier or a parabolic solution operator.  Forming
`MeasureTheory.Lp (WkpTensorQuot ...)` and applying Mathlib's
`ContractingWith.fixedPoint` directly would require standard measurable,
metric/normed-additive, and complete-space structures.  Those structures are
deliberately not introduced here; the dimension-general solver must either
receive them as explicit local inputs or continue with an explicitly
parameterized time-space construction.

## Boundary and progress

The algebraic, norm, metric, and Cauchy/metric-limit theorem values are
source-complete, but 0% Lean-verified. No global additive, module, metric,
normed-space, or complete-space instance is installed. After verification, a
later authorized file can package these existing functions and theorem values
locally.
