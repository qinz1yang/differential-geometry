# Fixed-chart minimizer regularity

## Result

`lChart_min_c1` is focused-green without warnings or placeholders. From the
same regular-time, chart-image, and actual local-minimum data consumed by
`lChart_weak_euler`, it produces a continuous representative of the weak
coordinate velocity, almost-everywhere equality with `u.deriv`, closed-
interval `ContDiffOn Real 1` regularity of `u.toFun`, and the pointwise
`derivWithin` identification.

The checked chain is:

1. `lChart_weak_euler` supplies the integrable native chart force and weak
   identity.
2. `chartGram_time` supplies the measurable uniformly bounded native Gram
   coefficient.
3. The force and weak identity are doubled because `lChartAct` uses one half
   of `chartGramOp`, while `chartVel_rep_cont` is stated for the full Gram
   operator.
4. `chartVel_rep_cont` produces the continuous velocity representative.
5. Equality on the open interval is transported by equality of the two `ae`
   filters, without rewriting the measure parameter inside the dependent
   `Lp` coercion; `toFun_c1_of_rep` then supplies the C1 conclusion.

The theorem now states the exact assumptions used by its verified upstream
producer: positive model dimension, a boundaryless model, and a T2 manifold.
No stronger compactness or scalar-sign hypothesis was added.

Focused verification and the targeted module refresh passed. The public
L-geometry umbrella now imports both `ActionWeakEuler` and `ActionRegular` and
is focused-green.

## Project position

`lChart_min_c1` is 100% verified. Its fixed-chart weak-Euler-to-C1 assembly is
100% for the stated interface. The adjacent-node momentum match and global
C1 gluing remain separate: `lNode_mom_match` is 0% until stated and proved.
The terminal regular `exists_lMinimizer` and `redVolume_anti` remain 0%.
