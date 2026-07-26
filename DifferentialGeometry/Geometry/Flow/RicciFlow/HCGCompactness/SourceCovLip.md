# SourceCovLip

## Role

`SourceCovLip.lean` is the source-native, constants-first analytic interface for
the P4 open-window convergence producer.  It intentionally does not mention a
`BumpFamily`, `gSeqExt`, target collars, or target-side compact sets.

The structure `SrcCovLipData` records two uniform outputs.  For each requested
order, its constant is selected before the varying source index `k`:

- whole-source bounds for `metricCovDerivNorm` throughout the closed window;
- whole-source time-Lipschitz bounds for every lower `metricDerivNorm` order.

The theorem `srcCovLip_of_soln` states the honest producer from a uniform
source-metric equivalence, uniform moving Shi estimates, and one uniform
initial covariant envelope.

The module imports the source-flow/extension foundation in
`ConvFieldAssembly` and reuses the existing explicit order-zero metric bound
`covNorm0_le` from `ConvFieldInputs`.  No duplicate tensor-norm proof is kept
locally.

## Constants-first proof

`srcCovLip_of_soln` is now sorry-free and focused-green. Its order-zero branch
uses `covRic0_le`. At positive order, strong induction performs the following
steps before fixing the varying source index:

- select all lower-order constants from the induction hypothesis;
- form one numeric `RicTowerCoeffs` package;
- define the explicit Gronwall output `Cq`;
- define `Lq = 2 * (slope * Cq + offset)`.

For each source type, `hevComp_of_solutions` supplies the realized flow
evolution, `covOrderBound_stage_on` proves the whole-source order-`q` metric
bound, and `ric_bound_field_on` proves the corresponding
`-2 * nabla^q Ric` bound. Thus no compact finite subcover, per-source constant,
or wrapper hypothesis is used.

The Ricci-evolution half then feeds `timeLipschitz_of_hasDerivAt`; a finite sum
over `Finset.range (p + 1)` gives one nonnegative Lipschitz constant for every
order `q <= p`.

No endpoint assumption or branch-specific field has been added.  Downstream,
`SrcCovLipData.cov` feeds the grow-local `covTail_of_bounds`, while
`SrcCovLipData.lip` feeds both the grow-local and compact-source time estimates.

## Verification and accounting

Focused verification is GREEN with zero diagnostics and no
`sorry`/`admit`/`axiom`; the exact artifact refresh is GREEN (`4067/4067`).
The theorem proof and its dedicated constants-first machinery are 100%.
This closes the independent `SourceCovLip` producer, not the separate
solution-generated `ShiCutoffData` frontier. The whole HCG supporting
machinery remains about 60%, and unconditional `compactnessSol` remains
theorem-level 0%.
