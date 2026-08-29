# ActionLocalMin

## Result

This file now provides the complete action-realization and local-minimality
transfer brick:

- `lChartAct_split`: the genuine nonlinear chart action is the sum of its Gram
  kinetic and scalar-potential integrals;
- `lRegAction_chart_sum`: a finite chart realization computes the global
  regularized action as the sum of the chart actions;
- `lChartAct_local`: global minimality against fixed-endpoint global `C¹`
  curves implies `IsLocalMinOn` of every positive-length chart `timeH1` piece
  in its fixed-endpoint affine class.

The transfer uses the canonical `exists_chart_splice` producer. It introduces
no closure hypothesis or supplied action-comparison assumption.

## Proof route

The coordinate image of the selected `timeH1` piece is compact and lies in the
open extended-chart target. A positive metric thickening stays inside that
target. The estimate `timeH1.norm_toFun_le_norm` converts a sufficiently small
`timeH1` ball into uniform pointwise control, so every fixed-endpoint curve in
that ball is an admissible chart replacement.

`exists_chart_splice` realizes the replacement as a continuous global manifold
curve with the dependent `Function.update` representative family. Applying
`lAction_c1_dense` gives global fixed-endpoint `C¹` recovery curves. Global
minimality holds along that sequence, and `le_of_tendsto'` applied to the
negated actions passes the inequality to the splice limit. The two
`lRegAction_chart_sum` identities reduce this to finite sums; erasing the
selected index and cancelling the identical remaining sum gives the desired
chart-action inequality.

Repeated subdivision nodes cause no additional assumption: they are handled
inside `exists_chart_splice`. Only the selected segment is required to have
positive length.

## Verification

Focused verification and the targeted module refresh passed without warnings.
No placeholders are present, and all public names satisfy the twenty-character
limit.

The focused recheck after generalizing `lChartAct_local` also passed without
warnings, and the exported module was refreshed. The theorem now exports
without an ambient `CompactSpace M` instance; its proof uses only the supplied
finite realization and the compact chart images already constructed locally.

## Project position

- `lChartAct_split`, `lRegAction_chart_sum`, and `lChartAct_local`: 100%.
- Global-to-local minimizing transfer and its dedicated splice machinery:
  100%.
- The next regularity phase can now consume a genuine chart `IsLocalMinOn`
  theorem rather than a frontier hypothesis.
- Terminal regular `exists_lMinimizer`: 0% until stated and proved.
- Dedicated L-geometry machinery: about 82--86%.
- Reduced-volume monotonicity: 0%; P2 remains below 1%, and the full Poincare
  formalization remains about 3--5%.
