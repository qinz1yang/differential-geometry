# ConvFieldOpenAssembly

## Purpose

`open_upgrade_of_raw` is the concrete P4 capstone between the four raw
open-window estimates and the final Hamilton compactness endpoint.  It returns
one `FlowUpgradeData` and proves completeness of every time slice of the same
constructed limit flow.

## 2026-07-18 implementation

The theorem now performs the full intended assembly:

- `exists_openConv_raw` selects one subsequence and one compatible open limit;
- `OpenConvOut.isSolution` constructs the Ricci-flow certificate;
- `OpenConvOut.gInf_zero_eq` and `conv0_of_cp` identify the time-zero metric;
- `OpenConvOut.scalar_conv` supplies scalar convergence, transported along the
  checked time-zero equality;
- `flowUpgrade_of_open` builds the concrete upgrade record;
- `gSeqExt_lower` and `OpenConvOut.complete_at` prove all-time completeness.

No endpoint field, compactness assumption, or radius hypothesis was added.
The scalar transport now uses pointwise eventual equality instead of a large
`simpa`; the dependent equality is discharged by the canonical
`flowUpgrade_open_L` projection lemma.  Focused verification and the exact
module refresh are green, and neither file contains `sorry`, `admit`, or
`axiom`.

## Honest accounting

- `open_upgrade_of_raw`: checked theorem, 100%.
- Dedicated open-assembly machinery: 100%.
- Dedicated P4 machinery: about 97%.  The remaining work is producer-side:
  derive the raw open-window estimates and preserve the canonical time-zero
  convergence witness erased by the abstract metric-compactness package.
- Unconditional `compactnessSol`: 0%.  After this assembly, its principal P4
  gap is the uniform noncompact open-window Shi/whole-source producer from the
  theorem's raw curvature hypotheses.
- Whole HCG support machinery: about 60%.

## 2026-07-18 grow-local raw assembly

`open_upgrade_of_raw` now accepts the uniform covariant tail only on
`bf.grow k`, consistently with every downstream consumer. The old
whole-source bump-collar estimate and `hchi` input are absent from the complete
raw assembly chain. Focused verification and the exact module refresh pass.

This interface migration is complete (100%). Dedicated P4 machinery remains
about 97%, while unconditional `compactnessSol` remains theorem-level 0%; its
real producer frontiers are the complete-noncompact open-window Shi theorem,
the constants-first source covariant/Lipschitz theorem, and the concrete Step-D
canonical-provenance sidecar.

## 2026-07-24 concrete Ricci-norm assembly

`open_upgrade_of_raw` now derives the open-window intrinsic squared Ricci-norm
convergence from the same `cLow`, metric bound, and covariant-tail inputs as
scalar convergence. It transports only the fully evaluated real-valued
sequence across the time-zero target cast and passes that witness to
`flowUpgrade_of_open`; no consumer-side convergence hypothesis was added.

Source wiring is complete, and the three upstream artifacts
`ConvFieldPDE`, `ConvFieldOpenScalar`, and `ConvFieldOpenEndgame` are
exact-current. Focused verification of this final assembly passes with no
diagnostics, and its exact artifact is current.
