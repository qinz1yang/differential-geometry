# Read-only Hurewicz reuse source

These exact source snapshots come from `E:/testdifferential-geometry-t1-433`.
They are reference material, not native imports or a standalone buildable project.
Source headers and available upstream/root licensing notices are preserved.
`T1Provider.lean` is the already extracted narrow provider; the full general
six-sphere toolbox and unrelated source trees are deliberately not included.

The provider and interface target Lean 4.33.0 and Type-0 homology with integer
coefficients. Native targets remain universe-polymorphic and use lifted integer
coefficients. Generalization, coefficient naturality, and equality with the
specified cubical Hurewicz map remain proof obligations. Old artifacts/audits
are not verification in the current 4.33.1 checkout.
`Poincare/Targets.lean` is included to make the remaining manifold homology
obligations visible, not as a completed producer. Its other imports require
its original checkout; do not try to build this reference folder in isolation.

Read the receiving project's `Surgery/Topology/Background.md` before porting.
Do not import these files under a new competing foundational hierarchy.
