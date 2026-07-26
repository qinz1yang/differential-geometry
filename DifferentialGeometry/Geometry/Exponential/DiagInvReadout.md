# DiagInvReadout

## 2026-07-11 branch-parametric readout

The file defines the fixed-trivialization readout of an explicit
`DiagInvBranch`, its open readout domain, and `readoutDomInf`.  The latter
provides one common all-order domain together with the selected branch's right
inverse, base projection, and intrinsic exponential identities.

The proof consumes only `DiagInvBranch.inv_inf` and its derived inverse laws.
It does not inspect the qualitative `diagExpIFT` construction and does not
extract or discard any quantitative radius.  Focused verification passed
without warnings or local `sorry`s.

This generic readout brick is complete (100%).  The legacy `diagExpInv`
readout wrappers and the HCG quantitative branch can now specialize the same
interface, but the center-equation migration and concrete `StepB1RawInput`
producer remain unstated and 0%.
