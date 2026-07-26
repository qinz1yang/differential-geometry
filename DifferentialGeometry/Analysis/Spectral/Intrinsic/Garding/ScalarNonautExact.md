# `ScalarNonautExact` status

## 2026-07-19 exact all-scale source

Three exact-interval declarations are source-complete:

- `lapHs_norm_on` bounds every all-scale scalar Laplacian-difference operator
  on a caller-supplied reflected regular interval;
- `lapHs_A20_on` identifies its order-zero member with the genuine `A20`
  operator throughout that interval, consuming the finite-core equality
  already produced by `lapA20_span`;
- `lapHs_dyn_on` preserves every finite time regularity order on the full open
  interior of that same interval.

The norm proof uses joint scalar coefficient jets and the structural
`lapHs_eq` identity. The compatibility proof uses equality on the dense finite
spectral core. None of these theorems chooses or shortens a lifespan. The
`joint_jet_bdd` call explicitly takes `S = K`; reflected regularity is used to
obtain coefficient smoothness, not as the compact-set inclusion argument.

Focused verification is currently blocked before elaborating this source by
the active upstream spectral object refresh.  The exact missing import at the
latest check is `EigenvectorIteratedStep.olean`.

Honest accounting: all three declarations remain theorem-level **0%** until
focused verification passes; their dedicated source is approximately **95%**.
The exact Galerkin-limit assembly `gallim_on` remains a separate theorem-level
**0%** frontier. Perelman `NoLocalCollapsing` and
`ham3_noncollapse` remain theorem-level **0%**; broader entropy/noncollapsing
machinery remains approximately **97%**, and whole HCG machinery approximately
**60%**.

## 2026-07-23 post-merge check

The exact nonautonomous scalar module now imports the Hs source directly and
uses explicit `norm_nonneg` targets for the first- and second-order coefficient
differences.  Focused verification and the module artifact refresh both passed.
