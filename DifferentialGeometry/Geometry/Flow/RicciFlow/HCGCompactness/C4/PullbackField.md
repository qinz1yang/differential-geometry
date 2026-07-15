
## 2026-07-07 (goal session, cont.): B2-0 + B2-2 landed; B2 tower cancelled

**Landed (targeted build 3804 jobs green, axioms = [propext, Classical.choice, Quot.sound]):**
- `tangentCoordChange_opens` (B2-0): subtype tangent coordChange = ambient, at interior points.
  Proof: `tangentBundleCore_coordChange_achart` readout (rfl) + `Filter.EventuallyEq.fderivWithin_eq`
  on the subtype chart's `extend_target_mem_nhdsWithin` filter; pointwise via
  `subtypeRestr_symm_apply`; at-point via `EventuallyEq.eq_of_nhdsWithin` (point ∈ range I).
- `tensor0SModelAt_opens` (B2-2): subtype chart-local tensor readout = ambient.  Proof: the
  CML-bundle triv apply is rfl (`Trivialization.continuousMultilinearMap_apply`), symmL →
  coordChange via `TangentBundle.symmL_trivializationAt_eq_core`, close with B2-0 at q := x.
  The cross-manifold `A`-argument type (V-fiber vs M-fiber CML) elaborated WITHOUT any cast
  bridge — same defeq-abuse as the Mathlib core lemma.

**Lean lessons:**
- `𝓝[s] x` notation needs `open Topology` (silent `sorry`-filter + bogus `?m.261 sorry` otherwise).
- Names: `Tensor0SBundle.Tensor0SSpace`, `TensorLieDeriv.tensor0SModelAt`,
  `TangentBundle.symmL_trivializationAt_eq_core`, `TopologicalSpace.Opens.chartAt_eq` (rfl!),
  `OpenPartialHomeomorph.subtypeRestr_source/_symm_apply`, `Filter.EventuallyEq.eq_of_nhdsWithin`.
- C4 is NOT in the root import closure: bare `lake build` does NOT verify C4 files — always use
  targeted `build +DifferentialGeometry...C4.<Module>` (bare-build exit 0 here is vacuous).

**B2-3/4/5 CANCELLED** — the whole naturality tower already exists (see STEPD_PLAN codas 11–13):
OpenSubtypeNaturality.lean + MovingShiRestrictOpen.lean (`covDerivOfField_restrictOpen`) +
MetricCovDerivPullback.lean (`covDerivOfField_pullback`, field-level) + rfl/arity bridges
(`metricCovDeriv_eq_covDerivOfField`, `covDerivOfField_eq_iterCov`).  B2-0/B2-2 remain as
spare parts.  Next: the single (ii) assembly lemma per coda 13.

## 2026-07-07 (goal session, final): covNormWith_pd_zone PROVED sorry-free

D1a-(ii) endpoint complete: zone-local partial-pullback covariant-tower-norm naturality,
`tensor02CovDerivNormWith a δM G G x = tensor02CovDerivNormWith a δN g' g' (Φ x)` on x ∈ V ⊆
Φ.source, with hδ/hG the ambient-mfderiv realization hypotheses (PreApproxIsoDataOn shapes).
Verification: targeted build 3885 jobs green; axioms [propext, Classical.choice, Quot.sound].
Also green here: `tensor02_eq_covDOF` (tower bridge), private `srm_ext`.
Migrated OUT to `Tensor/RSTensor/Coordinates/OpensRestrict.lean` (canonical home): B2-0
`tangentCoordChange_opens`, B2-2 `tensor0SModelAt_opens`, `restrictOpen0S` (all green,
axiom-clean, 2731 jobs).

Key Lean lessons (this file's fight): see STEPD_PLAN codas 19–21 — def-context
section-variable inclusion does not retro-include synth-needed instances (FiniteDimensional
pending-leaf behind a NormedSpace(Tensor0SModel) error; diagnose with #synth probe);
structure-literal against Tensor0SField needs respectTransparency-false + letI-topology
(fromScalarField pattern); `mfderiv_subtype_val` CLM-form in simp (the _apply form fails the
inner-slot motive); cross-fiber CML equalities elaborate bare (defeq abuse);
ContMDiffSection FunLike-coe is not rfl.

Next brick: (iii) `partialData_comp` (coda 21).

## 2026-07-09 open-ball restriction API

The D1-to-direct-limit adapter is now explicit and verified:

- `PartialDiffeomorph.opensMap` codomain-restricts `Φ|U` into a larger target open `V`;
- `opensMap_isOpenEmb` proves it is an open embedding;
- `opensMap_contMDiff` proves forward smoothness;
- `opensMap_inv_mdiff` proves `Function.invFun` is smooth on the actual range.
- `opensDiffeo_mfderiv` exposes that the subtype diffeomorphism has the ambient
  `PartialDiffeomorph` differential.

The proof factors through `toOpensDiffeo` and the smooth inclusion of one open subtype into
another. The inverse theorem is deliberately range-scoped and requires `Nonempty U`, exactly as
the Step-D positive-radius balls provide.

## 2026-07-07 (goal session, rounds 5-7): partialData_comp PROVED — D1a complete

`partialData_comp` (D1a-(iii), the lbl406 composition brick) fully proved: two-sided partial
approx-iso data composes along `PartialDiffeomorph.trans` on any compact K inside the zone,
∀ε''-monotone/Nonempty form with C := max-of-four constants, hypotheses ε,ε' ≤ 1/2, lower
bound 2(ε+ε')+(ε+ε')C.  Proof ≈ 700 lines: forward + mirrored reverse pipelines, each =
collar realize (strengthened exists_pullbackField) + error triangle + four F5 inputs
(equiv/hgK/hδ₀/hδ₁ — hgK consumed from the OTHER side's reverse data, which is why the
book's data is two-sided) + comp_cov_le + germ-vanishing (restriction-naturality as
germ-congr) + tower/norm bridges.  Five covNormWith_pd_zone live calls total.
Axiom status at the time: `sorryAx` was inherited only from the then-open F4
assembly.  That F4 dependency is now closed; the composition proof itself remains
sorry-free.  Durable Lean lessons in STEPD_PLAN codas 22-36 (∃-elim-into-Prop hoisting,
acEquiv .symm direction, set_option ladder 1M→2M, left/right_inv coe traps).

## 2026-07-08: half-composition API frontier exposed

Added two data-producing interfaces for the D1b two-bracketing recursion:

- `compDataFwd`: forward half of `partialData_comp`, with only the forward
  asymmetric tolerance bound `ε/(1-ε) + ε' * max C 2`.
- `compDataRev`: reverse half of `partialData_comp`, with only the reverse
  asymmetric tolerance bound `ε'/(1-ε') + ε * max C 2`.

These are intentionally exposed at the `PullbackField` layer because the proof
organs already exist inside `partialData_comp` (`hc0P''`/`hcovP''` and
`hc0Pr`/`hcovPr`).  D1b should consume these halves separately: forward on the
peel-last `chainComp` ledger, reverse on the peel-first `chainComp'` ledger,
then assemble with `BookApproxIsoPartialData.ofParts`.

Verification: focused `PullbackField.lean` check passed.  The two new
interfaces are precise `sorry` frontiers; no Lean error remains in their
signatures.

## 2026-07-09: separated-parameter composition API

Added the first separated-parameter composition layer:

- `compSepFwd`: forward half, with explicit F5 feed `q` and new-step feed `e1`,
  outputting separated `c0''` and `cov''` ledgers;
- `compSepRev`: mirrored reverse half;
- `sepData_comp`: ordinary two-sided composition wrapper around the two halves.

Verification passed, and the targeted module build passed.  The forward/reverse
halves are precise `sorry` frontiers intended to reuse the existing
`partialData_comp` proof organs.  Important boundary: `sepData_comp` is a valid
ordinary two-sided composition wrapper, but it is not the D1b hacc replacement.
D1b still needs the half-composition split: forward on the peel-last ledger and
reverse on the peel-first shifted-tail ledger, then assemble with the existing
fold/germ transports.

## 2026-07-09: separated composition organs proved

`compSepFwd` and `compSepRev` are now proved, using the same forward/reverse
organs as `partialData_comp` but with separated ledgers.  The key formal repair
was to avoid routing through ordinary `PreApproxIsoDataOn`: separated data allows
zero ledgers, while the ordinary carrier requires a strictly positive epsilon.
The proof therefore uses `Classical.choose` witnesses for compact collars and
pullback fields, then feeds F5 directly with `q` and `e1`.

Verification passed for `PullbackField.lean`, and the targeted module build
also passed so the compiled upstream body is refreshed.  The remaining `sorry`
warnings in this file are the older ordinary half wrappers `compDataFwd` and
`compDataRev`; they are not the D1b separated-recursion organs.  D1b's
composition frontier has moved from `compSepFwd`/`compSepRev` to the upstream
B/C producer.  The F4/F5 uniform constant chain was proved later on 2026-07-09,
and `PullbackField.lean` rechecked successfully afterward.

## 2026-07-09: open-map differential

Added `PartialDiffeomorph.opensMap_mfderiv`: codomain restriction to a larger target open does
not change the ambient differential. The proof mirrors `opensDiffeo_mfderiv` through the two
open-subtype inclusions. Focused verification and the targeted producer build passed; the two
older ordinary-wrapper `sorry`s are unchanged.

## 2026-07-09: ambient open-target lift

`PartialDiffeomorph.liftTargetOpen` now lifts a full-target partial diffeomorphism into an open
subtype to the ambient manifold. Its inverse uses `Function.invFun Subtype.val` only on the open
range; `invSubtype_mdiff` proves precisely that range-scoped smoothness. `liftOpen_mfderiv` reads
the ambient differential back as the original subtype-valued differential. Focused verification
and the targeted producer build passed. No new `sorry` was introduced.
## 2026-07-13 short-time alignment

The composition organs were adapted to the merged non-reducible tensor API.
Fiber subtraction now uses `Tensor0SSpace.sub_apply`, section subtraction is
handled separately, and the `covDerivOfField_eq_iterCov` reindex readout uses
the explicit continuous-multilinear `domDomCongr` evaluation.  Obsolete
representation-level simp arguments were removed.

Focused verification passes.  No new frontier or theorem assumption was
introduced, and the HCG percentages remain those in `PROJECT_MAP.md`.

## 2026-07-13: unused ordinary wrappers removed

A repository-wide Lean reference audit found no consumers of `compDataFwd` or
`compDataRev`; only their declarations and historical Markdown mentions
remained.  Both obsolete single-ledger declarations were deleted.  The active
Step-D route continues to use the independently proved `compSepFwd` and
`compSepRev` organs.  Focused verification, the targeted producer refresh,
and the downstream `StepDDirected` check all passed.
