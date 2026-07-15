# Finite scalar Galerkin solutions

## 2026-07-14 source implementation

`ConjGalerkin.lean` defines the finite scalar spectral vector, the coordinate
embedding/restriction maps, the frozen diagonal heat operator, and the genuine
time-dependent perturbation

`lapDiffA20 + conjA1 ∘ (H² → H¹)`.

`scalarGalVec_supp` and `scalarGalVec_finite` expose the exact finite-support
facts needed by the later critical-energy consumer; no support witness is
added as a theorem hypothesis.  `scalarGalVec_inc` records that cross-scale
inclusion leaves those finite coordinates unchanged, while
`scalarGalRepr_eq` records that their genuine smooth representative is
independent of the Sobolev exponent used to package them.

The source proof of `scalar_gal_exists` applies the generic global
finite-dimensional ODE theorem on one short interval independent of the finite
spectral set.  The returned coefficient family is continuous on that interval,
solves the projected reversed conjugate-heat system, agrees with the initial
spectral coordinates on the chosen set, and is definitionally zero outside it.

Verification is pending because shared Lean writers were active while this
source pass was made.  No new consumer assumption, chart-selection hypothesis,
or frontier wrapper was introduced.

The next required coefficient bridge is now source-written as
`scalarGalPert_fin`.  It stays in the fully applied scalar normal form and uses
`lapDiffA20_core` plus `lapDiffCore_eq_cc` for A2, and
`scalarPotH0_apply` plus `scalarPotOp_core` for A1.  Its output is exactly the
`tensorL2Coeff` of the smooth sum consumed by `scalar_crit_tame`; it does not
assert equality of whole time-dependent operators.

After this bridge verifies, the next theorem is `scalar_gal_bound`: combine
`scalar_gal_exists`, `scalar_crit_tame`, and the generic
`galerkin_energy_uniform_bound_perScale` for an arbitrary sequence of finite
mode sets.  Scalar exhaustion/projection remains a later limit-layer API;
existing `eigenIdxFinset` and `TimeL2EigenProjection` are specialized to rank
`(0,2)` and cannot honestly be reused for `(0,0)`.

Honest accounting: `scalar_gal_exists` and `scalarGalPert_fin` are
source-written but theorem-level 0% until focused verification; their dedicated
source machinery is about 94%.
The scalar critical-tame theorem remains theorem-level 0% pending verification,
and the Galerkin-to-limit/second-order bootstrap remains 0%.  Perelman
no-local-collapsing and `ham3_noncollapse` remain endpoint-level 0%, with about
42% dedicated analytic machinery.  Whole HCG machinery remains about 54%, with
its endpoint theorems at 0%.

## 2026-07-14 verification and performance closure

Focused verification now passes for the complete file.  In particular,
`scalarGalPert_fin` and `scalar_gal_exists` are theorem-level **100% verified**
and contain no `sorry`.

The targeted module build also passes.  Its only local style warning, the
over-broad global Classical scope, was then narrowed to declaration-local
definition scopes and a proof-local `classical`; the post-cleanup focused check
passes.

The original performance failure had two independent causes.  First, the
existence theorem exposed a large reducible conjunction containing a nested
continuous-linear-map family.  The stable public normal form now separates
actual data and proofs: `ConjGalTime` stores the common time, `IsConjGalTime`
states positivity, the unit upper bound, and finite-system solvability, while
`IsConjGalSol` states the scalar coordinate equations.  This changes no
assumption and adds no frontier wrapper.

Second, the local vector-field estimate compared norms of whole nested CLMs.
That route timed out even after aliases were moved or annotated.  The checked
proof instead establishes `hfield_apply` after applying every operator to a
finite-dimensional vector.  All addition, composition, and Lipschitz steps are
then scalar or vector-valued; the Lipschitz estimate follows from `map_sub`.

After those normal-form changes, the remaining 200k failure was cumulative
across the single large ODE proof command rather than a local `whnf` wall.  A
theorem-scoped 800k budget verifies the applied proof; there is no global option
change and no consumer-side assumption.  Broad `simp` was removed from the
critical operator blocks.

Honest accounting after this check: the finite scalar Galerkin existence
theorem and its genuine A2/A1 coefficient realization are **100%**; the next
theorem `scalar_gal_bound` remains theorem-level **0% until its own focused
check**, with about **95%** of its dedicated source machinery assembled.
`scalar_gal_subseq` remains theorem-level **0%**, while its now-verified generic
compactness machinery is about **80%**.  Perelman no-local-collapsing and
`ham3_noncollapse` remain endpoint-level **0%**; their dedicated analytic
machinery is about **44%**.  Whole HCG machinery remains about **54%**, with its
endpoint theorems at **0%**.

## 2026-07-15 finite-path continuity producer

`scalarGalVec_cont` now packages coordinatewise continuity on the actual finite
support into continuity of the `H²` spectral vector.  The proof uses the
existing finite Euclidean embedding and checks the supported and unsupported
coefficients separately; it does not unfold the Sobolev representation or add
an assumption to a downstream theorem.  Focused verification passes without
warnings or `sorry`.

This is a completed low-layer producer.  The downstream strong-limit theorem is
tracked separately in `ConjGalerkinStrong.md`; its theorem percentage must not
be inferred from this helper alone.
