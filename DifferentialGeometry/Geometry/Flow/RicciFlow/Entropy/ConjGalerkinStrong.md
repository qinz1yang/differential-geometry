# ConjGalerkinStrong

## Role

This file turns the all-order spectral subsequential limit from
`ConjGalerkinLimit.lean` into a genuine `H¹_t H⁰_x` object while retaining the
explicit `H² → H⁰` companion path.  It is the intrinsic strong-limit producer;
it does not yet assert joint spacetime smoothness or `IsHeatPotOn`.

## Route

The proof first extends each compact-interval Sobolev path continuously, defines
the limiting `H⁰` velocity from the frozen scalar Laplacian and the moving
perturbation, and passes each finite coordinate ODE to the limit by the
right-sided FTC and dominated convergence.  The mode identities are assembled
with `coeffCLM` into an `H⁰` Bochner integral identity, then packaged by
`timeH1.mk` with the exact initial trace and derivative representative.

No consumer hypothesis, convergence predicate, locally constant chart choice,
or tensor-representation unfolding is added.  Continuity of the perturbation is
producer data already obtained while constructing `scalar_gal_subseq`.

The direct `hlim.pert_cont.norm` route is invalid here: `pert_cont` is recorded
in the strong-operator topology, while Mathlib's operator norm uses the norm
topology.  The proof instead takes a compact-time bound after applying the
operator to each fixed `H²` vector, then uses Banach--Steinhaus to obtain the
uniform operator-norm bound required by dominated convergence.

## Verification and frontier

`galLim_mode_ftc`, `galLim_ftc`, `scalar_gal_limit`, `galLimVel_lift`, and
`galLimExt_deriv` pass focused verification without warnings or `sorry`.  The
earlier module export build covers the strong-limit endpoint; the new all-scale
lift and derivative have focused verification.
Thus
`scalar_gal_limit` is theorem-level **100%**, and its dedicated strong-limit
machinery is **100%**.  It constructs a real `timeH1.mk` /
`MaxRegSolutionSpace` object with the exact initial trace, derivative
representative, and `H² → H⁰` companion path.

This closes only the intrinsic spectral strong-limit phase.  The proposed
`heatpot_of_maxreg` theorem is **0%**, and the jointly spacetime-smooth classical
moving conjugate-heat / `IsHeatPotOn` theorem is also **0%**.  Perelman
no-local-collapsing and `ham3_noncollapse` remain endpoint-level **0%**.  The
whole HCG machinery estimate remains about **57%**, with all HCG endpoint
theorems at **0%**.

## 2026-07-15 all-scale consult frontier

The checked strong limit now also has two scalar time-regularity producers:
`galLim_mode_deriv` identifies the ordinary derivative of each limiting mode
at every interior time, and `galLim_mode_c1` packages each mode as `C¹` on the
open interval.  Both pass focused verification.  These results do **not** imply
that the derivative belongs to every spatial Sobolev space: coordinatewise
smoothness plus all-order bounds for the values can still have an `H⁰` derivative
which is not in `H^m`.  An all-scale estimate for the PDE right-hand side is
therefore mathematically necessary.

A GPT Pro consultation was checked against the published
[`short-time-existence` branch](https://github.com/liao9yuan/differential-geometry/tree/short-time-existence).
The branch evidence used includes the generic frozen
[`tensorScaleLaplacian`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/MaximalRegularity/OperatorEquation.lean#L169-L186),
the all-spatial-order [`lim_mass`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinLimit.lean#L43-L96),
the low-scale [`galLimVel`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinStrong.lean#L79-L137),
the [`H² -> H⁰` perturbation](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkin.lean#L272-L283),
and the jointly smooth reflected
[`conjCoeff`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjPotential.lean#L46-L106).
The local worktree additionally confirms that `IsHeatPotOn` has exactly the
four fields `jointSmooth`, `jointCont`, `sliceSmooth`, and `equation`, while
`IsConjHeatOn` is already the reversed-family specialization in
`ConjugateHeat.lean`.

The ruling is:

1. `galLimVel_lift` is now proved.  It produces one positive slab, chosen before
   the Sobolev order, on which the limiting velocity has a continuous lift to
   every natural spatial order.
2. The first missing reusable operator is the moving scalar Laplacian
   difference `H^(m+2)(q) ->L H^m(q)`.  The generic frozen Laplacian already
   exists.
3. `RawConnLapToHsOrderDropping` does not close this problem: its completion
   theorem is fixed-metric and `(0,2)`-specific, whereas the scalar A2 operator
   needs fixed-background variable coefficients.  Importing it would merely
   replace the present coefficient-jet frontier by an unproved cross-metric
   Sobolev-equivalence frontier.
4. The implemented lower-layer chain is
   `app_hs_unif` -> `lapCoeff_slab` -> a smooth-core A2 `H^(m+2) -> H^m`
   estimate -> dense-core `extendOfNorm` -> inclusion compatibility -> operator
   bounds -> `galLimVel_lift`.
5. The scalar-potential arm follows the parallel, easier chain
   `smul_hs_unif` -> `scalarPotHm` -> parameter continuity.
6. Full-slab operator continuity was not needed for this milestone.  The proof
   bounds `galLimVelHs` uniformly one order above the requested lift, identifies
   its `H⁰` inclusion with the already continuous `galLimVel`, and applies
   `cont_of_coeff`.  This is cheaper and keeps all equalities fully applied.

The efficient endpoint architecture keeps all-spatial-order `j = 0` mass on
the full closed slab and proves only the lifted velocity continuously there.
Higher time jets are needed uniformly only on arbitrary compact subintervals
`[a,b] ⊂ (0,tau)`.  This is enough because `jointCont` and endpoint
`sliceSmooth` use `j = 0`, while `jointSmooth` is required only on the regular
interior.  After `galLimVel_lift`, the next substantial theorem is a simultaneous
induction over time-jet order, universally quantified over spatial Sobolev
order; its operator derivatives still map `H^(m+2) -> H^m` because time
differentiation hits only coefficients.  A rank-zero scalar spectral-series
reconstruction should then provide closed-slab joint continuity and slice
smoothness from the `j = 0` masses, and interior joint smoothness from the
compact-interior time-jet masses.  The pointwise PDE identification remains a
separate theorem from that reconstruction.

The first time jet is now closed.  `galLimExt_deriv` continuously extends the
`H^m` velocity lift and proves an `H^m`-valued FTC coefficientwise; hence the
all-order Galerkin path has a genuine strong derivative at every interior time.
This is stronger than the earlier coordinatewise `galLim_mode_c1`.  It does not
yet supply second and higher time jets: those require differentiating the
time-dependent A2 and scalar-potential coefficients as bounded maps between
the appropriate Sobolev orders.

Current honest accounting: `galLim_mode_deriv`, `galLim_mode_c1`,
`galLimVel_lift`, and `galLimExt_deriv` are each theorem-level **100%**.  The dedicated all-scale A2,
potential, inclusion, and lift machinery used here is also **100%**.  The
all-time-jet lift, scalar joint reconstruction, and `heatpot_of_gallim` remain
unstated/unproved (**0%** each); their preparatory infrastructure must be counted
separately.  `IsHeatPotOn` remains **0%** until interior time jets, scalar
reconstruction, and pointwise PDE identification are complete.

## 2026-07-15 higher-time-jet architecture ruling

The follow-up GPT Pro consultation used the published
[`short-time-existence` branch](https://github.com/liao9yuan/differential-geometry/tree/short-time-existence)
as reference and treated `galLimVel_lift` / `galLimExt_deriv` as newer local
facts.  The relevant branch checkpoints are the old
[`ConjGalerkinStrong`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinStrong.lean#L42-L137),
the `j = 0` spatial-mass tower in
[`ConjGalerkinLimit`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinLimit.lean#L40-L97),
the smooth-core action estimate
[`param_app_jet`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Sobolev/TensorHilbert/ParametricAppCcJetBound.lean#L197-L222),
and the heat-semigroup bootstrap whose forcing jets are hypotheses, not outputs
([`MaxRegInteriorTimeSmoothing`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegInteriorTimeSmoothing.lean#L93-L210)).

The ruling is a weakened route A: do not first prove a joint map in an
independent Sobolev variable, and do not differentiate a whole CLM-valued
path.  The missing reusable producer is a fully applied, pathwise finite-order
regularity theorem, provisionally `appHs_path_cd`: a jointly smooth
coefficient family applied to a `C^k` `H^n` path is again a `C^k` `H^n` path.
The local audit adds an important correction: there is currently no generic
completed `appHs` object.  `ParametricAppHs.lean` contains only the smooth-core
estimates `app_hs_unif`, `app_hs_const`, and `app_hs_small`; `lapDiffHs` and
`scalarPotHs` are separate scalar-specific `extendOfNorm` completions.
Therefore the first implementation phase must include the generic completion,
its smooth-core application lemma, and the applied path theorem.  Merely
publishing a theorem statement over an assumed `appHs` would hide the actual
frontier.

The intended dependency chain is:

1. generic completed coefficient action plus a fully applied smooth-core path
   lemma (`appCc_time_cd`) and `appHs_path_cd`;
2. public `scalarTrace_joint` and `connTrace_joint`, followed by
   `scalarPot_path_cd` and `lapDiff_path_cd`;
3. an all-scale strong equation `galLimExt_ode` and simultaneous-in-spatial-order
   successor `galLim_cd_succ`;
4. `galLimExt_smooth` on a possibly smaller `Ioo 0 tau'`;
5. only then `galLim_jet_mass`, obtained cheaply from compactness of the
   Banach-valued time derivatives at a higher spatial order and the Weyl
   negative-weight summability used in
   [`SeriesContinuous`](https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Tensor/SobolevScale/SeriesContinuous.lean#L59-L83).

The modewise ODE and the DeTurck time-jet stack do not bypass step 1.  The
former still needs a support-independent estimate for the differentiated
applied action.  The latter assumes forcing time jets and their spectral
majorants, and its public preservation theorems are `(0,2)`- and
DeTurck-specific.  `AnisoOn` is useful after the jets exist, not as a jet
generator.

Precise current frontier: `galLimExt_smooth` is theorem-level **0%** and its
dedicated higher-time-jet machinery is about **35%** (joint coefficient
smoothness mostly exists; completed applied-action time regularity is **0%**).
`galLim_jet_mass`, rank-zero joint reconstruction, and `heatpot_of_gallim` are
each theorem-level **0%**.  There is no mathematical obstruction presently;
the blocker is a substantial missing reusable completion/regularity API.

## 2026-07-16 all-time-jet assembly

`galLimVelCan` is the canonical all-scale velocity. `galLimVel_lift` and
`galLimExt_deriv` now retain equality with that velocity, and
`galLimExt_ode` states the strong interior ODE directly at every natural
Sobolev order.

`galLimExt_smooth` is proved on one common smaller positive interval. Its
simultaneous induction uses the `m+3` solution path, casts it to the natural
loss-two domain, applies the frozen Laplacian, dynamic Laplacian difference,
and dynamic scalar potential at order `m+1`, then includes the resulting
velocity once into order `m`. The canonical ODE closes the successor step via
`contDiffOn_succ_iff_deriv_of_isOpen`.

Focused verification is green. Thus `galLimExt_smooth` and its dedicated
higher-time-jet machinery are separately **100%**.

The next assembly theorem, `galLim_jet_mass`, is now proved in
`ConjGalerkinClassical.lean` and focused verification is green.  Its local body
has no `sorry`, but its closed-manifold counting input inherits the existing
`WeylEigenvalueCountingBound.lean` `sorry`; the full dependency chain must not
be called sorry-free.  Rank-zero joint reconstruction and
`heatpot_of_gallim` remain separate theorem-level **0%** frontiers. Classical
conjugate-heat dedicated machinery is about **90%**; whole HCG machinery is
conservatively about **59%**, while every HCG endpoint theorem remains **0%**.
