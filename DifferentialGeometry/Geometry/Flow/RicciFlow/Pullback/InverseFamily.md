# InverseFamily status

## Algebraic and inverse-regularity layer

- `Diffeomorph.pullbackMetric_trans` proves functoriality of metric pullback
  under composition.
- `Diffeomorph.pullbackMetric_symm` and
  `Diffeomorph.pullbackMetric_self` prove the two inverse-family cancellation
  identities.
- Source-written `gauge_vel_refl` is the initial compatibility identity for the positive
  gauge equation: at the identity diffeomorphism the pushed-forward DeTurck
  velocity is the original DeTurck vector field.
- Source-written `joint_symm_smooth` isolates the inverse-family regularity step: if the
  time-preserving total map `(t,x) |-> (t, psi_t x)` is a local
  diffeomorphism, its slice-wise bijectivity makes it a global diffeomorphism,
  whose smooth inverse is exactly `(t,x) |-> (t, psi_t^{-1} x)`.
- Source-written `joint_symm_smoothOn` is the consumer-faithful open-window variant.  It only
  assumes the total map is a local diffeomorphism on the PDE slab.  At each
  point, slice-wise injectivity identifies the set-theoretic inverse family
  with Mathlib's chosen smooth local inverse, so no regularity outside the
  solved time window is required.
- Source-written `symm_gauge_vel` is the differential consumer for the harmonic-map sign
  convention.  From `partial_t psi = -W composed with psi` and joint
  smoothness of the forward and inverse evaluation maps, it differentiates
  `psi_t(psi_t^{-1}(x)) = x` and obtains the positive pushed-forward velocity
  required by `ricci_pullback_DT`.

Only the three pullback identities were focused-green before the reverse gauge
and inverse-family regularity theorems were added.  Every item explicitly
labelled source-written above remains 0% accepted until the expanded file
passes a focused check.  The shared exported artifacts needed by the file have
now been restored, but the ordinary focused-check invocation still fails before
elaboration because one imported object path is 263 characters long.  The
object exists and is readable through the 204-character short build junction;
Lean reports it missing only when Lake exports the canonical long search path.
The next verification action is therefore the same lock-aware focused check
with Lake pointed at `lakefile.short.toml`, not a proof change.

## Reverse gauge theorem

`ricci_pullback_DT` states the consumer-shaped conditional identity.  If a
Ricci flow `g_RF` and a jointly smooth diffeomorphism family satisfy the
positive velocity equation

`partial_t Phi = Phi_* W(Phi^* g_RF, g_bg) composed with Phi`,

then `Phi^* g_RF` solves the Ricci--DeTurck equation on the same open time
window.  The proof combines:

- the Ricci-flow metric slot derivative;
- `flow_slot_pos` for the two moving push-forward slots;
- `evalForm_joint` and `deTurck_evalForm_chain_hasDerivWithinAt`;
- naturality of Ricci and of the metric Lie derivative.

This theorem does not assume or claim existence of the gauge family.  Its
focused verification is the next action after artifact restoration.

## Failed routes and exact analytic frontier

Three mathematically different uniqueness routes have been taken to their
first genuine obstruction:

1. The harmonic-map DeTurck ladder is the route developed in this file.  Its
   algebraic reverse-gauge and inverse-family steps are source-written, but HMF
   existence is absent.  The existing time-dependent ODE flow engine cannot
   construct it because the velocity depends on the unknown map and its
   spatial first and second derivatives.  The fixed tensor-bundle
   maximal-regularity engine becomes relevant only after the missing
   exponential-coordinate realization.
2. A direct Kotschwar route has componentwise connection/curvature evolution
   ingredients, but no coupled difference evolution, cross-metric energy
   estimate, or initial-edge regularization.  It is not presently shorter.
3. The checked maximal-regularity uniqueness theorem compares two forcing
   fixed points of one truncated map.  There is no reverse theorem taking an
   arbitrary geometric Ricci--DeTurck solution to that Duhamel/fixed-point
   representation.  Applying the same fixed-coordinate argument directly to
   Ricci flow retains the diffeomorphism kernel, so it does not bypass a gauge.

No route produced a counterexample to the endpoint statement.  The
classification is missing analytic producers/API, not a statement-design
failure.

The shortest faithful producer chain found so far after the conditional
identity uses an exponential-section chart on the mapping space, rather than a
new atlas-gluing solver for manifold-valued maps:

1. `ricci_edge_bounds`, deriving uniform fixed-background first-derivative and
   square-root-time weighted second-derivative bounds from the exact endpoint
   hypotheses;
2. write the raw harmonic-map heat gauge near the identity as
   `psi_t x = expMapIntrinsic g0 x (V_t x)`.  The unknown `V_t` is a section of
   the fixed tangent bundle, hence a `(1,0)` tensor and is eligible for the
   existing tensor maximal-regularity engine;
3. realize the harmonic-map tension equation as a strongly parabolic equation
   for `V`, split into the small time-dependent top-order arm and lower-order
   arms.  `TensorMaximalRegularity/Nonautonomous.lean` already supplies the
   linear time-dependent mixed-order fixed point; what is still missing is the
   locally-Lipschitz time-dependent Nemytskii combination and the geometric
   Sobolev-tame realization of the exponential-coordinate operator;
4. use the resulting short-time `C1` closeness to `id` to prove that `psi_t` is
   a diffeomorphism.  The local part uses the existing manifold IFT, uniformly
   on a finite compact cover: after shrinking the horizon, the same finite
   family of source neighborhoods is an injectivity cover for every `psi_t`.
   This uniformity is essential; choosing local injectivity neighborhoods
   separately after fixing `t` would not let `psi_t -> id` select one common
   horizon.  `NearIdentity.lean` now source-writes the global compact-uniform
   step.  A Lebesgue entourage subordinate to the fixed injectivity cover
   yields injectivity; a second entourage subordinate to the clopen connected
   components yields surjectivity from clopenness of the local-diffeomorphism
   range.  Hence no inadmissible `ConnectedSpace M` hypothesis is needed in
   this topological step;
5. package `Phi_t = psi_t.symm`, prove joint inverse smoothness, and
   differentiate `psi_t (Phi_t x) = x` to obtain the positive velocity equation
   consumed by `ricci_pullback_DT`;
6. apply `ricci_pullback_DT`.

The exponential-section route is partly supported by existing geometric APIs:
`diagExp_contMDiffAt_zero`, `diagExp_hasFDerivAt_zero_unipotent`, the
`diagExpInv`/`DiagInvBranch` inverse laws, and the intrinsic exponential
variation smoothness theorems.  The existing fixed-bundle top-order operator
can be expressed with `connLaplacian_vector` or, after bundling a vector field
as a smooth `(1,0)` tensor section, `connLaplacianMixed g 1 0`.  Thus the
linear rough-Laplacian target space is already present.

There are nevertheless two exact API restrictions which prevent this list
from being an HMF existence proof:

- no Lean definition or realization theorem for the tension field of a map
  between two Riemannian manifolds was found in `DifferentialGeometry/` or the
  checked Mathlib source;
  `HessianTraceRealization.lean` is scalar-valued only.  Consequently there is
  no theorem yet converting
  `psi_t x = expMapIntrinsic gBase x (V_t x)` into a quasilinear parabolic
  equation for the fixed tangent-bundle section `V`;
- the intrinsic moving-base exponential APIs above are currently declared
  under `[ConnectedSpace M]`.  The exact public statement of
  `ricci_flow_forward_unique` has no such hypothesis.  This is not a
  mathematical counterexample--the theorem is componentwise true--but a proof
  using these APIs must either localize and glue over connected components or
  first remove that unnecessary API restriction.  It may not silently add the
  instance to the endpoint.

The fixed-bundle maximal-regularity audit is equally specific.  The checked
`nonaut_strong_exists` accepts measurable uniformly bounded *linear*
time-dependent `H^(a+2) -> H^a` and `H^(a+1) -> H^a` perturbations.
`mixed_strong_exists` accepts autonomous globally Lipschitz nonlinear arms at
those two orders.  Neither theorem accepts the combination needed by the HMF
operator: a time-dependent, locally Lipschitz nonlinear map on a lower-norm
state ball.  The source-written `LocalNemytskii.lean` currently only packages
evaluation of a Lipschitz map defined on an almost-everywhere state set; it
does not yet supply the corresponding contraction estimate or a mixed
time-dependent fixed-point theorem.  Thus a reusable smallest analytic API is
a Caratheodory-style local mixed forcing operator (measurable in time,
uniformly Lipschitz on the state ball) and its forcing-space contraction.

Even that generic fixed-point package would not by itself close HMF.  One must
still prove that the exponential-coordinate tension operator has precisely
those measurability, state preservation, and Sobolev-tame estimates for the
domain metric `g_RF(t)`.  At the endpoint, `g_RF` is only chart-Gram continuous
at the initial edge; its spatial derivative bounds are not hypotheses.  This
is why merely feeding the smooth-interior coefficients into
`nonaut_strong_exists` is invalid: their operator norms need not be uniformly
bounded as `t` approaches the initial time.  The missing boundary estimate or
an appropriately weighted/rough-coefficient parabolic theorem remains a
genuine prerequisite.

The componentwise repair is not completely foundational: the repository
already has `SmoothRiemannianMetric.restrictOpen`,
`ricciTensor_restrictOpen`, `metricFamilySmoothOn_restrictOpen`, and
`metricVariationEquation_restrictOpen` in the open-subtype / HCG restriction
layer.  Mathlib also supplies open connected components on locally connected
spaces and finiteness of the component set for compact locally connected
spaces.  What is still missing for this endpoint is the adapter from its raw
chart-Gram/PDE hypotheses to those bundled restriction theorems, installation
of all required manifold/compact/connected instances on each component
subtype, and the final componentwise equality lift.  Hence component
localization is a credible way to respect the unchanged statement, but not a
one-line discharge of the current `ConnectedSpace` restriction.

A second, potentially shorter repair avoids global intrinsic geodesics.  The
chart-fixed `expMap g p` itself has `expMap_zero` and
`mfderiv_expMap_at_zero` without `[ConnectedSpace M]`.  The hard proofs of
`diagExp_contMDiffAt_zero` already factor the moving-base map through the local
chart geodesic flow; connectedness enters through the choice to identify that
local branch with the globally defined `expMapIntrinsic`.  Therefore one may
define only the local-addition germ
`u |-> (u.proj, expMap gBase u.proj u.snd)` and port the same chart-flow
factorization/unipotent IFT to it.  This would avoid componentwise gluing and is
not a new class or atlas.  No such moving-base chart-fixed theorem currently
exists, however, so this remains a real producer rather than an available API.

The DeTurck sign is settled independently of that missing existence theorem:
`deTurckVF g g_bg` is the `g`-trace of
`nabla(g) - nabla(g_bg)`, so the tension field of the identity map
`(M,g) -> (M,g_bg)` is its negative.  The textbook HMF convention
`partial_t psi = -W(h,g_bg) composed with psi` therefore has exactly the sign
consumed by source-written `symm_gauge_vel` after inversion.

The independent topology brick described above is now source-written in
`NearIdentity.lean`, including the disconnected componentwise-surjectivity
argument.  It still does not supply the uniform local injectivity cover; that
input must come from the parametric `C1` inverse-function argument for the HMF
solution family.  The same parametric inverse-function argument must also
produce the `IsLocalDiffeomorphOn` hypothesis of `joint_symm_smoothOn` for the
time-preserving total map.  Mathlib currently proves that a local
diffeomorphism has invertible `mfderiv`, but its manifold
`LocalDiffeomorph.lean` explicitly lists the converse inverse-function theorem
as a TODO, so this implication is not an existing one-line API.

## Honest progress

- The three metric-pullback cancellation identities: 100% focused-verified
  before the later expansion.
- Inverse-evaluation regularity, inverse velocity, and identity-gauge bricks:
  source-written, 0% accepted until the short-build-path focused check passes.
- Conditional reverse gauge identity `ricci_pullback_DT`: source-written, 0%
  accepted until the same focused check passes.
- Harmonic-map heat-flow existence and diffeomorphism preservation: 0%.
- Exact `ricci_flow_forward_unique`: 0%.
