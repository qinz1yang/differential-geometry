# RicciFlow LaTeX Theorem Status

Source: `RicciFlow/main.tex`.

Numbering note: the LaTeX file uses one shared theorem counter per section for
theorems, lemmas, propositions, corollaries, definitions, assumptions,
black boxes, and remarks.  This is why the Bochner statements in the appendix
are numbered `14.18`, `14.19`, and `14.22`: earlier definitions and remarks in
Section 14 also increment the counter.

Distance scale:

- `0`: native `RicciFlower` theorem is closed.
- `1`: essentially done; needs a presentation wrapper or small compatibility theorem.
- `2`: finite-sum/component consumer work remains.
- `3`: real geometric producer remains, such as Ricci identity, Bianchi,
  curvature construction, or metric-compatibility product rule.
- `4`: major analytic/global Ricci-flow infrastructure remains, or only the
  old synthetic route exists.
- `5`: deliberate black box or external-scale theorem for now.

## Current Dashboard

Start here when deciding what to work on next.  The detailed ledger below keeps
the full statements, theorem names, and file locations.

| Distance | Count | Current interpretation |
| --- | ---: | --- |
| `0` | 21 | Native theorem closed; only presentation wrappers or downstream use remain. |
| `1` | 0 | A checked consumer route remains one finite-sum/convention producer away. |
| `2` | 1 | In-tree component or finite-sum producer work remains. |
| `3` | 4 | A real geometric producer is still missing. |
| `4` | 16 | Major analytic/global Ricci-flow infrastructure or old synthetic route remains. |
| `5` | 11 | Deliberate black box or external-scale theorem for now. |

### Closed Native Results

| Area | Closed targets |
| --- | --- |
| Hamilton Section 6 evolution inputs | Lemma 6.1 inverse metric; Lemma 6.2 Christoffel variation; Lemma 6.3 Ricci evolution in local coordinate-frame component form; Corollary 6.5 Lichnerowicz form; Lemma 6.6 scalar evolution traced from Ricci evolution. |
| Maximum principle and 3D algebra | Theorem 7.1 scalar supersolution WMP; Theorem 7.2 scalar subsolution WMP wrapper; Lemma 8.1 Riemann-from-Ricci component identity. |
| Pinching algebra | Lemma 10.7 Q factorization; Lemma 10.8 eigenvalue lower bound. |
| Appendix tensor/calculus | Lemma 14.2; Lemma 14.10; Theorem 14.12; Remark 14.13; Lemma 14.18; Lemma 14.19; Proposition 14.22. |
| Appendix Ricci-flow variation | Lemma 14.23; Corollary 14.24; Definitions 14.25-14.26. |

### Active Native Frontiers

| Target | Distance | Smallest next step |
| --- | ---: | --- |
| Hamilton Section 6 remainder | `2` | Next local target is Lemma 6.7 / trace-free Ricci norm evolution; arbitrary-frame packaging of Lemma 6.3 is optional polish. |
| Lemma 10.5 quotient evolution | `2` | Port the pure scalar quotient algebra to `RicciFlower` if it is still needed by the pinching route. |
| Assumption 3.1 calculus package | `3` | Continue native Bianchi, contracted Bianchi, tensor commutator, and trace/norm infrastructure. |
| Lemma 6.7 | `3` | Prove the pointwise `(0,2)` tensor norm Hessian product rule `Tensor02NormHessianProductInBasis` from metric compatibility; the trace bridge to `Tensor02NormSecondProductInBasis` is now checked. |
| Corollary 11.4 and Lemma 11.15 | `3` | Finish the native 3D curvature/norm comparison and Einstein-space-form bridge. |

### Section 14 Snapshot

The appendix-calculus block through Corollary 14.24 is proof-closed at the
tracked native interfaces.  Remaining Section 14 entries are no longer tensor
calculus frontiers:

| Entries | State |
| --- | --- |
| 14.2, 14.10, 14.12, 14.13 | Tensor, curvature-on-one-forms, covariant Ricci identity, and mixed Ricci component algebra are closed. |
| 14.18, 14.19, 14.22 | Scalar Bochner-side calculus statements are closed at pointwise realized interfaces. |
| 14.23, 14.24, 14.25, 14.26 | Christoffel variation statements are closed; maximal/singular-time definitions are now drawn down. |
| 14.27, 14.29, 14.30 | These are maximal-time, extinction, or singular-time infrastructure questions, not local tensor algebra. |

Layering rule for cleanup work: if a theorem is already distance `0`, do not
move its proof downward into tensor representation internals.  Add only a thin
presentation wrapper unless the public statement itself is mathematically too
weak.

## 2026-05-11 Post-Refactor Update

The refactor moved reusable math out of `RicciFlower/Realized` and into
ordinary `RicciFlower/*` modules. In particular, the main theorem consumers now
live in `Operators.lean`, `RoughLaplacian.lean`, `Tensor/RicciIdentity.lean`,
`Curvature/Components.lean`, `Bianchi.lean`, `ScalarBochner.lean`,
`Bochner.lean`, and `LeviCivita/*.lean`.

This makes several LaTeX targets closer: the remaining work is now mostly
producer proofs, not realization-folder organization. The closest targets are
the scalar Bochner formula, the one-form Ricci identity endpoint,
Levi-Civita Hessian symmetry, the inverse-metric evolution lemma, quotient
evolution algebra, and finite-dimensional curvature algebra.

Detailed closure order and acceptance checks are recorded in
`RicciFlower/LATEX_THEOREM_CLOSURE_PLAN.md`.

## 2026-05-12 Local Closure Update

The scalar weak maximum-principle core is farther along than the earlier status
recorded: `strict_barrier_nonnegative`, the operator Laplacian-minimum input,
the Hessian-trace bridge, and the uniform/weighted value-set Lipschitz cores are
now native. The remaining scalar WMP work is presentation/interface packaging
for the exact LaTeX locally-Lipschitz phrasing.

The dimension-three algebra file now also closes the native eigenvalue form of
Lemma 10.8, `lem:Q-lower-bound`.  New scalar and volume evolution files are
present in the checkout.  The volume-evolution path has now been focused
checked and is recorded in the 2026-05-13 update below.

## 2026-05-13 Volume Evolution Update

The local RicciFlower volume stack now proves the measure/density route needed
for Ricci-flow volume evolution.  The checked native pieces include:

- `Analysis.Volume.FunctionRegularAt_const` and
  `Analysis.Volume.FunctionRegularAt_one`;
- `Analysis.Volume.MetricFamilyRegularAt.of_chartGram_timeDeriv`, the
  explicit `C^1_t C^0_x` chart-Gram bridge;
- `Realized.scalarCurvatureFromRicciTraceInFrame_realizes`;
- `RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar`;
- `RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv`.

Thus the formal statement

```text
d/dt int_M 1 dmu_g(t) = - int_M R dmu_g(t)
```

is native, assuming the supplied metric family satisfies the classical
Ricci-flow metric derivative equation and `MetricFamilyRegularAt`.  The latter
can now be produced from explicit continuous time derivatives of chart Gram
entries, so short-time existence and Ricci-flow analytic improvement are not
part of this volume bridge.

Remaining volume-side work is an optional convenience theorem deriving the
explicit chart-Gram derivative hypothesis from a stronger spacetime `C^1`,
smooth, or analytic metric-family predicate, plus separate maximal-interval
and extinction infrastructure.

## 2026-05-13 One-Form Ricci Identity Update

The Levi-Civita one-form Ricci identity endpoint is now closed natively.  The
checked path is:

- `Connection.oneFormRicciIdentity_algebra`, the RicciFlower-local algebraic
  bracket-form identity;
- `LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`, the intrinsic
  Levi-Civita endpoint used by scalar Bochner;
- `Tensor.oneForm_ricci_trace_comm_of_third_comm`, the trace bridge consumed by
  the rough-Laplacian/Bochner interface.

The proof does not import external `DifferentialGeometry` or synthetic modules.
It uses smooth vector-field extensions, the realized moving-slot formula for
one-forms, Levi-Civita torsion-freeness, curvature realization, and one-form
linearity through `cotangentToDual`.

This closes the one-form Ricci identity producer for the Levi-Civita scalar
Bochner path.  The separate Ricci-tensor contracted commutator/Bianchi package
needed for Hamilton Section 6 Ricci evolution is now closed along the local
coordinate-frame Lemma 6.3 route.

## Detailed Ledger

Use this section for the exact statement, current theorem names, file locations,
and next action for each LaTeX item.

### Theorem 2.1, `thm:main-hamilton-3d`

Statement:

```text
If M^3 is closed, connected, and smooth, and M admits a Riemannian metric
g0 with Ric(g0) > 0, then M admits a metric of constant positive sectional
curvature. Equivalently, M is diffeomorphic to a spherical space form.
```

Status: old synthetic assembly exists as `wordly_latex_thm_main_hamilton_3d`.
There is no native unconditional `RicciFlower` theorem yet.

Distance: `5`.

Next target: replace the typed synthetic assembly by concrete Ricci-flow
solution data, analytic inputs, realized curvature, and pinching/convergence
theorems.

### Assumption 3.1, `ass:riemannian-calculus`

Statement:

```text
Assume standard smooth Riemannian tensor calculus: Levi-Civita connection,
extension of nabla to tensors, torsion-free and metric-compatible properties,
Rm from commutators, Ricci and scalar curvature as contractions, Rm symmetries,
Bianchi identities, tensor commutator identities, norms, traces, divergences,
contractions, and rough Laplacian Delta T = g^{ij} nabla_i nabla_j T.
```

Status: partially native.  Relevant files include
`RicciFlower/Realized/Connection.lean`,
`RicciFlower/Realized/Curvature.lean`,
`RicciFlower/Realized/CurvatureTensor.lean`,
`RicciFlower/Realized/CurvatureComponents.lean`,
`RicciFlower/Tensor/RSTensor/NablaOnTensors.lean`, and tensor metric files.

Distance: `3`.

Next target: close tensor Ricci identity, Bianchi/contracted Bianchi, curvature
section producers, and intrinsic tensor rough Laplacian.

### Black Box 4.2, `bb:strictly-parabolic-short-time`

Statement:

```text
A smooth strictly parabolic system on a closed manifold with smooth initial
data has a smooth short-time solution, unique in the appropriate parabolic
class.
```

Status: explicit analytic black box in the old synthetic route.

Distance: `5`.

Next target: keep as black box unless the project expands to parabolic PDE
existence.

### Theorem 4.3, `thm:rf-short-time-existence`

Statement:

```text
For every smooth Riemannian metric g0 on a closed manifold M, there exists
T > 0 and a smooth Ricci flow g(t) on [0,T) with g(0) = g0.
```

Status: old synthetic wrapper `wordly_latex_thm_rf_short_time_existence`;
native `RicciFlower/Realized/RicciFlow.lean` has solution interfaces, not the
DeTurck existence theorem.

Distance: `5`.

Next target: build a concrete DeTurck wrapper around the analytic black box and
the realized Ricci-flow solution structure.

### Black Box 5.1, `bb:maximal-rf-interval`

Statement:

```text
Starting from any smooth metric on a closed manifold, there is a unique maximal
Ricci flow g(t), t in [0,Tmax), agreeing with every other flow on common
domains and admitting no smooth extension past Tmax.
```

Status: old synthetic maximal-flow interfaces only.

Distance: `5`.

Next target: concrete maximal-interval construction, uniqueness, and terminal
time API.

### Lemma 6.1, `lem:evol-inverse-metric`

Statement:

```text
Along Ricci flow, partial_t g^{ij} = 2 Ric^{ij}.
```

Status: closed natively as `RicciFlow.evol_inverse_metric_inFrame` in
`RicciFlower/RicciFlow/Evolution/Metric.lean`, using the existing
inverse-identity differentiation theorem.

Distance: `0`.

Next target: use this theorem as the inverse-metric input for later Ricci-norm
and raised-index evolution identities.

### Lemma 6.2, `lem:evol-christoffel`

Statement:

```text
Along Ricci flow,
partial_t Gamma^k_ij =
- g^{kl} (nabla_i Ric_jl + nabla_j Ric_il - nabla_l Ric_ij).
```

Status: closed in native fixed-frame component form by
`RicciFlow.evol_christoffel_inFrame`, which projects the checked
spacetime-smooth Christoffel evolution producer to the displayed Ricci-flow RHS.

Distance: `0`.

Next target: use this as the Christoffel-variation input for Ricci and
curvature evolution identities.

### Lemma 6.3, `lem:evol-ricci`

Statement:

```text
Along Ricci flow,
partial_t Ric_ij = Delta Ric_ij + 2 R_ikjl Ric^{kl}
  - 2 Ric_i^k Ric_kj.
Equivalently,
(partial_t - Delta) Ric_ij = 2 R_ikjl Ric^{kl} - 2 Ric_i^k Ric_kj.
```

Status: closed in local coordinate-frame component form in
`RicciFlower/RicciFlow/Evolution/Ricci.lean` by
`RicciFlow.evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators`.
The older fixed-frame consumer
`RicciFlow.evol_ricci_inFrame_of_variation_commutators` remains available for
compatibility when the Ricci variation formula is supplied directly.  The
component substitution
`christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame`
checks, and the contracted commutator/Bianchi producer now checks through
`RicciFlow.RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_tensor0S_ricciIdentity`.
The singleton coordinate-frame Ricci variation producer now checks through
`RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2`,
which differentiates the Christoffel Ricci trace formula, consumes Lemma 6.2
Christoffel evolution, and substitutes `nabla A = nabla^2 Ric`.

Distance: `0`.

Optional follow-up: package the singleton coordinate-frame producer into a
fully arbitrary-frame interface.  If that route must produce the mixed
Christoffel regularity input rather than assume it, derive
`ChristoffelVariationMixedDerivativeInFrameOn` from a spacetime-smooth
Christoffel or metric regularity package.

### Corollary 6.5, `cor:ricci-lichnerowicz`

Statement:

```text
Along Ricci flow, partial_t Ric = Delta_L Ric.
```

Status: closed in fixed-frame component form in
`RicciFlower/RicciFlow/Evolution/Ricci.lean` by
`RicciFlow.ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm`.
The file defines the Ricci-specialized Lichnerowicz RHS, proves the two Ricci
action terms specialize to the quadratic term using Ricci symmetry and inverse
metric symmetry, and rewrites the closed component Ricci evolution theorem into
`RicciLichnerowiczEquationInFrame`.  The coordinate-frame display wrapper
`RicciFlow.evol_ricci_lichnerowicz_coordFrameAt_of_christoffelEvolution_nabla2_commutators`
exposes the same result directly from the native coordinate-frame Lemma 6.3
producer.

Distance: `0`.

Next target: no active Corollary 6.5 work remains.

### Lemma 6.6, `lem:evol-scalar`

Statement:

```text
Along Ricci flow, partial_t R = Delta R + 2 |Ric|^2.
Equivalently, (partial_t - Delta) R = 2 |Ric|^2.
```

Status: closed as a trace-route theorem from Ricci evolution in
`RicciFlower/RicciFlow/Evolution/Scalar.lean`.  The theorem
`RicciFlow.scalarEvolutionEquationOn_of_ricciEvolution`
differentiates `R = g^{ij} Ric_ij`, consumes inverse-metric evolution and
Ricci evolution as `RicciEvolutionEquationInFrame`, and returns
`ScalarEvolutionEquationOn` for the canonical scalar trace and canonical traced
rough-Ricci Laplacian.  The separate scalar-trace, scalar-Laplacian-trace, and
curvature-trace inputs are discharged: `ScalarRmRicciTraceInFrame` is produced
internally by `RicciFlow.scalarRmRicciTraceInFrame_of_rm04_first_trace`, using
the curvature-layer identity
`Realized.metricTrace_rm04RicciContractionAt_eq_neg_inner`.

Distance: `0`.

Next target: no scalar trace algebra remains.  Optional polish is a convenience
wrapper that feeds the local coordinate-frame Lemma 6.3 theorem directly into
the scalar evolution route.

### Lemma 6.7, `lem:evol-ricci-norm`

Statement:

```text
Along Ricci flow,
(partial_t - Delta) |Ric|^2 =
-2 |nabla Ric|^2 + 4 R_ikjl Ric^{ij} Ric^{kl}.
```

Status: the time-derivative side is closed canonically in
`RicciFlow.ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical`.
The Laplacian side now has the exact coordinate expansion frontier
`Realized.RicciNormScalarLaplacianExpansionInFrame` and the producer
`Realized.ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion`.
The realized Bochner layer also has
`Realized.ricciNormScalarLaplacianExpansionInFrame_of_tensor02_product_rule`,
which reduces that exact expansion to the named `(0,2)` tensor norm product
rule `Realized.Tensor02NormSecondProductInBasis`.
The trace bridge
`Realized.Tensor02NormSecondProductInBasis.of_hessian_product` is checked: it
traces the pointwise `(0,2)` Hessian product rule and uses
`RoughLap0SRealizesMetricTraceInBasis` to replace the traced second derivative
by the supplied rough tensor.
The folder-level consumer
`RicciFlow.ricciNormHeatEquationOn_of_solution_canonical_laplacian` assembles
Lemma 6.7 from the closed time side and that exact Bochner expansion.

Distance: `3`.

Next target: prove `Tensor02NormHessianProductInBasis` from metric
compatibility.  The missing local API is the `(0,2)` tensor inner-product
derivative rule
`X <A,B> = <nabla_X A,B> + <A,nabla_X B>`, followed by one more derivative and
the Hessian correction.  The exact helper is now stated in
`Bochner.lean` as `Realized.tensor02_inner_extDerivFun_eq_inner_nabla`; its
proof is the remaining frontier.  This is a real tensor Bochner producer/API
theorem, not finite-sum algebra or Ricci-evolution work.  After it closes, feed
it through the existing trace bridge, mark Lemma 6.7 distance `0`, and then
repeat the pattern for the trace-free Ricci norm evolution needed by Hamilton's
pinching argument.

### Theorem 7.1, `thm:scalar-wmp-super`

Statement:

```text
For a scalar supersolution
partial_t u >= Delta_g(t) u + <X, grad u> + F(u,t),
with F locally Lipschitz and nondecreasing in u, comparison with the ODE
c' = F(c,t) preserves u >= c.
```

Status: closed natively as
`Realized.scalar_wmp_super_theorem_7_1` in
`RicciFlower/MaximumPrinciple/ScalarWeak.lean`.  The theorem uses the compact
value-set Lipschitz formulation; the book's monotonicity hypothesis is retained
as a book-facing input.  The pointwise calculus identities, compact
strict-barrier argument, operator Laplacian-minimum input, Hessian-trace
bridge, and uniform/weighted value-set Lipschitz variants are proved.

Distance: `0`.

Next target: optional interface refinement from pointwise locally-Lipschitz
time slices to a compact-value or weighted Lipschitz hypothesis.  No active
closure work remains for the proved compact-value theorem.

### Theorem 7.2, `thm:scalar-wmp-sub`

Statement:

```text
For the corresponding subsolution inequality
partial_t u <= Delta_g(t) u + <X, grad u> + F(u,t),
comparison with c' = F(c,t) preserves u <= c.
```

Status: closed natively in `RicciFlower/MaximumPrinciple/ScalarWeak.lean` as
`Realized.scalar_wmp_sub_theorem_7_2`.  The theorem applies the closed
supersolution theorem `scalar_wmp_super_theorem_7_1` to the sign-changed data
`-u`, `-c`, and `fun a t => -F (-a) t`, then translates the conclusion back to
`u <= c`.  Its regularity, parabolic-operator, and Lipschitz hypotheses are
stated for the sign-changed data rather than re-proving those transport lemmas
inside the wrapper.

Distance: `0`.

Next target: optional convenience wrapper transporting the regularity,
operator-linearity, and Lipschitz assumptions from the original `u`, `c`, and
`F` statements automatically.

### Corollary 7.3, `cor:scalar-lower-bound`

Statement:

```text
For Ricci flow on a closed n-manifold, if c0 = inf_M R(.,0), then
R(x,t) >= c0 / (1 - (2/n)c0 t)
while the denominator is positive. In particular, positive initial scalar
curvature remains positive.
```

Status: ODE-comparison layer native in
`RicciFlower/RicciFlow/Evolution/ScalarLowerBound.lean` as
`RicciFlow.scalar_curvature_lower_bound_of_parabolic_inequality`.  The theorem
uses the compact value-set scalar WMP directly, because the square reaction is
not globally monotone on negative scalar values.  The file also records the
all-times scalar-evolution bridge
`RicciFlow.scalar_parabolic_inequality_of_scalarEvolution_allTimes`.

Distance: `2`.

Next target: produce the bundled WMP regularity hypotheses from the eventual
Ricci-flow smoothness API.  Scalar evolution, heat realization, trace/norm
Cauchy-Schwarz, and the compact initial minimum wrapper are now native
producer inputs.

### Corollary 7.4, `cor:positive-scalar-finite-time`

Statement:

```text
If R(g(0)) > 0 on a closed n-manifold, then the maximal existence time
satisfies Tmax <= n / (2 min_M R(g(0))) < infinity.
```

Status: native conditional endpoint theorem in
`RicciFlower/RicciFlow/Evolution/ScalarFiniteTime.lean` as
`RicciFlow.positive_scalar_finite_time_of_scalarEvolution_closedOpen`.  The
real-analysis core proves that the Corollary 7.3 lower barrier is unbounded
before its pole, while scalar continuity bounds the scalar on the compact pole
slab.

Distance: `2`.

Next target: supply the remaining WMP regularity producer from geometric
smoothness data, then add a thin maximal-time compatibility wrapper if desired.

### Theorem 7.5, `thm:hamilton-tensor-wmp`

Statement:

```text
For a symmetric 2-tensor S satisfying
(partial_t - Delta) S_ij >= X^k nabla_k S_ij + N_ij(S,g,t),
if the null-eigenvector condition holds and S(0) >= 0, then S(t) >= 0.
```

Status: detailed LaTeX proof; RicciFlower-native
`Realized.hamilton_tensor_wmp` interface with one explicit analytic frontier.

Distance: `4`.

Next target: prove the analytic tensor maximum-principle frontier, or first
factor it through a general convex-cone/vector-bundle maximum-principle API.

### Black Box 7.6, `bb:scalar-strong-mp`

Statement:

```text
For a complete connected Ricci-flow background with the needed bounded geometry,
a nonnegative scalar supersolution that is not identically zero becomes
strictly positive at later times.
```

Status: synthetic strong maximum-principle interface.

Distance: `5`.

Next target: keep as analytic black box for blow-up limits.

### Lemma 7.7, `lem:limit-scalar-positive`

Statement:

```text
For a complete connected 3D blow-up limit with Ric >= 0, R >= 0, and
R(x0,0) = 1, one has R > 0 on N x (alpha,0].
```

Status: synthetic consumer of scalar strong MP.

Distance: `4`.

Next target: port after the complete-limit Ricci-flow setting and strong MP
interface exist natively.

### Lemma 8.1, `lem:3d-curvature-identities`

Statement:

```text
In dimension 3,
R_ijkl =
  g_ik Ric_jl - g_il Ric_jk
  - g_jk Ric_il + g_jl Ric_ik
  - (R/2)(g_ik g_jl - g_il g_jk).
If Ric has eigenvalues lambda_1, lambda_2, lambda_3, then
K_ij = (lambda_i + lambda_j - lambda_k)/2.
```

Status: native dimension-three component algebra is closed in
`DimensionThree.CurvatureAlgebra`, and the realized Levi-Civita component
wrapper is closed in `DimensionThree.RiemannFromRicci` as
`rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes`.

Distance: `0` for the Riemann-from-Ricci component identity.  The sectional
curvature eigenvalue presentation is still a separate wrapper/API task.

Next target: add the sectional-curvature/eigenvalue wrapper if needed by the
pinching chapter.

### Lemma 9.1, `lem:preserve-ricci-nonnegative`

Statement:

```text
For a closed 3D Ricci flow, Ric(g(0)) >= 0 implies Ric(g(t)) >= 0.
```

Status: synthetic tensor-WMP consumer.

Distance: `4`.

Next target: combine native Ricci evolution, 3D curvature algebra, and tensor
WMP.

### Lemma 9.2, `lem:preserve-ricci-pinching`

Statement:

```text
For 0 <= delta <= 1/3, if Ric(g(0)) >= delta R(g(0)) g(0), then
Ric(g(t)) >= delta R(g(t)) g(t).
```

Status: synthetic tensor-WMP consumer.

Distance: `4`.

Next target: prove shifted tensor reaction algebra and feed tensor WMP.

### Corollary 9.3, `cor:strict-positive-gives-pinching`

Statement:

```text
If M^3 is closed and Ric(g0) > 0, then there exists delta > 0, depending only
on g0, such that Ric(g0) >= delta R(g0) g0. Consequently the same pinching
holds along the Ricci flow from g0.
```

Status: not native.

Distance: `4`.

Next target: compactness of the unit tangent bundle/continuous eigenvalue
minimum plus Lemma 9.2.

### Lemma 10.4, `lem:evol-tracefree-ricci-norm`

Statement:

```text
In dimension 3, along Ricci flow and wherever R > 0,
(partial_t - Delta)|Ric^o|^2 =
  -2 |nabla Ric|^2 + (2/3)|nabla R|^2
  + (4 |Ric|^2 |Ric^o|^2 - 2 Q) / R.
```

Status: synthetic P3/P4 route.

Distance: `4`.

Next target: port trace-free decomposition, scalar evolution, Ricci norm
evolution, and the algebraic reaction reduction.

### Lemma 10.5, `lem:quotient-evolution`

Statement:

```text
For smooth spacetime functions phi >= 0 and psi > 0,
(partial_t - Delta)(phi^alpha / psi^beta)
equals the displayed product/chain-rule expression with gradient-square and
cross-gradient terms.
```

Status: synthetic algebra exists.

Distance: `2`.

Next target: port the pure scalar quotient algebra to `RicciFlower` if needed
by native pinching.

### Lemma 10.6, `lem:evol-pinching-P`

Statement:

```text
For P = |Ric^o|^2 / R^{2-eps}, 0 < eps < 1,
partial_t P =
Delta P + (2(1-eps)/R)<nabla R,nabla P>
- 2 R^{eps-4}|R nabla Ric - nabla R tensor Ric|^2
- eps(1-eps) R^{eps-4}|Ric^o|^2 |nabla R|^2
+ 2 R^{eps-3}(eps |Ric|^2 |Ric^o|^2 - Q).
```

Status: synthetic improved-pinching producer/interface.

Distance: `4`.

Next target: native trace-free Ricci evolution, quotient algebra, and
gradient-square rearrangement.

### Lemma 10.7, `lem:Q-factorization`

Statement:

```text
For Ricci eigenvalues lambda_1, lambda_2, lambda_3 and
R = lambda_1 + lambda_2 + lambda_3,
Q = sum_{i<j} (lambda_i - lambda_j)^2 (R - 2 lambda_k)^2.
```

Status: closed natively as
`DimensionThree.hamiltonCubicQ3_factorized` in
`RicciFlower/DimensionThree/PinchingAlgebra.lean`.

Distance: `0`.

Next target: port the ordered-eigenvalue lower-bound algebra for Lemma 10.8.

### Lemma 10.8, `lem:Q-lower-bound`

Statement:

```text
If R > 0 and Ric >= delta R g with delta > 0, then
Q >= 2 delta^2 |Ric|^2 |Ric^o|^2.
```

Status: closed natively in eigenvalue form as
`DimensionThree.hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues`
in `RicciFlower/DimensionThree/PinchingAlgebra.lean`.

Distance: `0`.

Next target: add the geometric bridge from a Ricci eigenframe and
`Ric >= delta R g` to the ordered-eigenvalue hypotheses, when the downstream
pinching package needs the geometric statement.

### Corollary 10.9, `cor:improved-ricci-pinching`

Statement:

```text
For a closed 3D Ricci flow with Ric(g0) > 0, there exist eps > 0 and C < infinity
depending only on g0 such that |Ric^o|^2 / R^2 <= C R^{-eps}.
```

Status: synthetic P4 wrapper.

Distance: `4`.

Next target: native scalar WMP, pinching evolution, and Q lower bound.

### Lemma 11.1, `lem:finite-time`

Statement:

```text
The maximal Ricci flow starting from a closed 3-manifold with R(g0) > 0 has
finite maximal time, bounded by data from g0.
```

Status: synthetic finite-time wrapper.

Distance: `4`.

Next target: follows natively after Corollary 7.4 and maximal interval API.

### Black Box 11.2, `bb:rf-extension-criterion`

Statement:

```text
If a closed-manifold Ricci flow on [0,T) has sup_{M x [0,T)} |Rm| < infinity,
then it extends smoothly to [0,T+eta).
```

Status: synthetic/global interface.

Distance: `5`.

Next target: keep as global analytic black box.

### Lemma 11.3, `lem:finite-time-curvature-blow-up`

Statement:

```text
For a maximal Ricci flow with finite maximal time Tmax,
sup_{M x [0,Tmax)} |Rm| = infinity.
```

Status: synthetic wrapper around extension criterion.

Distance: `4`.

Next target: native wrapper once maximal interval and extension criterion APIs
are concrete.

### Corollary 11.4, `cor:ricci-controls-rm`

Statement:

```text
There exists a universal constant C3 such that on any 3D Riemannian manifold
with Ric >= 0, |Rm| <= C3 R.
```

Status: synthetic curvature algebra route.

Distance: `3`.

Next target: port 3D sectional-curvature algebra and norm comparison.

### Lemma 11.6, `lem:point-selection-rescaling`

Statement:

```text
For the maximal Ricci flow from a closed 3-manifold with Ric(g0) > 0, there
exist points/times (x_i,t_i), t_i -> Tmax, and R_i = R(x_i,t_i) -> infinity,
such that the parabolically rescaled flows satisfy
R(g^{R_i})(x_i,0) = max_{M x [-R_i t_i,0]} R(g^{R_i}) = 1.
```

Status: synthetic Section 12 interface.

Distance: `4`.

Next target: finite-time scalar blow-up plus concrete point-selection/rescaling.

### Black Box 11.8, `bb:no-local-collapsing`

Statement:

```text
Perelman's no local collapsing theorem: for a closed Ricci flow on [0,T),
there is kappa > 0 such that the flow is kappa-noncollapsed at all scales
controlled by curvature, invariant under parabolic rescaling.
```

Status: black box.

Distance: `5`.

Next target: keep as global analytic/geometric black box.

### Lemma 11.10, `lem:cgh-curvature-convergence`

Statement:

```text
Under smooth pointed Cheeger-Gromov-Hamilton convergence, pulled-back Rm, Ric,
R, |Rm|^2, |Ric|^2, and |Ric^o|^2 converge smoothly on compact subdomains and
compact time subintervals.
```

Status: synthetic convergence interface.

Distance: `5`.

Next target: requires a concrete smooth CGH convergence theory; likely remains
black-box level.

### Corollary 11.11, `cor:cgh-curvature-ratio-convergence`

Statement:

```text
If the CGH limit has R > 0 on a compact spacetime set, then the pulled-back
ratios |Ric^o|^2 / R^2 converge smoothly to the limit ratio there.
```

Status: synthetic wrapper.

Distance: `4`.

Next target: prove as consumer of CGH curvature convergence and positivity of
the scalar limit.

### Black Box 11.12, `bb:cgh-compactness`

Statement:

```text
Hamilton compactness theorem for pointed Ricci flows with uniform local
curvature bounds and basepoint noncollapsing.
```

Status: black box.

Distance: `5`.

Next target: keep as global compactness input.

### Black Box 11.14, `bb:myers`

Statement:

```text
If a complete Riemannian manifold has Ric >= (n-1)k g for k > 0, then it is
compact and has diameter at most pi / sqrt(k).
```

Status: black box in the LaTeX spine.

Distance: `5`.

Next target: possibly use mathlib if available, otherwise keep as global input.

### Lemma 11.15, `lem:3d-einstein-space-form`

Statement:

```text
If (N^3,h) is connected, Ric^o(h) = 0, and R(h) is positive somewhere, then
R(h) is a positive constant and h has constant positive sectional curvature.
```

Status: synthetic algebra route; partial realized curvature objects exist.

Distance: `3`.

Next target: native contracted Bianchi plus 3D Riemann-from-Ricci formula and
sectional-curvature API.

## Appendix Calculus Statements

### Lemma 14.2, `lem:3D Riem as Ricci and R`

Statement:

```text
If n = 3, then
R_ijkl = R_il g_jk - R_jl g_ik - R_ik g_jl + R_jk g_il
  - (1/2) R (g_il g_jk - g_jl g_ik).
```

Status: closed in native component form.  The algebraic heart is
`DimensionThree.displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries`;
the realized Levi-Civita wrapper is
`DimensionThree.rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes`.

Distance: `0` for the pointwise Levi-Civita component statement.

Next target: only presentation wrappers remain, such as replacing the canonical
trace terms by separately supplied Ricci/scalar realization data in a chosen
frame if a downstream theorem needs that exact interface.

### Lemma 14.10, `lem:curvature_on_1forms`

Statement:

```text
(nabla_X nabla_Y omega)(Z) - (nabla_Y nabla_X omega)(Z)
  - (nabla_[X,Y] omega)(Z) = - omega(R(X,Y)Z).
```

Status: closed for the Levi-Civita/RicciFlower scalar-Bochner path by
`LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`, backed by the local
algebraic identity `Connection.oneFormRicciIdentity_algebra`.

Distance: `0` for the Levi-Civita endpoint.

Next target: if needed, generalize the closed Levi-Civita moving-slot proof to
a public smooth-connection theorem with the same explicit
`ContMDiffCovariantDerivativeLocally` hypothesis.

### Theorem 14.12, `thm:ricci_identity`

Statement:

```text
nabla_i nabla_j alpha_{k_1 ... k_s}
- nabla_j nabla_i alpha_{k_1 ... k_s}
= - sum_{q=1}^s sum_m R_{i j k_q}^m
    alpha_{k_1 ... k_{q-1} m k_{q+1} ... k_s}.
```

Status: closed for covariant `(0,s)` tensors in the intrinsic RicciFlower
interface.  The main theorem is
`tensor0S_ricciIdentity_with_torsion`, with torsion-free wrapper
`tensor0S_ricciIdentity_of_torsionFree` and Levi-Civita wrapper
`LeviCivita.tensor0S_ricciIdentity_of_leviCivita`.  The `s = 1` specialization
is checked by `tensor0S_ricciIdentity_one`, equivalent to the closed one-form
identity `OneFormThirdCovDerivCommAt`.

The coordinate component specialization following the displayed proof is
checked as `Realized.tensor0S_ricciIdentity_coordFrame_of_christoffelCurv` in
`RicciFlower/Curvature/Components.lean`.

Distance: `0`.

Next target: presentation only.  Keep the invariant theorem as the producer and
use coordinate specializations as consumers.

### Remark 14.13, mixed `(r,s)` Ricci identity

Statement:

```text
nabla_i nabla_j beta^L_K - nabla_j nabla_i beta^L_K
= sum_p sum_m R^{l_p}_{ijm} beta^{L[p:=m]}_K
  - sum_q sum_m R^m_{ij k_q} beta^L_{K[q:=m]}.
```

Status: component algebra and the coordinate first-product bridge are closed.
`RicciFlower/Tensor/RicciIdentity/MixedComponents.lean` contains the delta-probe
contraction identity, mixed curvature action, second-product contraction
algebra, and `coordDeriv_applyInput_eq_contractUpper` bridge.  The local-frame
normalization
`RicciFlower.Coordinates.constInChart_basisTensor0S_coordFrame` is now proved in
`RicciFlower/Coordinates/NablaComponents/TensorRS.lean`, so fixed-chart
constant upper inputs are identified with coordinate-frame tensor basis inputs.

Distance: `0`.

Next target: presentation or geometric-assembly wrappers only; do not reopen the
mixed Ricci component algebra for this remark unless a stronger public endpoint
is explicitly requested.

### Lemma 14.18, `ex:laplace_u_squared`

Statement:

```text
(1/2) Delta(u^2) = div(u grad u) = u Delta u + |grad u|^2.
```

Status: native theorem `half_laplacian_mul_self` in
`RicciFlower/Realized/Operators.lean`, under explicit differentiability
hypotheses.

Distance: `0`.

Next target: none for the algebraic identity; only improve presentation if
needed.

### Lemma 14.19, `lem:laplace_d_commutator`

Statement:

```text
Delta(du) = d(Delta u) + Ric(du),
where Ric acts on 1-forms by (Ric(alpha))(W) = alpha(Ric(W)).
```

Status: closed as a RicciFlower consumer theorem.  The rough-Laplacian trace
frontiers in `RoughLaplacian.lean` are discharged, and
`roughLap_du_eq_d_lap_add_ric` exposes the final one-form commutator formula
from the pointwise commutator interface.  The Levi-Civita path supplies that
interface through `oneForm_commutator_eval_of_lc`, using the closed
`LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`.

Distance: `0` for the pointwise realized formula with explicit trace/realization
inputs.

Next target: only package a cleaner one-line Levi-Civita wrapper if the book
companion needs the statement without intermediate realization arguments.

### Proposition 14.22, `prop:FundBochnerFormNormSq`

Statement:

```text
For any smooth function u on a Riemannian manifold,
(1/2) Delta |du|^2 =
  <du, d(Delta u)> + |nabla du|^2 + Ric(grad u, grad u).

Equivalently,
(1/2) Delta |grad u|^2 =
  <grad u, grad(Delta u)> + |nabla^(2) u|^2 + Ric(grad u, grad u).
```

Status: closed as a pointwise realized Bochner formula.  Native consumer
theorems include `fundamental_bochner`, `fundamental_bochner_of_terms`,
`fundamental_bochner_of_components`, and the Levi-Civita wrappers in
`RicciFlower/LeviCivita/ScalarBochner.lean`.  The rough-Laplacian trace and
one-form Ricci identity inputs are now produced by named RicciFlower theorems.

Distance: `0` for the pointwise realized formula with explicit realization and
trace inputs.

Next target: presentation cleanup only: expose the most book-like wrapper by
choosing the preferred bundle of realization hypotheses, rather than adding
new mathematics.

### Lemma 14.23, `lem:christoffel_evolution`

Statement:

```text
For a smooth metric family g(t) with h = partial_t g,
partial_t Gamma^k_ij =
  (1/2) g^{kl} (nabla_i h_jl + nabla_j h_il - nabla_l h_ij).
```

Status: closed in fixed local-frame interval-time form by
`RicciFlow.christoffelMetricVariationEquationInFrameOn_of_metricVariation`.
The public RHS is
`RicciFlow.christoffelVariationRHSFromMetricVariationInFrame`, and pointwise
consumers can use `RicciFlow.christoffelMetricVariation_hasDerivWithinAt`.

Distance: `0` for the fixed-frame `HasDerivWithinAt` statement with explicit
metric-variation regularity inputs.

Next target: optional presentation cleanup, such as a full-time `deriv` wrapper
or a bundled spacetime-smooth metric-family producer.

### Corollary 14.24, `cor:christoffel_evolution_RF`

Statement:

```text
Under Ricci flow,
partial_t Gamma^k_ij =
- g^{kl} (nabla_i R_jl + nabla_j R_il - nabla_l R_ij).
```

Status: closed in fixed local-frame interval-time form.  The book-facing
Ricci-flow display theorem is `RicciFlow.evol_christoffel_inFrame`; the older
coordinate interface `ricciFlow_christoffelSymbolEvolution_from_equation`
remains available as a compatibility consumer.

Distance: `0`.

Next target: use this theorem downstream in curvature and Ricci evolution
assembly; no Christoffel variation frontier remains here.

### Definition 14.25, maximal time

Statement:

```text
A Ricci flow on [alpha, omega) is maximal if it does not extend past omega.
```

Status: native definition layer is present in
`RicciFlower/RicciFlow/MaximalTime.lean`.  The interval-flexible solution data
now separates the real-time family from the interval witness:
`RicciFlow.SolutionFamily` stores the metric, connection, and Ricci section
families, while `RicciFlow.SolutionOn D` records metric compatibility on `D`
and preserves the old `S.family` and `S.ricci` accessors.  The maximal-time
file exposes `SolutionAgreesOn`, `ExtendsPastEndpoint`, and
`IsMaximalAtEndpoint`.

Distance: `0` for the definition/interface layer.

Next target: prove the global extension criterion needed to use
`IsMaximalAtEndpoint` in Lemma 14.27.

### Definition 14.26, singular time

Statement:

```text
A Ricci flow on [alpha, omega) forms a singularity at omega if the curvature
norm is unbounded on M x [alpha, omega).
```

Status: native definition layer is present in
`RicciFlower/RicciFlow/MaximalTime.lean` as `FormsSingularityAt`.  The
curvature squared norm is no longer an arbitrary scalar input: the file defines
`curvatureNormSq S Rm04 t x` by the metric-induced `(0,4)` tensor norm
`Tensor0SBundle.normSq0S (S.family.metric t) x 4 ((Rm04 t) x)`, and
`FormsSingularityAt` existentially supplies a lowered Riemann tensor family
realizing the solution curvature.  The same file exposes the 14.27 target
interface `SingularIffMaximalAtEndpoint`.

Distance: `0` for the definition/interface layer.

Next target: prove the bridge from fixed-frame component formulas such as
`rm04NormSqInFrame` to the intrinsic metric-induced `curvatureNormSq`, then
prove the extension-criterion theorem behind Lemma 14.27.

### Lemma 14.27, `lem: sing time iff max time`

Statement:

```text
A finite-endpoint Ricci flow forms a singularity at the endpoint if and only
if it is maximal.
```

Status: native endpoint interface exists as
`RicciFlow.SingularIffMaximalAtEndpoint`, using the definitions from
`RicciFlower/RicciFlow/MaximalTime.lean`.  The singularity side now uses the
metric-induced norm of a realizing lowered Riemann tensor family.  The theorem
itself remains a global extension-criterion frontier, not a tensor or
local-coordinate calculation.

Distance: `4`.

Next target: prove the smooth extension criterion and the two implications
between `FormsSingularityAt` and `IsMaximalAtEndpoint`.

### Lemma 14.29, `lem: vol extinct implies max`

Statement:

```text
If a closed connected Ricci flow becomes volume extinct at a finite time omega,
then the flow is maximal.
```

Status: no native target yet.

Distance: `4`.

Next target: maximal interval infrastructure plus a bridge from the real-valued
`int_M 1 dmu_g(t)` volume evolution theorem to the book's volume-extinction
predicate.

### Lemma 14.30, unlabeled

Statement:

```text
If a Ricci flow becomes volume extinct at finite time omega, then
sup_{M x [alpha,omega)} R = infinity. In particular, it forms a singularity.
```

Status: no native target yet.

Distance: `4`.

Next target: scalar curvature bounds, the volume-extinction-to-blow-up
argument, and the singular/maximal bridge.  The basic total-volume evolution
identity is now native.

## Near-Term Work Queue

Section 14 is no longer a tensor-calculation blocker.  The remaining useful
work is either presentation packaging for already-closed results or the
Hamilton Section 6 norm/pinching evolution pipeline.

1. Add book-facing wrappers for Lemma 14.19 and Proposition 14.22 if the
   current realized statements are too verbose for the companion text.
2. Optionally add a stronger public mixed `(r,s)` coordinate Ricci identity
   wrapper from the existing Remark 14.13 component algebra.  Keep the proof at
   the coordinate/local-frame layer; do not reopen lower-level tensor algebra.
3. Work on Lemma 6.7 and the trace-free Ricci norm evolution by connecting the
   closed Ricci and inverse-metric evolution producers to the finite-sum
   Bochner/Ricci-norm algebra.
4. Treat 14.27, 14.29, and 14.30 as maximal-time or singular-time
   infrastructure, not appendix tensor-calculus cleanup.
