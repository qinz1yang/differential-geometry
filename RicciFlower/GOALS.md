# Hamilton Positive Ricci Formalization Plan

This is the RicciFlower plan for proving Hamilton's positive Ricci curvature
theorem in a concrete realized setting. The older synthetic Ricci-flow tree is a
proof map, not a dependency.

## Target Theorem

Concrete geometric theorem:

```text
Let M be a closed smooth 3-manifold. If M admits a smooth Riemannian metric
with positive Ricci curvature, then M admits a smooth Riemannian metric with
constant positive sectional curvature.
```

Stronger flow theorem behind it:

```text
Let g0 be a smooth Riemannian metric with positive Ricci curvature on a closed
smooth 3-manifold M. The normalized Ricci flow starting at g0 exists for all
normalized time and converges smoothly, after the standard normalization, to a
metric of constant positive sectional curvature.
```

The first theorem is the final top-level deliverable. The second theorem is the
analytic Ricci-flow theorem that should produce it.

## Concrete Lean Setting

The intended realized context should look like this, modulo exact Mathlib class
names:

```lean
variable {H M : Type*}
variable [TopologicalSpace H] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [FiniteDimensional ℝ H]
variable (I : ModelWithCorners ℝ H H)
variable [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
variable [CompactSpace M] [T2Space M]
variable (h_dim : Module.finrank ℝ H = 3)
variable (g0 : SmoothRiemannianMetric I M)
variable (hRicPos : PositiveRicciMetric I g0)
```

Preferred final statements:

```lean
theorem hamilton_positive_ricci_exists_constant_positive_curvature_metric
    ... :
    ∃ g∞ : SmoothRiemannianMetric I M,
      HasConstantPositiveSectionalCurvature I g∞

theorem normalized_ricci_flow_converges_to_constant_positive_curvature
    ... :
    ∃ S : NormalizedRicciFlowSolution I M,
      S.initialMetric = g0 ∧
      SmoothConvergesToConstantPositiveCurvature S
```

The exact predicates should be defined in RicciFlower, not hidden behind the
old synthetic Section 12 wrappers.

## Current Status

RicciFlower currently has the right project shape but not yet the theorem:

- Dependency isolation is clean:
  `rg -n "^import\s+DifferentialGeometry|DifferentialGeometry\.|Synthetic\." RicciFlower -g "*.lean"`
  returns no matches.
- Realized tensor/vector-bundle files exist under `Tensor/` and
  `VectorBundle/`.
- Realized metric-family, connection, curvature, Ricci-flow, scalar-operator,
  local-frame, and Christoffel interface files exist under `Realized/` and
  `Coordinates/`.
- The scalar weak maximum-principle file exists, with controlled proof holes in
  `MaximumPrinciple/ScalarWeak.lean`.
- The old synthetic branch has substantial Section 12 proof work:
  P1 contracted second Bianchi, P2 3D Riemann-from-Ricci, P3 trace-free Ricci
  norm/cubic reaction, and P4 improved pinching producer. These are reference
  proof routes only.

Important distinction:

- Contracted second Bianchi is proved in the old synthetic stack.
- Contracted second Bianchi is not yet rebuilt as a native RicciFlower realized
  theorem.

## Immediate Goal: Close LaTeX Section 3

Section 3 of `RicciFlow/main.tex` is currently written as
`Assumption [Basic Riemannian tensor calculus]`. The immediate RicciFlower goal
is to replace this assumption by concrete realized code using bundle sections,
tensor bundles, and coordinate/local-frame formulas.

The current RicciFlower tree is now strong enough to make this realistic:

- tensor fields are bundle/section based:
  `Tensor0SField`, `TensorRSField`, `MixedSection`;
- tensor bundle and tensor product infrastructure exists under
  `VectorBundle/`, `Tensor/Product/`, `Tensor/Mixed/`, and `Tensor/RSTensor/`;
- local-frame component evaluation exists in `Coordinates/Tensor.lean`;
- Christoffel symbols and frame component formulas exist in
  `Coordinates/Christoffel.lean`;
- realized metric-family, connection, curvature, and operator interfaces exist
  in `Realized/`;
- covariant derivative model formulas for realized tensor fields exist in
  `Tensor/RSTensor/NablaOnTensors.lean`;
- the tensor/coordinate/realized foundation currently has no active `sorry`;
  the only `rg` hit in that layer is comment text in `VectorBundle/Frame.lean`.

### Section 3 Checklist

| LaTeX Section 3 item | RicciFlower status | Concrete next target |
| --- | --- | --- |
| Levi-Civita connection on vector fields extends to arbitrary tensors, satisfies linearity/Leibniz, and commutes with contractions | Mostly realizable now: `CovariantDerivative`, `RSTensor/NablaOnTensors.lean`, `RSTensor/Contract.lean` | Add RicciFlower-facing theorems for tensor covariant derivative linearity, Leibniz with tensor product, and contraction commutation |
| Torsion-free and metric-compatible, `∇g = 0` | Predicates exist in `Realized/Connection.lean`; metric as `(0,2)` tensor exists in `RSTensor/Metric.lean` | Prove accessors for the chosen Levi-Civita connection and expose `nabla_metric_eq_zero` as a theorem |
| Riemann tensor defined by commutator of covariant derivatives | Interface exists: `connectionRiemannField` in `Realized/Curvature.lean` | Bundle this as a `TensorRSField 1 3` or equivalent curvature section and prove coordinate evaluation |
| Ricci tensor and scalar curvature are contractions of `Rm` | Interfaces exist: `RicciFieldRealizesRiemannTrace`, `ScalarFieldRealizesRicciTrace` | Replace interfaces by realized construction theorems using metric trace/contraction |
| Algebraic symmetries of `Rm`, first and second Bianchi, contracted Bianchi | Old synthetic route proves these; RicciFlower has the objects needed to restate them | Create `Realized/Bianchi.lean`; prove symmetries and Bianchi from torsion-free/metric-compatible connection, then trace to contracted Bianchi |
| Standard commutator identities for covariant derivatives acting on tensors | Model formulas exist in `RSTensor/NablaOnTensors.lean` | State and prove `(0,s)` and `(r,s)` tensor Ricci identities in bundle-section form, with coordinate component wrappers |
| Norms, traces, divergences, contractions, and rough Laplacian `ΔT = g^{ij}∇ᵢ∇ⱼT` | Scalar operators and contractions exist; tensor rough Laplacian is not yet bundled | Add tensor trace/divergence/rough-Laplacian API, then prove local-frame coordinate formulas |

### Immediate Section 3 Files

Create or complete these files before pushing further into global Hamilton
theorems:

- `RicciFlower/Realized/FoundationalCalculus.lean`
  - imports the realized tensor, metric, connection, curvature, and coordinate
    layers;
  - states the Section 3 replacement theorem package;
  - contains no analytic/global `sorry`.
- `RicciFlower/Realized/Bianchi.lean`
  - second Bianchi;
  - lowered second Bianchi;
  - contracted second Bianchi.
- `RicciFlower/RicciFlow/Evolution/Commutators.lean`
  - Ricci identities for tensor fields;
  - coordinate component versions.
- `RicciFlower/RicciFlow/Evolution/RoughLaplacian.lean`
  - tensor rough Laplacian;
  - trace/divergence compatibility.
- `RicciFlower/wordlyLatex.lean`
  - presentation table for the main LaTeX file;
  - Section 3 rows should move from `assumption` to `proved` or
    `in progress`, not `analytic input`.

### Section 3 Definition Of Done

The LaTeX assumption is closed in RicciFlower when there is a theorem package,
for example:

```lean
structure BasicRiemannianTensorCalculusRealized
    (I : ModelWithCorners ℝ H H) (M : Type*) where
  nabla_tensor_linear : Prop
  nabla_tensor_leibniz : Prop
  nabla_commutes_with_contraction : Prop
  torsion_free : Prop
  metric_compatible : Prop
  riemann_commutator_formula : Prop
  ricci_is_trace_riemann : Prop
  scalar_is_trace_ricci : Prop
  riemann_symmetries : Prop
  first_bianchi : Prop
  second_bianchi : Prop
  contracted_bianchi : Prop
  tensor_ricci_identities : Prop
  tensor_rough_laplacian_defined : Prop
```

The actual fields should be theorem statements with concrete types, not
permanent `Prop` placeholders. The structure above is only the checklist shape:
each row should become a real theorem over bundle sections and local-frame
components.

## Main Dependency Ladder

### G0. Realized Foundation

Goal: make the geometric objects concrete enough that later identities are
about sections of actual tangent/tensor bundles.

Needed:

- tangent bundle sections and local frames;
- `Tensor0SField`, `TensorRSField`, and mixed tensor-field interfaces;
- tensor evaluation in frames;
- contraction and metric trace;
- metric raising/lowering;
- tensor product compatibility;
- smoothness predicates for tensor fields and tensor operations.

Work sites:

- `RicciFlower/VectorBundle/*`
- `RicciFlower/Tensor/*`
- `RicciFlower/Coordinates/Tensor.lean`

Do not reintroduce fixed-vector-space synthetic `TensorData` as the public
foundation.

### G1. Metric, Operators, And Compact Minimum Calculus

Goal: finish the scalar differential operators needed by maximum principles and
curvature evolution.

Needed definitions:

- gradient;
- divergence;
- Laplacian `Δ f = div (grad f)`;
- drift term `<X, grad f>`;
- heat operator with drift.

Needed local facts:

- gradient of constants;
- divergence of zero;
- Laplacian of constants;
- gradient vanishes at a spatial minimum;
- drift term vanishes at a spatial minimum;
- Laplacian is nonnegative at a spatial minimum;
- heat operator with drift has the correct sign at a spatial minimum.

Work sites:

- `RicciFlower/Realized/Operators.lean`
- `RicciFlower/MaximumPrinciple/ScalarWeak.lean`

### G2. Levi-Civita Connection And Curvature From Connection

Goal: curvature must be realized from the Levi-Civita connection of the metric,
not carried as an arbitrary field.

Needed:

- realized predicates for metric compatibility and torsion-free;
- theorem that the chosen connection is Levi-Civita;
- Riemann curvature from the connection;
- Ricci curvature as the trace of Riemann;
- scalar curvature as metric trace of Ricci;
- sectional curvature and constant positive sectional curvature.

Work sites:

- `RicciFlower/Realized/Connection.lean`
- `RicciFlower/Realized/Curvature.lean`
- future `RicciFlower/Realized/SectionalCurvature.lean`

### G3. Contracted Second Bianchi In RicciFlower

Goal: rebuild

```text
div Ric = (1 / 2) grad R
```

for the realized Levi-Civita connection.

Old proof map:

- vector second Bianchi;
- lower the curvature tensor with the metric;
- trace the second Bianchi identity twice;
- use metric compatibility and trace/Fubini rules;
- identify the divergence-of-Ricci term and scalar-gradient term.

Old reference files:

- `DifferentialGeometry/Synthetic/Geometry/Connection.lean`
- `DifferentialGeometry/Synthetic/Geometry/CurvatureContractions.lean`
- `DifferentialGeometry/Synthetic/Algebra/MetricTrace.lean`
- `DifferentialGeometry/Synthetic/Realization/MetricTraceFubini.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean`

RicciFlower target file:

- future `RicciFlower/Realized/Bianchi.lean`

This is a midterm goal. It should not be replaced by an assumption in the final
Hamilton theorem.

### G4. Short-Time And Maximal Ricci Flow

Goal: start the unnormalized Ricci flow from `g0`.

The mathematical theorem is analytic/global. It may be represented first as a
precise high-level theorem with controlled `sorry` only after the local realized
objects are correctly stated.

Needed:

- short-time existence and uniqueness from a smooth initial metric;
- maximal interval construction;
- extension criterion by curvature bounds;
- finite-time singularity for positive scalar/positive Ricci initial data in
  the unnormalized flow;
- normalized flow construction by time-dependent scaling.

Work sites:

- future `RicciFlower/Global/Existence.lean`
- future `RicciFlower/Realized/NormalizedRicciFlow.lean`

### G5. Ricci-Flow Evolution Equations

Goal: prove local evolution identities along Ricci flow.

Order:

1. metric variation: `∂t g = -2 Ric`;
2. inverse metric evolution;
3. connection/Christoffel evolution;
4. Riemann evolution;
5. Ricci evolution;
6. scalar curvature evolution;
7. `|Ric|^2` and `|Ric^0|^2` evolution;
8. quotient and pinching quantities.

Hamilton Section 6 status on 2026-05-15:

- The Ricci-flow equation itself is part of the solution interface.
- Lemma 6.1 inverse-metric evolution is closed by
  `RicciFlow.evol_inverse_metric_inFrame`.
- Lemma 6.2 Christoffel evolution is closed by
  `RicciFlow.evol_christoffel_inFrame`.
- Lemma 6.3 Ricci evolution is closed in local coordinate-frame component form
  by
  `RicciFlow.evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators`.
  Arbitrary-frame packaging is optional polish, not the next mathematical
  blocker.
- Lemma 6.6 scalar evolution is closed as a trace-route theorem in
  `RicciFlow/Evolution/Scalar.lean`; a convenience wrapper can later feed the
  coordinate-frame Lemma 6.3 producer directly into that theorem.
- Corollary 6.5 Lichnerowicz presentation is closed in fixed-frame component
  form by
  `RicciFlow.ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm`;
  the coordinate-frame exposure theorem is
  `RicciFlow.evol_ricci_lichnerowicz_coordFrameAt_of_christoffelEvolution_nabla2_commutators`.
- The remaining Hamilton Section 6 work is Riemann evolution packaging,
  Lemma 6.7 Ricci-norm evolution, the trace-free Ricci norm evolution, and
  then the quotient/pinching quantities.

Old reference files:

- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`
- `Evolution/RiemannEvolution.lean`
- `Evolution/RicciFromRiemann.lean`
- `Evolution/ScalarCurvature.lean`
- `Evolution/RicciNorm.lean`

RicciFlower target files:

- `RicciFlower/RicciFlow/Evolution/Metric.lean`
- `RicciFlower/RicciFlow/Evolution/Connection.lean`
- future `RicciFlower/RicciFlow/Evolution/Riemann.lean`
- `RicciFlower/RicciFlow/Evolution/Ricci.lean`
- `RicciFlower/RicciFlow/Evolution/Scalar.lean`
- future `RicciFlower/RicciFlow/Evolution/Norms.lean`

### G6. Maximum Principles

Goal: prove the maximum principles used by Hamilton's argument.

Needed:

- scalar weak maximum principle with drift, Hamilton Theorem 7.1;
- tensor maximum principle for preservation of positive Ricci;
- ODE comparison in the curvature cone/eigenvalue setting.

Work sites:

- `RicciFlower/MaximumPrinciple/ScalarWeak.lean`
- future `RicciFlower/MaximumPrinciple/Tensor.lean`

Do not start Section 12 consumers until the scalar weak maximum principle is
usable and the tensor maximum-principle interface is concretely stated.

### G7. Positive Ricci Preservation And Curvature Pinching

Goal: prove the dimension-three Hamilton pinching package needed for convergence.

Needed:

- positive Ricci cone is preserved under the 3D Ricci-flow curvature ODE/PDE;
- scalar curvature stays positive;
- Section 12 improved pinching quantity;
- algebraic lower bound for Hamilton's cubic `Q`;
- improved pinching estimate;
- trace-free Ricci ratio tends to zero after normalization/rescaling.

Old reference files:

- `DimensionThree/RiemannFromRicci3D.lean`
- `DimensionThree/CurvatureAlgebra.lean`
- `DimensionThree/RicciReaction.lean`
- `DimensionThree/Pinching.lean`
- `DimensionThree/ImprovedPinching.lean`
- `Global/Compactness.lean`
- `HamiltonThreeManifold.lean`

RicciFlower target files:

- future `RicciFlower/DimensionThree/RiemannFromRicci.lean`
- future `RicciFlower/DimensionThree/CurvatureAlgebra.lean`
- future `RicciFlower/DimensionThree/Pinching.lean`
- future `RicciFlower/DimensionThree/ImprovedPinching.lean`

### G8. Convergence To Constant Positive Curvature

Goal: assemble the analytic convergence theorem.

Needed:

- normalized flow exists for all normalized time;
- curvature remains positive and controlled after normalization;
- improved pinching gives `Ric^0 -> 0`;
- scalar curvature normalization controls the trace part;
- Riemann-from-Ricci in dimension three turns `Ric^0 -> 0` into constant
  positive sectional curvature in the limit;
- smooth compactness/convergence upgrades pointwise tensor convergence to a
  smooth limiting metric.

Work sites:

- future `RicciFlower/Global/Compactness.lean`
- future `RicciFlower/HamiltonPositiveRicci.lean`

## Formalization Phases

### Phase 1: Plan And Interfaces

Deliverables:

- this plan;
- concrete predicates:
  `PositiveRicciMetric`, `HasConstantPositiveSectionalCurvature`,
  `ClosedThreeManifoldSetting`, `NormalizedRicciFlowSolution`,
  `SmoothConvergesToConstantPositiveCurvature`;
- no proof-heavy global theorem yet.

### Phase 2: Local Calculus

Deliverables:

- finish operator minimum lemmas;
- finish scalar weak maximum-principle core;
- define sectional curvature and constant positive curvature;
- rebuild contracted second Bianchi in RicciFlower.

### Phase 3: Evolution Stack

Deliverables:

- metric, inverse metric, Christoffel, Riemann, Ricci, scalar, and norm
  evolution in realized form;
- coordinate wrappers only after invariant statements exist.

### Phase 4: Dimension-Three Algebra And Pinching

Deliverables:

- 3D Riemann-from-Ricci;
- positive Ricci cone algebra;
- cubic reaction lower bound;
- improved pinching quotient evolution;
- trace-free Ricci limit-zero theorem.

### Phase 5: Global Analytic Assembly

Deliverables:

- short-time/maximal/normalized-flow global interfaces with precise statements;
- tensor maximum principle;
- compactness/convergence interface;
- final positive Ricci theorem.

## Analytic Layer Skeleton

The analytic layer should be explicit code, not prose-only. It is acceptable for
the first pass to contain precise theorem-shaped `sorry`s for global PDE facts,
provided the statements are concrete and the downstream assembly theorems prove
what they can from those assumptions.

Planned files:

- `RicciFlower/Global/Existence.lean`
- `RicciFlower/Global/ExtensionCriterion.lean`
- `RicciFlower/Global/MaximumPrinciple.lean`
- `RicciFlower/Global/Compactness.lean`
- `RicciFlower/Global/Normalization.lean`
- `RicciFlower/HamiltonPositiveRicci.lean`
- optional presentation spine:
  `RicciFlower/wordlyLatex.lean`

The planned style is the same as the main LaTeX-facing file in the synthetic
tree: state each mathematical theorem in a concrete setting, mark whether it is
proved, assumed as an analytic input, or proved as a consumer of previous
inputs, and keep the dependency list next to the theorem.

### Analytic Input Shape

The first layer should introduce concrete theorem statements such as:

```lean
/-- Analytic input: short-time existence for Ricci flow from a smooth initial
metric on a closed manifold. This is global PDE theory, not tensor algebra. -/
theorem short_time_existence_from_smooth_metric
    (setting : ClosedManifoldSetting I M)
    (g0 : SmoothRiemannianMetric I M) :
    ∃ S : RealizedRicciFlowSolutionOnInterval I M,
      S.initialMetric = g0 ∧ S.existsForPositiveTime := by
  sorry

/-- Analytic input: maximal extension criterion by curvature bounds. -/
theorem ricci_flow_extension_criterion
    (S : RealizedRicciFlowSolutionOnInterval I M) :
    CurvatureBoundedUpToEndpoint S -> ExtendablePastEndpoint S := by
  sorry

/-- Analytic input: Hamilton compactness for normalized or rescaled flows. -/
theorem hamilton_compactness_for_normalized_flows
    (seq : NormalizedPointedRicciFlowSequence I M) :
    CompactnessHypotheses seq ->
      ∃ limit : SmoothRicciFlowLimit I, SmoothCGHConvergesTo seq limit := by
  sorry
```

These `sorry`s are allowed only because the statements are global analytic
theorems. They should not be used to hide local tensor identities, curvature
contractions, 3D algebra, or evolution calculations.

### Assumption-Driven Consumers

Once the analytic input statements exist, we should also write consumer
theorems that prove partial results from explicit assumptions. These should
usually be sorry-free assembly proofs.

Examples:

```lean
/-- Consumer theorem: short-time existence plus the extension criterion gives a
maximal-flow alternative. This should be proved from the two named inputs. -/
theorem maximal_flow_alternative_from_extension_criterion
    (S : RealizedRicciFlowSolutionOnInterval I M)
    (hExt : RicciFlowExtensionCriterion S) :
    LongTimeSolution S ∨ FiniteSingularEndpoint S := by
  -- expected proof: unfold the definitions and use `hExt`.
  ...

/-- Consumer theorem: P4 pinching plus compactness gives a constant-curvature
limit. This should be an assembly theorem once the named hypotheses are
available. -/
theorem constant_curvature_limit_from_pinching_and_compactness
    (S : NormalizedRicciFlowSolution I M)
    (hPinch : TracefreeRicciRatioTendsToZero S)
    (hScalar : NormalizedScalarBounds S)
    (hCompact : SmoothCompactnessConclusion S) :
    ∃ g∞ : SmoothRiemannianMetric I M,
      HasConstantPositiveSectionalCurvature I g∞ := by
  -- expected proof: extract the smooth limit, use trace-free Ricci limit zero,
  -- recover Einstein, then use 3D Riemann-from-Ricci.
  ...
```

This separation matters: the global PDE theorem may remain `sorry` for a while,
but the algebraic and logical handoffs should become real Lean proofs as soon
as their hypotheses are explicitly available.

### Presentation Spine

`RicciFlower/wordlyLatex.lean` should eventually mirror the theorem order of the
main LaTeX proof:

1. short-time existence;
2. scalar and tensor maximum principles;
3. preservation of positive Ricci;
4. evolution equations;
5. contracted second Bianchi;
6. 3D Riemann-from-Ricci;
7. trace-free Ricci norm evolution;
8. improved pinching quotient;
9. algebraic `Q` lower bound;
10. improved pinching estimate;
11. compactness and limit extraction;
12. final positive Ricci theorem.

Each row should say one of:

- `proved`: Lean proof in RicciFlower;
- `proved consumer`: follows from explicit named inputs;
- `analytic input`: theorem-shaped global PDE fact, currently allowed to use
  `sorry`;
- `not started`: no concrete statement yet.

## Black-Box Policy

Local tensor calculus, curvature contractions, dimension-three algebra, and
evolution identities should be proved in RicciFlower.

The following may initially be theorem-shaped high-level analytic inputs with
controlled `sorry`, after the precise realized statement is written:

- short-time existence and uniqueness;
- maximal interval construction;
- extension criterion;
- tensor maximum principle if the cone/PDE infrastructure is not ready;
- Hamilton compactness/smooth convergence;
- normalized-flow global convergence extraction.

Do not use `axiom` or `admit`.

## Post-Hamilton Global Topology TODO

After the Hamilton positive-Ricci theorem path is closed, return to the global
topology and covering-space layer.  In particular, formalize how Ricci flow
lifts to covering spaces and descends through quotients, and connect that with
the spherical-space-form endpoint.  This should not block the current
Hamilton proof pipeline, but it is part of the eventual global-geometry story:
constant-curvature metrics, quotient models, finite covers, and lifted Ricci
flows should be related by explicit theorem statements rather than informal
topological handoffs.

## Immediate Next Work

1. Close the LaTeX Section 3 assumption as a realized theorem package:
   `RicciFlower/Realized/FoundationalCalculus.lean`.
2. Re-export the existing tensor covariant-derivative model formulas through
   RicciFlower-facing theorem names in `Tensor/RSTensor/NablaOnTensors.lean`.
3. Start `RicciFlower/Realized/Bianchi.lean` from the old contracted-Bianchi
   proof route, but using bundle sections and coordinate components.
4. Add tensor rough Laplacian and tensor commutator APIs:
   `RicciFlower/RicciFlow/Evolution/RoughLaplacian.lean` and
   `RicciFlower/RicciFlow/Evolution/Commutators.lean`.
5. Create the concrete theorem-statement file:
   `RicciFlower/HamiltonPositiveRicci.lean`.
6. Define the theorem-facing predicates without proving the theorem yet.
7. Add `RicciFlower/Realized/SectionalCurvature.lean`.
8. Close the remaining operator minimum lemmas in
   `RicciFlower/Realized/Operators.lean`.
9. Continue `MaximumPrinciple/ScalarWeak.lean` until the supplied-Lipschitz
   core theorem checks.

## Narrow Checks

Use narrow checks first:

```powershell
lake env lean RicciFlower\Tensor\RSTensor\NablaOnTensors.lean
lake env lean RicciFlower\Coordinates\Tensor.lean
lake env lean RicciFlower\Coordinates\Christoffel.lean
lake env lean RicciFlower\Realized\Connection.lean
lake env lean RicciFlower\Realized\Curvature.lean
lake env lean RicciFlower\Realized\Operators.lean
lake env lean RicciFlower\MaximumPrinciple\ScalarWeak.lean
lake env lean RicciFlower.lean
```

Boundary checks:

```powershell
rg -n "^import\s+DifferentialGeometry|DifferentialGeometry\.|Synthetic\." RicciFlower -g "*.lean"
rg -n "sorry|admit|axiom" RicciFlower -g "*.lean"
```
