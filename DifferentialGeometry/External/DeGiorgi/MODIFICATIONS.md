# Modifications Log

Tracks modifications to the vendored DeGiorgi code (https://github.com/scottnarmstrong/DeGiorgi,
commit `4c1b307`) per Apache License 2.0 §4(b).

## Format

```
### <YYYY-MM-DD> — <short tag>

**Files**: <list of modified files, relative to this directory>
**Change**: <short description>
```

## Entries

### 2026-04-23 — initial vendoring

**Files**: (none modified)
**Change**: Repository vendored verbatim at commit 4c1b307.

### 2026-04-28 — import-path rewire

**Files**: all `.lean` files under this directory
**Change**: rewrote internal `import DeGiorgi.…` statements as `import DifferentialGeometry.External.DeGiorgi.…` to fit the project's module path layout.

### 2026-05-16 — style-warning cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `Harnack.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakHarnack.lean`

**Change**: addressed all Lean linter style warnings flagged by `lake build` under this directory. Changes are semantic-preserving and consist of:
- `show <goal>` rewritten to `change <goal>` at sites the linter flagged as goal-modifying;
- `simp [...]` rewritten to `simp only [...]` at sites flagged as flexible (lemma lists adjusted as needed to keep the next tactic step closing);
- `push_neg` replaced with `push Not`;
- isolated `·` bullets merged with the following line;
- `set_option maxHeartbeats N` and `set_option synthInstance.maxHeartbeats N` scoped via `... in` and given an inline comment describing the elaboration that needs the extended budget; a small number of declarations additionally use a narrow `set_option linter.style.setOption false in` so that the `... in`-scoped form is not itself flagged;
- one tactic call in `StampacchiaTruncation.lean` made unification-explicit (`(s := Ioo a b)`) to satisfy the "tactic operates on only one of multiple goals" linter.

### 2026-07-24 — linter cleanup under the project's final Lean options

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/Geometry.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/CoefficientOperator.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`

**Change**: the project's `lakefile.toml` now enables the full Mathlib standard linter set
(`weak.linter.mathlibStandardSet`) with no per-linter opt-outs, so this directory was brought
to zero warnings as well. All changes are semantic-preserving; no statement, proof or
declaration was added, removed or weakened:

- the `set_option linter.style.setOption false in` opt-outs added on 2026-05-16 were **removed**
  (the project no longer permits suppressing a linter anywhere). The underlying diagnostic is
  now avoided instead: a `set_option maxHeartbeats N in` is placed *outermost*, ahead of any
  `omit … in` modifier — Lean's `withSetOptionIn` only strips a leading `set_option`, and an
  `omit … in` in front of it made the option look unscoped — and is followed by a comment line
  explaining the raised budget, as `linter.style.maxHeartbeats` requires;
- source lines longer than 100 columns were re-flowed (`linter.style.longLine`); breaks are at
  existing token boundaries with the continuation indented past the enclosing construct;
- over-long prose lines inside `/-! … -/` module docstrings were re-wrapped;
- blank lines inside a command were removed (`linter.style.emptyLine`);
- binders unused by their declaration were renamed `x` → `_x`, which keeps the binder — and so
  the statement — unchanged (`linter.unusedVariables`);
- simp arguments the linter proved redundant were dropped (`linter.unusedSimpArgs`);
- spacing inside declaration binders was normalised (`linter.style.whitespace`);
- in `BallExtension/ApproximationControl.lean`, two `rw [abs_of_nonneg (by linarith […])]` steps
  were rewritten as a named `have hle : 0 ≤ …` followed by `rw [abs_of_nonneg hle]`, so the
  proof term fits the line limit without an inline nested tactic block. The proof is unchanged.

The original `LICENSE`, `README.md` and `CITATION.cff` remain unmodified.

### 2026-07-28 — heartbeat-free elaboration

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `Crossover/ExponentialIntegrability.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/StageOne.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`

**Change**: removed the remaining heartbeat-budget overrides and refactored the affected proof
bodies into explicit integrability, measurability, nonnegativity, monotonicity, and witness-
construction steps that elaborate under the project defaults.

### 2026-08-12 — isolated tactic-bullet cleanup

**Files**:
- `WeakHarnack.lean`

**Change**: merged two isolated tactic bullets with their following tactic lines. This is a
semantic-preserving source-style change; no statement, proof term or declaration was changed.

### 2026-08-17 — namespace-opening cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/Core.lean`
- `BallExtension/Geometry.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `Common.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `Crossover/PublicEstimate.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `DeGiorgiIteration/Recurrence.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/PublicEstimate.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `MoserIteration/Sequences.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/PositivePartPrelude.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/SmoothTests.lean`
- `WeakFormulation/SolutionInterfaces.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WholeSpaceSobolev.lean`

**Change**: removed namespace and notation-scope tokens that were not used by their files,
retaining each opening whose removal prevented elaboration. This is a semantic-preserving lexical
scope cleanup; no declaration, statement, or proof was changed.

### 2026-08-18 — explicit weak-Harnack chain estimates

**Files**:
- `WeakHarnack.lean`

**Change**: replaced broad simplification and nonlinear arithmetic in the weak-Harnack chain
constant estimates with explicit ring equalities, multiplication monotonicity, and a precise
simplification set. The theorem statements and mathematical inequalities are unchanged.

### 2026-08-18 — explicit crossover measurability

**Files**:
- `Crossover/ExponentialIntegrability.lean`

**Change**: supplied the measurable real exponential integrand and its almost-everywhere
measurability explicitly before applying the constant-multiple lintegral identity, and made a
nearby additive simplification precise. The theorem statements are unchanged.

### 2026-08-20 — explicit small-ball average estimate

**Files**:
- `Crossover/ExponentialIntegrability.lean`

**Change**: replaced a broad additive `simpa` in the small-ball average triangle estimate with
an explicit equality followed by `abs_add_le`. The theorem statement and mathematical argument
are unchanged.

### 2026-08-20 — explicit iteration inequalities

**Files**:
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/StageOne.lean`
- `WeakFormulation/ExistenceTheory.lean`

**Change**: replaced slow nonlinear arithmetic, broad simplification, and multi-rewrite steps
with direct nonnegativity products, monotonicity lemmas for squares and exponents, explicit factor
rearrangements, and an explicit inner-product congruence. The theorem statements and mathematical
arguments are unchanged.

### 2026-08-21 — declaration-linter cleanup

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `EllipticCoefficients.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Sequences.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WholeSpaceSobolev.lean`

**Change**: resolved Mathlib declaration-linter findings by classifying a proposition-valued
definition as a theorem, removing redundant hypotheses and typeclass assumptions, simplifying a
cast expression to its normal form, retaining a useful ellipticity-ratio theorem without a
redundant simp attribute, and making compatibility-preserving hypotheses explicit dependencies of
their proof terms. The affected mathematical conclusions are unchanged or generalized.

### 2026-08-21 — divergence-data uniqueness generality

**Files**:
- `WeakFormulation/ExistenceTheory.lean`

**Change**: removed a redundant `MemLp` hypothesis from the uniqueness theorem for the
inhomogeneous Dirichlet problem and updated its callers. Existence still requires the integrability
hypothesis; uniqueness now states only the assumptions used by its mathematical argument.

### 2026-08-23 — Mathlib 4.33 API migration

**Files**:
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/ProductBound.lean`
- `ScaledBallEstimates.lean`
- `WeakHarnack.lean`

**Change**: migrated renamed Mathlib APIs and made restriction coercions, rescaling identities,
measurability bridges, the John--Nirenberg level-set identification, the finite-dimensional volume
equivalence, affine ball rescaling, and the Fatou lemma indexing explicit. The theorem statements
and mathematical arguments are unchanged.

### 2026-08-24 — Mathlib 4.33 Lipschitz constant elaboration

**Files**:
- `Crossover/LogGradient.lean`

**Change**: made the nonnegative real type of a Lipschitz constant explicit after Mathlib's
subtype elaboration changed. The theorem statement and mathematical argument are unchanged.

### 2026-08-28 — Mathlib 4.33 migration and warning cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `FiniteCover.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `ScaledBallEstimates.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/CoefficientOperator.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakFormulation/SmoothTests.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`
- `WholeSpaceSobolev.lean`

**Change**: completed the remaining Mathlib 4.33 API and elaboration migration and brought the
vendored modules to the project's zero-warning standard. The semantic-preserving changes update
renamed or deprecated APIs and import paths, remove redundant simp arguments and obsolete tactic
steps, replace proof-valued local instances with ordinary local facts, repair declaration-linter
findings by removing genuinely unused assumptions, and make dependent casts and coercions explicit
where the newer elaborator no longer infers them. The affected conclusions and mathematical
arguments are unchanged or generalized. The original `LICENSE`, `README.md`, and `CITATION.cff`
remain unmodified.

### 2026-08-29 — definition-name normalization

**Files**:
- `BallExtension/RoughInput.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `Crossover/ExponentialIntegrability.lean`
- `Crossover/LocalIntegrability.lean`
- `Crossover/LogGradient.lean`
- `Crossover/ProductBound.lean`
- `Crossover/PublicEstimate.lean`
- `DeGiorgiIteration/CutoffAdmissibility.lean`
- `DeGiorgiIteration/Energy.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `Harnack.lean`
- `Holder/LocalBounds.lean`
- `Holder/OscillationDecay.lean`
- `Holder/PublicEstimate.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `MoserIteration/Constants.lean`
- `MoserIteration/CutoffPrep/Basics.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/PreEstimate.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/Iteration.lean`
- `MoserIteration/Linfty.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `ScaledBallEstimates.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/Witnesses.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/StageOne.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/IterationConstants.lean`
- `UnitBallApproximationCore/Approximation.lean`
- `UnitBallApproximationCore/Dilation.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/WeightedEstimates.lean`
- `WeakHarnack.lean`
- `WholeSpaceSobolev.lean`

**Change**: renamed definition, abbreviation, and structure-field identifiers from theorem-style
snake case to Mathlib camel case, and updated every internal reference. Two witness constructors
whose short source names also name Mathlib declarations were migrated only at their project-owned
declarations and qualified references. This is an API-only, semantic-preserving migration; theorem
statements and proof bodies are unchanged.

<!-- Add entries below as modifications occur. -->

### 2026-09-04 — theorem-name normalization

**Files**:
- `BallExtension/ApproximationControl.lean`
- `BallExtension/RoughInput.lean`

**Change**: renamed the equality theorem for `exactUnitBallExtensionGradApply` so that its
declaration name identifies the `smoothUnitBallExtensionGradCandidate` on its right-hand side.
Also removed the redundant `generic` suffix from a private norm-bound helper. The theorem
statements and proofs are unchanged.

### 2026-09-07 — positive-test density extension

**Files**:
- `SobolevSpace/PositiveTestDensity.lean`

**Change**: added the nonnegative smooth density theorem for pointwise nonnegative `H₀¹`
functions and the resulting smooth-test criterion for weak supersolutions, and adapted their
proofs to Mathlib 4.33 elaboration and indicator APIs. The density construction uses exact-support
smooth positive-part regularizations and preserves the limit witness's weak gradient.

### 2026-09-07 — strong minimum principle extension

**Files**:
- `StrongMinimum.lean`

**Change**: added the strong minimum principle on Euclidean balls from the weak Harnack
inequality, migrated renamed definitions and coefficient-rescaling elaboration to Mathlib 4.33,
and placed the two public conclusions in the `IsSupersolution` namespace with descriptive names.

### 2026-09-07 — homogeneous weak-solution equivalence

**Files**:
- `WeakFormulation/ExistenceTheory.lean`

**Change**: proved that a function which is simultaneously a weak subsolution and weak
supersolution satisfies the equality-form homogeneous weak identity against arbitrary signed
`H₀¹` tests. The proof decomposes smooth compactly supported tests into nonnegative tests and then
uses the existing Sobolev approximation and bilinear-continuity argument. Exposed that shared
extension as `bilinFormOfCoeff_eq_of_isSmoothTestOn`, the conversion in the `IsSolution` namespace,
the equivalence of the two solution interfaces, and vanishing of the bilinear form on signed
`H₀¹` tests. These additions migrate the source branch's smooth-test and homogeneous-solution
APIs without changing the established existence and uniqueness conclusions.

### 2026-09-07 — weak divergence pairing extension

**Files**:
- `WeakFormulation/BilinearForm.lean`
- `WeakFormulation/WeakDivergence.lean`

**Change**: added assembly of weak divergence from the componentwise weak partial derivatives
and the equality of the divergence-form functional with its scalar `L²` pairing on `H₀¹` tests.
Migrated finite-sum names and function-space elaboration to Mathlib 4.33, clarified the public
declaration names, and removed the redundant supplied Sobolev witness from the pairing theorem.
The witness-independence identity and the new pairing theorem hold in every finite dimension,
including dimension zero; removed their unnecessary `NeZero` assumption. The weak gradient used
in the proof remains the witness tied to the `H₀¹` approximation.


### 2026-09-27 — Mathlib 4.34 Lp and measure compatibility

**Files**:
- `LpFunctionToolkit.lean`
- `WholeSpaceSobolev.lean`
- `BallExtensionEstimates.lean`
- `Support/MeasureBounds.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`

**Change**: adapted the existing proofs to Mathlib 4.34's `eLpNorm`, which is infinite
for functions that are not almost everywhere strongly measurable, and its corresponding
single-inequality `MemLp` definition. Updated triangle, norm, monotonicity, convergence,
and Fatou lemma arguments using the existing measurability witnesses. The component norm
bound retains its original hypothesis-free statement by separating the measurable and
infinite-norm cases. Removed now-redundant measurability hypotheses from the bare-function
limit-membership and uniqueness theorems and updated their consumers; their conclusions
are unchanged. Replaced the retired `Measure.ae.neBot` name by instance synthesis from the
existing nonzero-measure instance, and replaced diagnosed deprecated conditional-rewrite
aliases by their current names. All original attribution, comments, documentation, and
vendor metadata are preserved; these changes are necessary dependency-upgrade compatibility
repairs and do not reorganize the vendored development.


### 2026-09-27 — remaining Lean 4.34 conditional aliases

**Files**:
- `Holder/Representative.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Poincare.lean`
- `ScaledBallEstimates.lean`
- `WeakFormulation/BilinearForm.lean`

**Change**: replaced 14 remaining uses of the officially deprecated Lean conditional
rewrite aliases `if_pos`, `if_neg`, `dif_pos`, and `dif_neg` with `ite_eq_left`,
`ite_eq_right`, `dite_eq_left`, and `dite_eq_right`. The old declarations are exact
applications of their replacements with the same universe parameters, binder order,
and hypotheses. This dependency-upgrade compatibility update prevents the corresponding
warnings as the remaining vendor consumers are rebuilt. No mathematical statement, proof
argument, import, namespace, attribution, comment, documentation, or string was changed.


### 2026-09-27 — further Mathlib 4.34 Lp consumers

**Files**:
- `SobolevSpace/WeakDerivatives.lean`
- `Poincare.lean`

**Change**: removed the obsolete measurability argument from `toReal_eLpNorm`, which
is now the unconditional definitional equality with `lpNorm`. Supplied the existing
measurability witnesses required by the current restriction, norm, monotonicity, and
nonnegative-real-power `eLpNorm` lemmas. The private identity relating the power integral
to `eLpNorm` now assumes measurability, as required by the updated infinite value for
nonmeasurable functions; its two consumers supply their existing witnesses. Replaced
the diagnosed `if_true` and `if_false` aliases by `ite_true` and `ite_false`. All public
statements and all original documentation and attribution are unchanged.


### 2026-09-27 — Sobolev witness addition under Mathlib 4.34

**Files**:
- `SobolevSpace/Witnesses.lean`

**Change**: updated the two triangle-inequality applications in `MemW01p.add` to the
current `eLpNorm_add_le`, which requires only the exponent bound. Removed the local
measurability preparations used exclusively by the obsolete arguments. The same
function and weak-gradient witnesses, approximation sequences, public hypotheses,
and conclusions are retained; all original documentation and attribution are unchanged.


### 2026-09-27 — positive-test density conditional aliases

**Files**:
- `SobolevSpace/PositiveTestDensity.lean`

**Change**: replaced one `if_true` and one `if_false` rewrite by the current official
`ite_true` and `ite_false` aliases. These applications use no named branch arguments;
the theorem parameters, their order, and their proofs are unchanged. This minimal
Lean 4.34 compatibility change prevents the corresponding warnings in the next full
build. All other source bytes, including attribution, documentation, comments, and
strings, are unchanged.


### 2026-09-27 — convolution approximation under Mathlib 4.34

**Files**:
- `SobolevSpace/Approximation.lean`

**Change**: supplied the current bounded-distance `eLpNorm` estimate with null
measurability derived from the existing measurable support set and almost-everywhere
strong measurability derived from continuity of the same normalized convolution minus
the original continuous function. Updated two triangle-inequality calls to their
current exponent-only API and removed their unused local measurability preparations.
The measure remains `volume`. All public signatures, actual convolution approximants,
common tail subsequences, supplied weak-gradient witnesses, convergence statements,
and original documentation and attribution are unchanged.


### 2026-09-27 — bilinear products and affine rescaling under Mathlib 4.34

**Files**:
- `WeakFormulation/BilinearForm.lean`
- `UnitBallApproximationCore/Rescaling.lean`

**Change**: matched the current left-to-right `MemLp.mul` hypothesis order to the
existing product of the two specified weak-gradient norms. Supplied the measurable
translation map to two updated measure-pushforward calls, and used the canonical
`eLpNorm_smul_measure_of_ne_zero_of_ne_top` with the existing exponent hypotheses for
the scaling identity. The scaling theorem still applies to arbitrary functions,
including the nonmeasurable case; no additional hypothesis is introduced. All public
and private signatures, actual affine scaling maps, bilinear integrands, documentation,
and attribution are unchanged.


### 2026-09-27 — smooth tests and unit-ball approximation under Mathlib 4.34

**Files**:
- `WeakFormulation/SmoothTests.lean`
- `UnitBallApproximationCore/Approximation.lean`

**Change**: removed two obsolete measurability arguments from the definitional
`toReal_eLpNorm` equality while retaining the actual Sobolev witnesses in the integral
norm formulas. Adapted unit-ball dilation and approximation proofs to the current
`MemLp` accessors, measurable monotonicity, and exponent-only triangle inequality.
Used `eLpNorm_sub_comm` for the same arbitrary-function symmetry and `memLp_congr_ae`
with the existing indicator identification for the localized weak derivative. The
required monotonicity measurability follows from the original continuous dilation.
All public and private signatures, actual approximants, localized weak-gradient
equalities, restricted measures, documentation, and attribution are unchanged.


### 2026-09-27 — measurable norm identities and rough extensions under Mathlib 4.34

**Files**:
- `WeakFormulation/WeakDivergence.lean`
- `WeakFormulation/CoefficientOperator.lean`
- `SobolevChainRule.lean`
- `BallExtension/RoughInput.lean`
- `BallExtension.lean`
- `BallExtensionEstimates.lean`
- `SobolevPoincare.lean`

**Change**: adapted newly reached weak-formulation, chain-rule, and extension proofs
to the current norm, monotonicity, finite-sum, convergence, and `MemLp` APIs. Every new
measurability argument comes from the existing function, Sobolev witness, or continuous
composition. The public `lintegral_rpow_norm_eq_eLpNorm_pow` identity and its private
norm-bound helper now require almost-everywhere strong measurability, because their
unrestricted forms are false when the updated `eLpNorm` assigns infinity to a
nonmeasurable function. The local caller and thirteen downstream callers supply their
actual existing witnesses, including the two native Rellich consumers coordinated
outside this vendor.

To keep `eLpNorm_unitBallExtension_sub_le_local` at its original natural signature,
moved the existing `aestronglyMeasurable_unitBallExtension_of_memLp` declaration from
`BallExtension.lean` to `BallExtension/RoughInput.lean` after its three existing
measurability prerequisites. The full declaration name, signature, proof, attached
documentation, and inline comments are preserved verbatim, and the original copy is
removed. This precise owner-authorized dependency repair avoids importing a downstream
module back into its prerequisite, copying its proof, or assuming the estimate's
conclusion. The estimate handles finite input norm with that existing theorem and
infinite input norm directly. The component estimate similarly retains its original
signature using the measurable and infinite-norm cases. All actual extension maps,
weak-gradient and approximation identifications, attribution, and original documents
are retained; no unrelated source reorganization was performed.


### 2026-09-27 — existence, positive parts, and smooth extensions under Mathlib 4.34

**Files**:
- `WeakFormulation/ExistenceTheory.lean`
- `PositivePart.lean`
- `BallExtension/SmoothApproximation.lean`

**Change**: updated the newly reached norm, finite-sum, monotonicity, convergence in
measure, uniform-integrability, and tightness calls to their current APIs. Existing
Sobolev, smooth-test, and continuous-composition witnesses supply the required
measurability for the same functions and gradients. Private positive-part estimates
now explicitly require measurability of their input functions, which is necessary
under the updated infinite `eLpNorm` for nonmeasurable functions; their actual callers
use the original witness and smooth sequence. The public almost-everywhere subsequence
theorem drops two now-redundant measurability premises, with its sole caller updated.
Uniform-tightness proofs obtain a measurable controlling set from the canonical API
before applying indicator estimates. Weak-solution equations, positive-part gradient
identifications, smooth-extension support and convergence statements, public conclusions,
and all original attribution and documentation are retained.


### 2026-09-27 — positive test density, extension estimates, and ball scaling

**Files**:
- `SobolevSpace/PositiveTestDensity.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `DeGiorgiIteration/Energy.lean`

**Change**: adapted the newly reached positive-density and extension-estimate proofs
to the current uniform-integrability, tightness, measurable monotonicity, finite-sum,
triangle, norm-conversion, and `MemLp` APIs. All required measurability is supplied by
the actual continuous approximants, original weak-gradient witnesses, or their
finite components. Integral identities name their actual difference function and
restricted measure explicitly to avoid function-notation inference ambiguity. Updated
the affine measure-pushforward proof with measurable translation and used the existing
nonzero, finite exponent assumptions for arbitrary-function norm scaling. Replaced
the retired componentwise measurability API by `AEMeasurable.of_eval`. Public and private
signatures, actual nonnegative smooth approximants, support and weak-gradient equations,
extension producers, attribution, and documentation are unchanged.


### 2026-09-27 — localization and Sobolev pre-iteration under Mathlib 4.34

**Files**:
- `Localization.lean`
- `SobolevPoincare.lean`
- `DeGiorgiIteration/PreIteration.lean`

**Change**: supplied the actual measurable translation in the affine measure map.
Adapted Sobolev–Poincare norm identities, monotonicity, finite sums, and triangle
estimates with the existing integrability, smooth-derivative, component, and weak-gradient
measurability witnesses. The pre-iteration support restriction uses measurability of the
same zero-extended cutoff witness; its `MemLp` proofs and real-norm conversions follow
the current definitions. All public and private signatures, localized measures,
normalizations, cutoff and weak-gradient objects, conclusions, documentation, and
attribution remain unchanged.


### 2026-09-28 — Moser cutoff preparation under Mathlib 4.34

**Files**:
- `MoserIteration/CutoffPrep/Basics.lean`

**Change**: adapted the existing Moser cutoff preparation proofs to the current
`AEMeasurable.of_eval`, uniform-integrability, uniform-tightness, restricted-norm,
and measure-pushforward APIs. Every added measurability argument is supplied by the
existing Sobolev witness or continuous affine map; cutoff, truncation, rescaling,
and subsolution statements are unchanged. This is a dependency-upgrade compatibility
repair only; attribution and the vendored development remain intact.


### 2026-09-28 — Moser regularization linter and conversion cleanup under Mathlib 4.34

**Files**:
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/ExactRegularization.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`

**Change**: removed obsolete tactic sequencing flagged by the Mathlib standard linter and
removed a redundant post-`convert` proof step whose goal is discharged by the current
Lean 4.34 elaborator. The regularized energy integrability proof now uses the current
conversion result directly. No declaration, statement, regularization profile, witness,
energy estimate, documentation, or attribution was changed.


### 2026-09-28 — Moser witness construction under Mathlib 4.34

**Files**:
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`

**Change**: removed redundant post-`convert` tactic steps and adapted the component
decomposition estimate to the current exponent-only `eLpNorm_add_le` API. The obsolete
measurability premises of that private helper were removed after the updated theorem
stopped requiring them. The limiting witness construction, all public statements, and
the original documentation and attribution remain unchanged.


### 2026-09-28 — Moser pre-estimate norm API under Mathlib 4.34

**Files**:
- `MoserIteration/CutoffPrep/PreEstimate.lean`

**Change**: adapted the Sobolev exponent finiteness proof to the current definitional
`MemLp` predicate and removed obsolete measurability arguments from the unconditional
`toReal_eLpNorm` identity. The pre-estimate statements, witness, energy bound,
documentation, and attribution remain unchanged.


### 2026-09-28 — supersolution test-function measure APIs under Mathlib 4.34

**Files**:
- `Supersolutions/TestFunctions.lean`

**Change**: replaced the retired componentwise almost-everywhere measurability constructor
with `AEMeasurable.of_eval`, adapted the dominated `L²` convergence argument to the current
`UnifIntegrable` and `UnifTight` parameter conventions, and supplied the measurable-superset
step required by the updated `eLpNorm` monotonicity API. The supersolution estimates,
measurability hypotheses, and mathematical conclusions are unchanged; original source
documentation and attribution remain intact.


### 2026-09-28 — supersolution energy compatibility under Mathlib 4.34

**Files**:
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/ForwardIteration/OneStep.lean`
- `Supersolutions/ForwardIteration/Iteration.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/InverseOneStep.lean`
- `Supersolutions/InverseIteration.lean`
- `Supersolutions/StageOne.lean`

**Change**: removed obsolete post-`convert` tactic steps and adapted the forward-energy
integrability proof to the current continuous-enorm instance and exponent-only
`eLpNorm_add_le` API. Updated the one-step and stage-one Sobolev bounds to the current
single-inequality `MemLp` predicate and unconditional `toReal_eLpNorm` identity, and
replaced the old positive-product API by `Finset.prod_le_prod₀`. The Caccioppoli,
forward-iteration, inverse-iteration, and stage-one estimates, witnesses, and public
conclusions are unchanged; original source documentation and attribution remain intact.


### 2026-09-28 — crossover local integrability compatibility under Mathlib 4.34

**Files**:
- `Crossover/LocalIntegrability.lean`

**Change**: supplied the almost-everywhere measurability witness required by the updated
measure-scaling API, and adapted the local `L²` norm conversions to the unconditional
`toReal_eLpNorm` identity. Removed obsolete post-rewrite proof steps while preserving the
affine rescaling, local integrability, and Poincare estimates, together with all original
documentation and attribution.


### 2026-09-28 — weak-Harnack norm conversion under Mathlib 4.34

**Files**:
- `WeakHarnack.lean`

**Change**: adapted the exponent comparison's `L^p` conversion to the unconditional
`toReal_eLpNorm` identity. The weak-Harnack chain estimates and all public conclusions
are unchanged; source documentation and attribution remain intact.


### 2026-09-28 — scaled-ball measure-map compatibility under Mathlib 4.34

**Files**:
- `ScaledBallEstimates.lean`

**Change**: supplied explicit almost-everywhere measurability and scalar/function
arguments to the updated `Measure.map_smul` API in the affine and inverse-affine
ball rescaling proofs. The scaling identities and all estimates are unchanged;
source documentation and attribution remain intact.


### 2026-09-28 — Harnack affine measure-map compatibility under Mathlib 4.34

**Files**:
- `Harnack.lean`

**Change**: supplied explicit almost-everywhere measurability and scalar/function
arguments to the updated `Measure.map_smul` API in the affine ball restriction proof.
The Harnack estimates and public conclusions are unchanged; source documentation and
attribution remain intact.
