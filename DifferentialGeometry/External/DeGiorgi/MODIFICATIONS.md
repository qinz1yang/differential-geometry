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

### 2026-08-12 — isolated tactic-bullet cleanup

**Files**:
- `WeakHarnack.lean`

**Change**: merged two isolated tactic bullets with their following tactic lines. This is a
semantic-preserving source-style change; no statement, proof term or declaration was changed.

<!-- Add entries below as modifications occur. -->
