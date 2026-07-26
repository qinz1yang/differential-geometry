# B1 generic ODE stability consultation

## Checked stop

The metric-to-spray part of the approved architecture is implemented and
focused-green.  Generic map-convergence definitions and closures now live in
`Analysis/Calculus`; `IsCoercive.sharp_eq_inverse`, the proof-independent
metric spray, `MetricKoszul.metricSpray_conv`, and
`normalGeodesicSpray_conv` are checked.  No velocity bound, stage-family stay
assumption, or endpoint-radius input was introduced.

The exact theorem below is stated and typechecked in
`Analysis/ODE/CInfConvergence.lean`.  Its proof is the first honest analytic
frontier and remains one explicit `sorry`.

## Pasteable consultation request

```text
We need a proof-level Lean architecture for the first genuinely new analytic
theorem in a Hamilton--Cheeger--Gromov compactness formalization.  Please do not
redesign the downstream geometry: the generic ODE theorem below is now the
agreed lowest-layer frontier.

Checked current state
---------------------

1. `MapCInfConvOnCompacts` and its generic composition/derivative closures now
   live in `DifferentialGeometry/Analysis/Calculus` (public namespace and names
   unchanged).
2. `MapCInfConvOnCompacts.fderivOn` is checked.
3. `MapCInfConvOnCompacts.ringInv` is checked.
4. The total proof-independent coordinate metric spray, based on `Ring.inverse`
   of the canonical Gram operator and `MetricKoszul.koszulCovCLM`, is checked.
5. `MetricKoszul.metricSpray_conv` and the thin geometric theorem
   `normalGeodesicSpray_conv` are focused-green.
6. The next public theorem is already stated exactly as follows and typechecks
   with one intentional `sorry`:

theorem MapCInfConvOnCompacts.ode_solutionAt
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A) (hJ : IsOpen J) (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁) (hI : Set.Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X} {vInf : ℝ → X → X}
    (hv_cd : ∀ n, ContDiffOn ℝ ∞
      (fun q : ℝ × X => v n q.1 q.2) (J ×ˢ V))
    (hvInf_cd : ContDiffOn ℝ ∞
      (fun q : ℝ × X => vInf q.1 q.2) (J ×ˢ V))
    (hv_conv : MapCInfConvOnCompacts (J ×ˢ V)
      (fun n q => v n q.1 q.2) (fun q => vInf q.1 q.2))
    {a : ℕ → P → X} {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X} {γInf : P → ℝ → X}
    (hγ : ∀ n p, p ∈ A →
      γ n p t₀ = a n p ∧
      IsIntegralCurveOn (γ n p) (v n) (Set.Icc t₀ t₁))
    (hγInf : ∀ p, p ∈ A →
      γInf p t₀ = aInf p ∧
      IsIntegralCurveOn (γInf p) vInf (Set.Icc t₀ t₁))
    (hstayInf : ∀ p ∈ A, ∀ t ∈ Set.Icc t₀ t₁, γInf p t ∈ V) :
    MapCInfConvOnCompacts A
      (fun n p => γ n p t₁) (fun p => γInf p t₁)

Existing native ODE APIs found
------------------------------

- Mathlib defines
  `IsIntegralCurveOn γ v s := ∀ t ∈ s, HasDerivWithinAt γ (v t (γ t)) s t`
  and provides `IsIntegralCurveOn.continuousOn`.
- `Analysis/ODE/TimeDependentFlow/SmoothInSpace/VariationalODE/BanachIC.lean`
  has `exists_isLocalFlow_contDiffOn_top` for globally smooth time-dependent
  Banach-space vector fields.
- `Analysis/ODE/TimeDependentFlow/SmoothDependence/Parameter.lean` has a
  continuous-parameter smooth local-flow theorem, but the sequence index here
  is discrete and has no supplied continuous extension.
- `Analysis/ODE/Flow/ParametricLinearODE.lean` has
  `linearODESolution_dist_le` and `linearODESolution_contDiffOn_top`.
- No checked theorem currently gives convergence of nonlinear flows or
  arbitrary parameter jets for converging vector fields.

The intended mathematical route is: shrink around an arbitrary compact
`K ⊆ A`; build a compact limit-trajectory tube inside `J × V`; obtain
eventual stage containment by a first-exit argument plus C0 Grönwall; use a
fixed cutoff extension and uniqueness to identify selected curves with smooth
local flows; then prove convergence of parameter derivatives by variational
equations and induction on jet order.

Questions
---------

1. Is the public theorem exactly valid as stated, in particular with only the
   limit-family stay condition and no stage-family stay assumption?  If not,
   identify the precise mathematical counterexample or the smallest genuinely
   necessary hypothesis; do not add a convenience assumption.
2. Give the smallest sequence of reusable internal theorem signatures needed
   for a Lean proof.  We expect a relatively compact parameter-domain helper
   and a finite-order engine such as `ode_cPConvOn`; please state all important
   quantifiers and domains.
3. Which existing RicciFlower/Mathlib theorem should implement each step:
   compact trajectory tube, uniform local Lipschitz bound, first-exit
   containment, C0 Grönwall stability, selected-solution uniqueness, smooth
   dependence, first variational equation, and higher-jet induction?
4. For the arbitrary-order step, should we compare inhomogeneous variational
   equations with `linearODESolution_dist_le`, build a jet bundle ODE and apply
   a finite-order induction, or use a different existing API?  Give the route
   least likely to create a parallel ODE framework.
5. Explain how to prove endpoint `ContDiffOn` for the selected families only
   on the eventual compact tube, without globally extending the public input or
   adding stage containment to the theorem statement.
6. Name the first intermediate lemma that is likely to require genuinely new
   analysis rather than routine localization/packaging, and give a detailed
   proof skeleton in Lean terms (filters, compact sets, derivatives, and
   relevant theorem names).
7. Flag any hidden endpoint issue at `t₀` or `t₁` caused by
   `IsIntegralCurveOn` on the closed interval, and state the cleanest native
   repair if one is needed.

Hard constraints
----------------

- Keep the public `ode_solutionAt` statement at the low `Analysis/ODE` layer.
- Do not add metrics, normal charts, HCG data, endpoint-radius assumptions, or
  a stage-family stay premise unless it is mathematically indispensable.
- Do not treat the discrete sequence index as a smooth parameter by assumption.
- Reuse the native ODE/flow and linear-ODE APIs; do not build a parallel solver.
- Keep `StepB1RawInput` unchanged.
- The downstream order remains: ODE stability -> forward normal phase -> fixed
  compact moving root -> selected inverse -> `invVelSum` center roots.
- Distinguish theorem proof completion from supporting machinery.  The public
  `ode_solutionAt` proof is currently 0%.
```

## Accounting

- `normalGeodesicSpray_conv`: 100%, focused-green.
- `MapCInfConvOnCompacts.ode_solutionAt`: statement 100%; proof 0%.
- Dedicated all-order ODE-stability machinery: 0%.
- `StepB1RawInput` producer and textbook B1: 0%.
- Rounded machinery estimates remain 95% / 87% / 57% for dedicated B1 /
  Chapter 4 / whole HCG.
