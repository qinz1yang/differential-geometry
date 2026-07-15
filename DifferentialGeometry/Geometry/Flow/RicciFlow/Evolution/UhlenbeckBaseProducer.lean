import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Rm13DerivProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.BookData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Lichnerowicz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation
import DifferentialGeometry.Tensor.RSTensor.ProductNablaLeibniz
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RiemannFromRicci
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UhlReaction3

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Uhlenbeck base `∂ₜRm04` discharge — Lemma 6.1 (in progress)

Discharge of `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (Hamilton's curvature
evolution `∂ₜRm = ΔRm + Rm∗Rm`), the gating geometric input of the BBS pillar.  See
`UhlenbeckBaseProducer.md` for the full route.  Built so far:

* `metricCompInFrame_timeDeriv` — the component metric evolution `∂ₜg_{ij} = −2 Ric_{ij}`
  in a local frame, directly from the Ricci-flow PDE.  Input #1 to the A2 lowering
  product rule `∂ₜRm04 = (∂ₜg)·Rm13 + g·(∂ₜRm13)`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*}

/-- **Component metric evolution `∂ₜg_{ij} = −2 Ric_{ij}`.**  The time derivative of the
local-frame metric components of a Ricci-flow solution, extracted from the PDE
`MetricVariationEquationOn`.  Frame vectors are held fixed; the derivative is taken
within `D.carrier` at a regular time. -/
theorem metricCompInFrame_timeDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have h := hS.equation t x (frame i x) (frame j x)
  simpa [metricCompInFrame, ricciCompInFrame, RicciAtFamily.toTensorField_apply] using h

/-- **Component lowering realization (A2 gateway).**  At the centre `x₀` of the
coordinate frame, the lowered Riemann base component array is the metric-lowering of the
`(1,3)` Christoffel curvature coefficient:
`Rm04_{m₀m₁m₂m₃} = Σ_p curvCoeff^p_{m₀m₁m₂} · g_{m₃ p}`.
Derived by chaining the tensor-level lowering `solution_rm04LowersRm13At` with the
component realization `rm13_eval_eq_christoffelCurvCoord` and evaluating the metric flat. -/
theorem realizedRmBase_eq_curvCoeff_lower
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (hRm : DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
      (S.family.connection t) (S.base.rm13 t))
    (hcurv : DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I)
      (S.family.connection t) x₀)
    (m : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
    realizedRmBase (I := I) S x₀ t x₀ m
      = ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection t) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ (m 3) p := by
  classical
  have hvec : (fun q : Fin 4 => coordinateFrameAt (I := I) x₀ (m q) x₀)
      = DifferentialGeometry.Integral.Connection.vec4
          (coordinateFrameAt (I := I) x₀ (m 0) x₀)
          (coordinateFrameAt (I := I) x₀ (m 1) x₀)
          (coordinateFrameAt (I := I) x₀ (m 2) x₀)
          (coordinateFrameAt (I := I) x₀ (m 3) x₀) := by
    funext q; fin_cases q <;> rfl
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (1 : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  rw [realizedRmBase_apply, hvec,
    solution_rm04LowersRm13At S t x₀
      (coordinateFrameAt (I := I) x₀ (m 0) x₀)
      (coordinateFrameAt (I := I) x₀ (m 1) x₀)
      (coordinateFrameAt (I := I) x₀ (m 2) x₀)
      (coordinateFrameAt (I := I) x₀ (m 3) x₀),
    DifferentialGeometry.Integral.Connection.rm13_eval_eq_christoffelCurvCoord
      (I := I) (S.family.connection t) hcov (S.base.rm13 t) x₀
      (dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) (S.base.metric t) x₀)
          (coordinateFrameAt (I := I) x₀ (m 3) x₀)))
      hRm hcurv (m 0) (m 1) (m 2)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1

/-- **A2 — the lowered Riemann time derivative `∂ₜRm04` in `∇²Ric`-expanded form.**
Differentiating the component lowering realization `realizedRmBase_eq_curvCoeff_lower`
through the product rule: `∂ₜ(curvCoeff·g) = (∂ₜcurvCoeff)·g + curvCoeff·(∂ₜg)`, with
`∂ₜcurvCoeff = rm13Deriv_of_solution` and `∂ₜg = metricCompInFrame_timeDeriv = −2Ric`.
The output is the expanded `∇²Ric` form; step B converts it to `ΔRm04 + 2B − drift`. -/
theorem realizedRmBase_timeDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt : Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal (I := I) S
      (coordInv (I := I) S x₀) gInvDt (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀))
    (hSmooth : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M => (S.family.metric q.1).inner q.2
          (coordinateFrameAt (I := I) x₀ a q.2) (coordinateFrameAt (I := I) x₀ b q.2)) (s, x))
    (hFdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.carrier ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y
          (coordinateFrameAt (I := I) x₀ a y) (coordinateFrameAt (I := I) x₀ b y)) x)
    (hFtdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s y a b) x)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
        (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)))
    (hRm : ∀ s, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection s) (S.base.rm13 s))
    (hcurv : ∀ s, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I)
        (S.family.connection s) x₀)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (m : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ((christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 0) p (m 1) (m 2)
            - christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 1) p (m 0) (m 2))
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p
          + DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (S.family.connection (t : Real)) x₀ (m 0) (m 1) (m 2) p
            * ((-2 : Real) * ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p)))
      D.carrier
      (t : Real) := by
  have hbase : ∀ s, s ∈ D.carrier ->
      realizedRmBase (I := I) S x₀ s x₀ m =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection s) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ (m 3) p :=
    fun s hs => realizedRmBase_eq_curvCoeff_lower S x₀ s (hRm s hs) (hcurv s hs) m
  have hterm : ∀ p ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection s) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ (m 3) p)
        ((christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 0) p (m 1) (m 2)
            - christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 1) p (m 0) (m 2))
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p
          + DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (S.family.connection (t : Real)) x₀ (m 0) (m 1) (m 2) p
            * ((-2 : Real) * ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p))
        D.carrier (t : Real) := by
    intro p _
    have h1 := rm13Deriv_of_solution (I := I) S hS x₀ gInvDt hmetricFrame hSmooth hFdiff hFtdiff hmix
      t (m 0) (m 1) (m 2) p
    have h2 := metricCompInFrame_timeDeriv (I := I) S hS (coordinateFrameAt (I := I) x₀) t x₀ (m 3) p
    exact h1.mul h2
  exact (HasDerivWithinAt.sum hterm).congr
    (fun y hy => by rw [Finset.sum_apply]; exact hbase y hy)
    (by rw [Finset.sum_apply]; exact hbase (t : Real) (D.regular_subset t.2))

/-- **B3a′+B3b-input: the sign-correct 3D Kulkarni–Nomizu identity for the solution.**
For a Ricci-flow solution in dim 3, the lowered Riemann tensor is the metric KN combination
of the *geometric* Ricci/scalar fields (the convention used by the proved `∂ₜRic`/`∂ₜS`).
The displayed-vs-geometric sign bridge is isolated here (via the banked `traceData_can`, which
produces the trace data with `−Ric`/`−scalar`), so downstream differentiation works purely in
the geometric convention.  The orthonormal basis is only a proof device — the conclusion is
basis-free. -/
theorem solution_rm04_kn_firstTrace_gform_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis)
    (X Y Z W : TangentSpace I x) :
    S.base.rm04 t x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      -(S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
          * (S.base.metric t).inner x Y W
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
          * (S.base.metric t).inner x X W
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
          * (S.base.metric t).inner x Y Z
        - S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
          * (S.base.metric t).inner x X Z
        + (S.scalar t x / 2)
          * ((S.base.metric t).inner x X Z * (S.base.metric t).inner x Y W
              - (S.base.metric t).inner x Y Z * (S.base.metric t).inner x X W) := by
  have h :=
    DifferentialGeometry.Integral.Connection.rm04_kn_gform (I := I)
      (traceData_can (I := I) S horth) X Y Z W
  simp only [Tensor0SSpace.neg_apply] at h
  rw [h]
  ring

/-- **Step 2 — the KN identity as a pointwise field (basis hidden).**  At any time `s`
and point `x` of a dim-3 solution, the lowered Riemann tensor is the geometric KN
combination of `Ric`/`scalar`/`g`.  The orthonormal basis is produced internally by
`exists_orthonormalBasisAt`, so this is differentiable in `s` (for B3b) and in `x`. -/
theorem solution_rm04_kn_field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (X Y Z W : TangentSpace I x) :
    S.base.rm04 s x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      -(S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
          * (S.base.metric s).inner x Y W
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
          * (S.base.metric s).inner x X W
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
          * (S.base.metric s).inner x Y Z
        - S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
          * (S.base.metric s).inner x X Z
        + (S.scalar s x / 2)
          * ((S.base.metric s).inner x X Z * (S.base.metric s).inner x Y W
              - (S.base.metric s).inner x Y Z * (S.base.metric s).inner x X W) := by
  obtain ⟨basis, horth⟩ :=
    DifferentialGeometry.Integral.Connection.exists_orthonormalBasisAt (I := I)
      (S.base.metric s) x hdim
  exact solution_rm04_kn_firstTrace_gform_at (I := I) S s x horth X Y Z W

/-- **Step 4 (B3b) — time derivative of `Rm04` via the KN identity.**  Differentiate the
pointwise KN field `solution_rm04_kn_field` in `t`: the product rule on the `Ric`/`scalar`/`g`
scalar factors, with `∂ₜg = −2Ric` supplied internally by the PDE (`hS.equation`) and the
`Ric`/`scalar` time-derivatives taken as hypotheses (to be discharged from the proved
Ricci/scalar evolutions in the final assembly).  The derivative is the full 3D reaction–diffusion
right-hand side prior to the diffusion-split and reaction normalization. -/
theorem solution_rm04_timeDeriv_kn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (X Y Z W : TangentSpace I x)
    {ricXZ' ricYZ' ricXW' ricYW' sc' : Real}
    (hXZ : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
      ricXZ' D.carrier (t : Real))
    (hYZ : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z))
      ricYZ' D.carrier (t : Real))
    (hXW : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W))
      ricXW' D.carrier (t : Real))
    (hYW : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W))
      ricYW' D.carrier (t : Real))
    (hSc : HasDerivWithinAt (fun σ : Real => S.scalar σ x) sc' D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun σ : Real => S.base.rm04 σ x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W))
      (-(ricXZ' * (S.base.metric (t : Real)).inner x Y W
          + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z)
            * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)))
        + (ricYZ' * (S.base.metric (t : Real)).inner x X W
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)))
        + (ricXW' * (S.base.metric (t : Real)).inner x Y Z
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)))
        - (ricYW' * (S.base.metric (t : Real)).inner x X Z
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z)))
        + (sc' / 2
            * ((S.base.metric (t : Real)).inner x X Z * (S.base.metric (t : Real)).inner x Y W
                - (S.base.metric (t : Real)).inner x Y Z * (S.base.metric (t : Real)).inner x X W)
          + S.scalar (t : Real) x / 2
            * ((-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
                  * (S.base.metric (t : Real)).inner x Y W
                + (S.base.metric (t : Real)).inner x X Z
                  * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W))
                - ((-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z))
                      * (S.base.metric (t : Real)).inner x X W
                    + (S.base.metric (t : Real)).inner x Y Z
                      * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W))))))
      D.carrier (t : Real) := by
  have hfield :
      (fun σ : Real => S.base.rm04 σ x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W))
        = fun σ : Real =>
          -(S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
              * (S.base.metric σ).inner x Y W
            + S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
              * (S.base.metric σ).inner x X W
            + S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
              * (S.base.metric σ).inner x Y Z
            - S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
              * (S.base.metric σ).inner x X Z
            + (S.scalar σ x / 2)
              * ((S.base.metric σ).inner x X Z * (S.base.metric σ).inner x Y W
                  - (S.base.metric σ).inner x Y Z * (S.base.metric σ).inner x X W) :=
    funext fun σ => solution_rm04_kn_field (I := I) S σ x hdim X Y Z W
  rw [hfield]
  have hg : ∀ P Q : TangentSpace I x,
      HasDerivWithinAt (fun σ : Real => (S.base.metric σ).inner x P Q)
        (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) P Q))
        D.carrier (t : Real) := by
    intro P Q
    have h := hS.equation t x P Q
    simpa [RicciAtFamily.toTensorField_apply] using h
  have hd :=
    ((((((hXZ.neg.mul (hg Y W)).add ((hYZ.mul (hg X W)))).add (hXW.mul (hg Y Z))).sub
      (hYW.mul (hg X Z))).add
      (((hSc.div_const 2).mul (((hg X Z).mul (hg Y W)).sub ((hg Y Z).mul (hg X W)))))))
  convert hd using 1
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- **Scalar = Ricci trace at an orthonormal basis (htr discharger).**  Combines the
intrinsic trace identity `scalar_eq_metricTrace` with the banked `scalarTrace_delta`,
collapsing the `delta3` weights.  Discharges the `htr` input of `rm04BaseEvolution_at`
(`sc (R t) = R t 0 0 + R t 1 1 + R t 2 2` after identifying `R` via `hR`). -/
theorem scalar_eq_trace_ortho
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    S.scalar t x =
      S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 0) (basis 0))
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 1) (basis 1))
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 2) (basis 2)) := by
  classical
  have h : DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I)
        (S.base.metric t) (S.ricciAt t x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        DifferentialGeometry.Integral.Connection.delta3 i j *
          S.ricciAt t x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) :=
    scalarTrace_delta (I := I) (S.base.metric t) (S.ricciAt t x) horth
  rw [show S.scalar t x =
        DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I)
          (S.base.metric t) (S.ricciAt t x) from
      SolutionOn.scalar_eq_metricTrace (I := I) S t x, h]
  simp [DifferentialGeometry.Integral.Connection.delta3, Fin.sum_univ_three]

open DifferentialGeometry.Dim3Reaction in
/-- **Scalar evolution in `normSq` form (hScDot discharger).**  Converts the banked
`ScalarEvolutionEquationOn` (`∂ₜS = ΔS + 2|Ric|²`, produced by `scalarEvolOfSmooth`) to the
`rm04BaseEvolution_at` input shape `∂ₜS = lapS + 2·normSq R` at a `g_t`-orthonormal basis,
via `ricciNorm_inner` (orthonormal `|Ric|²` = component square sum). -/
theorem scalarDot_ortho
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (scalarLap : Real -> M -> Real)
    (hsc : ScalarEvolutionEquationOn (D := D) S.scalar scalarLap (ricciNorm (I := I) S))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric (t : Real)) x basis)
    (R : Fin 3 -> Fin 3 -> Real)
    (hRdef : forall i j : Fin 3,
      R i j = S.ricciAt (t : Real) x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j))) :
    HasDerivWithinAt (fun s : Real => S.scalar s x)
      (scalarLap (t : Real) x + 2 * normSq R)
      D.carrier (t : Real) := by
  classical
  refine (hsc t x).congr_deriv ?_
  have hinv := DifferentialGeometry.Integral.Connection.orthonormal_invBasis3
    (I := I) (S.base.metric (t : Real)) basis horth
  have hnorm :
      ricciNormAt (I := I) (S.base.ricciAt (t : Real) x) basis =
        ricciNorm (I := I) S (t : Real) x := by
    simpa [ricciNorm, SolutionOn.ricci, SolutionOn.ricciAt] using
      (ricciNorm_inner (I := I) (S.base.metric (t : Real))
        (S.base.ricciAt (t : Real) x) basis hinv)
  rw [← hnorm]
  have hcomp : forall i j : Fin 3,
      DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis
          (S.base.ricciAt (t : Real) x) i j = R i j := by
    intro i j
    rw [DifferentialGeometry.Integral.Connection.ricciCompAt_apply, hRdef]
    rfl
  unfold ricciNormAt normSq
  simp only [hcomp]

open DifferentialGeometry.Dim3Reaction in
/-- **Dim-3 KN realization of supplied `Rm04` components (hkn discharger).**  At `(t,x)`
with the supplied `Rm04` section realizing the solution's lowered Riemann tensor and a
`g_t`-orthonormal frame, the `rm04Comp` component array is the bare KN array `rm R` of
the frame Ricci components.  From `solution_rm04_kn_field` (dim 3, Weyl = 0). -/
theorem rm04CompknOrtho
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsec : forall v : Fin 4 -> TangentSpace I x, Rm04 t x v = S.base.rm04 t x v)
    (horthf : forall i j : Fin 3,
      (S.base.metric t).inner x (frame i x) (frame j x) = (if i = j then (1 : Real) else 0))
    (R : Fin 3 -> Fin 3 -> Real)
    (hRdef : forall i j : Fin 3,
      R i j = S.ricciAt t x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)))
    (htr : S.scalar t x = sc R)
    (i k j l : Fin 3) :
    DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l
      = rm R i k j l := by
  have hR' : forall a b : Fin 3,
      S.ricciAt t x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame a x) (frame b x))
        = R a b := fun a b => (hRdef a b).symm
  unfold DifferentialGeometry.Integral.Connection.rm04Comp
  rw [hsec, solution_rm04_kn_field (I := I) S t x hdim, htr]
  simp only [horthf, hR']
  unfold rm kd
  ring

open DifferentialGeometry.Dim3Reaction in
/-- **Lichnerowicz evolution in `Cc`/`Rsq` form (hRicDot discharger).**  Converts the
banked `RicciLichnerowiczEquationInFrame` instance at `(t,x)` to the
`rm04BaseEvolution_at` input shape `∂ₜR_ij = lap_ij − 2·Cc − 2·Rsq`, given a
`δ`-orthonormal inverse metric at `(t,x)` and the dim-3 KN realization `hkn` of the
supplied `Rm04` components.  The raised/one-up Ricci components collapse to the plain
components, the curvature contraction becomes `Cc`, and the two Ricci actions become
`2·Rsq` (using `R`-symmetry). -/
theorem ricDot_ortho
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (hlich : RicciLichnerowiczEquationInFrame (D := D) (I := I) S Rm04 gInv frame roughLapRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hginv : forall i j : Fin 3, gInv (t : Real) x i j = (if i = j then (1 : Real) else 0))
    (R : Real -> Fin 3 -> Fin 3 -> Real)
    (hRdef : forall (s : Real) (i j : Fin 3),
      R s i j = ricciCompInFrame (I := I) S frame s x i j)
    (hsym : forall i j : Fin 3, R (t : Real) i j = R (t : Real) j i)
    (hkn : forall i k j l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
        = rm (R (t : Real)) i k j l)
    (i j : Fin 3) :
    HasDerivWithinAt (fun s : Real => R s i j)
      (roughLapRic (t : Real) x i j - 2 * Cc (R (t : Real)) i j - 2 * Rsq (R (t : Real)) i j)
      D.carrier (t : Real) := by
  classical
  have h := hlich t x i j
  have h' := h.congr (fun s _ => (hRdef s i j)) (hRdef (t : Real) i j)
  refine h'.congr_deriv ?_
  have hR' : forall (s : Real) (a b : Fin 3),
      S.ricciAt s x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame a x) (frame b x))
        = R s a b := fun s a b => (hRdef s a b).symm
  unfold lichnerowiczRHSInFrame ricciLeftActionCompInFrame ricciRightActionCompInFrame
    ricciOneUpCompInFrame raisedRicciCompInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame
    ricciTwoTensorField ricciCompInFrame Cc Rsq
  simp only [hginv, hkn, hR', Fin.sum_univ_three, Fin.isValue,
    Fin.reduceEq, reduceIte, ite_mul, mul_ite, one_mul, zero_mul, mul_zero, mul_one,
    add_zero, zero_add]
  simp only [hsym j 0, hsym j 1, hsym j 2, hsym 0 i, hsym 1 i, hsym 2 i]
  ring

set_option maxHeartbeats 1000000 in
open DifferentialGeometry.Dim3Reaction in
/-- Ricci component evolution in an arbitrary orthonormal `Fin 3` basis,
produced directly from `IsSolutionOn` without a supplied frame equation. -/
theorem ricDot_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric (t : Real)) x basis)
    (R : Real → Fin 3 → Fin 3 → Real)
    (hR : ∀ (s : Real) (i j : Fin 3),
      R s i j = S.ricciAt s x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)))
    (i j : Fin 3) :
    HasDerivWithinAt (fun s : Real => R s i j)
      (DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt
          (I := I) (S.base.metric (t : Real))
          (ricciNabla2WMP (I := I) S (t : Real) x)
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) -
        2 * Cc (R (t : Real)) i j - 2 * Rsq (R (t : Real)) i j)
      D.carrier (t : Real) := by
  classical
  have hRic : ∀ a b : Fin 3,
      S.ricciAt (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis b)) =
        R (t : Real) a b := fun a b => (hR (t : Real) a b).symm
  have hRicSec : ∀ a b : Fin 3,
      S.ricci (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis b)) =
        R (t : Real) a b := by
    intro a b
    simpa [SolutionOn.ricci, SolutionOn.ricciAt, SolutionFamily.ricci,
      SolutionFamily.ricciAt] using hRic a b
  have horthf : ∀ a b : Fin 3,
      (S.base.metric (t : Real)).inner x (basis a) (basis b) =
        (if a = b then (1 : Real) else 0) := by
    intro a b
    simpa [DifferentialGeometry.Integral.Connection.delta3] using horth a b
  have htr : S.scalar (t : Real) x = sc (R (t : Real)) := by
    rw [scalar_eq_trace_ortho (I := I) S (t : Real) x horth]
    unfold sc
    rw [hR (t : Real) 0 0, hR (t : Real) 1 1, hR (t : Real) 2 2]
  have hRm : ∀ a k b l : Fin 3,
      S.base.rm04 (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (basis a) (basis k) (basis b) (basis l)) =
        rm (R (t : Real)) a k b l := by
    intro a k b l
    rw [solution_rm04_kn_field (I := I) S (t : Real) x hdim, htr]
    simp only [horthf, hRic]
    unfold rm kd
    ring
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric (t : Real)) x basis
        (identityInvMetric (Idx := Fin 3)) :=
    by
      have hinv' :=
        DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
          (I := I) (S.base.metric (t : Real)) basis horthf
      simpa [identityInvMetric, diagonalInvMetric] using hinv'
  have hreact :
      ricciActualReactAt (I := I) S (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) =
        -2 * Cc (R (t : Real)) i j - 2 * Rsq (R (t : Real)) i j := by
    rw [actualReact_comp (I := I) (M := M) S (t : Real) x basis
      (identityInvMetric (Idx := Fin 3)) hinv i j]
    unfold DifferentialGeometry.Integral.Connection.rm04RicciContractionAt
      DifferentialGeometry.Integral.Connection.raised02CompAt
      DifferentialGeometry.Integral.Connection.ricciQuadraticAt
      DifferentialGeometry.Integral.Connection.oneUp02CompAt Cc Rsq
    simp only [identityInvMetric, diagonalInvMetric, hRm, hRicSec,
      Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, reduceIte,
      ite_mul, mul_ite, one_mul, zero_mul, mul_zero, mul_one, add_zero, zero_add]
  have hpair := ricciPairDeriv (I := I) S hS t x (basis i) (basis j)
  have hRfun : ∀ s : Real,
      R s i j = S.ricci s x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) := by
    intro s
    simpa [SolutionOn.ricci, SolutionOn.ricciAt, SolutionFamily.ricci,
      SolutionFamily.ricciAt] using hR s i j
  have hpair' := hpair.congr (fun s _ => hRfun s) (hRfun (t : Real))
  refine hpair'.congr_deriv ?_
  rw [hreact]
  ring

set_option maxHeartbeats 1000000 in
open DifferentialGeometry.Dim3Reaction in
/-- **Pointwise Uhlenbeck-base packaging (B3e core).**  At a `g_t`-orthonormal frame
`e` at `(t,x)` of a dim-3 solution, with the Ricci/scalar time-derivatives supplied in
diffusion-plus-reaction form (`∂ₜRic = lap + Q_Ric`, `∂ₜS = lapS + Q_S`, the proved
Lichnerowicz/scalar shapes), the lowered Riemann components satisfy the corrected-sign
pre-Uhlenbeck evolution `∂ₜRm04 = KN(lap,lapS,δ) − 2·B# − drift`, with `B#`/`drift` the
bare dim-3 reaction algebra of `UhlReaction3` (identified with the
`uhlenbeckBTensorInFrame`/`riemann04RicciDriftInFrame` arrays by `uhlBt_eq_bt` /
`uhlDrift_eq_drift`).  Combines the KN time derivative `solution_rm04_timeDeriv_kn`
with the reaction match `reaction_match` and Ricci symmetry `ricciSym_can`. -/
theorem rm04BaseEvolution_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (e : Fin 3 -> TangentSpace I x)
    (horth : forall i j : Fin 3,
      (S.base.metric (t : Real)).inner x (e i) (e j) = (if i = j then (1 : Real) else 0))
    (R : Real -> Fin 3 -> Fin 3 -> Real)
    (hR : forall (s : Real) (i j : Fin 3),
      R s i j = S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (e i) (e j)))
    (lap : Fin 3 -> Fin 3 -> Real) (lapS : Real)
    (hRicDot : forall i j : Fin 3, HasDerivWithinAt (fun s : Real => R s i j)
      (lap i j - 2 * Cc (R (t : Real)) i j - 2 * Rsq (R (t : Real)) i j)
      D.carrier (t : Real))
    (hScDot : HasDerivWithinAt (fun s : Real => S.scalar s x)
      (lapS + 2 * normSq (R (t : Real))) D.carrier (t : Real))
    (htr : S.scalar (t : Real) x = sc (R (t : Real)))
    (a b c d : Fin 3) :
    HasDerivWithinAt
      (fun s : Real => S.base.rm04 s x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) (e a) (e b) (e c) (e d)))
      (-(lap a c) * kd b d + lap b c * kd a d + lap a d * kd b c - lap b d * kd a c
          + lapS / 2 * (kd a c * kd b d - kd b c * kd a d)
        - 2 * (Bt (R (t : Real)) a b c d - Bt (R (t : Real)) a b d c
            + Bt (R (t : Real)) a c b d - Bt (R (t : Real)) a d b c)
        - drift (R (t : Real)) a b c d)
      D.carrier (t : Real) := by
  classical
  have hsym : forall i j : Fin 3, R (t : Real) i j = R (t : Real) j i := by
    intro i j
    rw [hR, hR]
    exact ricciSym_can (I := I) S (t : Real) x (e i) (e j)
  have horthk : forall i j : Fin 3,
      (S.base.metric (t : Real)).inner x (e i) (e j) = kd i j := horth
  have hXZ := (hRicDot a c).congr (fun s _ => (hR s a c).symm) ((hR (t : Real) a c).symm)
  have hYZ := (hRicDot b c).congr (fun s _ => (hR s b c).symm) ((hR (t : Real) b c).symm)
  have hXW := (hRicDot a d).congr (fun s _ => (hR s a d).symm) ((hR (t : Real) a d).symm)
  have hYW := (hRicDot b d).congr (fun s _ => (hR s b d).symm) ((hR (t : Real) b d).symm)
  have hbig :=
    solution_rm04_timeDeriv_kn (I := I) S hS t x hdim
      (e a) (e b) (e c) (e d) hXZ hYZ hXW hYW hScDot
  refine hbig.congr_deriv ?_
  have hmatch := DifferentialGeometry.Dim3Reaction.reaction_match hsym a b c d
  simp only [DifferentialGeometry.Dim3Reaction.KNQ, DifferentialGeometry.Dim3Reaction.QRic,
    DifferentialGeometry.Dim3Reaction.QS, DifferentialGeometry.Dim3Reaction.Gg,
    DifferentialGeometry.Dim3Reaction.Bsharp] at hmatch
  simp only [horthk, htr]
  simp only [show forall (s : Real) (i j : Fin 3),
      S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (e i) (e j))
        = R s i j from fun s i j => (hR s i j).symm]
  linear_combination hmatch

/-- **Fixed-frame Ricci symmetry for any frame (hlich wiring input).**  Instantiates the
metric-derived pointwise symmetry `ricciSym_can`; with the standing
`h_ricci : RicciEvolutionEquationInFrame` and a symmetric `gInv`, this feeds
`ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm` to produce the
`hlich` input of `ricDot_ortho` — no further new code is needed on that wire. -/
theorem ricciSymFrame_can
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} (frame : Idx -> (x : M) -> TangentSpace I x) :
    RicciSymmetricInFrameOn (I := I) S frame :=
  fun t x i j => ricciSym_can (I := I) S t x (frame i x) (frame j x)

/-- **The dim-3 KN identity at arbitrary multilinear inputs (B3c step 0).**  The
all-slots form of `solution_rm04_kn_field`, turning the `vec4`-tuple statement into an
identity of the full multilinear maps — the shape needed to push the rough Laplacian
through the Kulkarni–Nomizu combination (`∇g = 0` diffusion split). -/
theorem solution_rm04_kn_all
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : Fin 4 -> TangentSpace I x) :
    S.base.rm04 s x v =
      -(S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 0) (v 2)))
          * (S.base.metric s).inner x (v 1) (v 3)
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 1) (v 2))
          * (S.base.metric s).inner x (v 0) (v 3)
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 0) (v 3))
          * (S.base.metric s).inner x (v 1) (v 2)
        - S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 1) (v 3))
          * (S.base.metric s).inner x (v 0) (v 2)
        + (S.scalar s x / 2)
          * ((S.base.metric s).inner x (v 0) (v 2) * (S.base.metric s).inner x (v 1) (v 3)
              - (S.base.metric s).inner x (v 1) (v 2) * (S.base.metric s).inner x (v 0) (v 3)) := by
  have hv : v = DifferentialGeometry.Integral.Connection.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext q
    fin_cases q <;> rfl
  rw [hv]
  exact solution_rm04_kn_field (I := I) S s x hdim (v 0) (v 1) (v 2) (v 3)

set_option maxHeartbeats 1000000 in
/-- **(45a) Coordinate-frame `hrm` from orthonormal-frame derivatives.**  The tower's
`hrm` input (`realizedRmBase` time derivative at the centre `x₀`, coordinate frame) follows
from the per-component derivatives in any tangent basis (the `rm04BaseEvolution_at`
outputs at an orthonormal basis) by the time-independent change of basis:
`realizedRmBase s x₀ m = Σ_slots rm04(s)(basis∘slots)·K(slots,m)` for ALL `s` by
4-multilinearity, with constant coefficients `K = ∏ₐ basis.coord (slots a) (∂_{m a})`.
No frame redesign is needed: the tower consumes `hrm` per regular time. -/
theorem rmBaseDeriv_basis
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x₀))
    (V : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (hD : forall a b c d : Fin 3, HasDerivWithinAt
      (fun s : Real => S.base.rm04 s x₀
        (DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (basis a) (basis b) (basis c) (basis d)))
      (V a b c d) D.carrier (t : Real))
    (m : Fin 4 -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
      (∑ slots : Fin 4 -> Fin 3,
        V (slots 0) (slots 1) (slots 2) (slots 3) *
          ∏ a : Fin 4, basis.coord (slots a)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ (m a) x₀))
      D.carrier (t : Real) := by
  classical
  have hexp : (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
      = fun s : Real =>
        ∑ slots : Fin 4 -> Fin 3,
          S.base.rm04 s x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3))) *
            ∏ a : Fin 4, basis.coord (slots a)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ (m a) x₀) := by
    funext s
    rw [realizedRmBase_apply,
      tensor0S_apply_eq_sum (I := I) basis (S.base.rm04 s x₀)
        (fun q => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ (m q) x₀)]
    refine Finset.sum_congr rfl fun slots _ => ?_
    have hvec :
        (fun a : Fin 4 => basis (slots a)) =
          DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
      funext q
      fin_cases q <;> rfl
    rw [component0S_apply, hvec]
  rw [hexp]
  refine HasDerivWithinAt.fun_sum ?_
  intro slots _
  exact (hD (slots 0) (slots 1) (slots 2) (slots 3)).mul_const _

/-- The solution's connection at time `t` is `∞`-smooth (Levi-Civita). -/
theorem connSmoothSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

/-- Metric compatibility of the solution's connection at time `t` (Levi-Civita). -/
theorem metricCompatSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.family.metric t) := by
  simpa [SolutionFamily.connection, SolutionOn.family_metric] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t)

/-- **The canonical `∇Ric` realizer for the solution (B3c-1 input).**  The canonical
total covariant derivative of the time-`t` Ricci field realizes `∇Ric` in the
`TotalNabla0SRealizes` sense — the Ricci-side input of the KN diffusion split, to be
combined with `zero_realizes_metric`/`nabla_smul_metric`/`nabla0S_product_realizes`/
`totalNabla0SRealizes_domDomCongr`. -/
theorem ricNablaRealizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t)
      (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t))) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (S.family.connection t) (S.ricci t) _

set_option backward.isDefEq.respectTransparency false in
/-- **B3c-1, generic Ric⊗g KN term:** any slot-permuted product `(Ric ⊗ g)·e` — the
T1–T4 terms of the Kulkarni–Nomizu combination are the instances `e = swap(1,2)`,
`(swap 1 2).trans (swap 0 1)`, `(swap 2 3).trans (swap 1 3)`, and
`((swap 3 2).trans (swap 1 3)).trans (swap 0 1)` — has its covariant derivative
realized by the permuted product-Leibniz right-hand side (the `∇g`-half is the zero
field).  Composes `nabla0S_product_realizes` (with `ricNablaRealizes` and
`zero_realizes_metric`) with `totalNabla0SRealizes_domDomCongr`. -/
theorem knTermRealizes
    [IsManifold I 2 M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 2) (S.family.connection t)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) e
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
          (S.ricci t) (metricTensorField (I := I) (S.family.metric t))))
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (frontExtendEquiv e)
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 2)
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2)
              (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 (S.family.connection t) (S.ricci t)
                (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                  2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
              (metricTensorField (I := I) (S.family.metric t)))
          + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 2)
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1)
              (S.ricci t) 0))) :=
  totalNabla0SRealizes_domDomCongr (I := I)
    (S.family.connection t) e _ _
    (nabla0S_product_realizes (I := I) (S.family.connection t)
      (S.ricci t) (metricTensorField (I := I) (S.family.metric t)) _ 0
      (ricNablaRealizes (I := I) S t)
      (zero_realizes_metric (I := I) (S.family.connection t)
        (S.family.metric t) (metricCompatSol (I := I) S t)))

set_option backward.isDefEq.respectTransparency false in
/-- **B3c-1, generic scalar KN term:** any slot-permuted product `((S·g) ⊗ g)·e` — the
two `(S/2)·δδ`-terms of the Kulkarni–Nomizu combination are (half of) the instances
`e = swap 1 2` and `e = (swap 1 2).trans (swap 0 1)` — has its covariant derivative
realized by the permuted product-Leibniz right-hand side, with the `∇(S·g)`-half given
by `nabla_smul_metric` (`∇(S·g) = dS⊗g`, `dS = duSec`) and the `∇g`-half zero. -/
theorem knScalRealizes
    [IsManifold I 2 M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 2) (S.family.connection t)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) e
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
          (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (S.scalar t) (scalarSmoothOfSol (I := I) S t)
            (metricTensorField (I := I) (S.family.metric t)))
          (metricTensorField (I := I) (S.family.metric t))))
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (frontExtendEquiv e)
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 2)
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2)
              (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
                (DifferentialGeometry.Integral.Connection.duSec (I := I)
                  (S.scalar t) (scalarSmoothOfSol (I := I) S t))
                (metricTensorField (I := I) (S.family.metric t)))
              (metricTensorField (I := I) (S.family.metric t)))
          + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 2)
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1)
              (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
                (S.scalar t) (scalarSmoothOfSol (I := I) S t)
                (metricTensorField (I := I) (S.family.metric t)))
              0))) :=
  totalNabla0SRealizes_domDomCongr (I := I)
    (S.family.connection t) e _ _
    (nabla0S_product_realizes (I := I) (S.family.connection t)
      _ (metricTensorField (I := I) (S.family.metric t)) _ 0
      (nabla_smul_metric (I := I) (M := M) (S.family.connection t)
        (S.family.metric t) (metricCompatSol (I := I) S t)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t)
        (DifferentialGeometry.Integral.Connection.duSec (I := I)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t))
        (fun x v => by
          rw [DifferentialGeometry.Integral.Connection.duSec_apply]
          exact DifferentialGeometry.Integral.Connection.differential1FormFun_apply_eq_extDerivFun
            (I := I) (S.scalar t) x v))
      (zero_realizes_metric (I := I) (S.family.connection t)
        (S.family.metric t) (metricCompatSol (I := I) S t)))

section KnField

set_option backward.isDefEq.respectTransparency false

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- The generic Ric⊗g KN term as a field. -/
private noncomputable def knRicT
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) e
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
      (S.ricci t) (metricTensorField (I := I) (S.family.metric t)))

/-- The generic (S·g)⊗g KN term as a field. -/
private noncomputable def knScalT
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) e
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
      (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t)
        (metricTensorField (I := I) (S.family.metric t)))
      (metricTensorField (I := I) (S.family.metric t)))

/-- The slot permutations of the four Ric⊗g KN terms and the two scalar terms:
`e₁` realizes `A(v₀,v₂)·B(v₁,v₃)`, `e₂` realizes `A(v₁,v₂)·B(v₀,v₃)`,
`e₃` realizes `A(v₀,v₃)·B(v₁,v₂)`, `e₄` realizes `A(v₁,v₃)·B(v₀,v₂)`. -/
private def knE1 : Fin (2 + 2) ≃ Fin (2 + 2) := Equiv.swap 1 2
private def knE2 : Fin (2 + 2) ≃ Fin (2 + 2) := (Equiv.swap (1 : Fin (2 + 2)) 2).trans (Equiv.swap 0 1)
private def knE3 : Fin (2 + 2) ≃ Fin (2 + 2) := (Equiv.swap (2 : Fin (2 + 2)) 3).trans (Equiv.swap 1 3)
private def knE4 : Fin (2 + 2) ≃ Fin (2 + 2) :=
  ((Equiv.swap (3 : Fin (2 + 2)) 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 1)

/-- **The dim-3 Kulkarni–Nomizu field** `KN(Ric, S, g)` as a signed combination of the
slot-permuted products: `−T₁ + T₂ + T₃ − T₄ + (1/2)·T₅ₐ − (1/2)·T₅ᵦ`. -/
private noncomputable def knField
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  ((-1 : Real) • knRicT (I := I) S t knE1 + knRicT (I := I) S t knE2)
    + (knRicT (I := I) S t knE3 + (-1 : Real) • knRicT (I := I) S t knE4)
    + ((1 / 2 : Real) • knScalT (I := I) S t knE1
        + (-(1 / 2) : Real) • knScalT (I := I) S t knE2)

set_option maxHeartbeats 1000000 in
/-- **B3c-1 sum step: the KN field's covariant derivative is realized** by the
corresponding signed combination of the term realizers (`knTermRealizes` ×4,
`knScalRealizes` ×2, combined by `TotalNabla0SRealizes.add`/`.smul`).  The realizer is
the underscore-elaborated combination; its KN-shape normal form is the ext-transport
step's concern, not this lemma's. -/
private theorem knFieldRealizes
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    ∃ knField' : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (2 + 2 + 1),
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (2 + 2) (S.family.connection t) (knField (I := I) S t) knField' :=
  ⟨_, (((knTermRealizes (I := I) S t knE1).smul (-1 : Real)).add
        (knTermRealizes (I := I) S t knE2)).add
      (((knTermRealizes (I := I) S t knE3).add
          ((knTermRealizes (I := I) S t knE4).smul (-1 : Real)))) |>.add
      (((knScalRealizes (I := I) S t knE1).smul (1 / 2 : Real)).add
        ((knScalRealizes (I := I) S t knE2).smul (-(1 / 2) : Real)))⟩

/-- **The canonical `∇²Ric` realizer (B3c-2 input):** the canonical total covariant
derivative of the canonical `∇Ric` field realizes the second Ricci derivative. -/
theorem ric2NablaRealizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 1) (S.family.connection t)
      (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
      (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (2 + 1) (S.family.connection t)
        (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (S.ricci t)
          (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
            2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          (2 + 1) (S.family.connection t) (connSmoothSol (I := I) S t) _)) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (2 + 1) (S.family.connection t) _ _

/-- **The canonical `∇(dS)` (Hessian) realizer (B3c-2 input).** -/
theorem duNablaRealizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t)
      (DifferentialGeometry.Integral.Connection.duSec (I := I)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t))
      (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 (S.family.connection t)
        (DifferentialGeometry.Integral.Connection.duSec (I := I)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          1 (S.family.connection t) (connSmoothSol (I := I) S t) _)) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.family.connection t) _ _

/-- The realizer of a generic Ric⊗g KN term (the `knTermRealizes` witness). -/
private noncomputable def knRicD
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2 + 1) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) (frontExtendEquiv e)
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 2)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2)
          (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.family.connection t) (S.ricci t)
            (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
              2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
          (metricTensorField (I := I) (S.family.metric t)))
      + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 2)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1)
          (S.ricci t) 0))

/-- The realizer of a generic (S·g)⊗g KN term (the `knScalRealizes` witness). -/
private noncomputable def knScalD
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2 + 1) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) (frontExtendEquiv e)
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 2)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.duSec (I := I)
              (S.scalar t) (scalarSmoothOfSol (I := I) S t))
            (metricTensorField (I := I) (S.family.metric t)))
          (metricTensorField (I := I) (S.family.metric t)))
      + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 2)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1)
          (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (S.scalar t) (scalarSmoothOfSol (I := I) S t)
            (metricTensorField (I := I) (S.family.metric t)))
          0))

/-- **The explicit KN-form realizer of `∇Rm04`** (dim 3): the signed combination of the
six term realizers, mirroring `knField`. -/
private noncomputable def knFieldD
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2 + 1) :=
  ((-1 : Real) • knRicD (I := I) S t knE1 + knRicD (I := I) S t knE2)
    + (knRicD (I := I) S t knE3 + (-1 : Real) • knRicD (I := I) S t knE4)
    + ((1 / 2 : Real) • knScalD (I := I) S t knE1
        + (-(1 / 2) : Real) • knScalD (I := I) S t knE2)

set_option maxHeartbeats 1000000 in
/-- **B3c-2, generic second derivative of a Ric⊗g KN term:** `∇(knRicD e)` is realized
by the one-rank-up closure stack — outer `frontExtendEquiv (frontExtendEquiv e)`, the
two Leibniz branches differentiated again (`∇²Ric`, `∇g = 0`, `∇0 = 0`). -/
private theorem knTerm2Realizes
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 2 + 1) (S.family.connection t)
      (knRicD (I := I) S t e)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (frontExtendEquiv (frontExtendEquiv e))
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (frontExtendEquiv (leibnizLeftEquiv 2 2))
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv (2 + 1) 2)
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1 + 1) (q := 2)
                  (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    (2 + 1) (S.family.connection t)
                    (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                      2 (S.family.connection t) (S.ricci t)
                      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                        2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      (2 + 1) (S.family.connection t) (connSmoothSol (I := I) S t) _))
                  (metricTensorField (I := I) (S.family.metric t)))
              + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv (2 + 1) 2)
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                  (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    2 (S.family.connection t) (S.ricci t)
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
                  0))
          + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (frontExtendEquiv (leibnizRightEquiv 2 2))
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 (2 + 1))
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                  (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    2 (S.family.connection t) (S.ricci t)
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
                  0)
              + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 (2 + 1))
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1 + 1)
                  (S.ricci t) 0)))) :=
  totalNabla0SRealizes_domDomCongr (I := I)
    (S.family.connection t) (frontExtendEquiv e) _ _
    ((totalNabla0SRealizes_domDomCongr (I := I)
        (S.family.connection t) (leibnizLeftEquiv 2 2) _ _
        (nabla0S_product_realizes (I := I) (S.family.connection t)
          _ (metricTensorField (I := I) (S.family.metric t)) _ 0
          (ric2NablaRealizes (I := I) S t)
          (zero_realizes_metric (I := I) (S.family.connection t)
            (S.family.metric t) (metricCompatSol (I := I) S t)))).add
      (totalNabla0SRealizes_domDomCongr (I := I)
        (S.family.connection t) (leibnizRightEquiv 2 2) _ _
        (nabla0S_product_realizes (I := I) (S.family.connection t)
          (S.ricci t) 0 _ 0
          (ricNablaRealizes (I := I) S t)
          (zero_realizes_nabla (I := I) (2 + 1) (S.family.connection t)))))

set_option maxHeartbeats 1000000 in
/-- **B3c-2, generic second derivative of a scalar KN term:** `∇(knScalD e)` is
realized by the one-rank-up closure stack, with the `∇((dS⊗g)⊗g)`-branch supplied by
the Hessian handle `duNablaRealizes` and the `∇((S·g)⊗0)`-branch by
`nabla_smul_metric` and the zero realizers. -/
private theorem knScal2Realizes
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 2 + 1) (S.family.connection t)
      (knScalD (I := I) S t e)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (frontExtendEquiv (frontExtendEquiv e))
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (frontExtendEquiv (leibnizLeftEquiv 2 2))
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv (2 + 1) 2)
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1 + 1) (q := 2)
                  (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 1 2)
                      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1 + 1) (q := 2)
                        (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                          1 (S.family.connection t)
                          (DifferentialGeometry.Integral.Connection.duSec (I := I)
                            (S.scalar t) (scalarSmoothOfSol (I := I) S t))
                          (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                            1 (S.family.connection t) (connSmoothSol (I := I) S t) _))
                        (metricTensorField (I := I) (S.family.metric t)))
                    + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 1 2)
                      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2 + 1)
                        (DifferentialGeometry.Integral.Connection.duSec (I := I)
                          (S.scalar t) (scalarSmoothOfSol (I := I) S t))
                        0))
                  (metricTensorField (I := I) (S.family.metric t)))
              + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv (2 + 1) 2)
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
                    (DifferentialGeometry.Integral.Connection.duSec (I := I)
                      (S.scalar t) (scalarSmoothOfSol (I := I) S t))
                    (metricTensorField (I := I) (S.family.metric t)))
                  0))
          + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (frontExtendEquiv (leibnizRightEquiv 2 2))
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 (2 + 1))
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
                    (DifferentialGeometry.Integral.Connection.duSec (I := I)
                      (S.scalar t) (scalarSmoothOfSol (I := I) S t))
                    (metricTensorField (I := I) (S.family.metric t)))
                  0)
              + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 (2 + 1))
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1 + 1)
                  (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
                    (S.scalar t) (scalarSmoothOfSol (I := I) S t)
                    (metricTensorField (I := I) (S.family.metric t)))
                  0)))) :=
  totalNabla0SRealizes_domDomCongr (I := I)
    (S.family.connection t) (frontExtendEquiv e) _ _
    ((totalNabla0SRealizes_domDomCongr (I := I)
        (S.family.connection t) (leibnizLeftEquiv 2 2) _ _
        (nabla0S_product_realizes (I := I) (S.family.connection t)
          _ (metricTensorField (I := I) (S.family.metric t)) _ 0
          (nabla0S_product_realizes (I := I) (S.family.connection t)
            (DifferentialGeometry.Integral.Connection.duSec (I := I)
              (S.scalar t) (scalarSmoothOfSol (I := I) S t))
            (metricTensorField (I := I) (S.family.metric t)) _ 0
            (duNablaRealizes (I := I) S t)
            (zero_realizes_metric (I := I) (S.family.connection t)
              (S.family.metric t) (metricCompatSol (I := I) S t)))
          (zero_realizes_metric (I := I) (S.family.connection t)
            (S.family.metric t) (metricCompatSol (I := I) S t)))).add
      (totalNabla0SRealizes_domDomCongr (I := I)
        (S.family.connection t) (leibnizRightEquiv 2 2) _ _
        (nabla0S_product_realizes (I := I) (S.family.connection t)
          _ 0 _ 0
          (nabla_smul_metric (I := I) (M := M) (S.family.connection t)
            (S.family.metric t) (metricCompatSol (I := I) S t)
            (S.scalar t) (scalarSmoothOfSol (I := I) S t)
            (DifferentialGeometry.Integral.Connection.duSec (I := I)
              (S.scalar t) (scalarSmoothOfSol (I := I) S t))
            (fun x v => by
              rw [DifferentialGeometry.Integral.Connection.duSec_apply]
              exact DifferentialGeometry.Integral.Connection.differential1FormFun_apply_eq_extDerivFun
                (I := I) (S.scalar t) x v))
          (zero_realizes_nabla (I := I) (2 + 1) (S.family.connection t)))))

set_option maxHeartbeats 2000000 in
/-- **B3c-1 ext-transport: the KN field IS the lowered Riemann tensor** (dim 3,
Weyl = 0).  Pointwise from `solution_rm04_kn_all`; the slot-permuted product fields
evaluate to exactly the KN formula's six terms. -/
private theorem knField_eq_rm04
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : forall x : M, Module.finrank Real (TangentSpace I x) = 3) :
    knField (I := I) S t = S.base.rm04 t := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 2 + 2)
  apply DFunLike.ext
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hric : forall (w : Fin 2 -> TangentSpace I x) (a b : Fin 4),
      w 0 = v a -> w 1 = v b ->
      S.ricci t x w =
        S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v a) (v b)) := by
    intro w a b h0 h1
    change S.ricci t x w = S.ricci t x
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v a) (v b))
    congr 1
    funext j
    fin_cases j
    · simpa [DifferentialGeometry.Integral.Connection.vec2] using h0
    · simpa [DifferentialGeometry.Integral.Connection.vec2] using h1
  rw [solution_rm04_kn_all (I := I) S t x (hdim x) v]
  have hadd (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2)) :
      ((A + B) x) v = A x v + B x v := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
  have hsmul (c : Real)
      (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (2 + 2)) :
      ((c • A) x) v = c * A x v := by
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul]
  have hricT (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
      knRicT (I := I) S t e x v =
        S.ricci t x ((fun i => v (e i)) ∘ Fin.castAdd 2) *
          (S.base.metric t).inner x
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 0)
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 1) := by
    unfold knRicT
    change (ContinuousMultilinearMap.domDomCongr e _) v = _
    rw [Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply,
      metricTensorField_apply, SolutionOn.family_metric]
  have hscalT (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
      knScalT (I := I) S t e x v =
        S.scalar t x *
            (S.base.metric t).inner x
              (((fun i => v (e i)) ∘ Fin.castAdd 2) 0)
              (((fun i => v (e i)) ∘ Fin.castAdd 2) 1) *
          (S.base.metric t).inner x
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 0)
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 1) := by
    unfold knScalT
    change (ContinuousMultilinearMap.domDomCongr e _) v = _
    rw [Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply,
      tensor0SField_smulByFun_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul, metricTensorField_apply,
      metricTensorField_apply, SolutionOn.family_metric]
  have hE1 : (fun i : Fin (2 + 2) => v (knE1 i)) =
      DifferentialGeometry.Integral.Connection.vec4
        (v 0) (v 2) (v 1) (v 3) := by
    funext i
    fin_cases i <;>
      simp [knE1, DifferentialGeometry.Integral.Connection.vec4,
        Equiv.swap_apply_def]
  have hE2 : (fun i : Fin (2 + 2) => v (knE2 i)) =
      DifferentialGeometry.Integral.Connection.vec4
        (v 1) (v 2) (v 0) (v 3) := by
    funext i
    fin_cases i <;>
      simp [knE2, DifferentialGeometry.Integral.Connection.vec4,
        Equiv.swap_apply_def]
  have hE3 : (fun i : Fin (2 + 2) => v (knE3 i)) =
      DifferentialGeometry.Integral.Connection.vec4
        (v 0) (v 3) (v 1) (v 2) := by
    funext i
    fin_cases i <;>
      simp [knE3, DifferentialGeometry.Integral.Connection.vec4,
        Equiv.swap_apply_def]
  have hE4 : (fun i : Fin (2 + 2) => v (knE4 i)) =
      DifferentialGeometry.Integral.Connection.vec4
        (v 1) (v 3) (v 0) (v 2) := by
    funext i
    fin_cases i <;>
      simp [knE4, DifferentialGeometry.Integral.Connection.vec4,
        Equiv.swap_apply_def]
  unfold knField
  repeat rw [hadd]
  repeat rw [hsmul]
  rw [hricT knE1, hricT knE2, hricT knE3, hricT knE4,
    hscalT knE1, hscalT knE2]
  rw [hric _ 0 2 (by simp [knE1, Equiv.swap_apply_def])
        (by simp [knE1, Equiv.swap_apply_def]),
      hric _ 1 2 (by simp [knE2, Equiv.swap_apply_def])
        (by simp [knE2, Equiv.swap_apply_def]),
      hric _ 0 3 (by simp [knE3, Equiv.swap_apply_def])
        (by simp [knE3, Equiv.swap_apply_def]),
      hric _ 1 3 (by simp [knE4, Equiv.swap_apply_def])
        (by simp [knE4, Equiv.swap_apply_def])]
  rw [hE1, hE2, hE3, hE4]
  simp [DifferentialGeometry.Integral.Connection.vec4]
  ring

set_option maxHeartbeats 1000000 in
/-- **B3c-1 ENDPOINT: `∇Rm04` is realized in Kulkarni–Nomizu form** (dim 3).  The
covariant derivative of the solution's lowered Riemann tensor is realized by the
explicit signed combination `knFieldD` of slot-permuted products of `∇Ric`, `dS`, and
`g` — the input that B3c-2 differentiates once more and traces into
`ΔRm04 = KN(ΔRic, ΔS, g)`. -/
private theorem nablaRm04Kn
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : forall x : M, Module.finrank Real (TangentSpace I x) = 3) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + 2) (S.family.connection t) (S.base.rm04 t) (knFieldD (I := I) S t) := by
  rw [← knField_eq_rm04 (I := I) S t hdim]
  exact (((knTermRealizes (I := I) S t knE1).smul (-1 : Real)).add
        (knTermRealizes (I := I) S t knE2)).add
      (((knTermRealizes (I := I) S t knE3).add
          ((knTermRealizes (I := I) S t knE4).smul (-1 : Real)))) |>.add
      (((knScalRealizes (I := I) S t knE1).smul (1 / 2 : Real)).add
        ((knScalRealizes (I := I) S t knE2).smul (-(1 / 2) : Real)))

set_option maxHeartbeats 2000000 in
/-- **B3c-2 PACKAGE: the full first- and second-derivative KN package for `Rm04`**
(dim 3): `∇Rm04` realized by `knFieldD` (KN of `∇Ric`, `dS`, `g`) and `∇(knFieldD)`
realized by the signed combination of the six explicit level-2 witnesses.  This is the
`CanonicalSpatialDerivs0S`-shaped input for the trace step
(`ΔRm04 = KN(ΔRic, ΔS, g)`), mirroring `metricDerivsZero`. -/
private noncomputable def rm04DerivsKn
    [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : forall x : M, Module.finrank Real (TangentSpace I x) = 3) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) (S.base.rm04 t) :=
  ⟨knFieldD (I := I) S t, _,
    nablaRm04Kn (I := I) S t hdim,
    (((knTerm2Realizes (I := I) S t knE1).smul (-1 : Real)).add
        (knTerm2Realizes (I := I) S t knE2)).add
      (((knTerm2Realizes (I := I) S t knE3).add
          ((knTerm2Realizes (I := I) S t knE4).smul (-1 : Real)))) |>.add
      (((knScal2Realizes (I := I) S t knE1).smul (1 / 2 : Real)).add
        ((knScal2Realizes (I := I) S t knE2).smul (-(1 / 2) : Real)))⟩

/-- The second derivative in the KN package is the canonical all-order
`nablaKRm04Field` at level two. -/
private theorem rm04Nab2Kn_eq
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    (rm04DerivsKn (I := I) S t hdim).nabla2A =
      nablaKRm04Field (I := I) S t 2 := by
  let P := rm04DerivsKn (I := I) S t hdim
  have hfirst : P.nablaA = nablaKRm04Field (I := I) S t 1 :=
    totalNabla0SRealizes_unique P.first
      (nablaKRm04Field_realizes (I := I) S t 0)
  have hsecond := P.second
  rw [hfirst] at hsecond
  exact totalNabla0SRealizes_unique hsecond
    (nablaKRm04Field_realizes (I := I) S t 1)

/-! ### B3c-2 trace step: the rough Laplacian `ΔRm04 = KN(ΔRic, ΔS, g)` (dim 3)

`metricTraceFirstTwoField g` contracts the two leading covariant-derivative slots of the
second covariant derivative `∇²Rm04` — the rough Laplacian `Δ = gⁱʲ∇ᵢ∇ⱼ`.  Applied termwise
to the KN-form package `rm04DerivsKn` (whose `nabla2A` is the signed six-term combination of
the explicit level-2 witnesses) each Leibniz tree collapses: the `∇g = 0`/`∇0 = 0` branches
vanish (`product_zero`/`domDomCongr_zero`), the value-preserving `frontExt`-of-`leibnizLeft`
layers are the identity (`domDomCongr_id_of_valPres`), and the front-factor trace lands on
`∇²Ric` (resp. `∇²S`) by `metricTraceFirstTwoField_product`.  The result is the
Kulkarni–Nomizu combination of the Laplacians. -/

open DifferentialGeometry.Integral.Connection in
/-- Trace of the generic `Ric⊗g` level-2 KN witness (the `knTerm2Realizes` target shape):
the three `∇g = 0`/`∇0 = 0` Leibniz branches vanish and the surviving `∇²Ric ⊗ g` front
factor traces to `(ΔRic) ⊗ g`. -/
private theorem traceRicWit
    [IsManifold I 1 M] [IsManifold I 2 M]
    (gm : SmoothRiemannianMetric I M)
    (e : Fin (2 + 2) ≃ Fin (2 + 2))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 1 + 1))
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 1))
    (C : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (gf : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    metricTraceFirstTwoField (I := I) (M := M) gm
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (frontExtendEquiv (frontExtendEquiv e))
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (frontExtendEquiv (leibnizLeftEquiv 2 2))
              (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv (2 + 1) 2)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1 + 1) (q := 2)
                    A gf)
                + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv (2 + 1) 2)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                    B 0))
            + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (frontExtendEquiv (leibnizRightEquiv 2 2))
              (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 (2 + 1))
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                    B 0)
                + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 (2 + 1))
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1 + 1)
                    C 0))))
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
            (metricTraceFirstTwoField (I := I) (M := M) gm A) gf) := by
  rw [metricTraceFirstTwoField_domDomCongr]
  congr 1
  simp only [MultilinearSection.product_zero, MultilinearSection.domDomCongr_zero,
    add_zero]
  rw [MultilinearSection.domDomCongr_id_of_valPres (∞ : WithTop ℕ∞)
      (frontExtendEquiv (leibnizLeftEquiv 2 2)) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [frontExtendEquiv_succ]
      simp only [leibnizLeftEquiv, finCongr_apply, Fin.val_succ, Fin.val_cast])]
  simp only [leibnizLeftEquiv]
  rw [metricTraceFirstTwoField_product]

open DifferentialGeometry.Integral.Connection in
/-- Trace of the generic `(S·g)⊗g` level-2 KN witness (the `knScal2Realizes` target shape):
all `∇g = 0`/`∇0 = 0` branches vanish and the two nested front-factor traces land on `∇²S`,
giving `((ΔS·g)⊗g)` in the `product (ΔS) g ⊗ g` (rank-0 leading factor) form. -/
private theorem traceScalWit
    [IsManifold I 1 M] [IsManifold I 2 M]
    (gm : SmoothRiemannianMetric I M)
    (e : Fin (2 + 2) ≃ Fin (2 + 2))
    (Hess : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (1 + 1))
    (D1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (Sg : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (gf : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    metricTraceFirstTwoField (I := I) (M := M) gm
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (frontExtendEquiv (frontExtendEquiv e))
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (frontExtendEquiv (leibnizLeftEquiv 2 2))
              (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv (2 + 1) 2)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1 + 1) (q := 2)
                    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 1 2)
                        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1 + 1) (q := 2)
                          Hess gf)
                      + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                        (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 1 2)
                        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2 + 1)
                          D1 0))
                    gf)
                + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv (2 + 1) 2)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
                      D1 gf)
                    0))
            + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (frontExtendEquiv (leibnizRightEquiv 2 2))
              (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 (2 + 1))
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2 + 1) (q := 2 + 1)
                    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
                      D1 gf)
                    0)
                + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 (2 + 1))
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 + 1 + 1)
                    Sg 0))))
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 0) (q := 2)
              (metricTraceFirstTwoField (I := I) (M := M) gm Hess) gf)
            gf) := by
  rw [metricTraceFirstTwoField_domDomCongr]
  congr 1
  simp only [MultilinearSection.product_zero, MultilinearSection.domDomCongr_zero,
    add_zero]
  rw [MultilinearSection.domDomCongr_id_of_valPres (∞ : WithTop ℕ∞)
      (frontExtendEquiv (leibnizLeftEquiv 2 2)) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [frontExtendEquiv_succ]
      simp only [leibnizLeftEquiv, finCongr_apply, Fin.val_succ, Fin.val_cast])]
  simp only [leibnizLeftEquiv]
  rw [metricTraceFirstTwoField_product, metricTraceFirstTwoField_product]

open DifferentialGeometry.Integral.Connection in
/-- The KN `Ric⊗g` term with `Ric` replaced by its rough Laplacian `ΔRic = trace₁₂ ∇²Ric`. -/
private noncomputable def knRicLapT
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) e
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
      (metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t)
        (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (2 + 1) (S.family.connection t)
          (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.family.connection t) (S.ricci t)
            (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
              2 (S.family.connection t) (connSmoothSol (I := I) S t) (S.ricci t)))
          (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
            (2 + 1) (S.family.connection t) (connSmoothSol (I := I) S t) _)))
      (metricTensorField (I := I) (S.family.metric t)))

open DifferentialGeometry.Integral.Connection in
/-- The KN `(S·g)⊗g` term with `S` replaced by `ΔS = trace₁₂ ∇²S` (rank-0 leading factor). -/
private noncomputable def knScalLapT
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) e
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 0) (q := 2)
        (metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t)
          (totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 (S.family.connection t)
            (DifferentialGeometry.Integral.Connection.duSec (I := I)
              (S.scalar t) (scalarSmoothOfSol (I := I) S t))
            (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
              1 (S.family.connection t) (connSmoothSol (I := I) S t) _)))
        (metricTensorField (I := I) (S.family.metric t)))
      (metricTensorField (I := I) (S.family.metric t)))

/-- **The dim-3 Kulkarni–Nomizu field of the Laplacians** `KN(ΔRic, ΔS, g)`, mirroring
`knField` with `Ric ↦ ΔRic`, `S ↦ ΔS`. -/
private noncomputable def lapRm04Kn
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2) :=
  ((-1 : Real) • knRicLapT (I := I) S t knE1 + knRicLapT (I := I) S t knE2)
    + (knRicLapT (I := I) S t knE3 + (-1 : Real) • knRicLapT (I := I) S t knE4)
    + ((1 / 2 : Real) • knScalLapT (I := I) S t knE1
        + (-(1 / 2) : Real) • knScalLapT (I := I) S t knE2)

open DifferentialGeometry.Integral.Connection in
/-- Pointwise evaluation of the KN diffusion field in terms of the canonical
rough Ricci tensor and scalar Hessian trace. -/
private theorem lapRm04Kn_apply
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    lapRm04Kn (I := I) S t x v =
      -metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x) (vec2 (I := I) (v 0) (v 2)) *
          (S.base.metric t).inner x (v 1) (v 3) +
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x) (vec2 (I := I) (v 1) (v 2)) *
          (S.base.metric t).inner x (v 0) (v 3) +
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x) (vec2 (I := I) (v 0) (v 3)) *
          (S.base.metric t).inner x (v 1) (v 2) -
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x) (vec2 (I := I) (v 1) (v 3)) *
          (S.base.metric t).inner x (v 0) (v 2) +
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
            (scalarHessSec (I := I) S t x) Fin.elim0 / 2 *
          ((S.base.metric t).inner x (v 0) (v 2) *
              (S.base.metric t).inner x (v 1) (v 3) -
            (S.base.metric t).inner x (v 1) (v 2) *
              (S.base.metric t).inner x (v 0) (v 3)) := by
  classical
  have hadd (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 + 2)) :
      ((A + B) x) v = A x v + B x v := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
  have hsmul (c : Real)
      (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (2 + 2)) :
      ((c • A) x) v = c * A x v := by
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul]
  have hricT (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
      knRicLapT (I := I) S t e x v =
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
            (ricciNabla2WMP (I := I) S t x)
            ((fun i => v (e i)) ∘ Fin.castAdd 2) *
          (S.base.metric t).inner x
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 0)
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 1) := by
    unfold knRicLapT
    change (ContinuousMultilinearMap.domDomCongr e _) v = _
    rw [Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply,
      metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      metricTensorField_apply, SolutionOn.family_metric]
    rfl
  have hscalT (e : Fin (2 + 2) ≃ Fin (2 + 2)) :
      knScalLapT (I := I) S t e x v =
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
            (scalarHessSec (I := I) S t x) Fin.elim0 *
          (S.base.metric t).inner x
            (((fun i => v (e i)) ∘ Fin.castAdd 2) 0)
            (((fun i => v (e i)) ∘ Fin.castAdd 2) 1) *
          (S.base.metric t).inner x
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 0)
            (((fun i => v (e i)) ∘ Fin.natAdd 2) 1) := by
    let rawHess : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 (S.family.connection t)
        (duSec (I := I) (S.scalar t) (scalarSmoothOfSol (I := I) S t))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          1 (S.family.connection t) (connSmoothSol (I := I) S t) _)
    have hHess : rawHess = scalarHessSec (I := I) S t := by
      simp only [rawHess, scalarHessSec, hessianSec, SolutionOn.family_connection]
    unfold knScalLapT
    change (ContinuousMultilinearMap.domDomCongr e _) v = _
    rw [Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply]
    change (Bundle.continuousMultilinearMap.product_fun _ _) _ * _ = _
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hzero :
        (((fun i => v (e i)) ∘ Fin.castAdd 2) ∘ Fin.castAdd 2) =
          (Fin.elim0 : Fin 0 → TangentSpace I x) := Subsingleton.elim _ _
    rw [hzero]
    change ((metricTraceFirstTwoField (I := I) (M := M)
          (S.family.metric t) rawHess) x) Fin.elim0 *
        ((metricTensorField (I := I) (S.family.metric t)) x) _ *
        ((metricTensorField (I := I) (S.family.metric t)) x) _ = _
    rw [hHess, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      metricTensorField_apply, metricTensorField_apply, SolutionOn.family_metric]
    simp
  have hE1 : (fun i : Fin (2 + 2) => v (knE1 i)) =
      vec4 (I := I) (v 0) (v 2) (v 1) (v 3) := by
    funext i
    fin_cases i <;> simp [knE1, vec4, Equiv.swap_apply_def]
  have hE2 : (fun i : Fin (2 + 2) => v (knE2 i)) =
      vec4 (I := I) (v 1) (v 2) (v 0) (v 3) := by
    funext i
    fin_cases i <;> simp [knE2, vec4, Equiv.swap_apply_def]
  have hE3 : (fun i : Fin (2 + 2) => v (knE3 i)) =
      vec4 (I := I) (v 0) (v 3) (v 1) (v 2) := by
    funext i
    fin_cases i <;> simp [knE3, vec4, Equiv.swap_apply_def]
  have hE4 : (fun i : Fin (2 + 2) => v (knE4 i)) =
      vec4 (I := I) (v 1) (v 3) (v 0) (v 2) := by
    funext i
    fin_cases i <;> simp [knE4, vec4, Equiv.swap_apply_def]
  have hT1 : vec4 (I := I) (v 0) (v 2) (v 1) (v 3) ∘ Fin.castAdd 2 =
      vec2 (I := I) (v 0) (v 2) := by
    funext i
    fin_cases i <;> rfl
  have hT2 : vec4 (I := I) (v 1) (v 2) (v 0) (v 3) ∘ Fin.castAdd 2 =
      vec2 (I := I) (v 1) (v 2) := by
    funext i
    fin_cases i <;> rfl
  have hT3 : vec4 (I := I) (v 0) (v 3) (v 1) (v 2) ∘ Fin.castAdd 2 =
      vec2 (I := I) (v 0) (v 3) := by
    funext i
    fin_cases i <;> rfl
  have hT4 : vec4 (I := I) (v 1) (v 3) (v 0) (v 2) ∘ Fin.castAdd 2 =
      vec2 (I := I) (v 1) (v 3) := by
    funext i
    fin_cases i <;> rfl
  unfold lapRm04Kn
  repeat rw [hadd]
  repeat rw [hsmul]
  rw [hricT knE1, hricT knE2, hricT knE3, hricT knE4,
    hscalT knE1, hscalT knE2]
  rw [hE1, hE2, hE3, hE4]
  rw [hT1, hT2, hT3, hT4]
  simp [vec2, vec4]
  ring

set_option maxHeartbeats 1000000 in
open DifferentialGeometry.Integral.Connection in
/-- **B3c-2 ENDPOINT: the rough Laplacian of `Rm04` is the Kulkarni–Nomizu combination of
the Laplacians** (dim 3): `ΔRm04 = trace₁₂ ∇²Rm04 = KN(ΔRic, ΔS, g)`.  This is the diffusion
half of the Uhlenbeck base evolution `∂ₜRm04 = ΔRm04 − 2B# − drift`; the six explicit
level-2 witnesses of `rm04DerivsKn.nabla2A` each trace through `traceRicWit`/`traceScalWit`
into the corresponding `Δ`-of-leaf KN term. -/
theorem traceRm04Kn
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : forall x : M, Module.finrank Real (TangentSpace I x) = 3) :
    metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t)
        (rm04DerivsKn (I := I) S t hdim).nabla2A
      = lapRm04Kn (I := I) S t := by
  simp only [rm04DerivsKn]
  simp only [metricTraceFirstTwoField_add, metricTraceFirstTwoField_smul]
  rw [traceRicWit, traceRicWit, traceRicWit, traceRicWit, traceScalWit, traceScalWit]
  rfl

open DifferentialGeometry.Integral.Connection DifferentialGeometry.Dim3Reaction in
/-- The canonical rough Laplacian of `Rm04`, evaluated in an orthonormal
`Fin 3` basis, is the dimension-three KN combination of the canonical rough
Ricci tensor and scalar Laplacian. -/
theorem roughRm04_comp
    [IsManifold I 1 M] [IsManifold I 2 M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3,
      (S.base.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (I0 : Fin 4 → Fin 3) :
    tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin 3))
          (nablaKRm04Field (I := I) S t 2 x)) (fun i => basis i) I0 =
      -metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x)
          (vec2 (I := I) (basis (I0 0)) (basis (I0 2))) * kd (I0 1) (I0 3) +
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x)
          (vec2 (I := I) (basis (I0 1)) (basis (I0 2))) * kd (I0 0) (I0 3) +
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x)
          (vec2 (I := I) (basis (I0 0)) (basis (I0 3))) * kd (I0 1) (I0 2) -
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x)
          (vec2 (I := I) (basis (I0 1)) (basis (I0 3))) * kd (I0 0) (I0 2) +
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I)
            (flowG (I := I) S) t (S.scalar t) x / 2 *
          (kd (I0 0) (I0 2) * kd (I0 1) (I0 3) -
            kd (I0 1) (I0 2) * kd (I0 0) (I0 3)) := by
  classical
  let v : Fin 4 → TangentSpace I x := fun p => basis (I0 p)
  have hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin 3)) := by
    have hinv' := metricInverseInBasis_of_orthonormal
      (I := I) (S.base.metric t) basis horth
    simpa [identityInvMetric, diagonalInvMetric] using hinv'
  have htrace :
      tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin 3))
            (nablaKRm04Field (I := I) S t 2 x)) (fun i => basis i) I0 =
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (nablaKRm04Field (I := I) S t 2 x) v := by
    rw [tensor0SComponent_apply, metricTrace0S2TensorInBasis_apply]
    exact metricTrace0S2InBasis_eq_metricTrace (I := I) (S.base.metric t)
      basis (identityInvMetric (Idx := Fin 3)) hinv
      (nablaKRm04Field (I := I) S t 2 x) v
  have hfield :
      metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t 2) =
        lapRm04Kn (I := I) S t := by
    rw [← rm04Nab2Kn_eq (I := I) S t hdim]
    simpa [SolutionOn.family_metric] using traceRm04Kn (I := I) S t hdim
  have hpoint := congrArg (fun A => A x v) hfield
  simp only [metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply] at hpoint
  rw [htrace, hpoint, lapRm04Kn_apply (I := I) S t x v,
    scalarHessTrace_eq_lap (I := I) S t x]
  simp only [v, horth, kd]

end KnField

set_option maxHeartbeats 1000000 in
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Dim3Reaction in
/-- The level-zero Uhlenbeck/StarSum time input produced directly from a
dimension-three Ricci-flow solution. -/
theorem rm04Base_of_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D)
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3) :
    ∀ (y : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I y))
      (_horth : ∀ i j : Fin 3,
        (S.base.metric (t : Real)).inner y (basis i) (basis j) =
          if i = j then (1 : Real) else 0)
      (I0 : Fin 4 → Fin 3),
      HasDerivWithinAt
        (fun r : Real => S.base.rm04 r y (fun p => basis (I0 p)))
        (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
              (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : Real) 2 y))
            (fun i => basis i) I0 +
          (-2 * (Bt (fun i j => S.ricciAt (t : Real) y
                    (vec2 (I := I) (basis i) (basis j)))
                  (I0 0) (I0 1) (I0 2) (I0 3) -
                Bt (fun i j => S.ricciAt (t : Real) y
                    (vec2 (I := I) (basis i) (basis j)))
                  (I0 0) (I0 1) (I0 3) (I0 2) +
                Bt (fun i j => S.ricciAt (t : Real) y
                    (vec2 (I := I) (basis i) (basis j)))
                  (I0 0) (I0 2) (I0 1) (I0 3) -
                Bt (fun i j => S.ricciAt (t : Real) y
                    (vec2 (I := I) (basis i) (basis j)))
                  (I0 0) (I0 3) (I0 1) (I0 2)) -
            drift (fun i j => S.ricciAt (t : Real) y
                (vec2 (I := I) (basis i) (basis j)))
              (I0 0) (I0 1) (I0 2) (I0 3)))
        D.carrier (t : Real) := by
  classical
  intro y basis horth I0
  let R : Real → Fin 3 → Fin 3 → Real := fun r i j =>
    S.ricciAt r y (vec2 (I := I) (basis i) (basis j))
  let lap : Fin 3 → Fin 3 → Real := fun i j =>
    metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
      (ricciNabla2WMP (I := I) S (t : Real) y)
      (vec2 (I := I) (basis i) (basis j))
  let scalarLap : Real → M → Real := fun r z =>
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I)
      (flowG (I := I) S) r (S.scalar r) z
  let lapS : Real := scalarLap (t : Real) y
  have hRicDot : ∀ i j : Fin 3,
      HasDerivWithinAt (fun r : Real => R r i j)
        (lap i j - 2 * Cc (R (t : Real)) i j - 2 * Rsq (R (t : Real)) i j)
        D.carrier (t : Real) := by
    intro i j
    exact ricDot_of_solution (I := I) S hS t y (hdim y) basis horth R
      (fun _ _ _ => rfl) i j
  have hscalar : ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
      (ricciNorm (I := I) S) := by
    intro r z
    simpa [scalarLap, ricciNorm] using
      (scalarEvolOfSol (I := I) S hS (flowG (I := I) S)
        (by intro _; rfl) (by intro _; rfl) r z)
  have hScDot : HasDerivWithinAt (fun r : Real => S.scalar r y)
      (lapS + 2 * normSq (R (t : Real))) D.carrier (t : Real) := by
    simpa [lapS] using scalarDot_ortho (I := I) S scalarLap hscalar t y horth
      (R (t : Real)) (fun _ _ => rfl)
  have htr : S.scalar (t : Real) y = sc (R (t : Real)) := by
    rw [scalar_eq_trace_ortho (I := I) S (t : Real) y horth]
    simp [R, sc]
  have hbase := rm04BaseEvolution_at (I := I) S hS t y (hdim y)
    (fun i => basis i) horth R (fun _ _ _ => rfl) lap lapS hRicDot hScDot htr
    (I0 0) (I0 1) (I0 2) (I0 3)
  have hfun : ∀ r : Real,
      S.base.rm04 r y (fun p => basis (I0 p)) =
        S.base.rm04 r y
          (vec4 (I := I) (basis (I0 0)) (basis (I0 1))
            (basis (I0 2)) (basis (I0 3))) := by
    intro r
    congr 1
    funext p
    fin_cases p <;> rfl
  have hbase' := hbase.congr (fun r _ => hfun r) (hfun (t : Real))
  refine hbase'.congr_deriv ?_
  have hrough := roughRm04_comp (I := I) S (t : Real) hdim y basis horth I0
  dsimp only [lap, lapS, scalarLap, R]
  rw [hrough]
  ring

set_option maxHeartbeats 1000000 in
open DifferentialGeometry.Dim3Reaction in
/-- **Capstone: the tower's `hrm` input from the standing analytic layer (dim 3).**
Composes the whole banked per-point pipeline at a regular time `t` and the frame
centre `x₀`: a `g_t`-orthonormal basis (with a frame family matching it at `x₀` and a
`δ` inverse there), the standing Lichnerowicz input `hlich` (from the `h_ricci`
conditional layer via `ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm` +
`ricciSymFrame_can`), and the proven scalar evolution `hsc`, yield the time derivative
of `realizedRmBase` at the coordinate frame — exactly the `hrm` consumed by
`nablaKRm_timeDeriv_of_solution` — with the explicit corrected-sign value
`C⁴-transform of (KN(ΔRic, ΔS, δ) − 2·B# − drift)`. -/
theorem rm04HrmProducer
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (hdim : Module.finrank Real (TangentSpace I x₀) = 3)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x₀))
    (horthB : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric (t : Real)) x₀ basis)
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (hframe0 : forall i : Fin 3, frame i x₀ = basis i)
    (hginv : forall i j : Fin 3, gInv (t : Real) x₀ i j = (if i = j then (1 : Real) else 0))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hsec : forall v : Fin 4 -> TangentSpace I x₀, Rm04 (t : Real) x₀ v = S.base.rm04 (t : Real) x₀ v)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (hlich : RicciLichnerowiczEquationInFrame (D := D) (I := I) S Rm04 gInv frame roughLapRic)
    (scalarLap : Real -> M -> Real)
    (hsc : ScalarEvolutionEquationOn (D := D) S.scalar scalarLap (ricciNorm (I := I) S))
    (R : Real -> Fin 3 -> Fin 3 -> Real)
    (hRdef : forall (s : Real) (i j : Fin 3),
      R s i j = ricciCompInFrame (I := I) S frame s x₀ i j)
    (m : Fin 4 -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
      (∑ slots : Fin 4 -> Fin 3,
        (-(roughLapRic (t : Real) x₀ (slots 0) (slots 2)) * kd (slots 1) (slots 3)
            + roughLapRic (t : Real) x₀ (slots 1) (slots 2) * kd (slots 0) (slots 3)
            + roughLapRic (t : Real) x₀ (slots 0) (slots 3) * kd (slots 1) (slots 2)
            - roughLapRic (t : Real) x₀ (slots 1) (slots 3) * kd (slots 0) (slots 2)
            + scalarLap (t : Real) x₀ / 2 *
              (kd (slots 0) (slots 2) * kd (slots 1) (slots 3)
                - kd (slots 1) (slots 2) * kd (slots 0) (slots 3))
          - 2 * (Bt (R (t : Real)) (slots 0) (slots 1) (slots 2) (slots 3)
              - Bt (R (t : Real)) (slots 0) (slots 1) (slots 3) (slots 2)
              + Bt (R (t : Real)) (slots 0) (slots 2) (slots 1) (slots 3)
              - Bt (R (t : Real)) (slots 0) (slots 3) (slots 1) (slots 2))
          - drift (R (t : Real)) (slots 0) (slots 1) (slots 2) (slots 3)) *
          ∏ a : Fin 4, basis.coord (slots a)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ (m a) x₀))
      D.carrier (t : Real) := by
  classical
  have horthf : forall i j : Fin 3,
      (S.base.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀)
        = (if i = j then (1 : Real) else 0) := by
    intro i j
    rw [hframe0 i, hframe0 j]
    exact horthB i j
  have hsym : forall i j : Fin 3, R (t : Real) i j = R (t : Real) j i := by
    intro i j
    rw [hRdef, hRdef]
    exact ricciSym_can (I := I) S (t : Real) x₀ (frame i x₀) (frame j x₀)
  have hRdefB : forall i j : Fin 3,
      R (t : Real) i j = S.ricciAt (t : Real) x₀
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    rw [hRdef]
    unfold ricciCompInFrame
    rw [hframe0 i, hframe0 j]
  have htr : S.scalar (t : Real) x₀ = sc (R (t : Real)) := by
    rw [scalar_eq_trace_ortho (I := I) S (t : Real) x₀ horthB]
    unfold sc
    rw [hRdefB 0 0, hRdefB 1 1, hRdefB 2 2]
  have hkn : forall i k j l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x₀ i k j l
        = rm (R (t : Real)) i k j l :=
    rm04CompknOrtho (I := I) S Rm04 frame (t : Real) x₀ hdim hsec horthf (R (t : Real))
      (fun a b => by rw [hRdef]; rfl) htr
  have hRicDot := fun i j : Fin 3 =>
    ricDot_ortho (I := I) S Rm04 gInv frame roughLapRic hlich t x₀ hginv R hRdef hsym hkn i j
  have hScDot :=
    scalarDot_ortho (I := I) S scalarLap hsc t x₀ horthB (R (t : Real)) hRdefB
  have hD := fun a b c d : Fin 3 =>
    rm04BaseEvolution_at (I := I) S hS t x₀ hdim (fun i => basis i)
      (fun i j => horthB i j) R
      (fun s i j => by rw [hRdef]; unfold ricciCompInFrame; rw [hframe0 i, hframe0 j])
      (fun i j => roughLapRic (t : Real) x₀ i j) (scalarLap (t : Real) x₀)
      hRicDot hScDot htr a b c d
  exact rmBaseDeriv_basis (I := I) S x₀ t basis _ hD m

section Dim3Bridges

/-! ### Bridges from the bare `Fin 3` reaction algebra to the Uhlenbeck component API

At an orthonormal frame (`gInv = δ`) with the lowered Riemann components in the dim-3
Kulkarni–Nomizu form `rm R` (`R` = frame Ricci components), the Uhlenbeck `B`-tensor and
Ricci-drift component arrays are the corresponding `Dim3Reaction` algebra objects.  These
identify the reaction algebra (whose match `reaction_match` is proved in `UhlReaction3`)
inside the target predicate `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`. -/

open DifferentialGeometry.Dim3Reaction

variable {N : Type*}

/-- At an orthonormal inverse metric, `uhlenbeckBTensorInFrame` is the bare `Bt`. -/
theorem uhlBt_eq_bt
    (gInv : MatrixComp N (Fin 3)) (Rm04c : FourComp N (Fin 3))
    (R : Fin 3 -> Fin 3 -> Real) (t : Real) (x : N)
    (horth : forall i j, gInv t x i j = (if i = j then (1 : Real) else 0))
    (hcomp : forall a b c d, Rm04c t x a b c d = rm R a b c d)
    (a b c d : Fin 3) :
    uhlenbeckBTensorInFrame gInv Rm04c t x a b c d = Bt R a b c d := by
  unfold uhlenbeckBTensorInFrame Bt
  simp only [horth, hcomp, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, reduceIte,
    one_mul, zero_mul, mul_zero, mul_one, add_zero, zero_add]

/-- The Ricci-drift component array is the bare `drift`. -/
theorem uhlDrift_eq_drift
    (Rup : MatrixComp N (Fin 3)) (Rm04c : FourComp N (Fin 3))
    (R : Fin 3 -> Fin 3 -> Real) (t : Real) (x : N)
    (hup : forall i j, Rup t x i j = R i j)
    (hcomp : forall a b c d, Rm04c t x a b c d = rm R a b c d)
    (i j k l : Fin 3) :
    riemann04RicciDriftInFrame Rup Rm04c t x i j k l = drift R i j k l := by
  unfold riemann04RicciDriftInFrame drift
  simp only [hup, hcomp, Fin.sum_univ_three]
  ring

end Dim3Bridges

end DifferentialGeometry.PDE.RicciFlow
