import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Ricci-norm heat assembly

This module contains the scalar-evolution predicate, Ricci-norm heat component
assembly, and smooth-solution package built on the core Ricci-flow API.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- Scalar curvature evolution in Section 6.2:
`∂_t R = Δ R + 2 |Ric|²`. -/
def ScalarEvolutionEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap (t : Real) x + 2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-! ## Lemma 6.7: Ricci norm heat equation, component assembly -/

/-- Time derivative component identity for `|Ric|²`.

This is the point where differentiating inverse metrics and using Lemma 6.3 has
already cancelled the cubic `Ric_i^k Ric_kj` terms. -/
def RicciNormTimeDerivativeComponentsOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (ricciNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x)
      D.carrier
      (t : Real)

section RicciNormDerivative

variable {Idx : Type*} [Fintype Idx]

/-- The time-derivative identity for `|Ric|^2` once the component evolution
equations and the remaining finite-sum simplification are supplied. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      roughLapInner reaction := by
  intro t x
  have hnorm :=
    ricciNormSqInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x (by simp)
  simpa [h_simplify t x] using hnorm

/-- Canonical time-derivative identity for `|Ric|^2` from Lemma 6.3 and the
inverse-metric evolution equation. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) :=
  ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic
    (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    h_inv h_ricci
    (ricciNormDerivativeSimplifiesInFrame_canonical
      (I := I) S Rm04 gInv frame roughLapRic hInvSym hRicSym)

end RicciNormDerivative

/-- Laplacian component identity for `|Ric|²`:
`Δ |Ric|² = 2 <Δ Ric, Ric> + 2 |∇Ric|²`. -/
def RicciNormLaplacianComponentsOn
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Bridge from the realized Bochner coordinate predicate to the interval
Ricci-flow predicate. -/
theorem ricciNormLaplacianComponentsOn_of_bochner
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormLaplacianComponentsInFrame
      (M := M) (Time := Real) ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormLaplacianComponentsOn ricciNormLap roughLapInner nablaRicNormSq :=
  h_lap

/-- Canonical interval-level Ricci-norm Laplacian identity from the exact
coordinate Bochner expansion for `|Ric|^2`. -/
theorem ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv) := by
  have hrealized :=
    DifferentialGeometry.Integral.Connection.ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic h_lap
  intro t x
  simpa [roughLapRicciInnerInFrame, nablaRicciNormSqInFrame] using hrealized t x

/-- Canonical inverse-metric coefficients in the coordinate frame centered at
`x0`, for the metric at time `t`. -/
noncomputable def coordInv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :=
  fun t x i j =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.family.metric t) x0 i j (extChartAt I x0 x)

/-- The canonical coordinate inverse really is the inverse metric in the
centered coordinate basis at the center point. -/
theorem coordInvReal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) (t : Real) :
    Tensor0SBundle.MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x0
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x0)
      (fun i j => coordInv (I := I) S x0 t x0 i j) := by
  simpa [coordInv] using
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) (S.family.metric t) x0

/-- Canonical coordinate rough Laplacian components
`g^{ab} (nabla_a nabla_b Ric)_ij` in the coordinate frame centered at `x0`,
once the coordinate components of `nabla^2 Ric` have been produced. -/
noncomputable def coordRoughRic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (nabla2Ric : Real -> M ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) :
    Real -> M ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
  fun t x i j =>
    ∑ a : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ b : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x0 t x a b * nabla2Ric t x a b i j

/-- Canonical coordinate components of the second covariant derivative of the
Ricci tensor, in the coordinate frame centered at `x0`. -/
noncomputable def coordNab2Ric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    Real -> M ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
  fun t x d a i j =>
    extDerivFun (I := I)
        (fun y : M =>
          nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            t y a i j)
        x
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 d x) -
      (∑ p : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d a p *
          nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            t x p i j) -
      (∑ p : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d i p *
          nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            t x a p j) -
      (∑ p : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d j p *
          nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            t x a i p)

/-- Heat-equation form of Lemma 6.7:
`∂_t |Ric|² = Δ |Ric|² - 2 |∇Ric|² + 4 R_ikjl Ric^{ij} Ric^{kl}`. -/
def RicciNormHeatEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (ricciNormSq ricciNormLap nablaRicNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (ricciNormLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of Lemma 6.7 from the time-derivative and Laplacian
component identities. -/
theorem ricciNormHeatEquationOn_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (ricciNormSq ricciNormLap roughLapInner nablaRicNormSq reaction : Real -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsOn
      (D := D) ricciNormSq roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction := by
  intro t x
  have hvalue :
      ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

/-- Strong Ricci-flow solution predicate used by global Hamilton packages.

`IsSolutionOn` records the Ricci-flow equation and the interval-wise metric and
connection smoothness currently used by the local evolution files.  The
Hamilton/global layer also needs the canonical scalar and Ricci quantities
supplied by a smooth Ricci flow to be regular on spacetime and to satisfy the
coordinate-frame evolution and Bochner identities used by Section 6. -/
structure IsSmoothSolutionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  isSolution : IsSolutionOn (I := I) S
  scalarSTCont : ScalarSTContOn (I := I) (M := M) S
  scalarRegular : CanonicalScalarRegularOn (I := I) (M := M) S
  ricciRegular : CanonicalRicciRegularOn (I := I) (M := M) S
  scalarEvolution : ∀
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real),
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.metric (t : Real) = S.family.metric (t : Real)) ->
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.connection (t : Real) = S.family.connection (t : Real)) ->
      ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
        HasDerivWithinAt
          (fun s : Real => S.scalar s x)
          (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
              (S.scalar (t : Real)) x +
            2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
              (S.ricci (t : Real) x))
          D.carrier
          (t : Real)
  invEvol :
    ∀ x0 : M,
      InverseMetricEvolutionEquationInFrame
        (I := I) S (coordInv (I := I) S x0)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0)
  ricciEvol :
    ∀ x0 : M, ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E),
      HasDerivWithinAt
        (fun s : Real =>
          ricciCompInFrame (I := I) S
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) s x0 i j)
        (ricciEvolutionRHSInFrame
          (I := I) S S.base.rm04 (coordInv (I := I) S x0)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
          (coordRoughRic (I := I) S x0 (coordNab2Ric (I := I) S x0))
          (t : Real) x0 i j)
        D.carrier
        (t : Real)
  invSymm :
    ∀ x0 : M, ∀ t i j,
      coordInv (I := I) S x0 t x0 i j =
        coordInv (I := I) S x0 t x0 j i
  ricciSymm :
    ∀ x0 : M, ∀ t i j,
      ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 i j =
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 j i
  ricciLap :
    ∀ t x,
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
              (coordInv (I := I) S x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x +
          2 * ricciGradSq (I := I) S t x

namespace IsSmoothSolutionOn

/-- A smooth solution is in particular a Ricci-flow solution in the ordinary
folder-level sense. -/
theorem toIsSolutionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    IsSolutionOn (I := I) S :=
  hS.isSolution

/-- A smooth solution supplies the scalar spacetime-continuity package used by
scalar maximum-principle packages. -/
theorem scalarCont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    ScalarSTContOn (I := I) (M := M) S :=
  hS.scalarSTCont

/-- A smooth solution supplies the canonical scalar regularity package used by
scalar maximum-principle producers. -/
theorem scalarReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    CanonicalScalarRegularOn (I := I) (M := M) S :=
  hS.scalarRegular

end IsSmoothSolutionOn

section RicciNormAssembly

variable {Idx : Type*} [Fintype Idx]

/-- Section 6.2 Ricci-norm heat identity for a folder-level solution, reduced
to inverse-metric evolution, Ricci evolution, symmetry, and the Bochner
Laplacian component frontier. -/
theorem ricciNormHeatEquationOn_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap nablaRicNormSq : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
      (ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S Rm04 gInv frame roughLapRic
        h_inv h_ricci hInvSym hRicSym)
      h_lap

/-- Canonical Lemma 6.7 consumer using the exact Ricci-norm Bochner expansion
instead of an already-packaged Laplacian component identity. -/
theorem ricciNormHeatEquationOn_of_solution_canonical_laplacian
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_solution
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      h_inv h_ricci hInvSym hRicSym
      (ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S gInv frame roughLapRic ricciNormLap nablaRic h_lap)

/-- Canonical Lemma 6.7 consumer from the metric-compatible `(0,2)` tensor
Bochner producer, without asking callers for a prepackaged Laplacian
expansion predicate. -/
theorem ricci_heat_mc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (X : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Real -> (x : M) -> DifferentialGeometry.Integral.Connection.Tensor02At (I := I) x)
    (nablaA : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hframe : forall x i, basis x i = frame i x)
    (hinv : forall t x,
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x
        (basis x) (gInv t x))
    (hfields : forall x, DifferentialGeometry.Integral.Connection.SmoothBasisFieldsAt (I := I) (basis x) (X x))
    (hlapTrace : forall t x,
      ricciNormLap t x =
        DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hA : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (S.base.connection t) (A t) (nablaA t))
    (h2 : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (S.base.connection t) (nablaA t) (nabla2A t))
    (hdu : forall t,
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I)
        (fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (S.base.metric t) y (A t y))
        (du t))
    (hHess : forall t x,
      DifferentialGeometry.Integral.Connection.HessianRealizesNablaDuAt (I := I) (S.base.connection t) (du t)
        (normSecond t) x)
    (hrough : forall t x,
      DifferentialGeometry.Integral.Connection.RoughLap0SRealizesMetricTraceInBasis (I := I)
        (basis x) (gInv t x) (s := 2) (roughA t x) (nabla2A t x))
    (hAComp : forall t x i j,
      A t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        ricciTwoTensorField (I := I) S t x (frame i x) (frame j x))
    (hroughComp : forall t x i j,
      roughA t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : forall t x a i j,
      nablaA t x (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  let G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real :=
    { metric := S.base.metric
      connection := S.base.connection
      metricCompatible := by
        intro t
        simpa [SolutionFamily.connection] using
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) (S.base.metric t)) }
  exact
    ricciNormHeatEquationOn_of_solution_canonical_laplacian
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
      h_inv h_ricci hInvSym hRicSym
      (DifferentialGeometry.Integral.Connection.ricci_lap_mc (I := I) (Time := Real) G
        ricciNormLap roughLapRic (ricciTwoTensorField (I := I) S)
        gInv frame nablaRic basis X A roughA nablaA nabla2A du normSecond
        hframe hinv hfields hlapTrace hA h2 hdu hHess hrough
        hAComp hroughComp hnablaComp)

end RicciNormAssembly

end DifferentialGeometry.PDE.RicciFlow
