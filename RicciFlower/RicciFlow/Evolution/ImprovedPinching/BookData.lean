import RicciFlower.RicciFlow.Evolution.ImprovedPinching.TfHeatAssembly

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved pinching BookData

Split-out component of `RicciFlow.Evolution.ImprovedPinching`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Intrinsic `|∇ R|²` for the scalar curvature of a solution candidate. -/
def scalGradSq
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    (S.family.metric t).inner x
      (Realized.gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x)
      (Realized.gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x)

/-- Intrinsic Laplacian of `|Ric°|²` for a solution candidate. -/
def tfLapBook
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    Realized.laplacianAt (I := I) (flowG (I := I) S) t
      (fun y : M => tfRicNormSq S.scalar (ricciNorm (I := I) S) t y) x

/-- Canonical smooth section representing `∇ Ric` for a solution candidate at
a fixed time.  This is the bundled section form of the pointwise
`totalNabla0SFun` used in `ricciGradSq`. -/
noncomputable def ricciNablaSec
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  (CanonicalSpatialDerivs0S.of_smooth_connection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t)
    (by
      simpa [SolutionFamily.connection, metricCov] using
        metricCov_smooth (I := I) (M := M) (S.base.metric t))
    (S.ricci t)).nablaA

/-- Canonical smooth one-form section representing `d |Ric|²` for a solution
candidate at a fixed time. -/
noncomputable def ricciNormDuSec
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  Realized.duSec (I := I)
    (fun y : M =>
      Realized.normSq02 (I := I) (S.base.metric t) y (S.ricci t y))
    (by
      exact Realized.norm02_smooth (I := I) (M := M)
        (S.base.metric t) (S.ricci t))

/-- The canonical tensor-square term in Lemma 10.6 for a solution candidate. -/
def pinchCoupleSol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  ricciGradCoupleSq (I := I)
    (fun t : Real => S.family.metric t) S.scalar
    (fun t y => S.ricci t y)
    (fun t y => ricciNablaSec (I := I) S t y)

/-- Lemma 10.6 book-form evolution with the Ricci-section realization data
produced canonically from a solution candidate.

This removes the manual `RicSec`, `∇RicSec`, `du |Ric|²`, inverse-basis, and
norm-identification inputs from `pinchEvol_sec`.  It still deliberately
consumes the raw quotient setup and pointwise scalar regularity/positivity
inputs; producing those is the remaining solution-level wrapper frontier. -/
theorem pinchEvol_solSec
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon)
    (hscalar : forall (t : Realized.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x)
    (htfDiff : forall (t : Realized.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x)
    (hscalarDiff : forall (t : Realized.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
            (pinchCoupleSol (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let Idx := Coordinates.CoordinateIdx (𝕜 := Real) E
  let basis :
      forall (_t : Realized.RealTimeInterval.RegularTime D) (x : M),
        Module.Basis Idx Real (TangentSpace I x) :=
    fun _t x => Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      forall (_t : Realized.RealTimeInterval.RegularTime D) (_x : M),
        Idx -> Idx -> Real :=
    fun t x i j => coordInv (I := I) S x (t : Real) x i j
  refine pinchEvol_sec (I := I) (Idx := Idx) (G := flowG (I := I) S)
    S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
    (scalGradSq (I := I) S)
    (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
    (fun t => S.ricci t) (fun t => ricciNablaSec (I := I) S t)
    (fun t => ricciNormDuSec (I := I) S t)
    epsilon hsetup hscalar ?_ htfDiff hscalarDiff
    basis gInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simp [scalGradSq, flowG]
  · intro t x
    simpa [basis, gInv, flowG] using coordInvReal (I := I) S x (t : Real)
  · intro t x
    simp [ricciGradSq, ricciNablaSec, flowG,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  · intro t x
    simp [ricciNorm, flowG]
  · intro t
    exact (flowG (I := I) S).metricCompatible (t : Real)
  · intro t
    simpa [ricciNablaSec, flowG] using
      (CanonicalSpatialDerivs0S.of_smooth_connection
        (E := E) (H := H) (I := I) (M := M)
        (S.base.connection (t : Real))
        (by
          simpa [SolutionFamily.connection, metricCov] using
            metricCov_smooth (I := I) (M := M)
              (S.base.metric (t : Real)))
        (S.ricci (t : Real))).first
  · intro t
    simpa [ricciNormDuSec, flowG] using
      Realized.duSec_realizes (I := I)
        (fun y : M =>
          Realized.normSq02 (I := I)
            ((flowG (I := I) S).metric (t : Real)) y
            (S.ricci (t : Real) y))
        (by
          simpa [flowG] using
            Realized.norm02_smooth (I := I) (M := M)
              (S.base.metric (t : Real)) (S.ricci (t : Real)))
  · intro t y
    simp [ricciNorm, Realized.normSq02, Realized.inner02, flowG]
  · intro t x
    have hf :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            Realized.normSq02 (I := I)
              ((flowG (I := I) S).metric (t : Real)) y
              (S.ricci (t : Real) y)) := by
      simpa [flowG] using
        Realized.norm02_smooth (I := I) (M := M)
          (S.base.metric (t : Real)) (S.ricci (t : Real))
    exact hf.contMDiffAt.mdifferentiableAt (by simp)

/-- The metric-derived Ricci tensor is symmetric at each point. -/
theorem ricciSym_can
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DimensionThree.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
        Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  have hInvSym : ∀ i j, gInv i j = gInv j i :=
    invMetric_symm (I := I) (S.base.metric t) x basis gInv hinv
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      Realized.Rm13RealizesConnection (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 :
      Realized.Rm04RealizesConnection (I := I) (S.base.metric t)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 :
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hLowerAt :
      Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    Realized.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hTrace :
      Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (S.base.rm04 t x) gInv basis :=
    Realized.ricciFirstTraceAt_of_rm13 (I := I) (S.base.metric t)
      basis gInv hinv (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt hInvSym
  exact ricciSym_rm04 (I := I) basis gInv
    (S.ricciAt t x) (S.base.rm04 t x) hTrace
    (RicciFlower.LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t) (hcov := hcov)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (RicciFlower.LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t) (hcov := hcov)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (RicciFlower.LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    hInvSym

/-- Canonical signed three-dimensional trace data for the metric-derived
curvature tensor, in any orthonormal `Fin 3` basis. -/
theorem traceData_can
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    DimensionThree.RiemannFromRicci3DTraceDataAt
      (I := I) (S.base.metric t) (-(S.ricciAt t x))
      (-(S.scalar t x)) (S.base.rm04 t x) basis := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      Realized.Rm13RealizesConnection (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 :
      Realized.Rm04RealizesConnection (I := I) (S.base.metric t)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 :
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hLowerAt :
      Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    Realized.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hcurv :
      DimensionThree.AlgebraicCurvatureSymmetries3
        (DimensionThree.standardRmCompAt (I := I) basis (S.base.rm04 t x)) :=
    DimensionThree.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t) (hcov := hcov)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04) basis
  have hRicFirst :
      Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (S.base.rm04 t x) DimensionThree.delta3 basis :=
    firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt
  have hScalarTrace :
      Realized.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DimensionThree.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  exact DimensionThree.traceDataOfFirst (I := I) (M := M) horth
    hcurv hRicFirst hScalarTrace

/-- Intrinsic zero-order reaction relation for the canonical metric-derived
Ricci and Riemann tensors.  The proof uses a pointwise Ricci eigenbasis only;
no smooth eigenframe is selected. -/
theorem tfReactSmooth
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicReactRel
      S.scalar (ricciNorm (I := I) S)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      (ricciReact (I := I) S) := by
  classical
  intro t x hR
  rcases DimensionThree.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricciSym_can (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag0⟩
  have hScalarTrace :
      Realized.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DimensionThree.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar :
      S.scalar t x =
        DimensionThree.ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_diag (I := I) hScalarTrace hdiag0
  have hdiag :
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (S.scalar t x) l1 l2 l3 basis := by
    exact ⟨hscalar, hdiag0.2⟩
  have hcube :
      ricciCube (I := I) S t x =
        DimensionThree.ricciEigenTraceCube3 l1 l2 l3 :=
    ricciCubeInv_diag (I := I) (S.base.metric t) horth hdiag0
  have hrel := tfRel_trace (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := S.base.rm04 t x)
    (basis := basis) (traceData_can (I := I) S horth) hdiag hcube hR
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) (S.base.metric t) basis horth
  have hnorm :
      ricciNormAt (I := I) (S.base.ricciAt t x) basis =
        ricciNorm (I := I) S t x := by
    simpa [ricciNorm, SolutionOn.ricci, SolutionOn.ricciAt] using
      (ricciNorm_inner (I := I) (S.base.metric t)
        (S.base.ricciAt t x) basis hinv)
  have hreact :
      reactAt (I := I) (S.base.ricciAt t x) (S.base.rm04 t x) basis =
        ricciReact (I := I) S t x := by
    simpa [SolutionOn.ricciAt] using
      (reactAt_eq_react (I := I) S horth)
  simpa [tfRicNormSq, cubicQ, SolutionOn.scalar_eq_metricTrace,
    hnorm, hreact] using hrel

/-- Section 10 assembly producer for the book-facing trace-free heat equation.
The Ricci-norm heat equation is supplied by the lower `ricciHeatSmooth`, and
the trace-free Laplacian identity is supplied by `tfLapCore` at regular times. -/
theorem ricciDataSmooth
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) ∧
    (∀ (t : Realized.RealTimeInterval.RegularTime D) x,
      tfLapBook (I := I) S (t : Real) x =
        tfLap S.scalar
          (fun t x =>
            Realized.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
      (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) := by
  refine ⟨ricciHeatSmooth (I := I) S _hS, ?_⟩
  intro t x
  have h := tfLapCore (I := I) S _hS (t : Real) (D.regular_subset t.2) x
  simpa [tfLapBook, tfLap, scalarSqLap, scalGradSq, tfRicNormSq,
    tfRicNormSqAt, ricciNormLap, flowG] using h

/-- Trace-free Laplacian projection from the canonical lower analytic
producer. -/
theorem tfLapBook_eq
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∀ (t : Realized.RealTimeInterval.RegularTime D) x,
      tfLapBook (I := I) S (t : Real) x =
        tfLap S.scalar
          (fun t x =>
            Realized.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
          (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x :=
  (ricciDataSmooth (I := I) S hS hdim).2

/-- Smooth-solution producer frontier for the canonical non-scalar data in the
book-facing Lemma 10.4.

The Ricci-norm Laplacian is fixed to the intrinsic `ricciNormLap S`; the
remaining missing work is isolated in `ricciDataSmooth`, while the pointwise
three-dimensional cubic reaction relation is proved by `tfReactSmooth`. -/
theorem tfDataSmooth
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ reaction : Real -> M -> Real,
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : Realized.RealTimeInterval.RegularTime D) x,
        tfLapBook (I := I) S (t : Real) x =
          tfLap S.scalar
            (fun t x =>
              Realized.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) ∧
      tfRicReactRel
        S.scalar (ricciNorm (I := I) S)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases ricciDataSmooth (I := I) S _hS _hdim with ⟨hRic, hLap⟩
  exact ⟨ricciReact (I := I) S, hRic, hLap, tfReactSmooth (I := I) S _hdim⟩

/-- Producer frontier for the non-scalar part of the book-facing Lemma 10.4
statement.  The remaining mathematical frontier is now `tfDataSmooth`, where
the Ricci-norm Laplacian has already been fixed to the canonical intrinsic
operator `ricciNormLap S`. -/
theorem tfBookData
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ (ricciNormLap reaction : Real -> M -> Real),
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) ricciNormLap
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : Realized.RealTimeInterval.RegularTime D) x,
        tfLapBook (I := I) S (t : Real) x =
          tfLap S.scalar
            (fun t x =>
              Realized.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalGradSq (I := I) S) ricciNormLap (t : Real) x) ∧
      tfRicReactRel
        S.scalar (ricciNorm (I := I) S)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases tfDataSmooth (I := I) S _hS _hdim with ⟨reaction, hRic, hLap, hRel⟩
  exact ⟨ricciNormLap (I := I) S, reaction, hRic, hLap, hRel⟩

/-- Lemma 10.4 in its book-facing form.

This is intentionally stated outside the component-frame/eigenbasis route:
the conclusion is the heat equation for `|Ric°|²` along a smooth
three-dimensional Ricci flow, wherever scalar curvature is nonzero.  The proof
frontier is now the producer chain from the canonical intrinsic quantities to
the checked frame-level Section 6 and 3D reaction identities above. -/
theorem tfHeat_book
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  let G : Realized.RealizedMetricFamily (I := I) (M := M) Real := flowG (I := I) S
  let scalarLap : Real -> M -> Real :=
    fun t x => Realized.laplacianAt (I := I) G t (S.scalar t) x
  have hmetric : ∀ t : Realized.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real) := by
    intro t
    rfl
  have hconnection : ∀ t : Realized.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real) := by
    intro t
    rfl
  have hscalar :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    simpa [scalarLap, ricciNorm] using
      (scalarEvolOfSmooth (I := I) (M := M) S hS G hmetric hconnection)
  have hbridge :
      ∃ (ricciNormLap reaction : Real -> M -> Real),
        RicciNormHeatEquationOn
          (D := D) (ricciNorm (I := I) S) ricciNormLap
          (ricciGradSq (I := I) S) reaction ∧
        (∀ (t : Realized.RealTimeInterval.RegularTime D) x,
          tfLapBook (I := I) S (t : Real) x =
            tfLap S.scalar scalarLap (scalGradSq (I := I) S) ricciNormLap
              (t : Real) x) ∧
        tfRicReactRel
          S.scalar (ricciNorm (I := I) S)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
          reaction := by
    simpa [scalarLap, G] using tfBookData (I := I) S hS hdim
  rcases hbridge with ⟨ricciNormLap, reaction, hRic, hLap, hRel⟩
  have hcore :
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (tfLap S.scalar scalarLap (scalGradSq (I := I) S) ricciNormLap)
        (ricciGradSq (I := I) S)
        (scalGradSq (I := I) S)
        S.scalar
        (ricciNorm (I := I) S)
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) :=
    tfHeat_base
      (D := D)
      S.scalar scalarLap
      (ricciNorm (I := I) S)
      ricciNormLap
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      reaction
      hscalar hRic hRel
  intro t x hR
  have hcore' := hcore t x hR
  simpa [hLap t x] using hcore'

/-- Lemma 10.4 from the base Ricci-flow solution predicate.

This is the final consumer-facing form: the strengthened smooth-solution
package is produced by `smoothOfSol`, not passed as an endpoint hypothesis. -/
theorem tfHeat_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  exact tfHeat_book (I := I) S (smoothOfSol (I := I) S hS) hdim

/-- The trace-free Ricci norm square is nonnegative for the canonical
three-dimensional Ricci tensor. -/
theorem tfNonneg_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    forall t x,
      0 <= tfRicNormSq S.scalar (ricciNorm (I := I) S) t x := by
  classical
  intro t x
  rcases DimensionThree.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricciSym_can (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    scalarTrace_delta (I := I) (S.base.metric t) (S.ricciAt t x) horth
  have hscalar :
      S.scalar t x = DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
    calc
      S.scalar t x =
          Realized.metricTracePair0SAt (I := I) (S.family.metric t)
            (S.ricciAt t x) := SolutionOn.scalar_eq_metricTrace (I := I) S t x
      _ = Realized.metricTracePair0SAt (I := I) (S.base.metric t)
            (S.ricciAt t x) := by rfl
      _ = DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
            exact scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) (S.base.metric t)
      basis horth
  have hnorm :
      ricciNorm (I := I) S t x =
        ricciNormAt (I := I) (S.ricciAt t x) basis := by
    calc
      ricciNorm (I := I) S t x =
          normSq0S (I := I) (S.base.metric t) x 2 (S.ricciAt t x) := by
            simp [ricciNorm, SolutionOn.family, SolutionOn.ricci,
              SolutionOn.ricciAt]
      _ = ricciNormAt (I := I) (S.ricciAt t x) basis := by
            exact (ricciNorm_inner (I := I) (S.base.metric t)
              (S.ricciAt t x) basis hinv).symm
  have htf :
      tfRicNormSq S.scalar (ricciNorm (I := I) S) t x =
        DimensionThree.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
    rw [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf,
      hscalar, hnorm, ricciNormAt_diag (I := I) hdiag]
    unfold DimensionThree.tracefreeRicciEigenNormSq3
      DimensionThree.ricciEigenPairwiseGapSq3
      DimensionThree.ricciEigenNormSq3 DimensionThree.ricciEigenScalar3
    ring
  rw [htf]
  exact DimensionThree.tracefreeRicciEigenNormSq3_nonneg l1 l2 l3

/-- Spatial differentiability of the canonical trace-free Ricci norm square. -/
theorem tfDiff_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : Realized.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  simpa [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf] using
    (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht x).sub
      (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht x)

/-- Gradient-field differentiability of the canonical trace-free Ricci norm
square. -/
theorem tfGrad_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : Realized.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  let f : M -> Real := ricciNorm (I := I) S (t : Real)
  let h : M -> Real := fun y : M => S.scalar (t : Real) y ^ 2 / 3
  have hgrad_eq :
      (fun y : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        fun y : M =>
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y := by
    funext y
    simpa [f, h, flowG, tfRicNormSq, tracefreeRicciNormSqOf,
      tracefreeRicciNormSqAtOf] using
      Realized.gradientFun_sub (I := I) ((flowG (I := I) S).metric (t : Real))
        (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht y)
        (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht y)
  have hnormGrad : MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y) x := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.ricciRegular.ricci_norm_grad (t : Real) ht x
  have hthirdGrad : MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    simpa [h, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_sq_div_grad (t : Real) ht x
  have hcombined : MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y -
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    exact mdifferentiableAt_sub_section hnormGrad hthirdGrad
  have hsection_eq :
      (T% fun y : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        (T% fun y : M =>
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y) := by
    funext y
    simpa using congrFun hgrad_eq y
  rw [hsection_eq]
  exact hcombined

/-- Gradient-field differentiability for the negative scalar power appearing
in Hamilton's quotient. -/
theorem scalarPowGrad_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (epsilon : Real)
    (hscalar : forall (t : Realized.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    forall (t : Realized.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) y := by
  intro t y
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  let p : Real := -(2 - epsilon)
  let f : M -> Real := S.scalar (t : Real)
  let coeff : M -> Real := fun z : M => p * f z ^ (p - 1)
  have hcoeff : MDifferentiableAt I 𝓘(Real, Real) coeff y := by
    have hp :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M => f z ^ (p - 1)) y :=
      Realized.mdifferentiableAt_rpow (I := I) (p - 1)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht y)
        (hscalar t y)
    simpa [coeff] using mdifferentiableAt_const.mul hp
  have hgrad_eq :
      (fun z : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        coeff • fun z : M =>
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z := by
    funext z
    simpa [p, f, coeff] using
      Realized.gradientFun_rpow (I := I) ((flowG (I := I) S).metric (t : Real))
        (p := p)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht z)
        (hscalar t z)
  have hscalarGrad : MDiffAt (T% fun z : M =>
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z) y := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_grad (t : Real) ht y
  have hsmul : MDiffAt (T% (coeff • fun z : M =>
      Realized.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z)) y := by
    exact hcoeff.smul_section hscalarGrad
  have hsection_eq :
      (T% fun z : M =>
        Realized.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        (T% (coeff • fun z : M =>
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z)) := by
    funext z
    simpa using congrFun hgrad_eq z
  rw [hsection_eq]
  exact hsmul

/-- Lemma 10.6 book-form evolution from a base Ricci-flow solution, after
assembling the raw quotient setup from Lemma 10.4 and scalar evolution.

The remaining explicit geometric region hypothesis is positivity of scalar
curvature, `R > 0`; quotient regularity and `|Ric^o|^2 >= 0` are produced from
the solution package. -/
theorem pinchEvol_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (epsilon : Real)
    (hscalar : forall (t : Realized.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
            (pinchCoupleSol (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let scalarLap : Real -> M -> Real :=
    fun t x =>
      Realized.laplacianAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x
  have hscalarHeat :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    intro t x
    have h := scalarEvolOfSol (I := I) S hS (flowG (I := I) S)
      (by intro t; rfl) (by intro t; rfl) t x
    simpa [scalarLap, ricciNorm, flowG] using h
  have hSmooth := smoothOfSol (I := I) S hS
  have htfDiff := tfDiff_sol (I := I) S hS
  have hscalarDiff :
      forall (t : Realized.RealTimeInterval.RegularTime D) x,
        MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_space (t : Real)
      (D.regular_subset t.2) x
  have htfNonneg :
      forall (t : Realized.RealTimeInterval.RegularTime D) y,
        0 <= tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real) y := by
    intro t y
    exact tfNonneg_sol (I := I) S hdim (t : Real) y
  have hgradTf := tfGrad_sol (I := I) S hS
  have hgradScalar :
      forall (t : Realized.RealTimeInterval.RegularTime D) x,
        MDiffAt (T% fun y : M =>
          Realized.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real))
            (S.scalar (t : Real)) y) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_grad (t : Real)
      (D.regular_subset t.2) x
  have hgradScalarPow := scalarPowGrad_sol (I := I) S hS epsilon hscalar
  have hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon := by
    refine pinchEvol_setup (I := I) (G := flowG (I := I) S)
      S.scalar scalarLap (ricciNorm (I := I) S) (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S) (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon (tfHeat_sol (I := I) S hS hdim) hscalarHeat ?_ ?_
      htfDiff hscalarDiff htfNonneg hscalar hgradTf hgradScalar
      hgradScalarPow
    · intro t x
      rfl
    · intro t x
      rfl
  exact pinchEvol_solSec (I := I) S epsilon hsetup hscalar htfDiff
    hscalarDiff

end RicciFlow
end RicciFlower
