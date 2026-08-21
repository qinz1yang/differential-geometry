import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicciEvolution
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]

def scalarGradientNormSq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    (S.family.metric t).inner x
      (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x)
      (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x)

def traceFreeRicciNormLaplacian
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
      (fun y : M => traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) t y) x

noncomputable def ricciCovariantDerivativeSection
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
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

noncomputable def ricciNormDifferentialSection
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  DifferentialGeometry.Geometry.Operator.duSec (I := I)
    (fun y : M =>
      DifferentialGeometry.Geometry.Curvature.normSq02 (I := I) (S.base.metric t) y (S.ricci t y))
    (by
      exact DifferentialGeometry.Geometry.Curvature.norm02_smooth (I := I) (M := M)
        (S.base.metric t) (S.ricci t))

def ricciGradientCouplingNormSq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  ricciGradCoupleSq (I := I)
    (fun t : Real => S.family.metric t) S.scalar
    (fun t y => S.ricci t y)
    (fun t y => ricciCovariantDerivativeSection (I := I) S t y)

omit [Module.Finite ℝ E] in
theorem pinch_quotient_evolution_of_solution_sections
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalarGradientNormSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon)
    (hscalar : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      0 < S.scalar (t : Real) x)
    (htfDiff : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      MDifferentiableAt I 𝓘(Real, Real)
        (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x)
    (hscalarDiff : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime
      D) x,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchEvolutionRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalarGradientNormSq (I := I) S)
            (ricciGradientCouplingNormSq (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let basis :
      forall (_t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
        Module.Basis Idx Real (TangentSpace I x) :=
    fun _t x => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      forall (_t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
        (_x : M),
        Idx -> Idx -> Real :=
    fun t x i j => coordInv (I := I) S x (t : Real) x i j
  refine pinch_quotient_evolution_of_tensor_sections (I := I) (Idx := Idx) (G := flowG (I := I) S)
    S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
    (scalarGradientNormSq (I := I) S)
    (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
    (fun t => S.ricci t) (fun t => ricciCovariantDerivativeSection (I := I) S t)
    (fun t => ricciNormDifferentialSection (I := I) S t)
    epsilon hsetup hscalar ?_ htfDiff hscalarDiff
    basis gInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simp [scalarGradientNormSq, flowG]
  · intro t x
    simpa [basis, gInv, flowG] using coordInvReal (I := I) S x (t : Real)
  · intro t x
    simp [ricciGradSq, ricciCovariantDerivativeSection, flowG,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  · intro t x
    simp [ricciNorm, flowG]
  · intro t
    exact (flowG (I := I) S).metricCompatible (t : Real)
  · intro t
    simpa [ricciCovariantDerivativeSection, flowG] using
      (CanonicalSpatialDerivs0S.of_smooth_connection
        (E := E) (H := H) (I := I) (M := M)
        (S.base.connection (t : Real))
        (by
          simpa [SolutionFamily.connection, metricCov] using
            metricCov_smooth (I := I) (M := M)
              (S.base.metric (t : Real)))
        (S.ricci (t : Real))).first
  · intro t
    simpa [ricciNormDifferentialSection, flowG] using
      DifferentialGeometry.Geometry.Operator.duSec_realizes (I := I)
        (fun y : M =>
          DifferentialGeometry.Geometry.Curvature.normSq02 (I := I)
            ((flowG (I := I) S).metric (t : Real)) y
            (S.ricci (t : Real) y))
        (by
          simpa [flowG] using
            DifferentialGeometry.Geometry.Curvature.norm02_smooth (I := I) (M := M)
              (S.base.metric (t : Real)) (S.ricci (t : Real)))
  · intro t y
    simp [ricciNorm, DifferentialGeometry.Geometry.Curvature.normSq02,
      DifferentialGeometry.Geometry.Curvature.inner02, flowG]
  · intro t x
    have hf :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            DifferentialGeometry.Geometry.Curvature.normSq02 (I := I)
              ((flowG (I := I) S).metric (t : Real)) y
              (S.ricci (t : Real) y)) := by
      simpa [flowG] using
        DifferentialGeometry.Geometry.Curvature.norm02_smooth (I := I) (M := M)
          (S.base.metric (t : Real)) (S.ricci (t : Real))
    exact hf.contMDiffAt.mdifferentiableAt (by simp)

omit [Module.Finite ℝ E] in
theorem ricci_is_symmetric
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  have hInvSym : ∀ i j, gInv i j = gInv j i :=
    invMetric_symm (I := I) (S.base.metric t) x basis gInv hinv
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).rm13Realizes
  have hRm04 :
      DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).rm04Realizes
  have hRic13 :
      S.ricciAt t x =
        DifferentialGeometry.Geometry.Curvature.ricciFromRm13At (I := I) (M := M)
          (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).ricciRealizes x
  have hLowerAt :
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hTrace :
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricciAt t x)
        (S.base.rm04 t x) gInv basis :=
    DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_rm13 (I := I) (S.base.metric t)
      basis gInv hinv (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt
  exact ricciSym_rm04 (I := I) basis gInv
    (S.ricciAt t x) (S.base.rm04 t x) hTrace
    (DifferentialGeometry.Geometry.Connection.rm04PairSymmAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (DifferentialGeometry.Geometry.Connection.rm04OutputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (DifferentialGeometry.Geometry.Connection.rm04InputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    hInvSym

omit [Module.Finite ℝ E] in
theorem riemann_from_ricci_trace_data
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
      (I := I) (S.base.metric t) (-(S.ricciAt t x))
      (-(S.scalar t x)) (S.base.rm04 t x) basis := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).rm13Realizes
  have hRm04 :
      DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).rm04Realizes
  have hRic13 :
      S.ricciAt t x =
        DifferentialGeometry.Geometry.Curvature.ricciFromRm13At (I := I) (M := M)
          (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).ricciRealizes x
  have hLowerAt :
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hcurv :
      DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Geometry.Curvature.standardRmCompAt (I := I) basis
          (S.base.rm04 t x)) :=
    DifferentialGeometry.Geometry.Curvature.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04) basis
  have hRicFirst :
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricciAt t x)
        (S.base.rm04 t x) DifferentialGeometry.Geometry.Curvature.delta3 basis :=
    firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt
  have hScalarTrace :
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  exact DifferentialGeometry.Geometry.Curvature.traceDataOfFirst (I := I) (M := M) horth
    hcurv hRicFirst hScalarTrace

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_reaction_relation_of_smooth_solution
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    TraceFreeRicciReactionRelation
      S.scalar (ricciNorm (I := I) S)
      (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      (ricciReact (I := I) S) := by
  classical
  intro t x hR
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricci_is_symmetric (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag0⟩
  have hScalarTrace :
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar :
      S.scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_diag (I := I) hScalarTrace hdiag0
  have hdiag :
      DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) (S.ricciAt t x)
        (S.scalar t x) l1 l2 l3 basis := by
    exact ⟨hscalar, hdiag0.2⟩
  have hcube :
      ricciCube (I := I) S t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3 :=
    ricciCubeInv_diag (I := I) (S.base.metric t) horth hdiag0
  have hrel := trace_free_ricci_reaction_relation_of_trace_data (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := S.base.rm04 t x)
    (basis := basis) (riemann_from_ricci_trace_data (I := I) S horth) hdiag hcube hR
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (S.base.metric t) basis
      horth
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
  simpa [traceFreeRicciNormSq, cubicQ, SolutionOn.scalar_eq_metricTrace,
    hnorm, hreact] using hrel

omit [Module.Finite ℝ E] in
theorem ricci_norm_heat_equation_data_of_smooth_solution
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) ∧
    (∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
      traceFreeRicciNormLaplacian (I := I) S (t : Real) x =
        traceFreeRicciNormSqLaplacian S.scalar
          (fun t x =>
            DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
      (scalarGradientNormSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) := by
  refine ⟨ricciHeatSmooth (I := I) S _hS, ?_⟩
  intro t x
  have h := trace_free_ricci_norm_sq_laplacian_identity (I := I) S _hS (t : Real) (D.regular_subset t.2) x
  simpa [traceFreeRicciNormLaplacian, traceFreeRicciNormSqLaplacian, scalarCurvatureSqLaplacian, scalarGradientNormSq, traceFreeRicciNormSq,
    traceFreeRicciNormSqAt, ricciNormLap, flowG] using h

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_norm_laplacian_eq
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
      traceFreeRicciNormLaplacian (I := I) S (t : Real) x =
        traceFreeRicciNormSqLaplacian S.scalar
          (fun t x =>
            DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
          (scalarGradientNormSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x :=
  (ricci_norm_heat_equation_data_of_smooth_solution (I := I) S hS).2

omit [Module.Finite ℝ E] in
theorem exists_trace_free_ricci_reaction_data_of_smooth_solution
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ reaction : Real -> M -> Real,
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
        traceFreeRicciNormLaplacian (I := I) S (t : Real) x =
          traceFreeRicciNormSqLaplacian S.scalar
            (fun t x =>
              DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalarGradientNormSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) ∧
      TraceFreeRicciReactionRelation
        S.scalar (ricciNorm (I := I) S)
        (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases ricci_norm_heat_equation_data_of_smooth_solution (I := I) S _hS with ⟨hRic, hLap⟩
  exact ⟨ricciReact (I := I) S, hRic, hLap, trace_free_ricci_reaction_relation_of_smooth_solution (I := I) S _hdim⟩

omit [Module.Finite ℝ E] in
theorem exists_trace_free_ricci_norm_sq_heat_equation_data
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ (ricciNormLap reaction : Real -> M -> Real),
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) ricciNormLap
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
        traceFreeRicciNormLaplacian (I := I) S (t : Real) x =
          traceFreeRicciNormSqLaplacian S.scalar
            (fun t x =>
              DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalarGradientNormSq (I := I) S) ricciNormLap (t : Real) x) ∧
      TraceFreeRicciReactionRelation
        S.scalar (ricciNorm (I := I) S)
        (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases exists_trace_free_ricci_reaction_data_of_smooth_solution (I := I) S _hS _hdim with ⟨reaction, hRic, hLap, hRel⟩
  exact ⟨ricciNormLap (I := I) S, reaction, hRic, hLap, hRel⟩

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_norm_sq_heat_equation_of_smooth_solution
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    TraceFreeRicciNormSqHeatEquationOn
      (D := D)
      (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
      (traceFreeRicciNormLaplacian (I := I) S)
      (ricciGradSq (I := I) S)
      (scalarGradientNormSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  let G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real :=
    flowG (I := I) S
  let scalarLap : Real -> M -> Real :=
    fun t x => DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (S.scalar t) x
  have hmetric : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real) := by
    intro t
    rfl
  have hconnection : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real) := by
    intro t
    rfl
  have hscalar :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    simpa [scalarLap, ricciNorm] using
      (scalar_evolution_of_smooth_solution
        (I := I) (M := M) S hS G hmetric hconnection)
  have hbridge :
      ∃ (ricciNormLap reaction : Real -> M -> Real),
        RicciNormHeatEquationOn
          (D := D) (ricciNorm (I := I) S) ricciNormLap
          (ricciGradSq (I := I) S) reaction ∧
        (∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
          traceFreeRicciNormLaplacian (I := I) S (t : Real) x =
            traceFreeRicciNormSqLaplacian S.scalar scalarLap (scalarGradientNormSq (I := I) S) ricciNormLap
              (t : Real) x) ∧
        TraceFreeRicciReactionRelation
          S.scalar (ricciNorm (I := I) S)
          (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
          (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
          reaction := by
    simpa [scalarLap, G] using exists_trace_free_ricci_norm_sq_heat_equation_data (I := I) S hS hdim
  rcases hbridge with ⟨ricciNormLap, reaction, hRic, hLap, hRel⟩
  have hcore :
      TraceFreeRicciNormSqHeatEquationOn
        (D := D)
        (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
        (traceFreeRicciNormSqLaplacian S.scalar scalarLap (scalarGradientNormSq (I := I) S) ricciNormLap)
        (ricciGradSq (I := I) S)
        (scalarGradientNormSq (I := I) S)
        S.scalar
        (ricciNorm (I := I) S)
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) :=
    trace_free_ricci_norm_sq_heat_equation
      (D := D)
      S.scalar scalarLap
      (ricciNorm (I := I) S)
      ricciNormLap
      (ricciGradSq (I := I) S)
      (scalarGradientNormSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      reaction
      hscalar hRic hRel
  intro t x hR
  have hcore' := hcore t x hR
  simpa [hLap t x] using hcore'

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_norm_sq_heat_equation_of_solution
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    TraceFreeRicciNormSqHeatEquationOn
      (D := D)
      (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
      (traceFreeRicciNormLaplacian (I := I) S)
      (ricciGradSq (I := I) S)
      (scalarGradientNormSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  exact trace_free_ricci_norm_sq_heat_equation_of_smooth_solution (I := I) S (smoothOfSol (I := I) S hS) hdim

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_norm_sq_nonneg
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    forall t x,
      0 <= traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) t x := by
  classical
  intro t x
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricci_is_symmetric (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    scalarTrace_delta (I := I) (S.base.metric t) (S.ricciAt t x) horth
  have hscalar :
      S.scalar t x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
    calc
      S.scalar t x =
          DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (S.family.metric t)
            (S.ricciAt t x) := SolutionOn.scalar_eq_metricTrace (I := I) S t x
      _ = DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (S.base.metric t)
            (S.ricciAt t x) := by rfl
      _ = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
            exact scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (S.base.metric t)
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
      traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) t x =
        DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
    rw [traceFreeRicciNormSq, traceFreeRicciNormSqOf, traceFreeRicciNormSqAtOf,
      hscalar, hnorm, ricciNormAt_diag (I := I) hdiag]
    unfold DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3
      DifferentialGeometry.Geometry.Curvature.ricciEigenPairwiseGapSq3
      DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    ring
  rw [htf]
  exact DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3_nonneg l1 l2 l3

omit [Module.Finite ℝ E] in
theorem trace_free_ricci_norm_sq_mdifferentiable
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  simpa [traceFreeRicciNormSq, traceFreeRicciNormSqOf, traceFreeRicciNormSqAtOf] using
    (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht x).sub
      (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht x)

omit [Module.Finite ℝ E] in
theorem gradient_trace_free_ricci_norm_sq
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  let f : M -> Real := ricciNorm (I := I) S (t : Real)
  let h : M -> Real := fun y : M => S.scalar (t : Real) y ^ 2 / 3
  have hgrad_eq :
      (fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y := by
    funext y
    simpa [f, h, flowG, traceFreeRicciNormSq, traceFreeRicciNormSqOf,
      traceFreeRicciNormSqAtOf] using
      DifferentialGeometry.Geometry.Operator.gradientFun_sub (I := I)
        ((flowG (I := I) S).metric (t : Real))
        (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht y)
        (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht y)
  have hnormGrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y) x := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.ricciRegular.ricci_norm_grad (t : Real) ht x
  have hthirdGrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    simpa [h, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_sq_div_grad (t : Real) ht x
  have hcombined : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y -
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    exact mdifferentiableAt_sub_section hnormGrad hthirdGrad
  have hsection_eq :
      (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        (T% fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y) := by
    funext y
    simpa using congrFun hgrad_eq y
  rw [hsection_eq]
  exact hcombined

omit [Module.Finite ℝ E] in
theorem gradient_scalar_rpow
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (epsilon : Real)
    (hscalar : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      0 < S.scalar (t : Real) x) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
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
      DifferentialGeometry.Geometry.Operator.mdifferentiableAt_rpow (I := I) (p - 1)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht y)
        (hscalar t y)
    simpa [coeff] using mdifferentiableAt_const.mul hp
  have hgrad_eq :
      (fun z : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        coeff • fun z : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z := by
    funext z
    simpa [p, f, coeff] using
      DifferentialGeometry.Geometry.Operator.gradientFun_rpow (I := I)
        ((flowG (I := I) S).metric (t : Real))
        (p := p)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht z)
        (hscalar t z)
  have hscalarGrad : MDiffAt (T% fun z : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z) y := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_grad (t : Real) ht y
  have hsmul : MDiffAt (T% (coeff • fun z : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z)) y := by
    exact hcoeff.smul_section hscalarGrad
  have hsection_eq :
      (T% fun z : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        (T% (coeff • fun z : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z)) := by
    funext z
    simpa using congrFun hgrad_eq z
  rw [hsection_eq]
  exact hsmul

omit [Module.Finite ℝ E] in
theorem pinch_quotient_evolution_of_solution_data
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (epsilon : Real)
    (hscalar : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      0 < S.scalar (t : Real) x) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (traceFreeRicciNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchEvolutionRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalarGradientNormSq (I := I) S)
            (ricciGradientCouplingNormSq (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let scalarLap : Real -> M -> Real :=
    fun t x =>
      DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x
  have hscalarHeat :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    intro t x
    have h := scalarEvolution_of_isSolution (I := I) S hS (flowG (I := I) S)
      (by intro t; rfl) (by intro t; rfl) t x
    simpa [scalarLap, ricciNorm, flowG] using h
  have hSmooth := smoothOfSol (I := I) S hS
  have htfDiff := trace_free_ricci_norm_sq_mdifferentiable (I := I) S hS
  have hscalarDiff :
      forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
        MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_space (t : Real)
      (D.regular_subset t.2) x
  have hgradTf := gradient_trace_free_ricci_norm_sq (I := I) S hS
  have hgradScalar :
      forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x,
        MDiffAt (T% fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real))
            (S.scalar (t : Real)) y) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_grad (t : Real)
      (D.regular_subset t.2) x
  have hgradScalarPow := gradient_scalar_rpow (I := I) S hS epsilon hscalar
  have hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalarGradientNormSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon := by
    refine pinch_quotient_evolution_of_heat_equations (I := I) (G := flowG (I := I) S)
      S.scalar scalarLap (ricciNorm (I := I) S) (traceFreeRicciNormLaplacian (I := I) S)
      (ricciGradSq (I := I) S) (scalarGradientNormSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon (trace_free_ricci_norm_sq_heat_equation_of_solution (I := I) S hS hdim) hscalarHeat ?_ ?_
      htfDiff hscalarDiff hscalar hgradTf hgradScalar
      hgradScalarPow
    · intro t x
      rfl
    · intro t x
      rfl
  exact pinch_quotient_evolution_of_solution_sections (I := I) S epsilon hsetup hscalar htfDiff
    hscalarDiff

end DifferentialGeometry.PDE.RicciFlow
