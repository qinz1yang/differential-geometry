import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.BookData
open DifferentialGeometry.Geometry.Curvature

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

omit [Module.Finite ℝ E] in
theorem pinchEvol_book
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    {epsilon : Real}
    (_heps_pos : 0 < epsilon)
    (_heps_lt : epsilon < 1)
    (hscalar : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      0 < S.scalar (t : Real) x) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
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
  exact pinchEvol_sol (I := I) S hS hdim epsilon hscalar

omit [Module.Finite ℝ E] in
theorem tfHeat_frame
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Geometry.Curvature.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j)
    (hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.stdRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  classical
  have hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i := by
    intro t x i j
    rw [hInv t x i j, hInv t x j i]
    fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.delta3]
  have hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i := by
    intro t x i j
    rw [hRic t x i j, hRic t x j i]
    fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3]
  exact tfHeat_sec6
    (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
    scalar scalarLap gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      ricciTraceCube)
    hscalarHeat h_inv h_ricci hInvSym hRicSym h_lap
    (tfRel_frame (I := I) S Rm04 gInv frame scalar ricciTraceCube
      l1 l2 l3 hscalar hcube hInv hRic hRm)

omit [Module.Finite ℝ E] in
theorem tfHeat_data
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Geometry.Curvature.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (htrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  have hRel :=
    tfRel_data (I := I) S Rm04 gInv frame basis scalar ricciTraceCube
      l1 l2 l3 hbasis htrace hscalar hcube hInv hRic
  exact tfHeat_sec6
    (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
    scalar scalarLap gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      ricciTraceCube)
    hscalarHeat h_inv h_ricci
    (by
      intro t x i j
      rw [hInv t x i j, hInv t x j i]
      fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.delta3])
    (by
      intro t x i j
      rw [hRic t x i j, hRic t x j i]
      fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3])
    h_lap hRel

omit [Module.Finite ℝ E] in
theorem tfHeat_first
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Geometry.Curvature.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (horth : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (basis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Geometry.Curvature.standardRmCompAt (I := I) (basis t x) (Rm04 t x)))
    (hRicTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt
        (I := I) (S.ricciAt t x) (Rm04 t x) DifferentialGeometry.Geometry.Curvature.delta3
        (basis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt
        (I := I) (scalar t x) (S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3
        (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  have hRel :=
    tfRel_first (I := I) S Rm04 gInv frame basis scalar ricciTraceCube
      l1 l2 l3 hbasis horth hcurv hRicTrace hScalarTrace hscalar hcube hInv hRic
  exact tfHeat_sec6
    (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
    scalar scalarLap gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      ricciTraceCube)
    hscalarHeat h_inv h_ricci
    (by
      intro t x i j
      rw [hInv t x i j, hInv t x j i]
      fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.delta3])
    (by
      intro t x i j
      rw [hRic t x i j, hRic t x j i]
      fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3])
    h_lap hRel

end DifferentialGeometry.PDE.RicciFlow
