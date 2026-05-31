import RicciFlower.RicciFlow.Evolution.ImprovedPinching.HamiltonRHS

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved pinching TfHeatAssembly

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

/-- Eigenvalue-facing form of Lemma 10.4.  This consumes Section 6 scalar and
Ricci-norm heat equations plus pointwise Ricci eigenvalue data for the scalar,
norm, cubic trace, and reaction term. -/
theorem tfHeat_eigen
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hreaction : ∀ t x,
      reaction t x = ricciReact3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube) reaction
    hscalarHeat hRicHeat
    (tfRel_from_eigen
      scalar ricciNormSq ricciTraceCube reaction
      l1 l2 l3 hscalar hnorm hcube hreaction)

/-- Diagonal-eigenframe form of Lemma 10.4, using the standard 3D diagonal
curvature contraction for the reaction term. -/
theorem tfHeat_diag
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq
        (diagReact3 l1 l2 l3))
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube)
    (diagReact3 l1 l2 l3)
    hscalarHeat hRicHeat
    (tfRel_from_diag
      (M := M)
      scalar ricciNormSq ricciTraceCube l1 l2 l3 hscalar hnorm hcube)

/-- Section 6 consumer for Lemma 10.4.  It uses the canonical Ricci-norm heat
equation route; the remaining geometric input is exactly the reaction relation
for the chosen three-dimensional convention. -/
theorem tfHeat_sec6
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (scalar scalarLap gradScalarNormSq Q : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hRel : tfRicReactRel
      scalar (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      Q (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame) Q := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap
    (ricciNormSqInFrame (I := I) S gInv frame)
    ricciNormLap
    (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
    gradScalarNormSq Q
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    hscalar
    (ricciNormHeatEquationOn_of_solution_canonical_laplacian
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
      h_inv h_ricci hInvSym hRicSym h_lap)
    hRel

/-- Section 10.4 from Section 6 heat equations, with an arbitrary orthonormal
heat frame and a separate pointwise Ricci eigenbasis for the reaction algebra. -/
theorem tfHeat_point
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
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
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (htrace : ∀ (t : Real) (x : M),
      DimensionThree.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
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
    fin_cases i <;> fin_cases j <;> simp [DimensionThree.delta3]
  have hRel :=
    tfRel_point_sec6 (I := I) S Rm04 gInv frame heatBasis eigBasis
      scalar ricciTraceCube l1 l2 l3 hheatBasis hheat heig htrace hdiag hcube hInv
  exact tfHeat_sec6
    (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
    scalar scalarLap gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      ricciTraceCube)
    hscalarHeat h_inv h_ricci hInvSym hRicSym h_lap hRel

/-- Section 10.4 arbitrary-heat-frame consumer with signed trace data produced
from first-trace Ricci/scalar realizations at the separate Ricci eigenbasis. -/
theorem tfHeat_pfirst
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
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
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DimensionThree.AlgebraicCurvatureSymmetries3
        (DimensionThree.standardRmCompAt (I := I) (eigBasis t x) (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (Rm04 t x) DimensionThree.delta3 (eigBasis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      Realized.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
        (S.ricciAt t x) DimensionThree.delta3 (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  refine tfHeat_point (I := I) S Rm04 gInv frame heatBasis eigBasis
    roughLapRic ricciNormLap nablaRic scalar scalarLap gradScalarNormSq
    ricciTraceCube l1 l2 l3 hscalarHeat h_inv h_ricci h_lap hheatBasis hheat heig
    ?_ hdiag hcube hInv hRicSym
  intro t x
  exact DimensionThree.traceDataOfFirst (I := I) (M := M) (heig t x)
    (hcurv t x) (hRicFirst t x) (hScalarTrace t x)

/-- Section 10.4 with the Ricci eigenbasis chosen pointwise from symmetry.

The conclusion returns the chosen eigenbasis/eigenvalue package and the
corresponding eigenvalue definition of `tr(Ric^3)`.  No smooth eigenframe is
asserted or needed. -/
theorem tfHeat_eig
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DimensionThree.AlgebraicCurvatureSymmetries3
          (DimensionThree.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DimensionThree.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DimensionThree.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 ricciTraceCube : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      (∀ t x,
        ricciTraceCube t x =
          DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) ∧
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
  have heigExists : ∀ t x,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        ∃ l1 l2 l3 : Real,
          DimensionThree.OrthonormalBasisAt
            (I := I) (S.base.metric t) x basis ∧
          DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
            (DimensionThree.ricciEigenScalar3 l1 l2 l3) l1 l2 l3 basis := by
    intro t x
    exact DimensionThree.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (hRicSymAt t x)
  choose eigBasis l1 l2 l3 heig using heigExists
  let cube : Real -> M -> Real := fun t x =>
    ricciCubeInvAt (I := I) (S.base.metric t) (S.ricciAt t x)
  have heigOn : ∀ t x,
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x) := by
    intro t x
    exact (heig t x).1
  have hdiag0 : ∀ t x,
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
        (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    exact (heig t x).2
  have hdiag : ∀ t x,
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    rcases hdiag0 t x with ⟨hscalar0, hric⟩
    have hscalar :
        scalar t x =
          DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) :=
      scalar_eq_diag (I := I) (hScalarTrace t x (eigBasis t x) (heigOn t x))
        (hdiag0 t x)
    exact ⟨hscalar, hric⟩
  have hcube : ∀ t x,
      cube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) := by
    intro t x
    exact ricciCubeInv_diag (I := I) (S.base.metric t)
      (heigOn t x) (hdiag0 t x)
  refine ⟨eigBasis, l1, l2, l3, cube, heigOn, hdiag, hcube, ?_⟩
  exact tfHeat_pfirst (I := I) S Rm04 gInv frame heatBasis eigBasis
    roughLapRic ricciNormLap nablaRic scalar scalarLap gradScalarNormSq
    cube l1 l2 l3 hscalarHeat h_inv h_ricci h_lap hheatBasis hheat heigOn
    (fun t x => hcurv t x (eigBasis t x) (heigOn t x))
    (fun t x => hRicFirst t x (eigBasis t x) (heigOn t x))
    (fun t x => hScalarTrace t x (eigBasis t x) (heigOn t x))
    hdiag hcube hInv hRicSym

/-- Section 10.4 with pointwise eigenbasis selection and the canonical cubic
trace `tr((Ric^#)^3)` scalar. -/
theorem tfHeat_can
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DimensionThree.AlgebraicCurvatureSymmetries3
          (DimensionThree.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DimensionThree.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DimensionThree.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  rcases tfHeat_eig (I := I) S Rm04 gInv frame heatBasis roughLapRic
      ricciNormLap nablaRic scalar scalarLap gradScalarNormSq hscalarHeat h_inv
      h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv hRicFirst
      hScalarTrace hInv hRicSym with
    ⟨eigBasis, l1, l2, l3, cube, heig, hdiag, hcube, hheatEq⟩
  have hcubeEq : cube = ricciCube (I := I) S := by
    funext t x
    calc
      cube t x =
          DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) :=
            hcube t x
      _ = ricciCube (I := I) S t x := by
            simpa [ricciCube] using
              (ricciCubeInv_diag (I := I) (S.base.metric t)
                (heig t x) (hdiag t x)).symm
  refine ⟨eigBasis, l1, l2, l3, heig, hdiag, ?_⟩
  simpa [hcubeEq] using hheatEq

/-- Canonical Section 10.4 consumer from an already packaged Ricci-norm heat
equation.  This is the entry point to use after Lemma 6.7 has been produced
elsewhere, avoiding another expansion of the inverse-metric/Ricci evolution and
Bochner inputs in this file. -/
theorem tfHeat_canR
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hRicHeat : RicciNormHeatEquationOn
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame))
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DimensionThree.AlgebraicCurvatureSymmetries3
          (DimensionThree.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DimensionThree.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DimensionThree.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  have heigExists : ∀ t x,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        ∃ l1 l2 l3 : Real,
          DimensionThree.OrthonormalBasisAt
            (I := I) (S.base.metric t) x basis ∧
          DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
            (DimensionThree.ricciEigenScalar3 l1 l2 l3) l1 l2 l3 basis := by
    intro t x
    exact DimensionThree.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (hRicSymAt t x)
  choose eigBasis l1 l2 l3 heig using heigExists
  have heigOn : ∀ t x,
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x) := by
    intro t x
    exact (heig t x).1
  have hdiag0 : ∀ t x,
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
        (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    exact (heig t x).2
  have hdiag : ∀ t x,
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    rcases hdiag0 t x with ⟨_hscalar0, hric⟩
    have hscalar :
        scalar t x =
          DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) :=
      scalar_eq_diag (I := I) (hScalarTrace t x (eigBasis t x) (heigOn t x))
        (hdiag0 t x)
    exact ⟨hscalar, hric⟩
  have hcube : ∀ t x,
      ricciCube (I := I) S t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) := by
    intro t x
    exact ricciCubeInv_diag (I := I) (S.base.metric t)
      (heigOn t x) (hdiag0 t x)
  have hRel :
      tfRicReactRel
        scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S))
        (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) :=
    tfRel_pfirst (I := I) S Rm04 gInv frame heatBasis eigBasis
      scalar (ricciCube (I := I) S) l1 l2 l3 hheatBasis hheat heigOn
      (fun t x => hcurv t x (eigBasis t x) (heigOn t x))
      (fun t x => hRicFirst t x (eigBasis t x) (heigOn t x))
      (fun t x => hScalarTrace t x (eigBasis t x) (heigOn t x))
      hdiag hcube hInv
  refine ⟨eigBasis, l1, l2, l3, heigOn, hdiag, ?_⟩
  exact tfHeat_base
    (D := D)
    scalar scalarLap
    (ricciNormSqInFrame (I := I) S gInv frame)
    ricciNormLap
    (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
    gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      (ricciCube (I := I) S))
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    hscalarHeat hRicHeat hRel

/-- Canonical Section 10.4 wrapper using `SolutionOn.scalar` as the scalar
curvature, so scalar trace realization is produced from the intrinsic metric
trace instead of supplied separately. -/
theorem tfHeat_scalar
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DimensionThree.AlgebraicCurvatureSymmetries3
          (DimensionThree.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DimensionThree.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_can (I := I) S Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic S.scalar scalarLap gradScalarNormSq hscalarHeat
    h_inv h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv hRicFirst ?_
    hInv hRicSym
  intro t x basis horth
  have htr := scalarTrace_delta (I := I) (S.base.metric t)
    (S.ricciAt t x) horth
  simpa [SolutionOn.scalar_eq_metricTrace] using htr

/-- Canonical Section 10.4 wrapper that also produces the first-trace Ricci
realization from an intrinsic `Rm13` trace and lowering relation. -/
theorem tfHeat_trace
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DimensionThree.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DimensionThree.AlgebraicCurvatureSymmetries3
          (DimensionThree.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRic13 : ∀ t x,
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (Rm13 t x))
    (hLower : ∀ t x,
      Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (Rm13 t x) (Rm04 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_scalar (I := I) S Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv ?_ hInv ?_
  · intro t x basis horth
    exact firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (Rm13 t x) (Rm04 t x) (hRic13 t x) (hLower t x)
  · intro t x i j
    simpa [ricciCompInFrame] using
      hRicSymAt t x (frame i x) (frame j x)

/-- Section 10.4 wrapper where the algebraic curvature symmetries and lowering
relation are produced from Levi-Civita `Rm13`/`Rm04` realization data. -/
theorem tfHeat_lc
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞))
    (hRm13 : ∀ t,
      Realized.Rm13RealizesConnection (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (Rm13 t))
    (hRm04 : ∀ t,
      Realized.Rm04RealizesConnection (I := I) (S.base.metric t)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (Rm04 t))
    (hRic13 : ∀ t x,
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (Rm13 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  have hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (Rm13 t x) (Rm04 t x) :=
      Realized.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := Rm13 t) (Rm04 := Rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DimensionThree.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (Rm13 t x) (Rm04 t x) (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DimensionThree.delta3
      (S.ricciAt t x) (Rm04 t x) hTrace
      (RicciFlower.LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  refine tfHeat_trace (I := I) S Rm13 Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim hRicSymAt ?_ hRic13 ?_ hInv
  · intro t x basis _horth
    exact
      DimensionThree.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t) basis
  · intro t x
    exact Realized.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := Rm13 t) (Rm04 := Rm04 t)
      (hRm13 t) (hRm04 t) x

/-- Section 10.4 using the canonical metric-derived Riemann curvature sections
of the solution candidate. -/
theorem tfHeat_metric
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_lc (I := I) S S.base.rm13 S.base.rm04 gInv frame heatBasis
    roughLapRic ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat
    h_inv h_ricci h_lap hheatBasis hheat hdim hcov ?_ ?_ ?_ hInv
  · intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  · intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  · intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x

/-- Section 10.4 using the canonical metric-derived curvature sections, with
the required order-one Levi-Civita smoothness produced from the metric. -/
theorem tfHeat_metric_smooth
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_metric (I := I) S gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim ?_ hInv
  intro t
  exact
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)

/-- Section 10.4 using the canonical metric-derived curvature sections and an
already packaged Section 6 Ricci-norm heat equation.  This is the shortest
current entry point once Lemma 6.7 has been proved separately. -/
theorem tfHeat_ricci
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hRicHeat : RicciNormHeatEquationOn
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame
        (I := I) S S.base.rm04 gInv frame))
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  have hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) := by
    intro t
    exact
      LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hRm13 : ∀ t,
      Realized.Rm13RealizesConnection (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 : ∀ t,
      Realized.Rm04RealizesConnection (I := I) (S.base.metric t)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 : ∀ t x,
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      Realized.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (S.base.rm04 t x) DimensionThree.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
        (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DimensionThree.delta3
      (S.ricciAt t x) (S.base.rm04 t x) hTrace
      (RicciFlower.LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  refine tfHeat_canR (I := I) S S.base.rm04 gInv frame heatBasis
    ricciNormLap nablaRic S.scalar scalarLap gradScalarNormSq
    hscalarHeat hRicHeat hheatBasis hheat hdim hRicSymAt ?_ ?_ ?_ hInv
  · intro t x basis _horth
    exact
      DimensionThree.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t) basis
  · intro t x basis horth
    have hLowerAt :
        Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      Realized.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    exact firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      (hRic13 t x) hLowerAt
  · intro t x basis horth
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr

/-- Section 10.4 packaged with the canonical metric-compatible producer for
Lemma 6.7.  This theorem supplies the Ricci-norm heat equation by calling
`ricci_heat_mc`, then applies `tfHeat_ricci`. -/
theorem tfHeat_mc
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (basis : (x : M) -> Module.Basis (Fin 3) Real (TangentSpace I x))
    (X : (x : M) -> Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Real -> (x : M) -> Realized.Tensor02At (I := I) x)
    (nablaA : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hframe : ∀ x i, basis x i = frame i x)
    (hinv : ∀ t x,
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := M)
        (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x,
      Realized.SmoothBasisFieldsAt (I := I) (basis x) (X x))
    (hlapTrace : ∀ t x,
      ricciNormLap t x =
        Realized.metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hA : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (S.base.connection t) (A t) (nablaA t))
    (h2 : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (S.base.connection t) (nablaA t) (nabla2A t))
    (hdu : ∀ t,
      Realized.DuFieldRealizes (I := I)
        (fun y : M => Realized.normSq02 (I := I) (S.base.metric t) y (A t y))
        (du t))
    (hHess : ∀ t x,
      Realized.HessianRealizesNablaDuAt (I := I) (S.base.connection t) (du t)
        (normSecond t) x)
    (hrough : ∀ t x,
      Realized.RoughLap0SRealizesMetricTraceInBasis (I := I)
        (basis x) (gInv t x) (s := 2) (roughA t x) (nabla2A t x))
    (hAComp : ∀ t x i j,
      A t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
        ricciTwoTensorField (I := I) S t x (frame i x) (frame j x))
    (hroughComp : ∀ t x i j,
      roughA t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : ∀ t x a i j,
      nablaA t x (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DimensionThree.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  have hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i := by
    intro t x i j
    rw [hInv t x i j, hInv t x j i]
    exact delta3_symm i j
  have hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) := by
    intro t
    exact
      LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hRm13 : ∀ t,
      Realized.Rm13RealizesConnection (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 : ∀ t,
      Realized.Rm04RealizesConnection (I := I) (S.base.metric t)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 : ∀ t x,
      S.ricciAt t x =
        Realized.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hRicSymAt : ∀ (t : Real) (x : M),
      DimensionThree.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        Realized.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      Realized.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (S.base.rm04 t x) DimensionThree.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
        (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DimensionThree.delta3
      (S.ricciAt t x) (S.base.rm04 t x) hTrace
      (RicciFlower.LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t) (hcov := hcov t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (RicciFlower.LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  have hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i := by
    intro t x i j
    simpa [ricciCompInFrame] using hRicSymAt t x (frame i x) (frame j x)
  have hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I)
        (S.base.connection t) (S.base.metric t) := by
    intro t
    simpa [SolutionFamily.connection] using
      (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))
  have hRicHeat :
      RicciNormHeatEquationOn
        (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
        ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        (ricciNormCurvatureReactionInFrame
          (I := I) S S.base.rm04 gInv frame) :=
    ricci_heat_mc (I := I) S S.base.rm04 gInv frame roughLapRic
      ricciNormLap nablaRic basis X A roughA nablaA nabla2A du normSecond
      h_inv h_ricci hInvSym hRicSym hmc hframe hinv hfields hlapTrace
      hA h2 hdu hHess hrough hAComp hroughComp hnablaComp
  exact tfHeat_ricci (I := I) S gInv frame heatBasis ricciNormLap nablaRic
    scalarLap gradScalarNormSq hscalarHeat hRicHeat hheatBasis hheat hdim hInv

end RicciFlow
end RicciFlower
