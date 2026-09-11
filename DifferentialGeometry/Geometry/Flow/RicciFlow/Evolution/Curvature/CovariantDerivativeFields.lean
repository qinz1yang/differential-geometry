import DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Components

open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
section Solution

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem connSmoothInf
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

def nablaRm04Field
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))

def nabla2Rm04Field
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))

def nabla3Rm04Field
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04Field_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04Field_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla3Rm04Field_realizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
      (nabla3Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))

def solutionChristoffelComponents
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real :=
  fun t x =>
    christoffelSymbolInFrame (S.family.connection t)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x

def solutionCurvatureComponents
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real :=
  fun t => frameComp0S (I := I) (S.base.rm04 t) (coordinateFrameAt (I := I) x₀)

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
@[simp] theorem solutionCurvatureComponents_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (t : Real) (x : M) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    solutionCurvatureComponents (I := I) S x₀ t x m =
      S.base.rm04 t x (fun q => coordinateFrameAt (I := I) x₀ (m q) x) := rfl

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_one_eq_nablaRm04Field
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (n : Fin 5 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (solutionChristoffelComponents (I := I) S x₀) (solutionCurvatureComponents (I := I) S x₀) 1 t x n =
      nablaRm04Field (I := I) S t x
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) := by
  rw [iteratedRmComp_succ]
  simp only [iteratedRmComp_zero]
  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t)
    (nablaRm04Field_realizes (I := I) S t)
    (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) hx n

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_two_eq_nabla2Rm04Field
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (n : Fin 6 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (solutionChristoffelComponents (I := I) S x₀) (solutionCurvatureComponents (I := I) S x₀) 2 t x₀ n =
      nabla2Rm04Field (I := I) S t x₀
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ n) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  have hlevel1 :
      (fun y : M =>
          iteratedRmComp (I := I) frame
            (solutionChristoffelComponents (I := I) S x₀) (solutionCurvatureComponents (I := I) S x₀) 1 t y) =ᶠ[nhds x₀]
        fun y : M =>
          frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame y := by
    refine Filter.eventually_of_mem
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds (coordinateFrameAt_mem (I := I) x₀))
      ?_
    intro y hy
    funext m
    simpa [frameComp0S, hframe_def] using
      iteratedRmComp_one_eq_nablaRm04Field (I := I) S x₀ t hy m
  rw [iteratedRmComp_succ]
  have hext :
      frameDirectionalDerivatives (I := I) frame
          (fun y : M =>
            iteratedRmComp (I := I) frame
              (solutionChristoffelComponents (I := I) S x₀) (solutionCurvatureComponents (I := I) S x₀) 1 t y) x₀ =
        frameDirectionalDerivatives (I := I) frame
          (frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame) x₀ := by
    funext m d
    simp only [frameDirectionalDerivatives]
    refine mvfderiv_eventuallyEq_congr (I := I) _ ?_
    exact hlevel1.mono fun y hy => congrFun hy m
  have hbase :
      iteratedRmComp (I := I) frame
          (solutionChristoffelComponents (I := I) S x₀) (solutionCurvatureComponents (I := I) S x₀) 1 t x₀ =
        frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame x₀ :=
    hlevel1.self_of_nhds
  rw [hext, hbase]
  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (nablaRm04Field (I := I) S t)
    (nabla2Rm04Field (I := I) S t)
    (nabla2Rm04Field_realizes (I := I) S t)
    frame
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) n

end Solution

section RicciIdentity

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Tensor.RicciIdentity.Nabla0SSectionRealizes (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) := by
  intro y X slots
  exact nablaRm04Field_realizes (I := I) S t X y slots

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Tensor.RicciIdentity.Nabla0SSectionRealizes (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) := by
  intro y X slots
  exact nabla2Rm04Field_realizes (I := I) S t X y slots

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Tensor.RicciIdentity.Nabla20SRealizesAt (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) x
      (nabla2Rm04Field (I := I) S t x) := by
  refine ⟨rm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla2Rm04Field_realizes (I := I) S t X x slots

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Tensor.RicciIdentity.Nabla20SRealizesAt (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) x
      (nabla3Rm04Field (I := I) S t x) := by
  refine ⟨nablaRm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla3Rm04Field_realizes (I := I) S t X x slots

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_ricciIdentityAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x)
      (nabla2Rm04Field (I := I) S (t : Real) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSolution (I := I) S (t : Real)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Tensor.RicciIdentity.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (S.base.rm04 (t : Real)) (nablaRm04Field (I := I) S (t : Real))
    (S.base.rm04 (t : Real) x) (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (rm13OfSolution (I := I) S (t : Real)) rfl rfl
    (rm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_ricciIdentityAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (nablaRm04Field (I := I) S (t : Real) x)
      (nabla3Rm04Field (I := I) S (t : Real) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSolution (I := I) S (t : Real)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Tensor.RicciIdentity.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (nablaRm04Field (I := I) S (t : Real)) (nabla2Rm04Field (I := I) S (t : Real))
    (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (nabla3Rm04Field (I := I) S (t : Real) x)
    (rm13OfSolution (I := I) S (t : Real)) rfl rfl
    (nablaRm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor

end RicciIdentity

end DifferentialGeometry.PDE.RicciFlow
