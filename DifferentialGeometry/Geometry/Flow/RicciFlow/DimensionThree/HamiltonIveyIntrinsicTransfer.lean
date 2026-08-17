import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyBundleRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckFrameAssembly

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

theorem curvatureOperatorRegionPropagationOn_of_fiberRegion_mem
    {T : ℝ} (hT : 0 < T)
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {K : ℝ} (hK : 0 < K)
    (hC : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈
        fiberHamiltonIveyRegion basisAt K t x) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        ∃ _horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis,
          curvatureOperatorMatrixAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ ∈
            hamiltonIveyConvexMatrixRegion K t := by
  intro t ht x
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : OrthonormalBasisAt (I := I) (S.base.metric t) x moving :=
    uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht
  have hA : uhlenbeckPulledRm04At S basisAt iota t x ∈
      fiberHamiltonIveyRegion basisAt K t x := hC t ht x
  rcases hA with ⟨hAlg, hmat⟩
  have hwitness : ∀ (h h' : uhlenbeckPulledRm04At S basisAt iota t x ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x),
      curvatureOperatorMatrixAt (I := I) x (basisAt x)
          ⟨uhlenbeckPulledRm04At S basisAt iota t x, h⟩ =
        curvatureOperatorMatrixAt (I := I) x (basisAt x)
          ⟨uhlenbeckPulledRm04At S basisAt iota t x, h'⟩ := by
    intro h h'
    ext i j
    rfl
  have hmat' : curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x,
          uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (M := M) S basisAt iota t x⟩ ∈
      hamiltonIveyConvexMatrixRegion K t := by
    rwa [hwitness hAlg uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule] at hmat
  have htransfer := curvatureOperatorMatrixAt_pulledTensor_eq_original_moving
    (I := I) (M := M) hT S basisAt iota hiota0 hgram ht x
  have hmat'' : curvatureOperatorMatrixAt (I := I) x moving
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ ∈
      hamiltonIveyConvexMatrixRegion K t := by
    rwa [← htransfer] at hmat'
  exact ⟨moving, hmovingOrth, hmat''⟩


theorem pulledCurvature_initial_mem_fiberRegion
    {T : ℝ} (hT : 0 < T)
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {K : ℝ} (hK : 0 < K) (x : M)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric 0) x
      ⟨S.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric 0) x⟩ K) :
    uhlenbeckPulledRm04At S basisAt iota 0 x ∈
      fiberHamiltonIveyRegion basisAt K 0 x := by
  have hzero : uhlenbeckPulledRm04At S basisAt iota 0 x = S.base.rm04 0 x :=
    uhlenbeckPulledRm04At_zero_eq_rm04 S basisAt iota hiota0 x
  rw [hzero]
  refine ⟨metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric 0) x, ?_⟩
  exact curvatureOperatorMatrixAt_initial_mem_hamiltonIveyConvexMatrixRegion
    (I := I) (M := M) S hK (basisAt x) (horth0 x) hinit

end DifferentialGeometry.PDE.RicciFlow

end
