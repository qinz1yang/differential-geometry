import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.ThreeQuadratic
import DifferentialGeometry.Analysis.Calculus.Multilinear
import DifferentialGeometry.Geometry.Curvature.QuadraticTensor
import DifferentialGeometry.Geometry.Curvature.RicciAction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
private theorem curvatureQuadraticCombination_coord
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (x : M) (m : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x
        (fun q => coordBasisAt (I := I) x (m q)) =
      bComp (coordInv S x t x) (rmComp S x t x) (m 0) (m 1) (m 2) (m 3) -
        bComp (coordInv S x t x) (rmComp S x t x) (m 0) (m 1) (m 3) (m 2) +
        bComp (coordInv S x t x) (rmComp S x t x) (m 0) (m 2) (m 1) (m 3) -
        bComp (coordInv S x t x) (rmComp S x t x) (m 0) (m 3) (m 1) (m 2) := by
  let basis := coordBasisAt (I := I) x
  let gInv := coordInv S x t x
  have hbasis : basis = coordinateFrameAtToBasis (I := I) x := by
    ext i
    simp [basis]
  have hinv : MetricInverseInBasisGen (I := I) (S.family.metric t) x basis gInv := by
    rw [hbasis]
    exact coordInvReal S x t
  have hRm (i j k l : CoordinateIdx (𝕜 := ℝ) E) :
      component0S (I := I) basis (S.base.rm04 t x) ![i, j, k, l] =
        rmComp S x t x i j k l := by
    change S.base.rm04 t x _ = S.base.rm04 t x _
    congr 1
    funext q
    fin_cases q <;> simp [basis, coordBasisAt_coe, vec4]
  have hB (a b c d : CoordinateIdx (𝕜 := ℝ) E) :
      bComp gInv (rmComp S x t x) a b c d =
        ∑ f, ∑ r, ∑ e, ∑ q, gInv f r * gInv e q *
          rmComp S x t x a e b f * rmComp S x t x c q d r := by
    unfold bComp
    rw [DifferentialGeometry.Tensor.SlotAlgebra.sum_rotate4_two]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcomp := curvatureQuadraticCombination_component
    (S.family.metric t) basis gInv hinv (S.base.rm04 t) m
  simp only [hRm] at hcomp
  rw [← hB, ← hB, ← hB, ← hB] at hcomp
  exact hcomp

private theorem ricciDrift04_coord
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (x : M) (m : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    ricciDrift04 (S.family.metric t) x
        (fun q => coordBasisAt (I := I) x (m q)) =
      rmDrift (ricciOneUpCompInFrame S (coordInv S x)
        (coordinateFrameAt (I := I) x) t x) (rmComp S x t x)
        (m 0) (m 1) (m 2) (m 3) := by
  let basis := coordBasisAt (I := I) x
  let gInv := coordInv S x t x
  have hbasis : basis = coordinateFrameAtToBasis (I := I) x := by
    ext i
    simp [basis]
  have hinv : MetricInverseInBasisGen (I := I) (S.family.metric t) x basis gInv := by
    rw [hbasis]
    exact coordInvReal S x t
  have hv : vec4 (I := I) (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3)) =
      fun q => coordBasisAt (I := I) x (m q) := by
    funext q
    fin_cases q <;> rfl
  have hc := ricciDrift_comp (S.family.metric t) basis gInv hinv
    (m 0) (m 1) (m 2) (m 3)
  rw [hv] at hc
  change ricciDrift04 (S.family.metric t) x _ = _ at hc
  rw [hc]
  simp only [rmDrift, ricciOneUpCompInFrame, ricciCompInFrame, SolutionOn.ricciAt,
    SolutionFamily.ricciAt, rmComp, SolutionFamily.rm04, metricRm04_apply,
    basis, gInv, coordBasisAt_coe, SolutionOn.family_metric]

theorem riemann_tensor_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M) :
    HasDerivAt (fun s => S.base.rm04 s x)
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
        ricciDrift04 (S.family.metric t) x) (t : ℝ) := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
  let rhs := roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
    (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
    ricciDrift04 (S.family.metric t) x
  have h : HasDerivAt (fun s => e (S.base.rm04 s x)) (e rhs) (t : ℝ) := by
    apply ContinuousMultilinearMap.hasDerivAt_of_basis_eval (coordBasisAt (I := I) x)
    intro m
    have hcoord := riemann_hasDerivAt_three_quadratic_of_solution S hS x t m
    simp only [solutionCurvatureComponents_apply, ← coordBasisAt_coe] at hcoord
    refine hcoord.congr_deriv ?_
    change _ = rhs (fun q => coordBasisAt (I := I) x (m q))
    dsimp only [rhs]
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    rw [curvatureQuadraticCombination_coord, ricciDrift04_coord,
      rmQuad_eq_b _ (rm04SymmOfSol S x t x)
        (coordInvSymmOn S x t (coordinateFrameAt_mem (I := I) x))]
    have hlap := rm04LapFam_real S (t : ℝ) x (m 0) (m 1) (m 2) (m 3)
    have hv : vec4 (I := I)
        (coordBasisAt (I := I) x (m 0)) (coordBasisAt (I := I) x (m 1))
        (coordBasisAt (I := I) x (m 2)) (coordBasisAt (I := I) x (m 3)) =
        fun q => coordBasisAt (I := I) x (m q) := by
      funext q
      fin_cases q <;> rfl
    rw [hv] at hlap
    change rmLap _ _ _ _ _ _ = _ at hlap
    rw [hlap]
    ring
  have h' := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (t : ℝ) h
  change HasDerivAt (fun s => S.base.rm04 s x) rhs (t : ℝ) at h'
  exact h'

theorem riemann_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    HasDerivAt (fun s => S.base.rm04 s x v)
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x v -
        2 * curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x v -
        ricciDrift04 (S.family.metric t) x v) (t : ℝ) := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ v
  have h := (ev.comp e.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt
    (t : ℝ) (riemann_tensor_hasDerivAt_of_solution S hS t x)
  change HasDerivAt (fun s => S.base.rm04 s x v)
    ((roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
      (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
      ricciDrift04 (S.family.metric t) x) v) (t : ℝ) at h
  simpa only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using h

theorem riemann_differentiableAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M) :
    DifferentiableAt ℝ (fun s => S.base.rm04 s x) (t : ℝ) :=
  (riemann_tensor_hasDerivAt_of_solution S hS t x).differentiableAt

end DifferentialGeometry.PDE.RicciFlow
