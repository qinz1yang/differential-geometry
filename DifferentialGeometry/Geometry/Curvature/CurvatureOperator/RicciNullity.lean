import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Metric

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensor04StdAt_eq_zero_of_sectional_eq_zero_of_curvatureOperator_nonnegative
    {x : M} (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {v w : TangentSpace I x}
    (hzero : tensor04StdAt (A : Tensor04At (I := I) (M := M) x) v w w v = 0)
    (a b : TangentSpace I x) :
    tensor04StdAt (A : Tensor04At (I := I) (M := M) x) a b w v = 0 := by
  let R := tensor04StdAt (A : Tensor04At (I := I) (M := M) x)
  change R v w w v = 0 at hzero
  have hsym : R v w b a = R a b w v := by
    have hcurv := mem_algebraicCurvatureTensorSubmodule.mp A.property
    change tensor04StdAt (A : Tensor04At (I := I) (M := M) x) v w b a = _
    rw [hcurv.pair_swap, hcurv.anti_first b a v w, hcurv.anti_last a b v w]
    exact neg_neg _
  have hpos (t : ℝ) : 0 ≤ R a b b a + 2 * t * R a b w v := by
    have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hA 2 ![1,t] ![a,v] ![b,w]
    simp only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one] at h
    change 0 ≤ R a b b a + t * R a b w v + (t * R v w b a + t * t * R v w w v) at h
    rw [hzero, hsym] at h
    nlinarith
  have hle : ∀ t : ℝ, (-(R a b b a) / 2) ≤ t * R a b w v := by
    intro t
    linarith [hpos t]
  by_contra hne
  have h := hle ((-(R a b b a) / 2 - 1) / R a b w v)
  rw [div_mul_cancel₀ _ hne] at h
  linarith

variable [T2Space M] [BoundarylessManifold I M]

theorem mem_curvatureOperatorImageAnnihilatorAt_of_ricciTensor_self_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : (⟨metricRm04At g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {v : TangentSpace I x} (hv : ricciTensor g x v v = 0) :
    v ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis ℝ (TangentSpace I x)
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩
  let R := tensor04StdAt (A : Tensor04At (I := I) (M := M) x)
  have htrace : ricciTensor g x v v = ∑ i, R (ob i) v v (ob i) := by
    rw [ricciTensor_apply, LinearMap.trace_eq_sum_inner _ ob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MetricFiberData.toCore_inner D]
    change g.inner x (ob i) (riemannOp (LeviCivita g) x (ob i) v v) = _
    rw [g.symm]
    exact (DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner g x (ob i) v v (ob i)).symm
  have hsec (i) : 0 ≤ R (ob i) v v (ob i) := by
    have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hR 1
      (fun _ => 1) (fun _ => ob i) (fun _ => v)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul] using h
  have hzero (i) : R (ob i) v v (ob i) = 0 := by
    apply le_antisymm
    · calc
        R (ob i) v v (ob i) ≤ ∑ j, R (ob j) v v (ob j) :=
          Finset.single_le_sum (fun j _ => hsec j) (Finset.mem_univ i)
        _ = 0 := htrace.symm.trans hv
    · exact hsec i
  apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StdAt_eq_zero g x
    ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ v).mpr
  intro a b w
  have hi (i) : R a b v (ob i) = 0 :=
    tensor04StdAt_eq_zero_of_sectional_eq_zero_of_curvatureOperator_nonnegative
      A hR (hzero i) a b
  have hlin : (A : Tensor04At (I := I) (M := M) x).toMultilinearMap.toLinearMap
      (vec4 a b v w) 3 = 0 := by
    apply ob.toBasis.ext
    intro i
    change (A : Tensor04At (I := I) (M := M) x)
      (Function.update (vec4 a b v w) (3 : Fin 4) (ob i)) = 0
    have hupd : Function.update (vec4 a b v w) (3 : Fin 4) (ob i) = vec4 a b v (ob i) := by
      funext k
      fin_cases k <;> rfl
    rw [hupd]
    exact hi i
  have hw := congrArg (fun f => f w) hlin
  rw [MultilinearMap.toLinearMap_apply] at hw
  have hupd : Function.update (vec4 a b v w) (3 : Fin 4) w = vec4 a b v w := by
    funext k
    fin_cases k <;> rfl
  rw [hupd] at hw
  exact hw


theorem mem_curvatureOperatorImageAnnihilatorAt_iff_ricciSharp_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : (⟨metricRm04At g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    v ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ ↔
      ricciSharp g x v = 0 := by
  constructor
  · exact ricciSharp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x
  · intro hv
    apply mem_curvatureOperatorImageAnnihilatorAt_of_ricciTensor_self_eq_zero g x hR
    rw [← inner_ricciSharp, hv]
    simp

theorem curvatureOperatorImageAnnihilatorAt_eq_ker_ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : (⟨metricRm04At g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ =
      (ricciSharp g x).ker := by
  ext v
  exact mem_curvatureOperatorImageAnnihilatorAt_iff_ricciSharp_eq_zero g x hR v

end DifferentialGeometry.Geometry.Curvature
