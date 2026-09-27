import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImagePlane
import DifferentialGeometry.Geometry.Metric.ExteriorSubmodule

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem curvatureOperatorImageAt_eq_musicalEquiv_exterior_orthogonal_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (I := I) g x A) = 1) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace I x) :=
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := (TangentSpace I : M → Type _)) x
    letI : InnerProductSpace ℝ (TangentSpace I x) :=
      Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
    curvatureOperatorImageAt (I := I) g x A =
      LinearMap.range ((exteriorPower.musicalEquiv 2 (E := TangentSpace I x)).toLinearMap.comp
        (exteriorPower.map 2 (curvatureOperatorImageAnnihilatorAt (I := I) g x A)ᗮ.subtype)) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) x
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
  exact ContinuousAlternatingMap.eq_musicalEquiv_map_orthogonal_contractionAnnihilator_of_finrank_eq_one
    hE (curvatureOperatorImageAt (I := I) g x A) hrank

theorem exists_smooth_parallel_curvatureOperatorImagePlane_with_exterior_image
    [I.Boundaryless] [T2Space M]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : ∀ x, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 1)
    (hkernel : Connection.IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (TangentSpace I x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := (TangentSpace I : M → Type _)) x
    letI : ∀ x, InnerProductSpace ℝ (TangentSpace I x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
    ∃ P : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      P.rank = 2 ∧
      (∀ x, P.fiber x = (tangentMetricData (I := I) g x).metric.orthogonal
        (curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩)) ∧
      Connection.IsParallelSubmoduleFamily g P.fiber ∧
      ∀ x, curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩ =
        LinearMap.range ((exteriorPower.musicalEquiv 2 (E := TangentSpace I x)).toLinearMap.comp
          (exteriorPower.map 2 (P.fiber x).subtype)) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : ∀ x, NormedAddCommGroup (TangentSpace I x) :=
    fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) x
  let _ : ∀ x, InnerProductSpace ℝ (TangentSpace I x) :=
    fun x => Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
  obtain ⟨P, hP, hfiber, hparallel⟩ :=
    exists_smooth_parallel_curvatureOperatorImagePlane hE g A hA hrank hkernel
  refine ⟨P, hP, hfiber, hparallel, ?_⟩
  intro x
  have horth : (tangentMetricData (I := I) g x).metric.orthogonal
      (curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩) =
      (curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩)ᗮ := by
    ext v
    rw [MetricFiberData.mem_orthogonal, Submodule.mem_orthogonal]
    rfl
  rw [hfiber, horth]
  exact curvatureOperatorImageAt_eq_musicalEquiv_exterior_orthogonal_of_finrank_eq_one
    hE g x ⟨A x, hA x⟩ (hrank x)

theorem exists_smooth_parallel_curvatureOperatorImageLinePlane
    [I.Boundaryless] [T2Space M]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : ∀ x, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 1)
    (hkernel : Connection.IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (TangentSpace I x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := (TangentSpace I : M → Type _)) x
    letI : ∀ x, InnerProductSpace ℝ (TangentSpace I x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
    ∃ L P : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      L.rank = 1 ∧ P.rank = 2 ∧
      (∀ x, L.fiber x = curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩) ∧
      Connection.IsParallelSubmoduleFamily g L.fiber ∧
      (∀ x, P.fiber x = (tangentMetricData (I := I) g x).metric.orthogonal (L.fiber x)) ∧
      Connection.IsParallelSubmoduleFamily g P.fiber ∧
      ∀ x, curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩ =
        LinearMap.range ((exteriorPower.musicalEquiv 2 (E := TangentSpace I x)).toLinearMap.comp
          (exteriorPower.map 2 (P.fiber x).subtype)) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : ∀ x, NormedAddCommGroup (TangentSpace I x) :=
    fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) x
  let _ : ∀ x, InnerProductSpace ℝ (TangentSpace I x) :=
    fun x => Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ :=
    exists_smooth_parallel_curvatureOperatorImageLine hE g A hA hrank hkernel
  obtain ⟨P, hP, hfiber, hparallel, himage⟩ :=
    exists_smooth_parallel_curvatureOperatorImagePlane_with_exterior_image hE g A hA hrank hkernel
  refine ⟨L, P, hLrank, hP, hLfiber, hLparallel, ?_, hparallel, himage⟩
  intro x
  rw [hLfiber]
  exact hfiber x

end DifferentialGeometry.Geometry.Curvature
