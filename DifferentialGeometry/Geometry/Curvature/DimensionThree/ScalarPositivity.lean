import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Tensor0SBundle
open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

noncomputable local instance scalarPositivityTwoFormFiniteDimensional
    (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

omit [T2Space M] in
theorem curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :
    0 ≤ (twoFormMetricData g x).inner (curvatureOperatorEndomorphismAt g x A a) a := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) x
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) x
  let ι : TangentSpace I x ≃L[ℝ] TangentSpace I x := ContinuousLinearEquiv.refl ℝ _
  have hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫ := by intros; rfl
  let e := (exteriorPower.musicalEquiv (E := TangentSpace I x) 2).trans
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
  obtain ⟨u, hu⟩ := e.surjective a
  have hpos := traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
    A hA ι.toContinuousLinearMap
  have hp := curvatureOperatorPairingAt_pullback_musical hdim g x A ι hmetric u u
  rw [twoFormMetricData_inner_curvatureOperatorEndomorphismAt, ← hu]
  exact hp ▸ hpos.inner_nonneg_left u


theorem metricScalarAt_pos_of_curvatureOperator_rank_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a)
    (hrank : Module.finrank Real
        (curvatureOperatorImageAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) = 1) :
    0 < metricScalarAt (I := I) g x := by
  exact Curvature.metricScalarAt_pos_of_curvatureOperator_rank_pos g x hpositive
    (by rw [hrank]; exact Nat.zero_lt_one)

theorem metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
    (hE : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (hcone : (⟨metricRm04At g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : Module.finrank Real (curvatureOperatorImageAt g x
      ⟨metricRm04At g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 1) :
    0 < metricScalarAt g x := by
  exact metricScalarAt_pos_of_curvatureOperator_rank_one g x
    (fun a => curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
      hE g x _ hcone a) hrank

end DifferentialGeometry.Geometry.Curvature.DimensionThree
