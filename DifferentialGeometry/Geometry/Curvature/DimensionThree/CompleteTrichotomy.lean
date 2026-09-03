import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelLineSplitting

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ
  (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
variable [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

noncomputable local instance completeTrichotomyTwoFormFiniteDimensional
    (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

theorem curvatureOperator_time_slice_rank_trichotomy_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) g y
            ⟨metricRm04 (I := I) g y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) g x⟩)) :
    (∀ x, curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0) ∨
      (And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) = 1)
        (HasGlobalSurfaceProductSplitting (I := I) (M := M) g)) ∨
      And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) = 3)
        (∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) g x).inner
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩ a) a) := by
  have hE : Module.finrank Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have htri := curvatureOperator_time_slice_trichotomy_of_metric
    (I := I) hE g hpositive hnull hrank hkernel
  rcases htri with hzero | hline | hpositiveRank
  · exact Or.inl hzero
  · refine Or.inr (Or.inl ⟨hline.1, ?_⟩)
    obtain ⟨S, hSrank, hSfiber, hSparallel⟩ :=
      exists_smooth_parallel_curvatureOperatorImageLine
        (I := I) hE g (metricRm04 (I := I) g)
        (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) g x) hline.1 hkernel
    exact hasGlobalSurfaceProductSplitting_of_parallel_line
      (I := I) (M := M) g hg S hSrank hSparallel
  · exact Or.inr (Or.inr hpositiveRank)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
