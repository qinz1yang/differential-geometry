import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelLineSplitting
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete
import DifferentialGeometry.Geometry.Metric.PullbackCross

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

def HasCurvatureSurfaceProductSplitting
    (g : SmoothRiemannianMetric I M) : Prop :=
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  ∃ (S : ContMDiffVectorSubbundle
      (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel 3)
      (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (P : GlobalSurfaceProductSplitting (I := I) (M := M) g),
    And (S.rank = 1)
      (And
        (∀ x, S.fiber x = curvatureOperatorImageAnnihilatorAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)
        (∀ y : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
          P.line.fiber y =
            (liftTangentSubbundle (I := I) (M := M) S).fiber y))

theorem _root_.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting.pullbackMetric_eq_prod
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    [LocallyPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [Inhabited M]
    (g : SmoothRiemannianMetric I M)
    (P : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting
      (I := I) (M := M) g) :
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    let _ : SigmaCompactSpace P.N := P.sigmaN
    Diffeomorph.pullbackMetricCross
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
        (J := I) (liftedMetric (I := I) g) P.F =
      P.metricN.prod (flatModelMetric ℝ) := by
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  apply SmoothRiemannianMetric.ext_inner
  intro z u v
  rw [Diffeomorph.pullbackMetricCross_inner]
  have h := P.isometry z.1 z.2 u.1 v.1 u.2 v.2
  have hu : u = (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (u.1, u.2)) := by rfl
  have hv : v = (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2)) := by rfl
  rw [hu, hv]
  rw [SmoothRiemannianMetric.prod_inner]
  have hfst (w : TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z) :
      (mfderiv (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod
        𝓘(ℝ, ℝ)) 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)
        Prod.fst z) w = w.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd (w : TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z) :
      (mfderiv (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod
        𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z) w = w.2 := by
    rw [mfderiv_snd]
    rfl
  rw [hfst (show TangentSpace
    (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
    from (u.1, u.2)),
    hfst (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2)),
    hsnd (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (u.1, u.2)),
    hsnd (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2))]
  have hflat : (flatModelMetric ℝ).inner z.2 u.2 v.2 = u.2 * v.2 := by
    change inner ℝ u.2 v.2 = _
    rw [RCLike.inner_apply]
    simp
    ring
  rw [hflat]
  have hFfun : (P.F : P.N × ℝ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) =
    (fun z => P.F z) := by rfl
  rw [hFfun]
  exact h

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
        (HasCurvatureSurfaceProductSplitting (I := I) (M := M) g)) ∨
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
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
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
    obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσ, h,
        hconnected, hsimplyConnected, hhcomplete, F, hF, hmetric⟩ :=
      exists_global_product_diffeomorph_of_parallel_line
        (I := I) (M := M) (m := 2) g hg S hSrank hSparallel
    let _ : TopologicalSpace N := topologyN
    let _ : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel 2) N := hcs
    let _ : IsManifold
        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) N := hmanifold
    let _ : T2Space N := ht2
    let _ : SigmaCompactSpace N := hσ
    have hS' := liftTangentSubbundle_isParallel_of_rank_eq_one
      (I := I) (M := M) g S hSrank hSparallel
    let P : GlobalSurfaceProductSplitting (I := I) (M := M) g := {
      N := N
      metricN := h
      connectedN := hconnected
      simplyConnectedN := hsimplyConnected
      completeN := hhcomplete
      F := F
      line := liftTangentSubbundle (I := I) (M := M) S
      line_rank := by simpa using hSrank
      line_parallel := hS'
      line_compatibility := hF
      isometry := hmetric
    }
    refine ⟨S, P, hSrank, ?_, ?_⟩
    · intro x
      exact hSfiber x
    · intro y
      rw [liftTangentSubbundle_fiber]
  · exact Or.inr (Or.inr hpositiveRank)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
