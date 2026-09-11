import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelLineSplitting
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.UniversalCover.Flat
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ
  (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
variable [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

noncomputable local instance completeTrichotomyTwoFormFiniteDimensional
    (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

omit [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M] in
private theorem riemannOp_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hzero : curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0) :
    ∀ X Y Z : TangentSpace I x,
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0 := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x
    (by
      exact (show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real
          (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans
        (by simp [DifferentialGeometry.Topology.Morse.MorseModel]))
  have hAzero :
      (⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) = 0 := by
    apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal
      (I := I) g x basis horth
    ext i j
    have hpair : curvatureOperatorPairingAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩
        (curvatureTwoFormBasisAt (I := I) basis i)
        (curvatureTwoFormBasisAt (I := I) basis j) = 0 := by
      rw [← twoFormMetricData_inner_curvatureOperatorEndomorphismAt, hzero]
      simp
    rw [curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth] at hpair
    change 2 * curvatureOperatorMatrixAt (I := I) x basis
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 at hpair
    have hij : curvatureOperatorMatrixAt (I := I) x basis
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 := by
      linarith
    simpa using hij
  have hRmzero : metricRm04 (I := I) g x = 0 :=
    congrArg Subtype.val hAzero
  intro X Y Z
  let R := riemannOp (LeviCivita (I := I) g) x X Y Z
  have hinner : g.inner x R R = 0 := by
    rw [← DifferentialGeometry.rm04_eq_inner_riem (I := I) g x X Y Z R]
    have happly := congrArg
      (fun A : Tensor04At (I := I) (M := M) x => A (vec4 X Y Z R)) hRmzero
    simpa using happly
  by_contra hR
  exact (ne_of_gt (g.pos x R hR)) hinner


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
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    let _ : SigmaCompactSpace P.N := P.sigmaN
    And (S.rank = 1)
      (And
        (∀ x, S.fiber x = curvatureOperatorImageAnnihilatorAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)
        (And
          (∀ y : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
            P.line.fiber y =
              (liftTangentSubbundle (I := I) (M := M) S).fiber y)
          (∀ y : P.N,
            0 < metricScalarAt
              (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
              P.metricN y)))

omit [Nonempty M] in
theorem _root_.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting.pullbackMetric_eq_prod
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M]
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
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
  have hflat : (flatModelMetric ℝ).inner z.2 u.2 v.2 = u.2 * v.2 := by
    change inner ℝ u.2 v.2 = _
    rw [RCLike.inner_apply]
    simp
    ring
  rw [hflat]
  convert P.isometry z.1 z.2 u.1 v.1 u.2 v.2 using 1
  all_goals rfl

variable {N : Type} [TopologicalSpace N]
  [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
  [T2Space N]

theorem metricScalarAt_prod_flat
    (g : SmoothRiemannianMetric
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) N)
    (y : N) (t : ℝ) :
    metricScalarAt
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(ℝ, ℝ))
        (g.prod (flatModelMetric ℝ)) (y, t) =
      metricScalarAt
        (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) g y := by
  rw [Curvature.metricScalarAt_productMetric,
    metricScalarAt_eq_zero_of_finrank_le_one (flatModelMetric ℝ)
      (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero]

theorem curvatureOperator_time_slice_rank_trichotomy_of_complete_metric_nonnegative_reaction_constant_rank_parallel_kernel
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
    (And
      (∀ x, curvatureOperatorEndomorphismAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0)
      (HasEuclideanUniversalCover
        (E := DifferentialGeometry.Topology.Morse.MorseModel 3)
        (I := I) (M := M) g)) ∨
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
  have htri := curvatureOperator_time_slice_trichotomy_of_metric_nonnegative_reaction_constant_rank_parallel_kernel
    (I := I) hE g hpositive hnull hrank hkernel
  rcases htri with hzero | hline | hpositiveRank
  · refine Or.inl ⟨hzero, ?_⟩
    let : NeZero (Module.finrank Real
        (DifferentialGeometry.Topology.Morse.MorseModel 3)) :=
      ⟨by rw [hE]; norm_num⟩
    apply hasEuclideanUniversalCover_of_riemannOp_eq_zero (I := I) g hg
    intro x
    exact riemannOp_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) g x (hzero x)
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
    have hfactor : ∀ y : P.N,
        metricScalarAt
            (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
            P.metricN y =
          metricScalarAt (I := I) (liftedMetric (I := I) g) (P.F (y, 0)) := by
      intro y
      have hprod := metricScalarAt_prod_flat P.metricN y (0 : ℝ)
      have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(ℝ, ℝ))
        (J := I) (g := liftedMetric (I := I) g) (Phi := P.F) (x := (y, 0))
      have heq := P.pullbackMetric_eq_prod g
      have heqscalar := congrArg
          (fun q : SmoothRiemannianMetric
            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
            (P.N × ℝ) => metricScalarAt
              (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                𝓘(ℝ, ℝ)) q (y, 0)) heq
      rw [hprod] at heqscalar
      exact heqscalar.symm.trans hpull
    refine ⟨S, P, hSrank, ?_, ?_, ?_⟩
    · intro x
      exact hSfiber x
    · intro y
      rw [liftTangentSubbundle_fiber]
    · intro y
      calc
        metricScalarAt
            (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
            P.metricN y =
            metricScalarAt (I := I) (liftedMetric (I := I) g) (P.F (y, 0)) :=
          hfactor y
        _ = metricScalarAt (I := I) g (proj (P.F (y, 0))) :=
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted
            (I := I) g (P.F (y, 0))
        _ > 0 := metricScalarAt_pos_of_curvatureOperator_rank_one
          (I := I) g (proj (P.F (y, 0)))
          (hpositive (proj (P.F (y, 0)))) (hline.1 (proj (P.F (y, 0))))
  · exact Or.inr (Or.inr hpositiveRank)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
