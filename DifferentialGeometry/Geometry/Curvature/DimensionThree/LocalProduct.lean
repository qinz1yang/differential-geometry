import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.LocalProduct
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open TopologicalSpace Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_positive_surface_local_product_of_curvatureOperator_rank_one
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M)
    (hcone : ∀ y, (⟨metricRm04At g y,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ y, Module.finrank ℝ (curvatureOperatorImageAt g y
      ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩) = 1)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun y => curvatureOperatorKernelAt g y
        ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩))
    (x : M) :
    ∃ (e : TangentSpace I x) (K : Opens (perpSpace g x e))
      (O : Opens ℝ)
      (phi : PartialDiffeomorph ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I
        (perpSpace g x e × ℝ) M ∞)
      (hPhi : IsLocalDiffeomorph ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I ∞
        (fun y : K × O => phi (y.1.1, y.2.1)))
      (h : SmoothRiemannianMetric (perpModel g x e) K),
      e ∈ curvatureOperatorImageAnnihilatorAt g x
        ⟨metricRm04At g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ ∧
      g.inner x e e = 1 ∧
      Module.finrank ℝ (perpSpace g x e) = 2 ∧
      (0 : perpSpace g x e) ∈ K ∧ (0 : ℝ) ∈ O ∧
      IsPreconnected (O : Set ℝ) ∧ phi.source = (K : Set _) ×ˢ (O : Set ℝ) ∧
      phi (0, 0) = x ∧
      (localPullMetric g
        (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
          h.prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ k : K, 0 < metricScalarAt h k) ∧
      (∀ (k : K) (v w : TangentSpace (perpModel g x e) k),
        LinearIndependent ℝ ![v, w] → 0 < Geometry.Riemannian.sectionalCurvature h k v w) ∧
      ∀ k ∈ K, ∀ r ∈ O, ∀ v : TangentSpace I (phi (k, r)),
        (v ∈ curvatureOperatorImageAnnihilatorAt g (phi (k, r))
          ⟨metricRm04At g (phi (k, r)),
            metricRm04At_mem_algebraicCurvatureTensorSubmodule g (phi (k, r))⟩ ↔
          ∃ q : ℝ, mfderiv ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I
            (fun z : perpSpace g x e × ℝ => phi z) (k, r) (0, q) = v) ∧
        ((∀ w ∈ curvatureOperatorImageAnnihilatorAt g (phi (k, r))
          ⟨metricRm04At g (phi (k, r)),
            metricRm04At_mem_algebraicCurvatureTensorSubmodule g (phi (k, r))⟩,
          g.inner (phi (k, r)) w v = 0) ↔
          ∃ u : TangentSpace (perpModel g x e) k,
            mfderiv ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I
              (fun z : perpSpace g x e × ℝ => phi z) (k, r) (u, 0) = v) := by
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ :=
    exists_smooth_parallel_curvatureOperatorImageLine hdim g (metricRm04 g)
      (fun y => metricRm04At_mem_algebraicCurvatureTensorSubmodule g y) hrank hkernel
  obtain ⟨U, X, -, hxU, hmem, hunit, -, K, O, phi, hproduct,
      hOconnected, -, -, halign⟩ :=
    L.exists_local_product_chart_of_rank_eq_one g hLrank hLparallel x
  rcases hproduct with ⟨hKopen, hzeroK, hOopen, hzeroO, hsource, hbase, hproduct⟩
  let K' : Opens (perpSpace g x (X x)) := ⟨K, hKopen⟩
  let O' : Opens ℝ := ⟨O, hOopen⟩
  let _ : (perpModel g x (X x)).Boundaryless := by
    constructor
    ext y
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y, rfl⟩
  obtain ⟨hPhi, h, -, hmetric, hscalar⟩ :=
    exists_metric_scalar_eq_of_local_product_partialDiffeomorph g
      K' O' hzeroO phi (by rw [hsource]; exact Subset.rfl) hproduct
  have hdimP : Module.finrank ℝ (perpSpace g x (X x)) = 2 := by
    rw [finrank_perpSpace _ _ _ (by
      intro hz
      have hu := hunit x hxU
      rw [hz, map_zero] at hu
      norm_num at hu), hdim]
  have hpos (k : K') : 0 < metricScalarAt h k := by
    rw [hscalar k ⟨0, hzeroO⟩]
    exact metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim g _ (hcone _) (hrank _)
  refine ⟨X x, K', O', phi, hPhi, h, hLfiber x ▸ hmem x hxU, hunit x hxU,
    hdimP, hzeroK, hzeroO, hOconnected, hsource, hbase, hmetric, hpos, ?_, ?_⟩
  · intro k v w hvw
    exact Geometry.Riemannian.sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
      h hdimP k (hpos k) v w hvw
  · intro k hk r hr v
    have ha := halign k hk r hr v
    simp only [hLfiber] at ha
    exact ha

end DifferentialGeometry.Geometry.Curvature.DimensionThree
