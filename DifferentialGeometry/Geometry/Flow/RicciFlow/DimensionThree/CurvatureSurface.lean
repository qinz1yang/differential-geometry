import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.LocalProduct

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open TopologicalSpace Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_positive_surface_local_product_at_later_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {x₀ : M} (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x₀
      ⟨metricRm04At (S.family.metric t) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x₀⟩) = 1) (x : M) :
    ∃ (e : TangentSpace I x) (K : Opens (perpSpace (S.family.metric t) x e))
      (O : Opens ℝ)
      (phi : PartialDiffeomorph ((perpModel (S.family.metric t) x e).prod 𝓘(ℝ, ℝ)) I
        (perpSpace (S.family.metric t) x e × ℝ) M ∞)
      (hPhi : IsLocalDiffeomorph ((perpModel (S.family.metric t) x e).prod 𝓘(ℝ, ℝ)) I ∞
        (fun y : K × O => phi (y.1.1, y.2.1)))
      (h : SmoothRiemannianMetric (perpModel (S.family.metric t) x e) K),
      e ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ ∧
      (S.family.metric t).inner x e e = 1 ∧
      Module.finrank ℝ (perpSpace (S.family.metric t) x e) = 2 ∧
      (0 : perpSpace (S.family.metric t) x e) ∈ K ∧ (0 : ℝ) ∈ O ∧
      IsPreconnected (O : Set ℝ) ∧ phi.source = (K : Set _) ×ˢ (O : Set ℝ) ∧
      phi (0, 0) = x ∧
      (localPullMetric (S.family.metric t)
        (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
          h.prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ k : K, 0 < metricScalarAt h k) ∧
      (∀ (k : K) (v w : TangentSpace (perpModel (S.family.metric t) x e) k),
        LinearIndependent ℝ ![v, w] → 0 < Geometry.Riemannian.sectionalCurvature h k v w) ∧
      ∀ k ∈ K, ∀ r ∈ O, ∀ v : TangentSpace I (phi (k, r)),
        (v ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) (phi (k, r))
          ⟨metricRm04At (S.family.metric t) (phi (k, r)),
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) (phi (k, r))⟩ ↔
          ∃ q : ℝ, mfderiv ((perpModel (S.family.metric t) x e).prod 𝓘(ℝ, ℝ)) I
            (fun z : perpSpace (S.family.metric t) x e × ℝ => phi z) (k, r) (0, q) = v) ∧
        ((∀ w ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) (phi (k, r))
          ⟨metricRm04At (S.family.metric t) (phi (k, r)),
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) (phi (k, r))⟩,
          (S.family.metric t).inner (phi (k, r)) w v = 0) ↔
          ∃ u : TangentSpace (perpModel (S.family.metric t) x e) k,
            mfderiv ((perpModel (S.family.metric t) x e).prod 𝓘(ℝ, ℝ)) I
              (fun z : perpSpace (S.family.metric t) x e × ℝ => phi z) (k, r) (u, 0) = v) := by
  exact DimensionThree.exists_positive_surface_local_product_of_curvatureOperator_rank_one
    hdim (S.family.metric t) (fun y => hR t (Set.right_mem_Icc.mpr hst.le) y)
    (fun y => (curvatureOperatorImageAt_finrank_eq_at_later_time
      S hS hdim hst hreg hR y x₀).trans hrank)
    (curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hst hreg hR) x

end DifferentialGeometry.PDE.RicciFlow
