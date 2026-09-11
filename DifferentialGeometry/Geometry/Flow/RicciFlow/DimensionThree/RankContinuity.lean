import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Analysis.FiniteDimensional.Rank

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem tensor04CurvatureOperatorMatrixAt_rank_le_image_finrank
    (g : SmoothRiemannianMetric I M) (x : M)
    (b : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    (tensor04CurvatureOperatorMatrixAt b (metricRm04At g x)).rank ≤
      Module.finrank ℝ (curvatureOperatorImageAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) := by
  have hdim : Module.finrank ℝ (TangentSpace I x) = 3 := Module.finrank_eq_card_basis b
  obtain ⟨c, hc⟩ := exists_orthonormalBasisAt g x hdim
  rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim,
    metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal g x hdim c hc]
  have hconj := tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal g c b hc
    ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩
  rw [hconj]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

private theorem tensor04CurvatureOperatorMatrixAt_continuousOn_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (x : M) (b : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    ContinuousOn (fun t => tensor04CurvatureOperatorMatrixAt b
      (metricRm04At (S.family.metric t) x)) D.carrier := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hS.rm04Cont.eval_continuous (P := D.carrier) continuous_subtype_val
    (fun r => r.property) continuous_const (fun _ => continuous_const)

theorem curvatureOperatorImageAt_finrank_eventually_ge
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) (x : M) {t : ℝ} (ht : t ∈ D.carrier) :
    ∀ᶠ r in 𝓝[D.carrier] t,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasisAt (S.family.metric t) x hdim
  let A := fun r => tensor04CurvatureOperatorMatrixAt b (metricRm04At (S.family.metric r) x)
  let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  have hc : ContinuousOn (fun r => L (A r)) D.carrier :=
    L.continuous_of_finiteDimensional.comp_continuousOn
      (tensor04CurvatureOperatorMatrixAt_continuousOn_time S hS x b)
  have hlower := (hc t ht).eventually_finrank_range_ge
  have heq (r : ℝ) : (A r).rank = Module.finrank ℝ (L (A r)).range :=
    Matrix.rank_eq_finrank_range_toLin (A r) (PiLp.basisFun 2 ℝ (Fin 3))
      (PiLp.basisFun 2 ℝ (Fin 3))
  filter_upwards [hlower] with r hr
  have hraw : (A t).rank ≤ (A r).rank := by simpa only [heq] using hr
  have htEq : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) =
        (A t).rank := by
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ x hdim,
      metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal _ x hdim b hb]
    rfl
  rw [htEq]
  exact hraw.trans (tensor04CurvatureOperatorMatrixAt_rank_le_image_finrank _ x b)

theorem isClosed_curvatureOperatorImageAt_finrank_le_on_closed_set
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) (x : M) (k : ℕ)
    {K : Set ℝ} (hK : IsClosed K) (hcar : K ⊆ D.carrier) :
    IsClosed ({t : ℝ | Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ k} ∩ K) := by
  let A : Set ℝ := {t : ℝ | Module.finrank ℝ
    (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ k} ∩ K
  apply isClosed_of_closure_subset
  intro t ht
  have htK : t ∈ K := hK.closure_subset (closure_mono inter_subset_right ht)
  have hlow := (curvatureOperatorImageAt_finrank_eventually_ge S hS hdim x (hcar htK)).filter_mono
    (nhdsWithin_mono t (show A ⊆ D.carrier from fun _ hr => hcar hr.2))
  have hne : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ht
  have hmem : ∀ᶠ r in 𝓝[A] t, r ∈ A := self_mem_nhdsWithin
  obtain ⟨r, hrank, hrA⟩ := @Filter.Eventually.exists ℝ _ (𝓝[A] t) hne (hlow.and hmem)
  exact ⟨hrank.trans hrA.1, htK⟩

theorem isClosed_curvatureOperatorImageAt_finrank_le_on_Icc
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) (x : M) (k : ℕ)
    {a b : ℝ} (hcar : Icc a b ⊆ D.carrier) :
    IsClosed ({t : ℝ | Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ k} ∩ Icc a b) := by
  exact isClosed_curvatureOperatorImageAt_finrank_le_on_closed_set S hS hdim x k
    isClosed_Icc hcar

end DifferentialGeometry.PDE.RicciFlow
