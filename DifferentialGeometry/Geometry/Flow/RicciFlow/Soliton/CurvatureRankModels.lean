import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRank
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCoverRankThree
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.MunteanuWangCompactness
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Operator.ModelChange

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem normalized_model_change
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    normalizedGradientRicciSoliton (g.transContinuousLinearEquiv L)
      (f.comp (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L).symm.toContMDiffMap) := by
  let Phi := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M L).symm
  refine ⟨RiemannianMetricComplete.pullbackCross g Phi h.1,
    gradientRicciSoliton_pullbackCross h.2.1 Phi, ?_⟩
  intro x
  change metricScalarAt (g.transContinuousLinearEquiv L) x +
    normGradSqFun (g.transContinuousLinearEquiv L) f x = f x
  rw [metricScalarAt_transContinuousLinearEquiv,
    normGradSqFun_transContinuousLinearEquiv g L f x (f.contMDiff.mdifferentiableAt (by simp))]
  exact h.2.2 x

theorem exists_roundThreeSphere_solitonModelCovering_of_rank_three
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 3) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := (toEuclidean (E := E)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv L
  let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
  let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
  let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
  have hu : normalizedGradientRicciSoliton k u := normalized_model_change h L
  have hrankk : ∀ x : M, metricCurvatureOperatorRankAt k x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) = 3 := by
    intro x
    have hrankg := (gradientRicciSoliton_metricCurvatureOperatorRankAt_eq g f (show (0 : ℝ) ≤ 1 by norm_num)
      h.1 h.2.1 hdim x x₀).trans hrank
    change metricCurvatureOperatorRankAt (Diffeomorph.pullbackMetricCross g Phi.symm) x _ = 3
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      metricCurvatureOperatorRankAt_localPull g Phi.symm Phi.symm.isLocalDiffeomorph x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) hdim]
    exact hrankg
  have hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt k x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := M) := by
    intro x
    exact gradientRicciSoliton_curvatureOperator_nonnegative k u
      (show (0 : ℝ) ≤ 1 by norm_num) hu.1 hu.2.1 (by simp) x
  have hsec : ∀ (x : M) (v w : TangentSpace J x),
      LinearIndependent ℝ (vec2 (I := J) v w) →
        0 < metricRm04StandardAt k x v w w v := by
    intro x v w hlin
    exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      k x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) (hrankk x) (hcone x) v w hlin
  let _ : CompactSpace M := positive_sectional_gradientRicciSoliton_compactness
    (by simp : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) hu.1 hu.2.1 zero_lt_one hsec
  obtain ⟨cover, hcover⟩ :=
    exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_sectional_pos
      hu (by simp) hsec
  refine ⟨cover, hcover.1, h, ?_, hcover.2.2.2.1, hcover.2.2.2.2.1, ?_, ?_⟩
  · change IsLocalDiffeomorph (𝓡 3) I ∞ ((Phi.symm : M → M) ∘ cover)
    exact isLocalDiffeomorph_comp Phi.symm.isLocalDiffeomorph hcover.2.2.1
  · intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [show k = g.transContinuousLinearEquiv L from rfl,
      SmoothRiemannianMetric.transContinuousLinearEquiv_inner] at hm
    have hchain := mfderiv_comp x
      (Phi.symm.contMDiff.mdifferentiableAt (by simp))
      ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) I cover x =
      (mfderiv J I id (cover x)).comp (mfderiv (𝓡 3) J cover x) at hchain
    rw [hchain]
    exact hm
  · intro x
    exact solitonModelCovering_potential hcover x

private theorem gaussian_cover_of_scalar_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hscalar : metricScalarAt g x₀ = 0) :
    ∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover := by
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := (toEuclidean (E := E)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv L
  let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
  let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
  let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
  have hu : normalizedGradientRicciSoliton k u := normalized_model_change h L
  have hz : metricScalarAt k x₀ = 0 :=
    (metricScalarAt_transContinuousLinearEquiv g L x₀).trans hscalar
  obtain ⟨cover, hcover⟩ :=
    exists_solitonModelCovering_of_normalizedGradientRicciSoliton_of_scalar_eq_zero hu hz
  refine ⟨cover, hcover.1, h, ?_, hcover.2.2.2.1, hcover.2.2.2.2.1, ?_, ?_⟩
  · change IsLocalDiffeomorph (𝓡 3) I ∞ ((Phi.symm : M → M) ∘ cover)
    exact isLocalDiffeomorph_comp Phi.symm.isLocalDiffeomorph hcover.2.2.1
  · intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [show k = g.transContinuousLinearEquiv L from rfl,
      SmoothRiemannianMetric.transContinuousLinearEquiv_inner] at hm
    have hchain := mfderiv_comp x
      (Phi.symm.contMDiff.mdifferentiableAt (by simp))
      ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) I cover x =
      (mfderiv J I id (cover x)).comp (mfderiv (𝓡 3) J cover x) at hchain
    rw [hchain]
    exact hm
  · intro x
    exact solitonModelCovering_potential hcover x

theorem exists_gaussian_solitonModelCovering_of_rank_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 0) :
    ∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover := by
  apply gaussian_cover_of_scalar_zero h hdim
  exact metricScalarAt_eq_zero_of_metricRm04At_eq_zero g x₀
    ((metricCurvatureOperatorRankAt_eq_zero_iff g x₀ hdim).mp hrank)

end DifferentialGeometry.Geometry
