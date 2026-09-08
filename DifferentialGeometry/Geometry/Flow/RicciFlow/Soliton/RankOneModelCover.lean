import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneSplitting
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ProductCover
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Operator.ModelChange
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree
open Riemannian.Topology.UniversalCover

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

private theorem cylinder_cover_of_rank_one_morseModel
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀
      (by change Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
          simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential g f cover := by
  have hsplit := gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one
    g f (show (0 : Real) ≤ 1 by norm_num) h.1 h.2.1 hrank
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨_, P, -, -, -, hpositive⟩ := hsplit
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) ∞ P.N :=
    P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : SimplyConnectedSpace P.N := P.simplyConnectedN
  let k : SmoothRiemannianMetric
      (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) P.N := P.metricN
  let Phi := P.F
  have hdim : Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hpull : Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) Phi =
      k.prod (euclideanMetric (E := Real)) := by
    simpa only [k, Phi, flatModelMetric] using P.pullbackMetric_eq_prod g
  have hpos : ∃ x : P.N, 0 < metricScalarAt
      (I := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) k x := by
    exact ⟨Classical.choice (inferInstance : Nonempty P.N), by simpa [k] using hpositive _⟩
  apply exists_roundThreeCylinder_solitonModelCovering_of_product_diffeomorph
    (E₂ := DifferentialGeometry.Topology.Morse.MorseModel 2)
    (J := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (N := P.N) (g := g) (f := f) (k := k) (Phi := Phi)
    (h := h) (hk := P.completeN) (hpull := hpull) hdim hpos

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem normalized_model_change
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (L : E ≃L[ℝ] DifferentialGeometry.Topology.Morse.MorseModel 3) :
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

theorem exists_roundThreeCylinder_solitonModelCovering_of_rank_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 1) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] DifferentialGeometry.Topology.Morse.MorseModel 3 :=
    (toEuclidean (E := E)).trans
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv.trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)))
  let J := I.transContinuousLinearEquiv L
  let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
  let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
  let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
  have hu : normalizedGradientRicciSoliton k u := normalized_model_change h L
  have hrankk : metricCurvatureOperatorRankAt k x₀ (by
      change Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
      simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1 := by
    change metricCurvatureOperatorRankAt (Diffeomorph.pullbackMetricCross g Phi.symm) x₀ _ = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      metricCurvatureOperatorRankAt_localPull g Phi.symm Phi.symm.isLocalDiffeomorph x₀
        (by change Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
            simp [DifferentialGeometry.Topology.Morse.MorseModel]) hdim]
    exact hrank
  obtain ⟨cover, hcover⟩ := cylinder_cover_of_rank_one_morseModel hu hrankk
  refine ⟨cover, hcover.1, h, ?_, hcover.2.2.2.1, hcover.2.2.2.2.1, ?_, ?_⟩
  · change IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) I ∞ ((Phi.symm : M → M) ∘ cover)
    exact isLocalDiffeomorph_comp Phi.symm.isLocalDiffeomorph hcover.2.2.1
  · intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [show k = g.transContinuousLinearEquiv L from rfl,
      SmoothRiemannianMetric.transContinuousLinearEquiv_inner] at hm
    have hchain := mfderiv_comp x
      (Phi.symm.contMDiff.mdifferentiableAt (by simp))
      ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I cover x =
      (mfderiv J I id (cover x)).comp (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) J cover x) at hchain
    rw [hchain]
    exact hm
  · intro x
    exact solitonModelCovering_potential hcover x

end DifferentialGeometry.Geometry
