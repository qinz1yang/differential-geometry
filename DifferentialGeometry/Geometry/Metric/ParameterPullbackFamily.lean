import DifferentialGeometry.Geometry.Metric.ParameterPullbackPairing
import DifferentialGeometry.Geometry.Metric.Family.Continuity



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem metricFamilySmoothOn_parameterPullback
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ} (hT : IsOpen T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (D' : RealTimeInterval) (hopen : D'.carrier = D'.regular)
    (hsub : D'.carrier ⊆ T ∩ D.regular) :
    MetricFamilySmoothOn D' (fun t => Diffeomorph.pullbackMetric (G t) (Φ t)) := by
  have hcoeff : ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, E) x),
      ContDiffOn ℝ ∞ (fun t => (Diffeomorph.pullbackMetric (G t) (Φ t)).inner x v w)
        D'.regular := by
    intro x v w
    rw [← contMDiffOn_iff_contDiffOn]
    intro t ht
    exact contMDiffWithinAt_parameterPullbackPairing hG hT hΦ
      contMDiffWithinAt_id contMDiffWithinAt_const
      (hsub (D'.regular_subset ht)).1
      (D.regular_isOpen.mem_nhds (hsub (D'.regular_subset ht)).2)
      contMDiffWithinAt_const contMDiffWithinAt_const
  have hpair : ∀ {u : Set M} (W Z : ∀ x, TangentSpace 𝓘(ℝ, E) x),
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (W x)) u →
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Z x)) u →
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => (Diffeomorph.pullbackMetric (G q.1) (Φ q.1)).inner q.2 (W q.2) (Z q.2))
        (D'.regular ×ˢ u) := by
    intro u W Z hW hZ q hq
    exact contMDiffWithinAt_parameterPullbackPairing hG hT hΦ
      contMDiffWithinAt_fst contMDiffWithinAt_snd
      (hsub (D'.regular_subset hq.1)).1
      (D.regular_isOpen.mem_nhds (hsub (D'.regular_subset hq.1)).2)
      ((hW.comp contMDiffOn_snd (fun _ hp => hp.2)) q hq)
      ((hZ.comp contMDiffOn_snd (fun _ hp => hp.2)) q hq)
  refine ⟨hcoeff, ?_, ?_, ?_⟩
  · intro x v w
    rw [hopen]
    exact (hcoeff x v w).continuousOn
  · apply metricTensorCont_of_chartGram
    intro x i j
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
    have hp := (hpair
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x i)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x j)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn x i)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn x j)).continuousOn
    have hc : Continuous (fun q : {t : ℝ // t ∈ D'.carrier} × M => (q.1.val, q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hm : MapsTo (fun q : {t : ℝ // t ∈ D'.carrier} × M => (q.1.val, q.2))
        {q | q.2 ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet}
        (D'.regular ×ˢ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet) :=
      fun q hq => ⟨hopen ▸ q.1.property, hq⟩
    exact hp.comp (f := fun q : {t : ℝ // t ∈ D'.carrier} × M => (q.1.val, q.2))
      hc.continuousOn hm
  · intro Idx _ frame u hframe i j
    exact hpair (frame i) (frame j) (hframe.contMDiffOn i) (hframe.contMDiffOn j)

end DifferentialGeometry.Geometry
