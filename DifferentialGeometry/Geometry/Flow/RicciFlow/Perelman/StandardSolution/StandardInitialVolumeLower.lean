import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVolumeLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeSetLower
import DifferentialGeometry.Geometry.Exponential.IntrinsicBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem standard_initial_ball_volume_lower :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ S : PartialStandardSolution, ∀ p : E3, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ENNReal.ofReal (intrinsicBallVolumeCoeff 3 * r ^ 3) ≤
          riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.metric 0)
            {y | riemannianEDistOf (S.metric 0) p y < ENNReal.ofReal r} := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  let g := DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
  let : RiemannianBundle (fun x : E3 ↦ TangentSpace (𝓡 3) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : E3 ↦ TangentSpace (𝓡 3) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let metricSpace : EMetricSpace E3 := EMetricSpace.ofRiemannianMetric (𝓡 3) E3
  let : PseudoEMetricSpace E3 := metricSpace.toPseudoEMetricSpace
  let : @CompleteSpace E3 metricSpace.toUniformSpace :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete.complete
  have hnorm : ∀ (p : E3) (v : TangentSpace (𝓡 3) p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    intro p v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  obtain ⟨K, hK, hcurv⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0
  obtain ⟨c, hc, hinj⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius
  have hRm : ∀ p : E3, Real.sqrt (normSq0S g p 4 (metricRm04At g p)) ≤ K :=
    fun p ↦ hcurv p
  have hInj : ∀ p : E3, ENNReal.ofReal c ≤ intrinsicInjRadius g hnorm p := hinj
  refine ⟨min (c / 2) (intrinsicNormalMetricRadius 3 K),
    lt_min (half_pos hc) (intrinsicNormalMetricRadius_pos 3 K hK.le), ?_⟩
  intro S p r hr hrad
  rw [S.initial]
  have hrad' : r ≤ min (c / 2) (intrinsicNormalMetricRadius (Module.finrank ℝ E3) K) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hrad
  have h := intrinsicBall_volume_ge_of_rm04_inj K hK.le c hc g hnorm hRm hInj p hr hrad'
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smallNormalBall,
    riemannianEDistOf] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem standard_uniform_initial_reducedVolume_lower (H : ℝ) (hH : 0 < H) :
    Nonempty StandardSolution ∧ ∃ v : ℝ, 0 < v ∧
      ∀ S : StandardSolution, ∀ T : ℝ, T ∈ S.val.domain → 0 < T → T ≤ H →
        ∀ x : E3, ENNReal.ofReal v ≤
          DifferentialGeometry.PDE.RicciFlow.redVolume S.val.toSolutionOn T x T := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  obtain ⟨K, hK, hinit⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0
  obtain ⟨c, hc, hinj⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius
  refine ⟨standard_solution_nonempty, initialReducedVolumeLowerCoeff 3 H K c,
    initialReducedVolumeLowerCoeff_pos 3 H K c hH hK hc, ?_⟩
  intro S T hTmem hT hTH x
  have hTlife := ((mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos T).mp hTmem).2
  have hslab : Icc (0 : ℝ) T ⊆ S.val.domain :=
    (Icc_subset_lifetimeInterval_iff S.val.lifetime S.val.lifetime_pos T hT.le).mpr hTlife
  have hreg : Ioc (0 : ℝ) T ⊆ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTlife⟩
  obtain ⟨B, _hB, hbound⟩ := S.val.curvature_bound T hT.le hTlife
  have hb : ∃ B' : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ z : E3,
      normSq0S (I := 𝓡 3) (S.val.toSolutionOn.base.metric t) z 4
        (S.val.toSolutionOn.base.rm04 t z) ≤ B' :=
    ⟨B ^ 2, fun t ht z ↦ (Real.sqrt_le_iff.mp (hbound t ht z)).2⟩
  have hi : ∀ z : E3, Real.sqrt (normSq0S (I := 𝓡 3)
      (S.val.toSolutionOn.base.metric 0) z 4 (S.val.toSolutionOn.base.rm04 0 z)) ≤ K := by
    intro z
    change Real.sqrt (normSq0S (S.val.metric 0) z 4 (metricRm04 (S.val.metric 0) z)) ≤ K
    rw [S.val.initial]
    exact hinit z
  have hcomplete := S.val.complete 0 (hslab ⟨le_rfl, hT.le⟩)
  have hInj : ∀ p : E3, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (S.val.toSolutionOn.base.metric 0) hcomplete p := by
    intro p
    simpa only [intrinsicInjectivityRadiusOf_model_eq,
      PartialStandardSolution.toSolutionOn_metric, S.val.initial] using hinj p
  have h := initial_reducedVolume_lower_connected H K c hH hK hc S.val.toSolutionOn
    S.val.isSolutionOn T hT hTH hcomplete hslab hreg hb hi hInj x
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using h

end DifferentialGeometry.PDE.RicciFlow

end
