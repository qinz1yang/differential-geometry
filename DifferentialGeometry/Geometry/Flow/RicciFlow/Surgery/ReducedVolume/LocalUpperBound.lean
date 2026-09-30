import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.TailEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.EventBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.CoreEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryScalarFloor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryHorizonExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.MetricGaussianTail

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature (metricScalarAt)
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private local instance : MeasurableSpace ThreeSpace := borel ThreeSpace

private local instance : BorelSpace ThreeSpace := ⟨rfl⟩

theorem historyReducedVolumeLocalUpperBound_holds :
    HistoryReducedVolumeLocalUpperBound.{u} := by
  refine ⟨(4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 36, by positivity, fun η hη => ?_⟩
  obtain ⟨R, -, htail⟩ := exists_uniform_tail_gaussian_metric.{u} (ENNReal.ofReal η)
    (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨σ, hσ, hσ1, hcore⟩ :=
    ObservedHistory.exists_lintegral_image_historyMinDomain_core_le.{u} R
  refine ⟨σ, hσ, hσ1, fun H t p r hball => ?_⟩
  obtain ⟨T', hT', G, hG, hagree⟩ := H.exists_extendHorizon_gt
  have hball' := H.isParabolicallyRmControlledBall_extendHorizon hT'.le G hG hagree t p r hball
  have hr : 0 < r := hball.1
  have hv : 0 < σ * r := mul_pos hσ hr
  have htmem : (t : ℝ) ∈ H.toHistory.stageDomain (H.toHistory.activeStage t) :=
    H.toHistory.activeStage_mem t
  have hmet := H.stageMetric_extendHorizon hT'.le G hG hagree _ htmem
  have hVeq : H.reducedVolume (H.toHistory.activeStage t) p t (σ * r) =
      (H.extendHorizon T' hT'.le G hG).reducedVolume (H.toHistory.activeStage t) p t (σ * r) :=
    (H.reducedVolume_extendHorizon hT'.le G hG hagree _ p t.2.2).symm
  rw [hVeq, ← hmet]
  obtain ⟨b, hb⟩ :=
    RetainedCoreHistory.exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico
      (H.extendHorizon T' hT'.le G hG)
  obtain ⟨b', -, hfl⟩ := (H.extendHorizon T' hT'.le G hG).exists_stageMetric_scalar_lower_bound
  set H' := H.extendHorizon T' hT'.le G hG with hH'
  set k := H.toHistory.activeStage t with hk
  set B₀ := max b b' with hB₀
  have hfloor : ∀ j, ∀ τ ∈ H'.toHistory.stageDomain j, ∀ x : (H'.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H'.toHistory.stageMetric j τ) x := fun j τ hτ x =>
    (neg_le_neg (le_max_right _ _)).trans (hfl j τ hτ x)
  have hTIco : (t : ℝ) ∈ Ico (H'.toHistory.time k) (H'.toHistory.stageEndTime k) :=
    ⟨H.toHistory.activeStage_time_le t, H.lt_stageEndTime_extendHorizon hT' G hG t⟩
  have htk' : (t : ℝ) ∈ H'.toHistory.stageDomain k :=
    H'.toHistory.activeStage_mem ⟨t.1, t.2.1, t.2.2.trans hT'.le⟩
  have hvt : (σ * r) ^ 2 ≤ t :=
    (pow_le_pow_left₀ hv.le (mul_le_of_le_one_left hr.le hσ1) 2).trans
      hball.radius_sq_le_time
  have hlow : (t : ℝ) - (σ * r) ^ 2 ∈ H'.toHistory.stageDomain
      (H'.toHistory.activeStage (projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2))) := by
    have h := H'.toHistory.activeStage_mem
      (projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2))
    have hv' : ((projIcc 0 H'.horizon H'.horizon_nonneg (t - (σ * r) ^ 2) : ℝ)) =
        t - (σ * r) ^ 2 := by
      rw [projIcc_of_mem _ ⟨by linarith, by
        have h1 : H'.horizon = T' := rfl
        have h2 := t.2.2
        nlinarith [sq_nonneg (σ * r), hT'.le]⟩]
    rwa [hv'] at h
  have ht0 : (t : ℝ) - (0 : ℝ) ^ 2 ∈ H'.toHistory.stageDomain k := by simpa using htk'
  have hle := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv.le hlow ht0
  rw [hb B₀ (le_max_left _ _) k p t (σ * r) hle hv hTIco]
  set K := H'.toHistory.historyMinDomain hle t B₀ (σ * r) p with hK
  set g := H'.toHistory.stageMetric k t with hg
  have hsplit : H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹' K) ⊆
      H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (K ∩ {Z | Real.sqrt (g.inner p Z Z) ≤ R})) ∪
        H'.toHistory.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (K ∩ {Z | R < Real.sqrt (g.inner p Z Z)})) := by
    rintro _ ⟨Z, hZ, rfl⟩
    rcases le_or_gt (Real.sqrt (g.inner p Z.1 Z.1)) R with h | h
    · exact Or.inl ⟨Z, ⟨hZ, h⟩, rfl⟩
    · exact Or.inr ⟨Z, ⟨hZ, h⟩, rfl⟩
  refine (lintegral_mono_set hsplit).trans ((lintegral_union_le _ _ _).trans (add_le_add ?_ ?_))
  · exact hcore H'.toHistory ⟨t.1, t.2.1, t.2.2.trans hT'.le⟩ p r B₀ hball'
      (H.lt_stageEndTime_extendHorizon hT' G hG t) hfloor hle
  · refine (ObservedHistory.lintegral_image_historyMinDomain_tail_le hfloor hTIco hv R).trans ?_
    exact htail g p

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
