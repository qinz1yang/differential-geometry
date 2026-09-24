import DifferentialGeometry.Analysis.Calculus.Derivative.Bounds
import DifferentialGeometry.Analysis.ODE.QuadraticBackwardBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let _ : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let _ : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

private theorem exists_old_event_of_mem_Ioo_not_mem_range
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    {t : ℝ} (ht : t ∈ Ioo (H.time first) (H.time last))
    (hne : t ∉ Set.range H.time) :
    ∃ j : Fin H.eventCount, first ≤ j.castSucc ∧ j.succ ≤ last ∧
      t ∈ Ioo (H.time j.castSucc) (H.time j.succ) := by
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1.le, ht.2.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt ht.2
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1.le
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  refine ⟨j, hkfirst, hk, ?_, ?_⟩
  · exact lt_of_le_of_ne (H.activeStage_time_le tH) (fun he => hne ⟨j.castSucc, he⟩)
  · exact H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)

variable {E J M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace J] {I : ModelWithCorners ℝ E J}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace J M]
  [IsManifold I ∞ M] [T2Space M]

theorem abs_derivWithin_scalar_parabolic_backwardSurvivorIncomingFootprint_le
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (Phi : M → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {Q θ q : ℝ} {C : ℝ≥0} (hQ : 0 < Q)
    (hmetric : ∀ v ∈ Icc (-θ) 0, S.base.metric v =
      localPullMetric (scaleMetric Q hQ (gflow (s + v / Q))) Phi hPhi)
    (hS : IsSolutionOn S) (hcarrier : Ioo (-θ) 0 ⊆ D.carrier)
    (hstart : H.time first ≤ s - θ / Q)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hfinal : ∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
      q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {v : ℝ} (hv : v ∈ Ioo (-θ) 0) (x : M) (hhigh : q / Q < S.scalar v x) :
    |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2 := by
  let A : Set ℝ := (fun t => Q * (t - s)) '' Set.range H.time
  have hA : A.Finite := (Set.finite_range H.time).image _
  have hdiff (w : ℝ) (hw : w ∈ Ioo (-θ) 0) :
      DifferentiableAt ℝ (fun a => S.scalar a x) w :=
    (hS.scalarTime hw hcarrier x).differentiableAt (Ioo_mem_nhds hw.1 hw.2)
  have hderiv (w : ℝ) (hw : w ∈ Ioo (-θ) 0) :
      derivWithin (fun a => S.scalar a x) (Iic w) w = deriv (fun a => S.scalar a x) w :=
    (hdiff w hw).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic w)
  rw [hderiv v hv]
  apply DifferentialGeometry.Analysis.abs_deriv_le_quadratic_of_finite_exception
    hA hdiff ?_ v hv hhigh
  intro w hw hwA hwhigh
  have hphysical : s + w / Q ∈ Ioo (H.time first) s := by
    have hlo := div_lt_div_of_pos_right hw.1 hQ
    have hhi := div_neg_of_neg_of_pos hw.2 hQ
    simp only [neg_div] at hlo
    constructor <;> linarith
  have hnot : s + w / Q ∉ Set.range H.time := by
    intro ht
    apply hwA
    refine ⟨s + w / Q, ht, ?_⟩
    dsimp only
    field_simp
    ring
  rw [← hderiv w hw]
  by_cases hlt : s + w / Q < H.time last
  · obtain ⟨j, hf, hl, ht⟩ := exists_old_event_of_mem_Ioo_not_mem_range H first last
      ⟨hphysical.1, hlt⟩ hnot
    let y := H.backwardSurvivorMap first last hle j.castSucc hf
      (j.castSucc_lt_succ.le.trans hl) (Phi x).val.val
    let r := fun t => (H.event j).incoming.flow.scalar t y
    have heq : (fun a => S.scalar a x) =ᶠ[𝓝 w] (fun a => Q⁻¹ * r (s + a / Q)) := by
      have htime : ContinuousAt (fun a : ℝ => s + a / Q) w := by fun_prop
      filter_upwards [Ioo_mem_nhds hw.1 hw.2,
        htime.eventually (Ioo_mem_nhds ht.1 ht.2)] with a ha hta
      change metricScalarAt (S.base.metric a) x = _
      rw [hmetric a ⟨ha.1.le, ha.2.le⟩, metricScalarAt_localPull, metricScalarAt_scaleMetric,
        hslabs j hf hl _ ⟨hta.1.le, hta.2.le⟩,
        CheegerGromovCompactness.metricScalarAt_restrictOpen,
        CheegerGromovCompactness.metricScalarAt_restrictOpen,
        backwardSurvivorSlabMetric, metricScalarAt_localPull,
        (H.event j).terminal.extendedMetric_before hta.2,
        CheegerGromovCompactness.metricScalarAt_restrictOpen]
      rfl
    have hdr : DifferentiableWithinAt ℝ r (Iic (s + w / Q)) (s + w / Q) :=
      ((H.event j).incoming.equation.scalarTime ht Ioo_subset_Ico_self y).differentiableAt
        (Ioo_mem_nhds ht.1 ht.2) |>.differentiableWithinAt
    rw [heq.derivWithin_eq_of_nhds, heq.eq_of_nhds]
    apply DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq hQ hdr
      (hbound j hf hl y _ ht)
    rwa [← heq.eq_of_nhds]
  · have ht : s + w / Q ∈ Ioo (H.time last) s := by
      refine ⟨lt_of_le_of_ne (not_lt.mp hlt) ?_, hphysical.2⟩
      intro he
      exact hnot ⟨last, he⟩
    let y := (H.backwardSurvivorIncomingFootprintMap first last hle G K (Phi x)).val
    let r := fun t => G.flow.scalar t y
    have heq : (fun a => S.scalar a x) =ᶠ[𝓝 w] (fun a => Q⁻¹ * r (s + a / Q)) := by
      have htime : ContinuousAt (fun a : ℝ => s + a / Q) w := by fun_prop
      filter_upwards [Ioo_mem_nhds hw.1 hw.2,
        htime.eventually (Ioo_mem_nhds ht.1 ht.2)] with a ha hta
      change metricScalarAt (S.base.metric a) x = _
      rw [hmetric a ⟨ha.1.le, ha.2.le⟩, metricScalarAt_localPull, metricScalarAt_scaleMetric,
        hlast _ ⟨hta.1.le, hta.2.le⟩,
        CheegerGromovCompactness.metricScalarAt_restrictOpen,
        backwardSurvivorIncomingMetric, metricScalarAt_localPull,
        L.extendedMetric_before hta.2, CheegerGromovCompactness.metricScalarAt_restrictOpen]
      rfl
    have hdr : DifferentiableWithinAt ℝ r (Iic (s + w / Q)) (s + w / Q) :=
      (G.equation.scalarTime ht Ioo_subset_Ico_self y).differentiableAt
        (Ioo_mem_nhds ht.1 ht.2) |>.differentiableWithinAt
    rw [heq.derivWithin_eq_of_nhds, heq.eq_of_nhds]
    apply DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq hQ hdr (hfinal y _ ht)
    rwa [← heq.eq_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
