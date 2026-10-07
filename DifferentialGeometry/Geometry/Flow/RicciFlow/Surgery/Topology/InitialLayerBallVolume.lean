import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerNoncollapsing

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private ObservedHistory.ball_volume_lower_bound_of_closedSlab_stage_zero from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerNoncollapsing

/-- Every ball below the prescribed radius ceiling has a uniform volume bound in
an initial smooth layer. The layer is chosen before the history, and no parabolic
backward-time condition or cutoff-model class is required. -/
theorem exists_initial_layer_all_ball_volume_lower_bound
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ρmax : ℝ} (hρmax : 0 < ρmax) :
    ∃ κ η : ℝ, 0 < κ ∧ 0 < η ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P₀ g₀ H.toHistory),
        (∀ i : Fin H.eventCount, (H.toHistory.event i).incoming.SingularEndpoint) →
      ∀ (t : Icc (0 : ℝ) H.toHistory.horizon),
        0 < (t : ℝ) → (t : ℝ) ≤ η →
      ∀ (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
        0 < r → r ≤ ρmax →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    exists_uniform_initial_closedSlab_ball_volume_lower_bound P₀ g₀
  obtain ⟨b, hb, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  let m : ℝ := min 1 (ρ / ρmax)
  have hm : 0 < m := lt_min one_pos (div_pos hρ hρmax)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmρ : m * ρmax ≤ ρ := (le_div_iff₀ hρmax).mp (min_le_right _ _)
  refine ⟨κ * m ^ 3, min τ (b / 2), mul_pos hκ (pow_pos hm 3),
    lt_min hτ (half_pos hb), ?_⟩
  intro H A hsingH t ht0 htη p r hr hrr
  have hfirst : ∀ k : Fin (H.eventCount + 1), H.time k ≤ (t : ℝ) → k = 0 := by
    intro k hk
    by_contra hk0
    have hpos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
    let j : Fin H.eventCount := ⟨0, by omega⟩
    have hjk : j.succ ≤ k := by
      change 1 ≤ k.val
      omega
    have hle := hsing H.toHistory A hsingH j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j) (hsingH j)
    have hmono : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hjk
    have hbt : b ≤ (t : ℝ) := hle.trans (hmono.trans hk)
    have htb : (t : ℝ) ≤ b / 2 := htη.trans (min_le_right _ _)
    linarith
  have hk : H.toHistory.activeStage t = 0 := hfirst _ (H.toHistory.activeStage_time_le t)
  have hlt : H.toHistory.time (H.toHistory.activeStage t) < (t : ℝ) := by
    rw [hk, H.toHistory.time_zero]
    exact ht0
  have hmrρ : m * r ≤ ρ := (mul_le_mul_of_nonneg_left hrr hm.le).trans hmρ
  have hmr : m * r ≤ r := mul_le_of_le_one_left hr.le hm1
  have hv := ObservedHistory.ball_volume_lower_bound_of_closedSlab_stage_zero A hbound
    (H.toHistory.activeStage t) hk rfl (H.toHistory.closedPrefixAt t hlt)
    (H.toHistory.closedPrefixAt_initial t hlt) t ⟨(H.toHistory.activeStage_time_le t), le_rfl⟩
    (htη.trans (min_le_left _ _)) p (m * r) (mul_pos hm hr) hmrρ
  rw [H.toHistory.closedPrefixAt_metric] at hv
  calc ENNReal.ofReal (κ * m ^ 3) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal κ * ENNReal.ofReal (m * r) ^ 3 := by
        rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_mul hm.le,
          ENNReal.ofReal_pow hm.le, mul_pow, mul_assoc]
    _ ≤ _ := hv
    _ ≤ _ := MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hmr)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
