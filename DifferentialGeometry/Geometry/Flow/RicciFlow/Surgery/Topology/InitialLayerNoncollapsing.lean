import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_initial_closedSlab_ball_volume_lower_bound
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ ρ κ : ℝ, 0 < τ ∧ 0 < ρ ∧ 0 < κ ∧
      ∀ {Q : OrientedThreeStage.{u}} {b : ℝ} (G : Q.ClosedSlab 0 b)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
        (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
          (G.flow.base.metric 0).inner (φ x)
            (mfderiv ThreeModel ThreeModel φ x v)
            (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
        ∀ t ∈ Icc (0 : ℝ) b, t ≤ τ → ∀ x : Q.Carrier,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure ThreeModel Q.Carrier (G.flow.base.metric t)
                (riemannianBallOf (G.flow.base.metric t) x r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_ball_volume_lower_bound g
  refine ⟨τ, ρ, κ, hτ, hρ, hκ, ?_⟩
  intro Q b G φ hmetric t ht htτ x r hr hrρ
  let S := G.flow.pullback φ
  have hS : IsSolutionOn S := G.equation.pullback G.flow φ
  have hinit : S.base.metric 0 = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  have hslab : Icc (0 : ℝ) t ⊆ (RealTimeInterval.closed 0 b G.lt.le).carrier :=
    fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hregular : Ioo (0 : ℝ) t ⊆ (RealTimeInterval.closed 0 b G.lt.le).regular :=
    fun u hu => ⟨hu.1, hu.2.trans_le ht.2⟩
  have hgram := fun (x₀ : P.Carrier) (i j : Fin (Module.finrank ℝ ThreeSpace)) =>
    (chartGramMatrix_joint_contMDiffOn_of_pullback G.flow.base.metric (Icc (0 : ℝ) b)
      G.smoothUpTo.jointContMDiffOn S.base.metric φ φ.contMDiff
      (fun u _ y v w => Diffeomorph.pullbackMetricCross_inner _ φ y v w) x₀ i j).mono
      (prod_mono hslab subset_rfl)
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hv := hbound S hS hinit hslab hregular hgram t ⟨ht.1, le_rfl⟩ htτ y r hr hrρ
  have hvolume := Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross
    (G.flow.base.metric t) φ y r
  apply (show ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
    riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric t)
      (riemannianBallOf (S.base.metric t) y r) from by
      simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hv).trans_eq
  exact hvolume

namespace ObservedHistory

private theorem ball_volume_lower_bound_of_closedSlab_stage_zero
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) {τ ρ κ : ℝ}
    (hbound : ∀ {Q : OrientedThreeStage.{u}} {b : ℝ} (G : Q.ClosedSlab 0 b)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
        (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
          (G.flow.base.metric 0).inner (φ x)
            (mfderiv ThreeModel ThreeModel φ x v)
            (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
        ∀ t ∈ Icc (0 : ℝ) b, t ≤ τ → ∀ x : Q.Carrier,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure ThreeModel Q.Carrier (G.flow.base.metric t)
                (riemannianBallOf (G.flow.base.metric t) x r))
    (k : Fin (H.eventCount + 1)) (hk : k = 0) {a b : ℝ} (ha : a = H.time k)
    (G : (H.stage k).ClosedSlab a b) (hG : G.flow.base.metric a = H.initialMetric k)
    (t : ℝ) (ht : t ∈ Icc a b) (htτ : t ≤ τ) (x : (H.stage k).Carrier)
    (r : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (G.flow.base.metric t)
        (riemannianBallOf (G.flow.base.metric t) x r) := by
  subst hk
  rw [H.time_zero] at ha
  subst ha
  refine hbound G A.map (fun y v w => ?_) t ht htτ x r hr hrρ
  rw [hG]
  exact A.metric_eq y v w

end ObservedHistory

theorem exists_initial_layer_noncollapsed (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ κ η ρ₁ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < ρ₁ ∧
      ∀ (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ), ρbound ≤ ρ₁ →
      ∀ H : RetainedCoreHistory.{u}, H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound →
      ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
        (t : ℝ) ≤ η → r ≤ 1 → H.toHistory.isParabolicallyRmControlledBall t p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    exists_uniform_initial_closedSlab_ball_volume_lower_bound P₀ g₀
  obtain ⟨a₁, ha₁, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  set m := min ρ 1 with hm
  have hm0 : 0 < m := lt_min hρ one_pos
  refine ⟨κ * m ^ 3, min τ (a₁ / 2), 1, by positivity, lt_min hτ (half_pos ha₁), one_pos, ?_⟩
  intro B p₀ δbound ρbound _ H hH t p r htη hr1 hball
  have hr : 0 < r := hball.1
  have hrt : r ^ 2 ≤ (t : ℝ) := hball.radius_sq_le_time H.toHistory
  have ht0 : 0 < (t : ℝ) := (pow_pos hr 2).trans_le hrt
  obtain ⟨pc, -, -, -, -, -, records, -, -, -⟩ := hH.2.2.2.1
  have A := hH.1.some
  have hfirst : ∀ k : Fin (H.eventCount + 1), H.time k ≤ (t : ℝ) → k = 0 := by
    intro k hk
    by_contra hk0
    have hpos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
    let j : Fin H.eventCount := ⟨0, by omega⟩
    have hjk : j.succ ≤ k := by
      change 1 ≤ k.val
      omega
    have hle := hsing H.toHistory A (fun i => (records i).singular) j.castSucc
      (H.time j.succ) (H.toHistory.event j).incoming (H.toHistory.event_initial j)
      (records j).singular
    have hmono : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hjk
    have : a₁ ≤ (t : ℝ) := hle.trans (hmono.trans hk)
    have : (t : ℝ) ≤ a₁ / 2 := htη.trans (min_le_right _ _)
    linarith
  have hk : H.toHistory.activeStage t = 0 := hfirst _ (H.toHistory.activeStage_time_le t)
  have hlt : H.toHistory.time (H.toHistory.activeStage t) < (t : ℝ) := by
    rw [hk, H.toHistory.time_zero]
    exact ht0
  set s := min r ρ with hs
  have hs0 : 0 < s := lt_min hr hρ
  have hv := ObservedHistory.ball_volume_lower_bound_of_closedSlab_stage_zero A hbound
    (H.toHistory.activeStage t) hk rfl (H.toHistory.closedPrefixAt t hlt)
    (H.toHistory.closedPrefixAt_initial t hlt) t ⟨(H.toHistory.activeStage_time_le t), le_rfl⟩
    (htη.trans (min_le_left _ _)) p s hs0 (min_le_right _ _)
  rw [H.toHistory.closedPrefixAt_metric] at hv
  have hmr : m * r ≤ s := le_min
    (mul_le_of_le_one_left hr.le (min_le_right _ _))
    ((mul_le_of_le_one_right hm0.le hr1).trans (min_le_left _ _))
  calc ENNReal.ofReal (κ * m ^ 3) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal κ * ENNReal.ofReal (m * r) ^ 3 := by
        rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_mul hm0.le, ENNReal.ofReal_pow hm0.le,
          mul_pow, mul_assoc]
    _ ≤ ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 := by
        gcongr
    _ ≤ _ := hv
    _ ≤ _ := MeasureTheory.measure_mono (riemannianBallOf_mono _ _ (min_le_left _ _))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
