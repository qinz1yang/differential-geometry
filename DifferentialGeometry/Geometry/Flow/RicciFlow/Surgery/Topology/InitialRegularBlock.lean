import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialSpatialMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialEndpointPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Seam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryHorizonExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedVolumeTruncation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem incomingSlab_cast_metric {P : OrientedThreeStage.{u}} {a b finish : ℝ}
    (h : a = b) (G : P.IncomingSlab a finish) :
    (h ▸ G : P.IncomingSlab b finish).flow.base.metric = G.flow.base.metric := by
  cases h
  rfl

private theorem stageEndTime_zero_ge_min (H : ObservedHistory.{u}) {a : ℝ}
    (ha : ∀ i : Fin H.eventCount, a ≤ H.time i.succ) :
    min a H.horizon ≤ H.stageEndTime 0 := by
  cases h : (0 : Fin (H.eventCount + 1)) using Fin.lastCases with
  | last => rw [H.stageEndTime_last]; exact min_le_right _ _
  | cast i => rw [H.stageEndTime_castSucc]; exact (min_le_left _ _).trans (ha i)

private theorem cost_budget_le {L t θ θ₀ K Bf B : ℝ} (hK : 0 ≤ K) (hBf : 0 ≤ Bf)
    (ht : 0 < t) (htB : t ≤ B) (hθθ₀ : θ ≤ θ₀) (hL : L ≤ 3 * Real.sqrt t) :
    L + 2 * Real.exp (18 * K * θ) ^ 2 *
        (L + (2 * Bf / 3) * (t * Real.sqrt t) + 2 * Bf * (t * Real.sqrt t)) +
      2 * Bf * (t * Real.sqrt t) + 6 * K * (t * Real.sqrt t) +
      Real.exp (18 * K * θ) * Real.sqrt t ≤
    (3 + 2 * Real.exp (18 * K * θ₀) ^ 2 * (3 + (2 * Bf / 3) * B + 2 * Bf * B) +
      2 * Bf * B + 6 * K * B + Real.exp (18 * K * θ₀)) * Real.sqrt t := by
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hts : t * Real.sqrt t ≤ B * Real.sqrt t := mul_le_mul_of_nonneg_right htB hs
  have hl : Real.exp (18 * K * θ) ≤ Real.exp (18 * K * θ₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hθθ₀ (mul_nonneg (by norm_num) hK))
  have hl0 : 0 ≤ Real.exp (18 * K * θ) := (Real.exp_pos _).le
  have hl2 : Real.exp (18 * K * θ) ^ 2 ≤ Real.exp (18 * K * θ₀) ^ 2 :=
    pow_le_pow_left₀ hl0 hl 2
  set Y := 3 * Real.sqrt t + (2 * Bf / 3) * (B * Real.sqrt t) + 2 * Bf * (B * Real.sqrt t)
    with hY
  have hB0 : 0 ≤ B := ht.le.trans htB
  have hBs : 0 ≤ B * Real.sqrt t := mul_nonneg hB0 hs
  have hY0 : 0 ≤ Y := by
    rw [hY]
    have h2Bf : 0 ≤ 2 * Bf := mul_nonneg (by norm_num) hBf
    have h2Bf3 : 0 ≤ 2 * Bf / 3 := div_nonneg h2Bf (by norm_num)
    nlinarith [mul_nonneg h2Bf3 hBs, mul_nonneg h2Bf hBs]
  have hX : L + (2 * Bf / 3) * (t * Real.sqrt t) + 2 * Bf * (t * Real.sqrt t) ≤ Y := by
    have h1 := mul_le_mul_of_nonneg_left hts (div_nonneg (mul_nonneg (by norm_num) hBf) (by norm_num) : 0 ≤ 2 * Bf / 3)
    have h2 := mul_le_mul_of_nonneg_left hts (mul_nonneg (by norm_num) hBf : 0 ≤ 2 * Bf)
    linarith
  have hmid : 2 * Real.exp (18 * K * θ) ^ 2 *
      (L + (2 * Bf / 3) * (t * Real.sqrt t) + 2 * Bf * (t * Real.sqrt t)) ≤
      2 * Real.exp (18 * K * θ₀) ^ 2 * Y :=
    (mul_le_mul_of_nonneg_left hX (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hY0)
  have h3 := mul_le_mul_of_nonneg_left hts (mul_nonneg (by norm_num) hBf : 0 ≤ 2 * Bf)
  have h4 := mul_le_mul_of_nonneg_left hts (mul_nonneg (by norm_num) hK : 0 ≤ 6 * K)
  have h5 := mul_le_mul_of_nonneg_right hl hs
  have heq : (3 + 2 * Real.exp (18 * K * θ₀) ^ 2 * (3 + (2 * Bf / 3) * B + 2 * Bf * B) +
      2 * Bf * B + 6 * K * B + Real.exp (18 * K * θ₀)) * Real.sqrt t =
      3 * Real.sqrt t + 2 * Real.exp (18 * K * θ₀) ^ 2 * Y + 2 * Bf * (B * Real.sqrt t) +
        6 * K * (B * Real.sqrt t) + Real.exp (18 * K * θ₀) * Real.sqrt t := by
    rw [hY]
    ring
  rw [heq]
  linarith

private theorem sq_le_tail_gap_mul_sqrt {t θ c : ℝ} (ht : 0 < t) (hθt : θ ≤ t)
    (hct : c ^ 2 * t ≤ θ / 2) :
    (c * Real.sqrt t) ^ 2 ≤ (Real.sqrt t - Real.sqrt (t - θ)) * Real.sqrt t := by
  have hs := Real.sq_sqrt ht.le
  have hs' := Real.sq_sqrt (sub_nonneg.mpr hθt)
  have hamgm : Real.sqrt (t - θ) * Real.sqrt t ≤ t - θ / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (t - θ) - Real.sqrt t)]
  have hlhs : (c * Real.sqrt t) ^ 2 = c ^ 2 * t := by rw [mul_pow, hs]
  rw [hlhs]
  nlinarith

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private theorem time_succ_ge_of_initialIdentification {P₀ : OrientedThreeStage.{u}}
    {g₀ : P₀.Metric} {aS : ℝ}
    (hsing : ∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (s : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      G.SingularEndpoint → aS ≤ s)
    (H : ObservedHistory.{u}) (A : InitialIdentification P₀ g₀ H)
    (hsingH : ∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint)
    (i : Fin H.eventCount) : aS ≤ H.time i.succ := by
  let j : Fin H.eventCount := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
  have hfirst := hsing H A hsingH j.castSucc (H.time j.succ) (H.event j).incoming
    (H.event_initial j) (hsingH j)
  exact hfirst.trans (H.time_strictMono.monotone
    (show j.succ ≤ i.succ from Nat.succ_le_succ (Nat.zero_le _)))

theorem exists_stage_zero_window_of_initialIdentification (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) {aS η K : ℝ}
    (hsing : ∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (s : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      G.SingularEndpoint → aS ≤ s)
    (hcurv : ∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      ∀ (e : ℝ) (G : (H.stage 0).IncomingSlab 0 e),
        G.flow.base.metric 0 = H.initialMetric 0 →
        ∀ τ, 0 ≤ τ → τ < e → τ ≤ η → ∀ x : (H.stage 0).Carrier,
          normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2)
    (H : ObservedHistory.{u}) (A : InitialIdentification P₀ g₀ H)
    (hsingH : ∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint)
    {t θ : ℝ} (ht : t ≤ H.horizon) (hθ : 0 < θ) (hθt : θ < t) (hθaS : θ < aS) (hθη : θ ≤ η) :
    ∃ (e : ℝ) (G : (H.stage 0).IncomingSlab 0 e), θ < e ∧ θ ∈ H.stageDomain 0 ∧
      G.flow.base.metric 0 = H.initialMetric 0 ∧
      (∀ s ∈ Ioo 0 e, H.stageMetric 0 s = G.flow.base.metric s) ∧
      ∀ τ ∈ Icc 0 θ, ∀ x : (H.stage 0).Carrier,
        normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2 := by
  have hgap : min aS H.horizon ≤ H.stageEndTime 0 :=
    stageEndTime_zero_ge_min H (time_succ_ge_of_initialIdentification hsing H A hsingH)
  have hθe : θ < H.stageEndTime 0 := lt_of_lt_of_le (lt_min hθaS (hθt.trans_le ht)) hgap
  have htime0 : H.time 0 = 0 := H.time_zero
  have he0 : H.time 0 < H.stageEndTime 0 := by rw [htime0]; exact hθ.trans hθe
  obtain ⟨G, hG0, hGstage⟩ := ObservedHistory.exists_incomingSlab_stageMetric (H := H) 0 he0
  let G' : (H.stage 0).IncomingSlab 0 (H.stageEndTime 0) := htime0 ▸ G
  have hG'metric : G'.flow.base.metric = G.flow.base.metric := incomingSlab_cast_metric htime0 G
  have hG'0 : G'.flow.base.metric 0 = H.initialMetric 0 := by
    rw [hG'metric, ← htime0]
    exact hG0
  refine ⟨H.stageEndTime 0, G', hθe,
    H.mem_stageDomain_of_mem_Ioo ⟨by rw [htime0]; exact hθ, hθe⟩, hG'0, ?_, ?_⟩
  · intro s hs
    rw [hG'metric]
    exact hGstage s (by rw [htime0]; exact hs)
  · intro τ hτ x
    exact hcurv H A _ G' hG'0 τ hτ.1 (hτ.2.trans_lt hθe) (hτ.2.trans hθη) x

private theorem window_radius_sq_le {t θ₀ B c : ℝ} (ht : 0 < t) (htB : t ≤ B) (hθ₀ : 0 < θ₀)
    (hc : 0 ≤ c) (hchalf : c ≤ 1 / 2) (hcθ : c ≤ Real.sqrt θ₀ / (2 * Real.sqrt B)) :
    c ^ 2 * t ≤ (min t θ₀ / 2) / 2 := by
  have hB : 0 < B := ht.trans_le htB
  have h1 : c ^ 2 * t ≤ t / 4 := by
    have := pow_le_pow_left₀ hc hchalf 2
    have hq : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [hq] at this
    have := mul_le_mul_of_nonneg_right this ht.le
    linarith
  have h2 : c ^ 2 * t ≤ θ₀ / 4 := by
    have hsq := pow_le_pow_left₀ hc hcθ 2
    have heq : (Real.sqrt θ₀ / (2 * Real.sqrt B)) ^ 2 = θ₀ / (4 * B) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hθ₀.le, Real.sq_sqrt hB.le]
      ring
    rw [heq] at hsq
    have hmul := mul_le_mul_of_nonneg_right hsq ht.le
    have hfrac : θ₀ / (4 * B) * t ≤ θ₀ / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_left htB hθ₀.le
      linarith
    linarith
  have hmin := le_min h1 h2
  have heq : min (t / 4) (θ₀ / 4) = min t θ₀ / 4 :=
    min_div_div_right (by norm_num : (0 : ℝ) ≤ 4) t θ₀
  rw [heq] at hmin
  linarith

private theorem window_radius_le {t B c ρv : ℝ} (htB : t ≤ B) (hB : 0 < B)
    (hρv : 0 < ρv) (hc : c ≤ ρv / Real.sqrt B) : c * Real.sqrt t ≤ ρv := by
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have htE : Real.sqrt t ≤ Real.sqrt B := Real.sqrt_le_sqrt htB
  calc c * Real.sqrt t ≤ ρv / Real.sqrt B * Real.sqrt B :=
        mul_le_mul hc htE (Real.sqrt_nonneg _) (div_pos hρv hsB).le
    _ = ρv := div_mul_cancel₀ ρv hsB.ne'

private theorem ball_volume_eq {κ c t : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    ENNReal.ofReal (κ * c ^ 3 * t ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal κ * ENNReal.ofReal (c * Real.sqrt t) ^ 3 := by
  rw [← ENNReal.ofReal_pow (mul_nonneg hc (Real.sqrt_nonneg _)), ← ENNReal.ofReal_mul hκ]
  congr 1
  rw [mul_pow, ← mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

theorem exists_uniform_initial_regular_block
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ C κ₀ : ℝ, 0 < a₀ ∧ 0 < κ₀ ∧
    (∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (r₀ qcan ρ : ℝ) (Ctime : ℝ≥0), 0 < r₀ → 0 < qcan → 0 < ρ →
    ∃ (δ₀ ε₀ R₀ : ℝ) (m₀ : ℕ), 0 < δ₀ ∧ 0 < ε₀ ∧ 0 < R₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ ε₀ → R₀ ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder →
      p₀.recenterConstant * δbound ≤ 1 / 2 → δbound ≤ δ₀ → ρbound ≤ ρ →
    ∀ (H : RetainedCoreHistory P₀), Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      H.horizon < B → H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    ∀ (t : Icc (0 : ℝ) H.toHistory.horizon), 0 < (t : ℝ) →
      HistoryScalarDerivativeBoundBefore H Ctime qcan t →
    ∀ (p : (H.toHistory.stageAt t).Carrier), H.toHistory.isParabolicallyRmControlledBall t p r₀ →
    ∃ U : Set (H.stage 0).Carrier, IsOpen U ∧
      ENNReal.ofReal (κ₀ * (t : ℝ) ^ (3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) U ∧
      ∀ q ∈ U,
        q ∈ H.toHistory.regularMinimizerEndpoints 0 (H.toHistory.activeStage t)
          (Fin.zero_le _) t (3 / a₀) (Real.sqrt t) p ∧
        H.toHistory.regularizedCost 0 (H.toHistory.activeStage t) (Fin.zero_le _) t (3 / a₀) 0
          (Real.sqrt t) p q ≤ ((2 * C * Real.sqrt t : ℝ) : WithTop ℝ) := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨aS, haS, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  obtain ⟨η, K, hη, hK, hcurv⟩ := exists_uniform_stage_zero_curvature_bound P₀ g₀
  obtain ⟨ρv, κv, hρv, hκv, hvol⟩ := exists_initial_small_ball_volume_lower_bound P₀ g₀
  obtain ⟨θ₀, hθ₀def⟩ : ∃ θ₀ : ℝ, θ₀ = min aS η := ⟨_, rfl⟩
  have hθ₀ : 0 < θ₀ := by rw [hθ₀def]; exact lt_min haS hη
  have hBf : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨Cmain, hCmain⟩ : ∃ Cmain : ℝ, Cmain = 3 + 2 * Real.exp (18 * K * θ₀) ^ 2 *
      (3 + (2 * (3 / a₀) / 3) * B + 2 * (3 / a₀) * B) + 2 * (3 / a₀) * B + 6 * K * B +
      Real.exp (18 * K * θ₀) := ⟨_, rfl⟩
  have hCmain0 : 0 ≤ Cmain := by
    have h1 : 0 ≤ 2 * (3 / a₀) * B := mul_nonneg (mul_nonneg (by norm_num) hBf) hB.le
    have h2 : 0 ≤ (2 * (3 / a₀) / 3) * B :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hBf) (by norm_num)) hB.le
    have h3 : 0 ≤ 6 * K * B := mul_nonneg (mul_nonneg (by norm_num) hK) hB.le
    have h4 : 0 ≤ 2 * Real.exp (18 * K * θ₀) ^ 2 *
        (3 + (2 * (3 / a₀) / 3) * B + 2 * (3 / a₀) * B) :=
      mul_nonneg (by positivity) (by linarith)
    have h5 := (Real.exp_pos (18 * K * θ₀)).le
    rw [hCmain]
    linarith
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = min (1 / 2) (min (ρv / Real.sqrt B)
      (Real.sqrt θ₀ / (2 * Real.sqrt B))) := ⟨_, rfl⟩
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    exact lt_min (by norm_num) (lt_min (div_pos hρv hsB)
      (div_pos (Real.sqrt_pos.mpr hθ₀) (by positivity)))
  have hc₁half : c₁ ≤ 1 / 2 := by rw [hc₁def]; exact min_le_left _ _
  have hc₁v : c₁ ≤ ρv / Real.sqrt B := by
    rw [hc₁def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc₁θ : c₁ ≤ Real.sqrt θ₀ / (2 * Real.sqrt B) := by
    rw [hc₁def]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a₀, Cmain / 2, κv * c₁ ^ 3, ha₀, mul_pos hκv (pow_pos hc₁ 3), hHI, ?_⟩
  intro r₀ qcan ρ Ctime hr₀ hqcan hρ
  obtain ⟨m₁, R₁, ε₁, δ₁, hR₁, hε₁, hδ₁, hL1⟩ :=
    ObservedHistory.exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul.{u}
      (Real.sqrt B) r₀ qcan a₀ ρ Ctime (Real.sqrt_nonneg _) hr₀ hqcan ha₀ hρ
  obtain ⟨m₂, R₂, ε₂, δ₂, hR₂, hε₂, hδ₂, hA24⟩ :=
    ObservedHistory.exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_recenter_budget.{u}
      (Cmain * Real.sqrt B + 1) (Real.sqrt B) r₀ qcan a₀ ρ Ctime (Real.sqrt_nonneg _) hr₀ hqcan
      ha₀ hρ
  refine ⟨min δ₁ δ₂, min ε₁ ε₂, max R₁ R₂, max m₁ m₂, lt_min hδ₁ hδ₂, lt_min hε₁ hε₂,
    hR₁.trans_le (le_max_left _ _), ?_⟩
  intro p₀ δbound ρbound haccuracy₀ hradius₀ horder₀ hbudget₀ hδbound hρbound H hid hhor hrec
    t ht hder p hball
  obtain ⟨A⟩ := hid
  obtain ⟨parameters, -, hradius, horder, haccuracy, hrecenter, records, hcanonical, hdelta,
    hneck⟩ := hrec
  have hpc (j : Fin H.eventCount) :
      parameters.recenterConstant * parameters.delta (H.time j.succ) ≤ 1 / 2 := by
    have hrc : 0 ≤ parameters.recenterConstant := by
      linarith [parameters.recenterConstant_ge_four]
    rw [hrecenter] at hrc ⊢
    exact (mul_le_mul_of_nonneg_left (hdelta j) hrc).trans hbudget₀
  have hstart := hHI H.toHistory A
  have htB : (t : ℝ) < B := t.property.2.trans_lt hhor
  have htE : Real.sqrt t ≤ Real.sqrt B := Real.sqrt_le_sqrt htB.le
  obtain ⟨q₀, L, hLmem, -, -, hLlt⟩ := hL1 H.toHistory parameters
    (horder ▸ (le_max_left _ _).trans horder₀) (hradius ▸ (le_max_left _ _).trans hradius₀)
    (haccuracy ▸ haccuracy₀.trans (min_le_left _ _)) hpc
    (fun j => (hdelta j).trans (hδbound.trans (min_le_left _ _)))
    (fun j => (hneck j).trans hρbound) records hstart.1 hstart.2 hcanonical t hder p hball htE
  have hpreserve := H.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hstart.1
    hstart.2
  have hscalar (j : Fin (H.eventCount + 1)) (s : ℝ) (hs : s ∈ H.toHistory.stageDomain j)
      (z : (H.stage j).Carrier) : -(3 / a₀) ≤ metricScalarAt (H.toHistory.stageMetric j s) z := by
    have hs0 : 0 ≤ s := (H.toHistory.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right hs0)
    have hlow : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlow.trans (hpreserve.1 j s hs z).2
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (t : ℝ) θ₀ / 2 := ⟨_, rfl⟩
  have hmin1 := min_le_left (t : ℝ) θ₀
  have hmin2 := min_le_right (t : ℝ) θ₀
  have hmin0 : 0 < min (t : ℝ) θ₀ := lt_min ht hθ₀
  have hθ : 0 < θ := by rw [hθdef]; linarith
  have hθt : θ < t := by rw [hθdef]; linarith
  have hθθ₀ : θ ≤ θ₀ := by rw [hθdef]; linarith
  have hθ₀aS : θ₀ ≤ aS := by rw [hθ₀def]; exact min_le_left _ _
  have hθ₀η : θ₀ ≤ η := by rw [hθ₀def]; exact min_le_right _ _
  have hθaS : θ < aS := by rw [hθdef]; linarith
  obtain ⟨e, G, hθe, hθdom, hG0, hGstage, hRm⟩ :=
    exists_stage_zero_window_of_initialIdentification P₀ g₀ hsing hcurv H.toHistory A
      (fun j => (records j).singular) t.property.2 hθ hθt hθaS (hθθ₀.trans hθ₀η)
  have hρ₁pos : 0 < c₁ * Real.sqrt t := mul_pos hc₁ (Real.sqrt_pos.mpr ht)
  have hρ₁gap : (c₁ * Real.sqrt t) ^ 2 ≤ (Real.sqrt t - Real.sqrt (t - θ)) * Real.sqrt t :=
    sq_le_tail_gap_mul_sqrt ht hθt.le (by
      rw [hθdef]
      exact window_radius_sq_le ht htB.le hθ₀ hc₁.le hc₁half hc₁θ)
  refine ⟨riemannianBallOf (H.initialMetric 0) q₀ (c₁ * Real.sqrt t),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ q₀) continuous_const, ?_, ?_⟩
  · rw [ball_volume_eq hκv.le hc₁.le t.property.1]
    exact hvol H.toHistory A q₀ _ hρ₁pos (window_radius_le htB.le hB hρv hc₁v)
  · intro q hq
    have hcost := H.toHistory.regularizedCost_le_of_initial_tail_replacement (Fin.zero_le _)
      (T := t) (B := 3 / a₀) (K := K) (θ := θ) (e := e) (L := L) (ρ := c₁ * Real.sqrt t) hBf
      hK hθ hθt hθe hθdom hscalar G hG0 hGstage hRm p q₀ q hLmem hq hρ₁gap
    have hbudget := cost_budget_le (B := B) hK hBf ht htB.le hθθ₀ hLlt.le
    rw [← hCmain] at hbudget
    have hcostC : H.toHistory.regularizedCost 0 (H.toHistory.activeStage t) (Fin.zero_le _) t
        (3 / a₀) 0 (Real.sqrt t) p q ≤ ((Cmain * Real.sqrt t : ℝ) : WithTop ℝ) :=
      hcost.trans (WithTop.coe_le_coe.mpr hbudget)
    refine ⟨?_, hcostC.trans (WithTop.coe_le_coe.mpr (le_of_eq (by ring)))⟩
    apply hA24 H.toHistory parameters (horder ▸ (le_max_right _ _).trans horder₀)
      (hradius ▸ (le_max_right _ _).trans hradius₀)
      (haccuracy ▸ haccuracy₀.trans (min_le_right _ _)) hpc
      (fun j => (hdelta j).trans (hδbound.trans (min_le_right _ _)))
      (fun j => (hneck j).trans hρbound) records hstart.1 hstart.2 t hder p hball 0
      (Fin.zero_le _) (Real.sqrt t) htE (fun i _ _ b => hcanonical i b) q
    refine hcostC.trans_lt (WithTop.coe_lt_coe.mpr ?_)
    have := mul_le_mul_of_nonneg_left htE hCmain0
    linarith

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private theorem exp_density_mul_volume_eq {t C κ₀ : ℝ} (ht : 0 < t) :
    Real.exp (-C - (3 / 2 : ℝ) * Real.log (Real.sqrt t ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi)) * (κ₀ * t ^ (3 / 2 : ℝ)) =
      κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sq_sqrt ht.le, Real.exp_sub, Real.exp_sub]
  have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
  have hpow : t ^ (3 / 2 : ℝ) = Real.exp ((3 / 2 : ℝ) * Real.log t) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have hpow4 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (Real.exp ((3 / 2 : ℝ) * Real.log (4 * Real.pi)))⁻¹ := by
    rw [Real.rpow_def_of_pos h4, ← Real.exp_neg]
    ring_nf
  rw [hpow, hpow4]
  have he1 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log t)).ne'
  have he2 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log (4 * Real.pi))).ne'
  field_simp

theorem RetainedCoreHistory.reducedVolume_ge_of_initial_regular_block
    {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) {Bf κ₀ C : ℝ}
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.toHistory.stageDomain j,
      ∀ x : (H.stage j).Carrier, -Bf ≤ metricScalarAt (H.toHistory.stageMetric j s) x)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (ht : 0 < (t : ℝ))
    (p : (H.toHistory.stageAt t).Carrier) (U : Set (H.stage 0).Carrier) (hU : IsOpen U)
    (hvol : ENNReal.ofReal (κ₀ * (t : ℝ) ^ (3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) U)
    (hblock : ∀ q ∈ U,
      q ∈ H.toHistory.regularMinimizerEndpoints 0 (H.toHistory.activeStage t) (Fin.zero_le _)
        t Bf (Real.sqrt t) p ∧
      H.toHistory.regularizedCost 0 (H.toHistory.activeStage t) (Fin.zero_le _) t Bf 0
        (Real.sqrt t) p q ≤ ((2 * C * Real.sqrt t : ℝ) : WithTop ℝ)) :
    ENNReal.ofReal (κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))) ≤
      H.reducedVolume (H.toHistory.activeStage t) p t (Real.sqrt t) := by
  classical
  have hsq : (t : ℝ) - Real.sqrt t ^ 2 = 0 := by rw [Real.sq_sqrt t.property.1, sub_self]
  have h0dom : (0 : ℝ) ∈ H.toHistory.stageDomain 0 := by
    have h := H.toHistory.time_mem_stageDomain 0
    rwa [show H.toHistory.time 0 = 0 from H.time_zero] at h
  have hact0 : H.toHistory.activeStage
      (projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - Real.sqrt t ^ 2)) = 0 := by
    rw [hsq]
    exact (H.toHistory.mem_stageDomain_iff _ 0).mp (by
      rw [projIcc_of_mem H.horizon_nonneg ⟨le_rfl, H.horizon_nonneg⟩]
      exact h0dom)
  have hle : H.toHistory.activeStage
      (projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - Real.sqrt t ^ 2)) ≤
        H.toHistory.activeStage t := by
    rw [hact0]
    exact Fin.zero_le _
  rw [RetainedCoreHistory.reducedVolume_eq_of_scalar_lower_bound_le hfloor _ p t
    (Real.sqrt t) le_rfl hle]
  generalize hf : H.toHistory.activeStage
    (projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - Real.sqrt t ^ 2)) = f at hle ⊢
  rw [hact0] at hf
  subst hf
  rw [hsq]
  have hmetric0 : H.toHistory.stageMetric 0 0 = H.initialMetric 0 := by
    have h := H.toHistory.stageMetric_initial 0
    rwa [show H.toHistory.time 0 = 0 from H.time_zero] at h
  rw [hmetric0]
  set μ := riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0)
  have hsqrt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  set c := ENNReal.ofReal (Real.exp (-C - (3 / 2 : ℝ) * Real.log (Real.sqrt t ^ 2) -
    (3 / 2 : ℝ) * Real.log (4 * Real.pi))) with hcdef
  have hdens : ∀ q ∈ U, c ≤ H.toHistory.regularizedDensity 0 (H.toHistory.activeStage t) hle t Bf
      (Real.sqrt t) p q := by
    intro q hq
    have hcost := (hblock q hq).2
    have hne : H.toHistory.regularizedCost 0 (H.toHistory.activeStage t) hle t Bf 0
        (Real.sqrt t) p q ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hcost
    obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [H.toHistory.regularizedDensity_eq_exp_of_regularizedCost_eq 0
      (H.toHistory.activeStage t) hle t Bf hsqrt p q hA.symm, hcdef]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hAle : A ≤ 2 * C * Real.sqrt t := by
      rw [← hA] at hcost
      exact WithTop.coe_le_coe.mp hcost
    have hdiv : A / (2 * Real.sqrt t) ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have : -A / (2 * Real.sqrt t) = -(A / (2 * Real.sqrt t)) := neg_div _ _
    linarith
  have hsub : U ⊆ H.toHistory.regularMinimizerEndpoints 0 (H.toHistory.activeStage t) hle t Bf
      (Real.sqrt t) p := fun q hq => (hblock q hq).1
  calc ENNReal.ofReal (κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)))
      = c * ENNReal.ofReal (κ₀ * (t : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [hcdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le, exp_density_mul_volume_eq ht]
    _ ≤ c * μ U := mul_le_mul' le_rfl hvol
    _ = ∫⁻ _ in U, c ∂μ := (setLIntegral_const U c).symm
    _ ≤ ∫⁻ q in U, H.toHistory.regularizedDensity 0 (H.toHistory.activeStage t) hle t Bf
          (Real.sqrt t) p q ∂μ :=
        lintegral_mono_ae ((ae_restrict_mem hU.measurableSet).mono fun q hq => hdens q hq)
    _ ≤ _ := lintegral_mono_set hsub

theorem RetainedCoreHistory.historyScalarDerivativeBoundBefore_of_eventSlabsDerivative
    {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) {Ctime : ℝ≥0} {qcan : ℝ}
    (hend : H.time (Fin.last H.eventCount) = H.horizon) (j : Fin H.eventCount)
    (hder : H.EventSlabsDerivative Ctime qcan j.castSucc) {t₀ : ℝ}
    (ht₀ : t₀ ≤ H.time j.succ)
    (hdb : (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀)
    {t : ℝ} (ht : t ≤ t₀) : HistoryScalarDerivativeBoundBefore H Ctime qcan t := by
  intro k y s hs hst hq
  cases k using Fin.lastCases with
  | last =>
    rw [H.toHistory.stageEndTime_last] at hs
    exact absurd hend (ne_of_lt (hs.1.trans hs.2))
  | cast i =>
    have hmetric : H.toHistory.stageMetric i.castSucc =
        (H.toHistory.event i).incoming.flow.base.metric := by
      funext τ
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rw [H.toHistory.stageEndTime_castSucc] at hs
    rw [hmetric] at hq ⊢
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hder i (Fin.castSucc_lt_castSucc_iff.mpr hij) y s hs hq
    · exact hdb y s ⟨hs.1, hst.trans_le ht⟩ hq
    · have hmono : H.time j.succ ≤ H.time i.castSucc :=
        H.time_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hji)
      exact absurd (hs.1.trans hst) (not_lt.mpr (hmono.trans' (ht.trans ht₀)))

theorem RetainedCoreHistory.historyScalarDerivativeBoundBefore_extendHorizon
    {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) {Ctime : ℝ≥0} {qcan : ℝ}
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hder : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount)) {t₀ : ℝ}
    (hdb : G.DerivativeBoundBefore Ctime qcan t₀) (T : ℝ)
    (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s) (hTt₀ : T ≤ t₀) {t : ℝ}
    (ht : t ≤ T) :
    HistoryScalarDerivativeBoundBefore
      (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG) Ctime qcan t := by
  intro k
  change Fin (H.eventCount + 1) at k
  intro y r hr hrt hq
  cases k using Fin.lastCases with
  | last =>
    rw [H.stageEndTime_extendHorizon_last (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG] at hr
    have hmem : r ∈ Icc (H.time (Fin.last H.eventCount)) T := ⟨hr.1.le, hr.2.le⟩
    have hmetric : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) T,
        (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.stageMetric
          (Fin.last H.eventCount) τ = G.flow.base.metric τ :=
      fun τ hτ => H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hT.le)
        (G.closedPrefix T hT hTs) hG hτ
    have hfun : (fun z => metricScalarAt
        ((H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.stageMetric
          (Fin.last H.eventCount) z) y) =ᶠ[𝓝[≤] r] fun z => G.flow.scalar z y := by
      have hnhds : Ioc (H.time (Fin.last H.eventCount)) r ∈ 𝓝[≤] r :=
        Ioc_mem_nhdsLE hr.1
      filter_upwards [hnhds] with z hz
      rw [hmetric z ⟨hz.1.le, hz.2.trans hr.2.le⟩]
      rfl
    have hderiv : derivWithin (fun z => metricScalarAt
        ((H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.stageMetric
          (Fin.last H.eventCount) z) y) (Iic r) r =
        derivWithin (fun z => G.flow.scalar z y) (Iic r) r :=
      hfun.derivWithin_eq (by rw [hmetric r hmem]; rfl)
    rw [hderiv, hmetric r hmem]
    rw [hmetric r hmem] at hq
    exact hdb y r ⟨hr.1, hrt.trans_le (ht.trans hTt₀)⟩ hq
  | cast i =>
    rw [H.stageEndTime_extendHorizon_castSucc (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG i,
      H.toHistory.stageEndTime_castSucc] at hr
    have hmetric : (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.stageMetric
        i.castSucc = (H.toHistory.event i).incoming.flow.base.metric := by
      funext τ
      unfold ObservedHistory.stageMetric
      erw [Fin.lastCases_castSucc]
      rfl
    rw [hmetric] at hq ⊢
    exact hder i (Fin.castSucc_lt_last i) y r hr hq

theorem historyReducedVolumeInitialLowerBound_holds (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) : HistoryReducedVolumeInitialLowerBound P₀ g₀ := by
  intro B ε C1 C2 τmin Ctime Cgrad phi hB _ _ _ _ _ _
  obtain ⟨a₀, C, κ₀, ha₀, hκ₀, hHI, hblock⟩ := exists_uniform_initial_regular_block P₀ g₀ B hB
  refine ⟨κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)), by positivity, ?_⟩
  intro qcan r₀ hqcan hr₀
  obtain ⟨δ₀, ε₀, R₀, m₀, hδ₀, hε₀, hR₀, hstep⟩ := hblock r₀ qcan 1 Ctime hr₀ hqcan one_pos
  refine ⟨δ₀, 1, ε₀, R₀, m₀, hδ₀, one_pos, hε₀, hR₀, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ H hH _
  obtain ⟨⟨A⟩, hend, hhor, hrec, hbudget⟩ := hH
  obtain ⟨parameters, -, -, -, -, -, records, -⟩ := id hrec
  have hstart := hHI H.toHistory A
  have hpreserve := H.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records ha₀
    hstart.1 hstart.2
  have hfloorOf (K : RetainedCoreHistory P₀) (hK : ∀ (j : Fin (K.eventCount + 1)) (s : ℝ),
      s ∈ K.toHistory.stageDomain j → ∀ x : (K.stage j).Carrier,
        -3 / (a₀ + s) ≤ metricScalarAt (K.toHistory.stageMetric j s) x) :
      ∀ (j : Fin (K.eventCount + 1)), ∀ s ∈ K.toHistory.stageDomain j,
        ∀ x : (K.stage j).Carrier, -(3 / a₀) ≤ metricScalarAt (K.toHistory.stageMetric j s) x := by
    intro j s hs x
    have hs0 : 0 ≤ s := (K.toHistory.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right hs0)
    have hlow : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlow.trans (hK j s hs x)
  refine ⟨?_, ?_⟩
  · intro j _ hder _ t₀ ht₀ _ hdb _ t p r htt₀ hr₀r _ hball
    have hr : 0 < r := hball.1
    have ht : 0 < (t : ℝ) := (pow_pos hr 2).trans_le hball.radius_sq_le_time
    obtain ⟨U, hU, hvol, hUblock⟩ := hstep p₀ δbound ρbound hacc hD hm hbudget hδ hρ H ⟨A⟩
      hhor hrec t ht
      (H.historyScalarDerivativeBoundBefore_of_eventSlabsDerivative hend j hder ht₀.2 hdb htt₀)
      p (ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀ hr₀r)
    exact H.reducedVolume_ge_of_initial_regular_block
      (hfloorOf H fun k s hs x => (hpreserve.1 k s hs x).2) t ht p U hU hvol hUblock
  · intro s G hG _ _ hder _ t₀ ht₀ _ hdb _ T hT hTs hTt₀
    set H' := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG.2 with hH'
    have hrec' : H'.hasCanonicalCutoffRecords p₀ δbound ρbound :=
      RetainedCoreHistory.hasCanonicalCutoffRecords_extendHorizon hrec T (hend ▸ hT.le) (G.closedPrefix T hT hTs)
        hG.2
    obtain ⟨parameters', -, -, -, -, -, records', -⟩ := hrec'
    have hpreserve' := H'.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records' ha₀
      hstart.1 hstart.2
    intro t p r htT hr₀r _ hball
    have hr : 0 < r := hball.1
    have ht : 0 < (t : ℝ) := (pow_pos hr 2).trans_le hball.radius_sq_le_time
    obtain ⟨U, hU, hvol, hUblock⟩ := hstep p₀ δbound ρbound hacc hD hm hbudget hδ hρ H' ⟨⟨A.map, A.positive, A.metric_eq⟩⟩
      (hTs.trans_le hG.1)
      (RetainedCoreHistory.hasCanonicalCutoffRecords_extendHorizon hrec T (hend ▸ hT.le) (G.closedPrefix T hT hTs)
        hG.2) t ht
      (H.historyScalarDerivativeBoundBefore_extendHorizon hend G hG.2 hder hdb T hT hTs hTt₀
        htT)
      p (ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀ hr₀r)
    exact H'.reducedVolume_ge_of_initial_regular_block
      (hfloorOf H' fun k s hs x => (hpreserve'.1 k s hs x).2) t ht p U hU hvol hUblock

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
