import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Window
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialSlabUniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Connector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian (edistOf_le_budget integrableOn_inner_mfderiv_self_of_contMDiffOn)
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_stage_zero_curvature_bound (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ η K : ℝ, 0 < η ∧ 0 ≤ K ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      ∀ (e : ℝ) (G : (H.stage 0).IncomingSlab 0 e),
        G.flow.base.metric 0 = H.initialMetric 0 →
        ∀ τ, 0 ≤ τ → τ < e → τ ≤ η → ∀ x : (H.stage 0).Carrier,
          normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2 := by
  obtain ⟨η, K, hη, hK⟩ := P.exists_uniform_initial_curvature_bound g
  refine ⟨η, max K 0, hη, le_max_right _ _, ?_⟩
  intro H A e G hG τ hτ0 hτe hτη x
  let F := G.pullback A.map
  have hinit : F.flow.base.metric 0 = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [OrientedThreeStage.IncomingSlab.pullback_metric, Diffeomorph.pullbackMetricCross_inner, hG]
    exact A.metric_eq y v w
  obtain ⟨y, rfl⟩ := A.map.surjective x
  have hbound := (hK e F hinit τ hτ0 hτe hτη y).2
  have hlocal : F.flow.base.metric τ =
      localPullMetric (G.flow.base.metric τ) A.map A.map.isLocalDiffeomorph := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [OrientedThreeStage.IncomingSlab.pullback_metric, Diffeomorph.pullbackMetricCross_inner,
      localPullMetric_inner]
  have hnat := normSq0S_metricRm04At_localPullMetric (G.flow.base.metric τ) A.map
    A.map.isLocalDiffeomorph y
  rw [← hlocal] at hnat
  have hF : normSq0S (F.flow.base.metric τ) y 4 (metricRm04At (F.flow.base.metric τ) y) ≤
      (max K 0) ^ 2 := by
    have hsq : Real.sqrt (normSq0S (F.flow.base.metric τ) y 4
        (metricRm04At (F.flow.base.metric τ) y)) ≤ max K 0 := by
      rw [← metricRm04_apply]
      exact hbound.trans (le_max_left _ _)
    have hnn : 0 ≤ normSq0S (F.flow.base.metric τ) y 4
        (metricRm04At (F.flow.base.metric τ) y) := normSq0S_nonneg _ _ _ _
    calc _ = (Real.sqrt (normSq0S (F.flow.base.metric τ) y 4
            (metricRm04At (F.flow.base.metric τ) y))) ^ 2 := (Real.sq_sqrt hnn).symm
      _ ≤ (max K 0) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  rw [hnat] at hF
  change normSq0S (G.flow.base.metric τ) (A.map y) 4
    (metricRm04 (G.flow.base.metric τ) (A.map y)) ≤ _
  rw [metricRm04_apply]
  exact hF

private theorem tail_replacement_budget {L a₂ aγ D d ρ l Δ T B K b c : ℝ}
    (hl : 1 ≤ l) (hB : 0 ≤ B) (hK : 0 ≤ K) (hΔ : 0 < Δ) (hΔb : Δ ≤ b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (hb2 : b ^ 2 = T) (hd : 0 ≤ d) (hdD : d ≤ D + ρ) (hρ : ρ ^ 2 ≤ Δ * b)
    (htail : D ^ 2 / (2 * l * Δ) - 2 * T * B * Δ ≤ a₂)
    (hhead : -(2 * B / 3) * (c ^ 3 - 0 ^ 3) ≤ L - a₂)
    (hconn : aγ ≤ l * d ^ 2 / (2 * Δ) + (2 * (9 * K) / 3) * (b ^ 3 - c ^ 3)) :
    L - a₂ + aγ ≤ L + 2 * l ^ 2 * (L + (2 * B / 3) * (T * b) + 2 * B * (T * b)) +
      2 * B * (T * b) + 6 * K * (T * b) + l * b := by
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hb : 0 ≤ b := hc.trans hcb
  have hTb : T * b = b ^ 3 := by rw [← hb2]; ring
  have hc3 : c ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hc hcb 3
  set X := D ^ 2 / (2 * l * Δ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hM : X ≤ L + (2 * B / 3) * (T * b) + 2 * B * (T * b) := by
    have h1 : 2 * T * B * Δ ≤ 2 * B * (T * b) := by
      have hT0 : 0 ≤ T := by rw [← hb2]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hΔb (by positivity : 0 ≤ 2 * T * B)]
    have h2 : (2 * B / 3) * c ^ 3 ≤ (2 * B / 3) * (T * b) := by
      rw [hTb]; exact mul_le_mul_of_nonneg_left hc3 (by positivity)
    nlinarith
  have hd2 : d ^ 2 ≤ 2 * D ^ 2 + 2 * ρ ^ 2 := by
    have := pow_le_pow_left₀ hd hdD 2
    nlinarith [sq_nonneg (D - ρ)]
  have hkin : l * d ^ 2 / (2 * Δ) ≤ 2 * l ^ 2 * X + l * b := by
    rw [hX, div_le_iff₀ (by positivity : 0 < 2 * Δ)]
    have hρb : l * (2 * ρ ^ 2) ≤ l * (2 * (Δ * b)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hl0.le
    have heq : 2 * l ^ 2 * (D ^ 2 / (2 * l * Δ)) * (2 * Δ) = l * (2 * D ^ 2) := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hd2 hl0.le]
  have hcube : (2 * (9 * K) / 3) * (b ^ 3 - c ^ 3) ≤ 6 * K * (T * b) := by
    rw [hTb]
    have : 0 ≤ c ^ 3 := by positivity
    nlinarith
  have hTB : 2 * T * B * Δ ≤ 2 * B * (T * b) := by
    have hT0 : 0 ≤ T := by rw [← hb2]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hΔb (by positivity : 0 ≤ 2 * T * B)]
  have hl2 : 0 ≤ 2 * l ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hM hl2]

namespace ObservedHistory

variable (H : ObservedHistory.{u})

theorem exists_head_tail_split_of_mem_regularizedC1ActionValues
    {last : Fin (H.eventCount + 1)} (hle : (0 : Fin (H.eventCount + 1)) ≤ last) {T B c L : ℝ}
    (hc0 : 0 ≤ c) (hcb : c ≤ Real.sqrt T) (hcdom : T - c ^ 2 ∈ H.stageDomain 0)
    (hscalar : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (p : (H.stage last).Carrier) (q₀ : (H.stage 0).Carrier)
    (hL : L ∈ H.regularizedC1ActionValues 0 last hle T 0 (Real.sqrt T) p q₀) :
    ∃ (α₀ : ℝ → (H.stage 0).Carrier) (x₁ : ℝ),
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α₀ (Icc c (Real.sqrt T)) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian 0 T α₀) volume c (Real.sqrt T) ∧
      α₀ (Real.sqrt T) = q₀ ∧
      (x₁ : WithTop ℝ) ∈ H.regularizedActionValues 0 last hle T B 0 c p (α₀ c) ∧
      L = x₁ + H.stageRegularizedAction 0 T α₀ c (Real.sqrt T) := by
  classical
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.sqrt T := ⟨_, rfl⟩
  rw [← hbdef] at hL hcb ⊢
  obtain ⟨-, hb0, hupperIcc, hpast, α, hα, hint, hαp, hαq, hnodes, hsum⟩ := hL
  have hαAC (j : H.StageInterval 0 last) : Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val) :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hα j).contMDiffOn
  have hfloor0 (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart T 0 0) (H.regularizedStageEnd T b 0))
      (x : (H.stage 0).Carrier) : -B ≤ metricScalarAt (H.stageMetric 0 (T - s ^ 2)) x :=
    hscalar 0 _ (H.mapsTo_regularizedStage_Ioo T 0 b 0 hs) x
  have hext : H.regularizedExtendedAction 0 last T B 0 b α = (L : WithTop ℝ) := by
    rw [H.regularizedExtendedAction_eq_sum_action 0 last le_rfl hb0 hupperIcc hpast α hint
      (fun j => (ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
        hscalar j.val _ (H.mapsTo_regularizedStage_Ioo T 0 b j.val hs) _), hsum]
  have hsplit := regularizedExtendedAction_eq_add_at_parameter (H := H) (first := 0)
    (last := last) 0 le_rfl hle (T := T) (B := B) (u := 0) (v := b) (c := c) le_rfl hc0 hcb
    hcdom hfloor0 α hαAC
  rw [hext] at hsplit
  have hA₁mem := mem_regularizedActionValues_upper_restrict (H := H) (first := 0) (last := last)
    0 le_rfl hle (T := T) (B := B) (u := 0) (v := b) (c := c) le_rfl hc0 hcb hupperIcc hpast
    hcdom α hαAC hnodes
  let j₀ : H.StageInterval 0 last := ⟨0, le_rfl, hle⟩
  have hbdom : T - b ^ 2 ∈ H.stageDomain 0 := hpast
  have hcIcc : T - c ^ 2 ∈ Icc (H.time 0) (H.stageEndTime 0) :=
    ⟨H.time_le_of_mem_stageDomain hcdom, H.le_stageEndTime_of_mem_stageDomain hcdom⟩
  have hstart0 : H.regularizedStageStart T 0 0 ≤ c := by
    have hh := (H.regularizedStage_bounds le_rfl hc0 hupperIcc hcdom j₀).2.1
    rwa [H.regularizedStageEnd_eq_of_mem_stageDomain hc0 hcdom] at hh
  have hend0 : H.regularizedStageEnd T b 0 = b :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hb0 hbdom
  have hstartc : H.regularizedStageStart T c 0 = c :=
    H.regularizedStageStart_eq_of_mem_Icc hc0 hcIcc
  have hint₀ : IntervalIntegrable (H.stageRegularizedLagrangian 0 T (α j₀)) volume c b := by
    have hh := hint j₀
    change IntervalIntegrable (H.stageRegularizedLagrangian 0 T (α j₀)) volume
      (H.regularizedStageStart T 0 0) (H.regularizedStageEnd T b 0) at hh
    rw [hend0] at hh
    exact hh.mono_set (by
      rw [uIcc_of_le hcb, uIcc_of_le (hstart0.trans hcb)]
      exact Icc_subset_Icc hstart0 le_rfl)
  have hsub : Subsingleton (H.StageInterval 0 0) :=
    ⟨fun i k => Subtype.ext ((le_antisymm i.property.2 i.property.1).trans
      (le_antisymm k.property.2 k.property.1).symm)⟩
  have hY : H.regularizedExtendedAction 0 0 T B c b
      (fun j => α ⟨j.val, j.property.1, j.property.2.trans hle⟩) =
        ((H.stageRegularizedAction 0 T (α j₀) c b : ℝ) : WithTop ℝ) := by
    rw [H.regularizedExtendedAction_eq_sum_action 0 0 hc0 hcb hcIcc hbdom _ ?_ ?_]
    · rw [Fintype.sum_subsingleton _ (⟨0, le_rfl, le_rfl⟩ : H.StageInterval 0 0)]
      change ((H.stageRegularizedAction 0 T (α j₀) (H.regularizedStageStart T c 0)
        (H.regularizedStageEnd T b 0) : ℝ) : WithTop ℝ) = _
      rw [hstartc, hend0]
    · intro j
      obtain ⟨jv, hj1, hj2⟩ := j
      obtain rfl : jv = 0 := le_antisymm hj2 hj1
      change IntervalIntegrable (H.stageRegularizedLagrangian 0 T (α j₀)) volume
        (H.regularizedStageStart T c 0) (H.regularizedStageEnd T b 0)
      rw [hstartc, hend0]
      exact hint₀
    · intro j
      refine (ae_restrict_mem measurableSet_Ioo).mono fun s hs => ?_
      exact hscalar j.val _ (H.mapsTo_regularizedStage_Ioo T c b j.val hs) _
  rw [hY] at hsplit
  obtain ⟨X, hXdef⟩ : ∃ X : WithTop ℝ, X = H.regularizedExtendedAction 0 last T B 0 c
      (fun j => α ⟨j.val, (le_refl (0 : Fin (H.eventCount + 1))).trans j.property.1,
        j.property.2⟩) := ⟨_, rfl⟩
  rw [← hXdef] at hsplit hA₁mem
  have hXtop : X ≠ ⊤ := by
    intro htop
    rw [htop, WithTop.top_add] at hsplit
    exact WithTop.coe_ne_top hsplit
  obtain ⟨x₁, hx₁⟩ := WithTop.ne_top_iff_exists.mp hXtop
  rw [← hx₁, ← WithTop.coe_add] at hsplit
  refine ⟨α j₀, x₁, (hα j₀).contMDiffOn, hint₀, hαq, ?_, WithTop.coe_injective hsplit⟩
  rw [hx₁, ← hαp]
  exact hA₁mem

theorem coe_stageRegularizedAction_mem_regularizedActionValues_stage_zero
    {T B c b : ℝ} (hc0 : 0 ≤ c) (hcb : c ≤ b) (hb0 : 0 ≤ b)
    (hcdom : T - c ^ 2 ∈ H.stageDomain 0) (hbdom : T - b ^ 2 ∈ H.stageDomain 0)
    (hscalar : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (γ : ℝ → (H.stage 0).Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hint : IntervalIntegrable (H.stageRegularizedLagrangian 0 T γ) volume c b) :
    ((H.stageRegularizedAction 0 T γ c b : ℝ) : WithTop ℝ) ∈
      H.regularizedActionValues 0 0 le_rfl T B c b (γ c) (γ b) := by
  classical
  have hcIcc : T - c ^ 2 ∈ Icc (H.time 0) (H.stageEndTime 0) :=
    ⟨H.time_le_of_mem_stageDomain hcdom, H.le_stageEndTime_of_mem_stageDomain hcdom⟩
  have hend0 : H.regularizedStageEnd T b 0 = b :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hb0 hbdom
  have hstartc : H.regularizedStageStart T c 0 = c :=
    H.regularizedStageStart_eq_of_mem_Icc hc0 hcIcc
  have hsub : Subsingleton (H.StageInterval 0 0) :=
    ⟨fun i k => Subtype.ext ((le_antisymm i.property.2 i.property.1).trans
      (le_antisymm k.property.2 k.property.1).symm)⟩
  let j₀ : H.StageInterval 0 0 := ⟨0, le_rfl, le_rfl⟩
  let β : (j : H.StageInterval 0 0) → ℝ → (H.stage j.val).Carrier := fun j =>
    (Subsingleton.elim j₀ j) ▸ γ
  refine ⟨hc0, hcb, hcIcc, hbdom, β, ?_, rfl, rfl,
    fun i _ hl => absurd hl (not_le.mpr (Fin.succ_pos i)), ?_⟩
  · intro j
    obtain ⟨jv, hj1, hj2⟩ := j
    obtain rfl : jv = 0 := le_antisymm hj2 hj1
    exact Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hγ.contMDiffOn
  rw [H.regularizedExtendedAction_eq_sum_action 0 0 hc0 hcb hcIcc hbdom _ ?_ ?_]
  · rw [Fintype.sum_subsingleton _ (⟨0, le_rfl, le_rfl⟩ : H.StageInterval 0 0)]
    change ((H.stageRegularizedAction 0 T γ (H.regularizedStageStart T c 0)
      (H.regularizedStageEnd T b 0) : ℝ) : WithTop ℝ) = _
    rw [hstartc, hend0]
  · intro j
    obtain ⟨jv, hj1, hj2⟩ := j
    obtain rfl : jv = 0 := le_antisymm hj2 hj1
    change IntervalIntegrable (H.stageRegularizedLagrangian 0 T γ) volume
      (H.regularizedStageStart T c 0) (H.regularizedStageEnd T b 0)
    rw [hstartc, hend0]
    exact hint
  · intro j
    refine (ae_restrict_mem measurableSet_Ioo).mono fun s hs => ?_
    exact hscalar j.val _ (H.mapsTo_regularizedStage_Ioo T c b j.val hs) _

end ObservedHistory

section StageZero

variable {P : OrientedThreeStage.{u}} {e : ℝ} (G : P.IncomingSlab 0 e)

theorem OrientedThreeStage.IncomingSlab.metric_inner_le_exp_of_curvature_bound {K θ : ℝ}
    (hK : 0 ≤ K) (hθ : 0 < θ) (hθe : θ < e)
    (hRm : ∀ τ ∈ Icc 0 θ, ∀ x : P.Carrier,
      normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2)
    (τ : ℝ) (hτ : τ ∈ Icc 0 θ) (x : P.Carrier) (w : TangentSpace ThreeModel x) :
    (Real.exp (18 * K * θ))⁻¹ * (G.flow.base.metric 0).inner x w w ≤
        (G.flow.base.metric τ).inner x w w ∧
      (G.flow.base.metric τ).inner x w w ≤
        Real.exp (18 * K * θ) * (G.flow.base.metric 0).inner x w w := by
  have hcarrier : Icc (0 : ℝ) θ ⊆ (RealTimeInterval.closedOpen 0 e G.lt).carrier :=
    fun τ hτ => ⟨hτ.1, hτ.2.trans_lt hθe⟩
  have hregular : Ioo (0 : ℝ) θ ⊆ (RealTimeInterval.closedOpen 0 e G.lt).regular :=
    fun τ hτ => ⟨hτ.1, hτ.2.trans hθe⟩
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by norm_num [ThreeSpace]
  have hbd := metric_inner_exp_bounds_of_curvature_bound G.flow G.equation hcarrier hregular x
    (fun r hr => hRm r hr x) hτ ⟨le_rfl, hθ.le⟩ w
  rw [hdim, Real.sqrt_sq hK, sub_zero, abs_of_nonneg hτ.1] at hbd
  have hexp : 2 * (3 : ℝ) ^ 2 * K * τ ≤ 18 * K * θ := by nlinarith [hτ.2]
  have hnn := metric_inner_self_nonneg (G.flow.base.metric 0) x w
  constructor
  · refine le_trans ?_ hbd.1
    apply mul_le_mul_of_nonneg_right _ hnn
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  · refine hbd.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hnn
    exact Real.exp_le_exp.mpr hexp

theorem OrientedThreeStage.IncomingSlab.scalar_le_of_curvature_bound {K τ : ℝ} (hK : 0 ≤ K)
    (x : P.Carrier)
    (hRm : normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2) :
    G.flow.scalar τ x ≤ 9 * K := by
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by norm_num [ThreeSpace]
  have hh := scalar_abs_le_rm (G.flow.base.metric τ) x
  have hn : Real.sqrt (normSq0S (G.flow.base.metric τ) x 4
      (metricRm04At (G.flow.base.metric τ) x)) ≤ K := by
    rw [← metricRm04_apply]
    exact Real.sqrt_le_iff.mpr ⟨hK, hRm⟩
  change metricScalarAt (G.flow.base.metric τ) x ≤ 9 * K
  have hdim' : (Module.finrank ℝ (TangentSpace ThreeModel x) : ℝ) = 3 := hdim
  rw [hdim'] at hh
  nlinarith [le_abs_self (metricScalarAt (G.flow.base.metric τ) x)]

theorem OrientedThreeStage.IncomingSlab.intervalIntegrable_lRegularizedLagrangian_of_contMDiff
    (T c b : ℝ) (hcb : c ≤ b) (γ : ℝ → P.Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hclock : ∀ s ∈ Icc c b, T - s ^ 2 ∈ Ico 0 e) :
    IntervalIntegrable (Perelman.lRegularizedLagrangian G.flow T γ) volume c b := by
  let _ : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel _
  let _ : PseudoMetricSpace P.Carrier := TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  exact Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier G.flow
    G.equation.smoothMetric ⟨G.equation.scalarCont⟩ T c b hcb γ hγ.contMDiffOn hclock

end StageZero

namespace ObservedHistory

variable (H : ObservedHistory.{u})

theorem regularizedCost_le_of_initial_tail_replacement
    {last : Fin (H.eventCount + 1)} (hle : (0 : Fin (H.eventCount + 1)) ≤ last)
    {T B K θ e L ρ : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hθ : 0 < θ) (hθT : θ < T) (hθe : θ < e)
    (hθdom : θ ∈ H.stageDomain 0)
    (hscalar : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (G : (H.stage 0).IncomingSlab 0 e) (hG0 : G.flow.base.metric 0 = H.initialMetric 0)
    (hGstage : ∀ s ∈ Ioo 0 e, H.stageMetric 0 s = G.flow.base.metric s)
    (hRm : ∀ τ ∈ Icc 0 θ, ∀ x : (H.stage 0).Carrier,
      normSq0S (G.flow.base.metric τ) x 4 (G.flow.base.rm04 τ x) ≤ K ^ 2)
    (p : (H.stage last).Carrier) (q₀ q : (H.stage 0).Carrier)
    (hL : L ∈ H.regularizedC1ActionValues 0 last hle T 0 (Real.sqrt T) p q₀)
    (hq : riemannianEDistOf (H.initialMetric 0) q₀ q < ENNReal.ofReal ρ)
    (hρ : ρ ^ 2 ≤ (Real.sqrt T - Real.sqrt (T - θ)) * Real.sqrt T) :
    H.regularizedCost 0 last hle T B 0 (Real.sqrt T) p q ≤
      ((L + 2 * Real.exp (18 * K * θ) ^ 2 *
          (L + (2 * B / 3) * (T * Real.sqrt T) + 2 * B * (T * Real.sqrt T)) +
        2 * B * (T * Real.sqrt T) + 6 * K * (T * Real.sqrt T) +
        Real.exp (18 * K * θ) * Real.sqrt T : ℝ) : WithTop ℝ) := by
  classical
  have hT : 0 < T := hθ.trans hθT
  have hcdom0 : T - Real.sqrt (T - θ) ^ 2 ∈ H.stageDomain 0 := by
    rw [Real.sq_sqrt (by linarith), sub_sub_cancel]
    exact hθdom
  have hcb0 : Real.sqrt (T - θ) < Real.sqrt T := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  obtain ⟨α₀, x₁, hα₀, hint₀, hαq, hA₁, hLx⟩ :=
    H.exists_head_tail_split_of_mem_regularizedC1ActionValues hle (Real.sqrt_nonneg _) hcb0.le
      hcdom0 hscalar p q₀ hL
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = Real.exp (18 * K * θ) := ⟨_, rfl⟩
  rw [← hldef]
  have hl : 1 ≤ l := hldef ▸ Real.one_le_exp (by positivity)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.sqrt T := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.sqrt (T - θ) := ⟨_, rfl⟩
  have hupperIcc : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hL.2.2.1
  rw [← hbdef, ← hcdef] at hρ hα₀ hint₀ hLx hcb0
  rw [← hbdef] at hαq
  rw [← hcdef] at hA₁ hcdom0
  rw [← hbdef]
  have hb : 0 < b := hbdef ▸ Real.sqrt_pos.mpr hT
  have hc0 : 0 ≤ c := hcdef ▸ Real.sqrt_nonneg _
  have hcb : c < b := hcb0
  have hb2 : b ^ 2 = T := by rw [hbdef]; exact Real.sq_sqrt hT.le
  have hc2 : c ^ 2 = T - θ := by rw [hcdef]; exact Real.sq_sqrt (by linarith)
  have htime0 : H.time 0 = 0 := H.time_zero
  have hθend : θ ≤ H.stageEndTime 0 := H.le_stageEndTime_of_mem_stageDomain hθdom
  have hmid (τ : ℝ) (h0 : 0 < τ) (hτ : τ < θ) : τ ∈ H.stageDomain 0 :=
    H.mem_stageDomain_of_mem_Ioo ⟨by rw [htime0]; exact h0, hτ.trans_le hθend⟩
  have hclockIcc (s : ℝ) (hs : s ∈ Icc c b) : T - s ^ 2 ∈ Icc 0 θ := by
    have h1 := pow_le_pow_left₀ hc0 hs.1 2
    have h2 := pow_le_pow_left₀ (hc0.trans hs.1) hs.2 2
    constructor <;> linarith
  have hclockIoo (s : ℝ) (hs : s ∈ Ioo c b) : T - s ^ 2 ∈ Ioo 0 θ := by
    have h1 := (sq_lt_sq₀ hc0 (hc0.trans hs.1.le)).mpr hs.1
    have h2 := (sq_lt_sq₀ (hc0.trans hs.1.le) hb.le).mpr hs.2
    constructor <;> linarith
  have hlag (γ : ℝ → (H.stage 0).Carrier) (s : ℝ) (hs : s ∈ Ioo c b) :
      H.stageRegularizedLagrangian 0 T γ s = Perelman.lRegularizedLagrangian G.flow T γ s := by
    have hτ := hclockIoo s hs
    unfold stageRegularizedLagrangian Perelman.lRegularizedLagrangian SolutionOn.scalar
      SolutionFamily.scalar
    rw [hGstage (T - s ^ 2) ⟨hτ.1, hτ.2.trans hθe⟩]
  have hcompare := G.metric_inner_le_exp_of_curvature_bound hK hθ hθe hRm
  rw [hG0, ← hldef] at hcompare
  obtain ⟨a₂, ha₂def⟩ : ∃ a : ℝ, a = H.stageRegularizedAction 0 T α₀ c b := ⟨_, rfl⟩
  rw [← ha₂def] at hLx
  have hhead : -(2 * B / 3) * (c ^ 3 - 0 ^ 3) ≤ x₁ :=
    WithTop.coe_le_coe.mp (H.regularizedActionValues_ge 0 last hle T B 0 c _ _ hA₁)
  have ha₂G : a₂ = Perelman.lRegularizedAction G.flow T α₀ c b := by
    rw [ha₂def]
    exact intervalIntegral.integral_congr_Ioo_of_le hcb.le (fun s hs => hlag α₀ s hs)
  have hLagG : IntervalIntegrable (Perelman.lRegularizedLagrangian G.flow T α₀) volume c b :=
    hint₀.congr_uIoo (by rw [uIoo_of_le hcb.le]; exact fun s hs => hlag α₀ s hs)
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = b - c := ⟨_, rfl⟩
  rw [← hΔdef] at hρ
  have hΔ : 0 < Δ := by rw [hΔdef]; exact sub_pos.mpr hcb
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ,
      D = (riemannianEDistOf (H.initialMetric 0) (α₀ c) (α₀ b)).toReal := ⟨_, rfl⟩
  have htailG :=
    Perelman.lRegularizedAction_ge_riemannianEDistOf_sq_div_add_constant_of_interior_bounds
      G.flow T α₀ (c := l⁻¹) (C := -(2 * T * B)) hcb (inv_nonneg.mpr (zero_le_one.trans hl))
      (H.initialMetric 0) hα₀
      (fun s hs => (hcompare (T - s ^ 2) (Ioo_subset_Icc_self (hclockIoo s hs)) _ _).1)
      (fun s hs => by
        have hτ := hclockIoo s hs
        have hR := hscalar 0 (T - s ^ 2) (hmid _ hτ.1 hτ.2) (α₀ s)
        rw [hGstage (T - s ^ 2) ⟨hτ.1, hτ.2.trans hθe⟩] at hR
        have hs2 : s ^ 2 ≤ T := by linarith [hτ.1]
        change -(2 * T * B) ≤ 2 * s ^ 2 * metricScalarAt (G.flow.base.metric (T - s ^ 2)) (α₀ s)
        nlinarith [mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * s ^ 2),
          mul_le_mul_of_nonneg_right hs2 (by positivity : 0 ≤ 2 * B)])
      hLagG
  rw [← ha₂G, ← hDdef, ← hΔdef] at htailG
  have htail : D ^ 2 / (2 * l * Δ) - 2 * T * B * Δ ≤ a₂ := by
    have heq : l⁻¹ * D ^ 2 / (2 * Δ) = D ^ 2 / (2 * l * Δ) := by
      field_simp
    linarith [htailG, heq]
  have hDfin : riemannianEDistOf (H.initialMetric 0) (α₀ c) (α₀ b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (edistOf_le_budget (H.initialMetric 0) hcb.le hα₀
        (integrableOn_inner_mfderiv_self_of_contMDiffOn (H.initialMetric 0) hα₀) le_rfl)
  have hρpos : 0 < ρ := by
    by_contra hn
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hn)] at hq
    exact ENNReal.not_lt_zero hq
  obtain ⟨x, hxdef⟩ : ∃ x, x = α₀ c := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact ENNReal.toReal_nonneg
  have hxq : riemannianEDistOf (H.initialMetric 0) x q ≤ ENNReal.ofReal (D + ρ) := by
    have hxq₀ : riemannianEDistOf (H.initialMetric 0) x q₀ = ENNReal.ofReal D := by
      rw [hxdef, ← hαq, hDdef]
      exact (ENNReal.ofReal_toReal hDfin).symm
    calc riemannianEDistOf (H.initialMetric 0) x q
        ≤ riemannianEDistOf (H.initialMetric 0) x q₀ +
          riemannianEDistOf (H.initialMetric 0) q₀ q :=
          riemannianEDistOf_triangle (H.initialMetric 0) x q₀ q
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal ρ := add_le_add hxq₀.le hq.le
      _ = ENNReal.ofReal (D + ρ) := (ENNReal.ofReal_add hD0 hρpos.le).symm
  have hxqR : riemannianEDistOf (H.initialMetric 0) x q < ENNReal.ofReal (D + ρ + 1) :=
    hxq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  obtain ⟨γ, hγ, hγc, hγb, -, hγact⟩ := Perelman.exists_lRegularizedAction_le_of_compact_ball
    G.flow G.equation T (H.initialMetric 0) x q (Λ := l) (C := 9 * K) hcb hxqR
    (DifferentialGeometry.Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
    (fun s hs => ⟨(hclockIcc s hs).1, (hclockIcc s hs).2.trans_lt hθe⟩)
    (fun s hs z _ w => (hcompare (T - s ^ 2) (Ioo_subset_Icc_self (hclockIoo s hs)) z w).2)
    (fun s hs z _ => G.scalar_le_of_curvature_bound hK z
      (hRm _ (Ioo_subset_Icc_self (hclockIoo s hs)) z))
  rw [← hΔdef] at hγact
  have hγC1 : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ := hγ.of_le (by norm_num)
  have hγLagG : IntervalIntegrable (Perelman.lRegularizedLagrangian G.flow T γ) volume c b :=
    G.intervalIntegrable_lRegularizedLagrangian_of_contMDiff T c b hcb.le γ hγC1
      (fun s hs => ⟨(hclockIcc s hs).1, (hclockIcc s hs).2.trans_lt hθe⟩)
  have hγLag : IntervalIntegrable (H.stageRegularizedLagrangian 0 T γ) volume c b :=
    hγLagG.congr_uIoo (by rw [uIoo_of_le hcb.le]; exact fun s hs => (hlag γ s hs).symm)
  have hbdom : T - b ^ 2 ∈ H.stageDomain 0 := by
    rw [hb2, sub_self]
    simpa only [htime0] using H.time_mem_stageDomain 0
  have hZmem := H.coe_stageRegularizedAction_mem_regularizedActionValues_stage_zero
    (B := B) hc0 hcb.le hb.le hcdom0 hbdom hscalar γ hγC1 hγLag
  have haγ : H.stageRegularizedAction 0 T γ c b = Perelman.lRegularizedAction G.flow T γ c b :=
    intervalIntegral.integral_congr_Ioo_of_le hcb.le (fun s hs => hlag γ s hs)
  rw [hγc, hγb, haγ] at hZmem
  have hcomp := (mem_regularizedActionValues_split_at_parameter (H := H) hle 0 le_rfl hle
    (T := T) (B := B) (u := 0) (v := b) (c := c)
    (A := ((x₁ + Perelman.lRegularizedAction G.flow T γ c b : ℝ) : WithTop ℝ)) le_rfl hc0
    hcb.le hupperIcc hbdom hcdom0
    (fun s hs z => hscalar 0 _ (H.mapsTo_regularizedStage_Ioo T 0 b 0 hs) z) p q).mpr
    ⟨x, (x₁ : WithTop ℝ), _, hxdef ▸ hA₁, hZmem, (WithTop.coe_add _ _).symm⟩
  refine (H.regularizedCost_le_of_competitor 0 last hle T B 0 b p q hcomp).trans ?_
  apply WithTop.coe_le_coe.mpr
  have hd0 : 0 ≤ (riemannianEDistOf (H.initialMetric 0) x q).toReal := ENNReal.toReal_nonneg
  have hdD : (riemannianEDistOf (H.initialMetric 0) x q).toReal ≤ D + ρ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hxq
  have hbudget := tail_replacement_budget (L := L) (a₂ := a₂)
    (aγ := Perelman.lRegularizedAction G.flow T γ c b) (D := D)
    (d := (riemannianEDistOf (H.initialMetric 0) x q).toReal) (ρ := ρ) (l := l) (Δ := Δ)
    (T := T) (B := B) (K := K) (b := b) (c := c) hl hB hK hΔ (by rw [hΔdef]; linarith) hc0
    hcb.le hb2 hd0 hdD hρ htail (by rw [hLx]; linarith) hγact
  rw [hLx] at hbudget ⊢
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
