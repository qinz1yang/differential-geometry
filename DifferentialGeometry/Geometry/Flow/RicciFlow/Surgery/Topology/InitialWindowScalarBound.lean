import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarDerivativeBounds

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

private theorem scalar_lt_of_stage_eq_zero {P : OrientedThreeStage.{u}} {g : P.Metric}
    {τ Qb : ℝ}
    (hscalar : ∀ {Q : OrientedThreeStage.{u}} {finish : ℝ} (G : Q.IncomingSlab 0 finish)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
      (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
        (G.flow.base.metric 0).inner (φ x) (mfderiv ThreeModel ThreeModel φ x v)
          (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
      ∀ t ∈ Icc 0 τ, t < finish → ∀ x : Q.Carrier, G.flow.scalar t x < Qb)
    (H : ObservedHistory.{u}) (A : InitialIdentification P g H) {k : Fin (H.eventCount + 1)}
    (hk : k = 0) {finish : ℝ} (G : (H.stage k).IncomingSlab (H.time k) finish)
    (hG : G.flow.base.metric (H.time k) = H.initialMetric k) {t : ℝ} (ht : H.time k ≤ t)
    (htτ : t ≤ τ) (htf : t < finish) (x : (H.stage k).Carrier) :
    G.flow.scalar t x < Qb := by
  subst hk
  have key : ∀ {a : ℝ}, a = 0 → ∀ F : (H.stage 0).IncomingSlab a finish,
      F.flow.base.metric a = H.initialMetric 0 → a ≤ t → F.flow.scalar t x < Qb := by
    intro a ha F hF hat
    subst ha
    refine hscalar F A.map (fun y v w => ?_) t ⟨hat, htτ⟩ htf x
    rw [hF]
    exact A.metric_eq y v w
  exact key H.time_zero G hG ht

private theorem le_time_of_ne_zero {P : OrientedThreeStage.{u}} {g : P.Metric} {aSing : ℝ}
    (hsingTime : ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (s : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      G.SingularEndpoint → aSing ≤ s)
    (H : ObservedHistory.{u}) (A : InitialIdentification P g H)
    (hsing : ∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint)
    {k : Fin (H.eventCount + 1)} (hk : k ≠ 0) : aSing ≤ H.time k := by
  have hpos : 0 < H.eventCount := by
    rcases Nat.eq_zero_or_pos H.eventCount with h | h
    · exact absurd (Fin.ext (by have := k.isLt; omega)) hk
    · exact h
  let j : Fin H.eventCount := ⟨0, hpos⟩
  have hfirst := hsingTime H A hsing j.castSucc (H.time j.succ) (H.event j).incoming
    (H.event_initial j) (hsing j)
  refine hfirst.trans (H.time_strictMono.monotone ?_)
  change 1 ≤ k.val
  exact Nat.one_le_iff_ne_zero.mpr (fun h => hk (Fin.ext h))

end ObservedHistory

theorem RetainedCoreHistory.exists_scalar_le_before_initial_window (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) :
    ∃ η₀ K : ℝ, 0 < η₀ ∧ ∀ (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ)
      (H : RetainedCoreHistory.{u}), H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (t : ℝ) (y : (H.stage j.castSucc).Carrier),
        H.time j.castSucc ≤ t → t < H.time j.succ → t < η₀ →
          (H.toHistory.event j).incoming.flow.scalar t y ≤ K) ∧
      ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s),
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        ∀ (t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier),
          H.time (Fin.last H.eventCount) ≤ t → t < s → t < η₀ → G.flow.scalar t y ≤ K := by
  obtain ⟨aSing, haSing, hsingTime⟩ :=
    exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  obtain ⟨τ, Qb, hτ, -, hscalar⟩ :=
    OrientedThreeStage.exists_uniform_initial_scalar_bound_of_isometry.{u, u} P₀ g₀
  refine ⟨min aSing τ, Qb, lt_min haSing hτ, ?_⟩
  intro B p₀ δbound ρbound H hH
  obtain ⟨A⟩ := hH.1
  obtain ⟨p, -, -, -, -, -, records, -⟩ := hH.2.2.2.1
  have hsing : ∀ j : Fin H.toHistory.eventCount, (H.toHistory.event j).incoming.SingularEndpoint :=
    fun j => (records j).singular
  have hzero : ∀ k : Fin (H.eventCount + 1), ∀ t : ℝ, H.time k ≤ t → t < min aSing τ → k = 0 := by
    intro k t hkt ht
    by_contra hk
    have h₁ : aSing ≤ H.time k :=
      ObservedHistory.le_time_of_ne_zero hsingTime H.toHistory A hsing hk
    have h₂ : t < aSing := ht.trans_le (min_le_left _ _)
    linarith
  refine ⟨fun j t y hjt hts htη => ?_, fun s G hG t y hlt hts htη => ?_⟩
  · exact (ObservedHistory.scalar_lt_of_stage_eq_zero hscalar H.toHistory A
      (hzero j.castSucc t hjt htη) (H.toHistory.event j).incoming (H.event_initial j) hjt
      (htη.le.trans (min_le_right _ _)) hts y).le
  · exact (ObservedHistory.scalar_lt_of_stage_eq_zero hscalar H.toHistory A
      (hzero (Fin.last H.eventCount) t hlt htη) G hG hlt
      (htη.le.trans (min_le_right _ _)) hts y).le

theorem RetainedCoreHistory.tendsto_scalar_mul_time_atTop_of_inCutoffClass
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {B δb ρb s t : ℕ → ℝ}
    {p₀ : ℕ → CutoffParameters} {H : ℕ → RetainedCoreHistory.{u}}
    (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ (B n) (p₀ n) (δb n) (ρb n))
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) ≤ t n ∧ t n < s n)
    (hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop) :
    Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop := by
  obtain ⟨η₀, K, hη₀, hwindow⟩ := exists_scalar_le_before_initial_window P₀ g₀
  have hlow : ∀ᶠ n in atTop,
      (G n).flow.scalar (t n) (y n) * η₀ ≤ (G n).flow.scalar (t n) (y n) * t n := by
    filter_upwards [hR.eventually_gt_atTop K, hR.eventually_ge_atTop 0] with n hK h0
    refine mul_le_mul_of_nonneg_left (le_of_not_gt fun hlt => ?_) h0
    exact not_le.mpr hK ((hwindow (B n) (p₀ n) (δb n) (ρb n) (H n) (hH n)).2 (s n) (G n) (hG n)
      (t n) (y n) (ht n).1 (ht n).2 hlt)
  exact tendsto_atTop_mono' atTop hlow (hR.atTop_mul_const hη₀)

theorem RetainedCoreHistory.tendsto_scalar_mul_earlier_time_atTop_of_inCutoffClass
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {B δb ρb s t t₀ : ℕ → ℝ}
    {p₀ : ℕ → CutoffParameters} {H : ℕ → RetainedCoreHistory.{u}}
    (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ (B n) (p₀ n) (δb n) (ρb n))
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) ≤ t n ∧ t n < s n)
    (hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop) {C : ℝ}
    (hgap : ∀ n, (G n).flow.scalar (t n) (y n) * (t n - t₀ n) ≤ C) :
    Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t₀ n) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right atTop (-C)
    (tendsto_scalar_mul_time_atTop_of_inCutoffClass hH G hG y ht hR))
  have h := hgap n
  rw [mul_sub] at h
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
