import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace BackwardPointTrace

variable {H : ObservedHistory.{u}}
    {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}

private theorem normSq0S_point_eq_of_stage_eq
    {j k : Fin (H.eventCount + 1)} (heq : j = k)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (hj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t)
    (hk : H.activeStage a ≤ k) (hkt : k ≤ H.activeStage t) (s : ℝ) :
    normSq0S (H.stageMetric j s) (A.point j hj hjt) 4
      (metricRm04At (H.stageMetric j s) (A.point j hj hjt)) =
    normSq0S (H.stageMetric k s) (A.point k hk hkt) 4
      (metricRm04At (H.stageMetric k s) (A.point k hk hkt)) := by
  subst k
  rfl

def isRmControlled (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
    (H.activeStage_mono hat) p) (r : ℝ) : Prop :=
  (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t),
    r ^ 4 * normSq0S (H.stageMetric (H.activeStage s) s)
      (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
      (metricRm04At (H.stageMetric (H.activeStage s) s)
        (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))) ≤ 1) ∧
  ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
    let x : (H.event i).incoming.terminalRegularOpen :=
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩
    r ^ 4 * normSq0S (H.event i).terminal.metric x 4
      (metricRm04At (H.event i).terminal.metric x) ≤ 1

theorem isRmControlled.restrictFirst
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p) {r r' : ℝ} (hA : A.isRmControlled (hat := hat) r)
    (hr' : 0 ≤ r') (hrr' : r' ≤ r)
    {b : Icc (0 : ℝ) H.horizon} (hab : a ≤ b) (hbt : b ≤ t) :
    (A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)).isRmControlled (hat := hbt) r' := by
  have hpow := pow_le_pow_left₀ hr' hrr' 4
  constructor
  · intro s hbs hst
    exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
      (hA.1 s (hab.trans hbs) hst)
  · intro i hf hl
    exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
      (hA.2 i ((H.activeStage_mono hab).trans hf) hl)

end BackwardPointTrace

namespace ObservedHistory

variable (H : ObservedHistory.{u})

def isParabolicallyRmControlledBall (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ) : Prop :=
  0 < r ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
    (a : ℝ) = (t : ℝ) - r ^ 2 ∧
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          A.isRmControlled (hat := hat) r

theorem isParabolicallyRmControlledBall.radius_sq_le_time
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (h : H.isParabolicallyRmControlledBall t p r) : r ^ 2 ≤ (t : ℝ) := by
  obtain ⟨_, a, _, heq, _⟩ := h
  have := a.property.1
  rw [heq] at this
  linarith

theorem isParabolicallyRmControlledBall.mono_radius
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r r' : ℝ}
    (h : H.isParabolicallyRmControlledBall t p r) (hr' : 0 < r') (hrr' : r' ≤ r) :
    H.isParabolicallyRmControlledBall t p r' := by
  obtain ⟨hr, a, hat, heq, htrace⟩ := h
  have hpow : r' ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr'.le hrr' 2
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - r' ^ 2, by have := a.property.1; rw [heq] at this; linarith,
      (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  have hab : a ≤ b := by change (a : ℝ) ≤ (t : ℝ) - r' ^ 2; rw [heq]; linarith
  have hbt : b ≤ t := show (t : ℝ) - r' ^ 2 ≤ t from sub_le_self _ (sq_nonneg _)
  refine ⟨hr', b, hbt, rfl, ?_⟩
  intro x hx
  obtain ⟨A, hA⟩ := htrace x (riemannianBallOf_mono _ _ hrr' hx)
  exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt),
    hA.restrictFirst A hr'.le hrr' hab hbt⟩


theorem isParabolicallyRmControlledBall_of_closedPrefixAt
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ))
    (B : Perelman.FlowMetricBall (H.closedPrefixAt t ht).flow
      ⟨t, (H.activeStage_time_le t), le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled) :
    H.isParabolicallyRmControlledBall t B.center B.radius := by
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - B.radius ^ 2,
    (H.time_nonneg _).trans (hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩).1,
    (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  have hat : a ≤ t := show (t : ℝ) - B.radius ^ 2 ≤ t from sub_le_self _ (sq_nonneg _)
  have hstage (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t) :
      H.activeStage s = H.activeStage t := by
    apply le_antisymm (H.activeStage_mono hst)
    apply H.le_activeStage
    exact (hB.1 ⟨has, hst⟩).1
  have hea : H.activeStage a = H.activeStage t := hstage a le_rfl hat
  refine ⟨B.radius_pos, a, hat, rfl, ?_⟩
  intro x hx
  let A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x :=
    { point := fun j _ hj => by
        have he : j = H.activeStage t := le_antisymm hj (by simpa only [hea] using ‹H.activeStage a ≤ j›)
        exact he.symm ▸ x
      endpoint_eq := rfl
      crossing := by
        intro i hf hl
        have hi := i.castSucc_lt_succ
        rw [hea] at hf
        exact False.elim ((not_lt_of_ge (hl.trans hf)) hi) }
  refine ⟨A, ?_, ?_⟩
  · intro s has hst
    have hs := hstage s has hst
    have hxB : x ∈ B.set := by
      change x ∈ riemannianBallOf ((H.closedPrefixAt t ht).flow.base.metric t) B.center B.radius
      rwa [H.closedPrefixAt_metric]
    have hb := hB.2 s ⟨has, hst⟩ x hxB
    change B.radius ^ 4 * normSq0S ((H.closedPrefixAt t ht).flow.base.metric s) x 4
      (metricRm04At ((H.closedPrefixAt t ht).flow.base.metric s) x) ≤ 1 at hb
    rw [H.closedPrefixAt_metric] at hb
    rw [A.normSq0S_point_eq_of_stage_eq (hat := hat) hs
      (H.activeStage_mono has) (H.activeStage_mono hst) (H.activeStage_mono hat) le_rfl]
    simpa only [A.endpoint_eq] using hb
  · intro i hf hl
    have hi := i.castSucc_lt_succ
    rw [hea] at hf
    exact False.elim ((not_lt_of_ge (hl.trans hf)) hi)

theorem exists_pos_isParabolicallyRmControlledBall_of_time_gt_stageTime
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : (H.stageAt t).Carrier, H.isParabolicallyRmControlledBall t p r := by
  let S := (H.closedPrefixAt t ht).flow
  have hS : IsSolutionOn S := (H.closedPrefixAt t ht).equation
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ :
      IsCompact (univ : Set (H.stageAt t).Carrier))).bddAbove_image hS.continuousOn_rmNormSq
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < (t : ℝ) - H.time (H.activeStage t) ∧
      r ^ 4 * C < 1 := by
    have hpow : Continuous (fun r : ℝ => r ^ 2) := continuous_id.pow 2
    have hmul : Continuous (fun r : ℝ => r ^ 4 * C) := (continuous_id.pow 4).mul_const C
    exact ((hpow.continuousAt.eventually_lt_const (by simpa using sub_pos.mpr ht))).and
      (hmul.continuousAt.eventually_lt_const (by norm_num))
  have hsmall' : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      r ^ 2 < (t : ℝ) - H.time (H.activeStage t) ∧ r ^ 4 * C < 1 :=
    hsmall.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hrpos, hrsmall⟩ := (hpos.and hsmall').exists
  refine ⟨r, hrpos, ?_⟩
  intro p
  let B : Perelman.FlowMetricBall S ⟨t, H.activeStage_time_le t, le_rfl⟩ := ⟨p, r, hrpos⟩
  have hB : B.IsParabolicallyRmControlled := by
    refine ⟨?_, ?_⟩
    · intro s hs
      change H.time (H.activeStage t) ≤ s ∧ s ≤ (t : ℝ)
      exact ⟨by have hleft : (t : ℝ) - r ^ 2 ≤ s := hs.1; linarith [hrsmall.1], hs.2⟩
    · intro s hs x hx
      have hs' : s ∈ Icc (H.time (H.activeStage t)) (t : ℝ) :=
        ⟨by have hleft : (t : ℝ) - r ^ 2 ≤ s := hs.1; linarith [hrsmall.1], hs.2⟩
      have hb : Perelman.FlowMetricBall.rmNormSq S s x ≤ C := hC ⟨(s, x), ⟨hs', mem_univ _⟩, rfl⟩
      exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ r ^ 4)).trans hrsmall.2.le
  exact H.isParabolicallyRmControlledBall_of_closedPrefixAt t ht B hB


theorem csSup_parabolicallyRmControlledBall_mem_Icc
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {q₀ R : ℝ}
    (hq₀ : H.isParabolicallyRmControlledBall t p q₀) (hR : q₀ ≤ R) :
    sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r} ∈ Icc q₀ R := by
  let S := {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}
  have hmem : q₀ ∈ S := ⟨⟨le_rfl, hR⟩, hq₀⟩
  have hbdd : BddAbove S := ⟨R, fun r hr => hr.1.2⟩
  exact ⟨le_csSup hbdd hmem, csSup_le ⟨q₀, hmem⟩ (fun r hr => hr.1.2)⟩

theorem isParabolicallyRmControlledBall_of_lt_csSup
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {q₀ R q : ℝ}
    (hq₀ : H.isParabolicallyRmControlledBall t p q₀) (hR : q₀ ≤ R)
    (hq : 0 < q)
    (hqs : q < sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}) :
    H.isParabolicallyRmControlledBall t p q := by
  have hmem : q₀ ∈ {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r} :=
    ⟨⟨le_rfl, hR⟩, hq₀⟩
  obtain ⟨r, hr, hqr⟩ := exists_lt_of_lt_csSup ⟨q₀, hmem⟩ hqs
  exact hr.2.mono_radius H hq hqr.le

theorem isParabolicallyRmControlledBall_of_csSup_eq_twice
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {q₀ ρ : ℝ}
    (hq₀ : H.isParabolicallyRmControlledBall t p q₀) (hq₀ρ : q₀ ≤ 2 * ρ)
    (hs : sSup {r ∈ Icc q₀ (2 * ρ) | H.isParabolicallyRmControlledBall t p r} = 2 * ρ) :
    H.isParabolicallyRmControlledBall t p ρ := by
  have hρ : 0 < ρ := by have := hq₀.1; linarith
  exact H.isParabolicallyRmControlledBall_of_lt_csSup hq₀ hq₀ρ hρ (by rw [hs]; linarith)


theorem isParabolicallyRmControlledBall.terminal_curvature_bound
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (h : H.isParabolicallyRmControlledBall t p r)
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) :
    r ^ 4 * normSq0S (H.stageMetric (H.activeStage t) t) x 4
      (metricRm04At (H.stageMetric (H.activeStage t) t) x) ≤ 1 := by
  obtain ⟨_, a, hat, _, htrace⟩ := h
  obtain ⟨A, hA⟩ := htrace x hx
  have hbound := hA.1 t hat le_rfl
  have he : A.point (H.activeStage t) (H.activeStage_mono hat) (H.activeStage_mono le_rfl) = x :=
    A.endpoint_eq
  rw [he] at hbound
  exact hbound

theorem curvature_bound_csSup_parabolicallyRmControlledBall
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {q₀ R : ℝ}
    (hq₀ : H.isParabolicallyRmControlledBall t p q₀) (hR : q₀ ≤ R)
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p
      (sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r})) :
    (sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}) ^ 4 *
      normSq0S (H.stageMetric (H.activeStage t) t) x 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) x) ≤ 1 := by
  let s := sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}
  have hs : 0 < s := hq₀.1.trans_le (H.csSup_parabolicallyRmControlledBall_mem_Icc hq₀ hR).1
  have hdist : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x).toReal < s :=
    ENNReal.toReal_lt_of_lt_ofReal hx
  have hmax : max (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x).toReal 0 < s :=
    max_lt hdist hs
  have hc : ContinuousAt (fun r : ℝ => r ^ 4 *
      normSq0S (H.stageMetric (H.activeStage t) t) x 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) x)) s := by fun_prop
  have : (𝓝[<] s).NeBot := inferInstance
  apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] s ≤ 𝓝 s))
  filter_upwards [Ioo_mem_nhdsLT hmax] with r hr
  have hrpos : 0 < r := (le_max_right _ _).trans_lt hr.1
  have hx' : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    exact (ENNReal.lt_ofReal_iff_toReal_lt (show
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≠ ⊤ from hx.ne_top)).mpr
      ((le_max_left _ _).trans_lt hr.1)
  exact (H.isParabolicallyRmControlledBall_of_lt_csSup hq₀ hR hrpos hr.2).terminal_curvature_bound H x hx'

theorem crossed_event_iff_mem_Ioc (H : ObservedHistory.{u})
    (a t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) :
    (H.activeStage a ≤ i.castSucc ∧ i.succ ≤ H.activeStage t) ↔
      H.time i.succ ∈ Ioc (a : ℝ) (t : ℝ) := by
  have ha := H.event_reached_iff a i
  have ht := H.event_reached_iff t i
  constructor
  · intro h
    constructor
    · apply lt_of_not_ge
      intro hbad
      have hai := ha.mp hbad
      have hval : (H.activeStage a).val ≤ i.val := h.1
      omega
    · apply ht.mpr
      have hval : i.val + 1 ≤ (H.activeStage t).val := h.2
      omega
  · intro h
    constructor
    · change (H.activeStage a).val ≤ i.val
      by_contra hbad
      have hlt : i.val < (H.activeStage a).val := by omega
      exact (not_le_of_gt h.1) (ha.mpr hlt)
    · change i.val + 1 ≤ (H.activeStage t).val
      exact Nat.succ_le_of_lt (ht.mp h.2)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (K : Set G.terminalRegularOpen)

private theorem rmNormSq_incomingFootprint_slab
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (v : ℝ) (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
    normSq0S (((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K)) z 4
      (metricRm04At (((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K)) z) =
    normSq0S ((H.event j).terminal.extendedMetric v)
      (H.backwardSurvivorTerminalMap first last hle j hf hl z.val.val) 4
      (metricRm04At ((H.event j).terminal.extendedMetric v)
        (H.backwardSurvivorTerminalMap first last hle j hf hl z.val.val)) := by
  rw [Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen,
    Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
  exact normSq0S_metricRm04At_localPullMetric _ _ _ _

private theorem rmNormSq_incomingFootprint_last
    (v : ℝ) (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
    normSq0S ((H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K)) z 4
      (metricRm04At ((H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K)) z) =
    normSq0S (L.extendedMetric v)
      (H.backwardSurvivorIncomingFootprintMap first last hle G K z) 4
      (metricRm04At (L.extendedMetric v)
        (H.backwardSurvivorIncomingFootprintMap first last hle G K z)) := by
  rw [Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
  exact normSq0S_metricRm04At_localPullMetric _ _ _ _

private theorem rmNormSq_incomingFootprint_slab_before
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (v : ℝ) (hv : v < H.time j.succ)
    (hg : gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (z : H.backwardSurvivorIncomingFootprint first last hle G K)
    (A : BackwardPointTrace H first last hle
      (H.backwardSurvivorIncomingFootprintMap first last hle G K z).val) :
    normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) =
      normSq0S (H.stageMetric j.castSucc v) (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) 4
        (metricRm04At (H.stageMetric j.castSucc v)
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) := by
  rw [hg, H.rmNormSq_incomingFootprint_slab, (H.event j).terminal.extendedMetric_before hv,
    Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen, H.backwardSurvivorTerminalMap_val,
    H.backwardSurvivorMap_eq_point first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl)
      z.val.val A]
  simp only [stageMetric, Fin.lastCases_castSucc]

private theorem trace_rmNormSq_eq_of_stage_eq
    {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) (v : ℝ) :
    normSq0S (H.stageMetric j v) (A.point j hj hjl) 4
      (metricRm04At (H.stageMetric j v) (A.point j hj hjl)) =
    normSq0S (H.stageMetric k v) (A.point k hk hkl) 4
      (metricRm04At (H.stageMetric k v) (A.point k hk hkl)) := by
  subst k
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem isParabolicallyRmControlledBall_of_incomingFootprint
    (a t : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t)
    (hfirst : H.time first ≤ (a : ℝ))
    (G : (H.stage (H.activeStage t)).IncomingSlab (H.time (H.activeStage t)) t)
    (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first (H.activeStage t) hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
    (hlast : ∀ v ∈ Icc (H.time (H.activeStage t)) t,
      gflow v = (H.backwardSurvivorIncomingMetric first (H.activeStage t) hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
    (hmatch : ∀ v ∈ Icc (H.time (H.activeStage t)) t,
      L.extendedMetric v = (H.stageMetric (H.activeStage t) v).restrictOpen G.terminalRegularOpen)
    (p : (H.stageAt t).Carrier) {r : ℝ} (hr : 0 < r)
    (ha : (a : ℝ) = (t : ℝ) - r ^ 2)
    (hball : riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ⊆
      range (fun z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K =>
        (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val))
    (hbound : ∀ v ∈ Icc (a : ℝ) t,
      ∀ z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
        r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1) :
    H.isParabolicallyRmControlledBall t p r := by
  have hfa : first ≤ H.activeStage a := H.le_activeStage a first hfirst
  refine ⟨hr, a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := hball hx
  let A : BackwardPointTrace H first (H.activeStage t) hle
      (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val :=
    Classical.choice z.val.val.property
  let A' := A.restrictFirst hfa (H.activeStage_mono hat)
  refine ⟨A', ?_, ?_⟩
  · intro v hav hvt
    have hfv : first ≤ H.activeStage v := hfa.trans (H.activeStage_mono hav)
    have hvl : H.activeStage v ≤ H.activeStage t := H.activeStage_mono hvt
    have hb := hbound v ⟨hav, hvt⟩ z
    by_cases hsame : H.activeStage v = H.activeStage t
    · have hvlast : H.time (H.activeStage t) ≤ (v : ℝ) := by
        rw [← hsame]
        exact H.activeStage_time_le v
      rw [hlast v ⟨hvlast, hvt⟩, H.rmNormSq_incomingFootprint_last, hmatch v ⟨hvlast, hvt⟩,
        Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen] at hb
      change r ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) hfv hvl) 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) (A.point (H.activeStage v) hfv hvl)) ≤ 1
      rw [H.trace_rmNormSq_eq_of_stage_eq first (H.activeStage t) hle hsame A
        hfv hvl hle le_rfl v, A.endpoint_eq]
      exact hb
    · have hlt : H.activeStage v < H.activeStage t := lt_of_le_of_ne hvl hsame
      let j : Fin H.eventCount := ⟨(H.activeStage v).val, by have := (H.activeStage t).isLt; omega⟩
      have hj : j.castSucc = H.activeStage v := rfl
      have hfl : first ≤ j.castSucc := hfv
      have hjl : j.succ ≤ H.activeStage t := hlt
      have hvj : (v : ℝ) ∈ Ico (H.time j.castSucc) (H.time j.succ) :=
        ⟨H.activeStage_time_le v, H.activeStage_before_next v j.isLt⟩
      rw [H.rmNormSq_incomingFootprint_slab_before first (H.activeStage t) hle G K gflow
        j hfl hjl v hvj.2 (hslabs j hfl hjl v ⟨hvj.1, hvj.2.le⟩) z A] at hb
      have hh := H.trace_rmNormSq_eq_of_stage_eq (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) hj.symm A' (H.activeStage_mono hav) (H.activeStage_mono hvt)
        (H.activeStage_mono hav) (j.castSucc_lt_succ.le.trans hjl) v
      rw [hh]
      exact hb
  · intro j hf hl
    have hjf : first ≤ j.castSucc := hfa.trans hf
    have hjtime := (H.crossed_event_iff_mem_Ioc a t j).mp ⟨hf, hl⟩
    have hb := hbound (H.time j.succ) ⟨hjtime.1.le, hjtime.2⟩ z
    rw [hslabs j hjf hl _ ⟨(H.time_strictMono j.castSucc_lt_succ).le, le_rfl⟩,
      H.rmNormSq_incomingFootprint_slab, (H.event j).terminal.extendedMetric_terminal] at hb
    have he : H.backwardSurvivorTerminalMap first (H.activeStage t) hle j hjf hl z.val.val =
        ⟨A'.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl),
          (A'.crossing j hf hl).mem_terminalRegularRegion (H.event j)⟩ := by
      apply Subtype.ext
      exact H.backwardSurvivorMap_eq_point first (H.activeStage t) hle j.castSucc hjf
        (j.castSucc_lt_succ.le.trans hl) z.val.val A
    rw [he] at hb
    exact hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem closedPrefixAt_endpointTerminalLimitMetric_extendedMetric
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ))
    {v : ℝ} (hv : v ≤ (t : ℝ)) :
    ((H.closedPrefixAt t ht).endpointTerminalLimitMetric (H.stageAt t)).extendedMetric v =
      (H.stageMetric (H.activeStage t) v).restrictOpen
        ((H.closedPrefixAt t ht).restrictIncoming le_rfl (H.closedPrefixAt t ht).lt le_rfl).terminalRegularOpen := by
  rw [OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le _ hv,
    H.closedPrefixAt_metric]

theorem isParabolicallyRmControlledBall_of_closedPrefixAt_incomingFootprint
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < (t : ℝ))
    (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) :
    let G := (H.closedPrefixAt t ht).restrictIncoming le_rfl (H.closedPrefixAt t ht).lt le_rfl
    let L := (H.closedPrefixAt t ht).endpointTerminalLimitMetric (H.stageAt t)
    ∀ (K : Set G.terminalRegularOpen)
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)),
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first (H.activeStage t) hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) →
    (∀ v ∈ Icc (H.time (H.activeStage t)) t,
      gflow v = (H.backwardSurvivorIncomingMetric first (H.activeStage t) hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)) →
    ∀ (p : (H.stageAt t).Carrier) (r Δ C : ℝ), 0 < r → r ^ 2 ≤ Δ →
    H.time first ≤ (t : ℝ) - Δ →
    riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ⊆
      range (fun z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K =>
        (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val) →
    (∀ v ∈ Icc ((t : ℝ) - Δ) t,
      ∀ z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K,
        DifferentialGeometry.Tensor0SBundle.normSq0S (gflow v) z 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (gflow v) z) ≤ C) →
    r ^ 4 * C ≤ 1 → H.isParabolicallyRmControlledBall t p r := by
  intro G L K gflow hslabs hlast p r Δ C hr hΔ hroom hball hbound hscale
  have hfirst : H.time first ≤ (t : ℝ) - r ^ 2 := hroom.trans (sub_le_sub_left hΔ _)
  let a : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - r ^ 2, (H.time_nonneg first).trans hfirst,
      (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  have hat : a ≤ t := show (t : ℝ) - r ^ 2 ≤ t from sub_le_self _ (sq_nonneg _)
  apply H.isParabolicallyRmControlledBall_of_incomingFootprint a t hat first hle hfirst
    G L K gflow hslabs hlast
    (fun v hv => H.closedPrefixAt_endpointTerminalLimitMetric_extendedMetric t ht hv.2)
    p hr rfl hball
  intro v hv z
  exact (mul_le_mul_of_nonneg_left (hbound v
    ⟨(sub_le_sub_left hΔ _).trans hv.1, hv.2⟩ z) (by positivity : 0 ≤ r ^ 4)).trans hscale

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
