import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
import DifferentialGeometry.Topology.Embedding.CompactFrontier
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

theorem isParabolicallyRmControlledBall_of_incomingFootprint_on_ball
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
        (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val ∈
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p r →
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
    have hb := hbound v ⟨hav, hvt⟩ z hx
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
    have hb := hbound (H.time j.succ) ⟨hjtime.1.le, hjtime.2⟩ z hx
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
  exact H.isParabolicallyRmControlledBall_of_incomingFootprint_on_ball a t hat first hle
    hfirst G L K gflow hslabs hlast hmatch p hr ha hball (fun v hv z _ => hbound v hv z)

private local instance (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem isParabolicallyRmControlledBall_of_incomingFootprint_flow_ball
    (t : Icc (0 : ℝ) H.horizon) (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t)
    {c : ℝ} (hfirst : H.time first ≤ c) (hct : c ≤ (t : ℝ))
    (G : (H.stage (H.activeStage t)).IncomingSlab (H.time (H.activeStage t)) t)
    (L : G.TerminalLimitMetric) (K : Set G.terminalRegularOpen)
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K)
      (RealTimeInterval.closed c t hct))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric v = ((H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first (H.activeStage t) hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
    (hlast : ∀ v ∈ Icc (H.time (H.activeStage t)) t,
      S.base.metric v = (H.backwardSurvivorIncomingMetric first (H.activeStage t) hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K))
    (hmatch : ∀ v ∈ Icc (H.time (H.activeStage t)) t,
      L.extendedMetric v = (H.stageMetric (H.activeStage t) v).restrictOpen G.terminalRegularOpen)
    (p : (H.stageAt t).Carrier)
    (B : Perelman.FlowMetricBall S ⟨t, hct, le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled)
    (himage : (fun z : H.backwardSurvivorIncomingFootprint first (H.activeStage t) hle G K =>
        (H.backwardSurvivorIncomingFootprintMap first (H.activeStage t) hle G K z).val) '' B.set =
      riemannianBallOf (H.stageMetric (H.activeStage t) t) p B.radius) :
    H.isParabolicallyRmControlledBall t p B.radius := by
  have hstart : c ≤ (t : ℝ) - B.radius ^ 2 :=
    (hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩).1
  let a : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - B.radius ^ 2, (H.time_nonneg first).trans (hfirst.trans hstart),
      (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  have hat : a ≤ t := show (t : ℝ) - B.radius ^ 2 ≤ t from sub_le_self _ (sq_nonneg _)
  apply H.isParabolicallyRmControlledBall_of_incomingFootprint_on_ball a t hat first hle
    (hfirst.trans hstart) G L K S.base.metric hslabs hlast hmatch p B.radius_pos rfl
  · rw [← himage]
    exact image_subset_range _ _
  · intro v hv z hz
    rw [← himage] at hz
    obtain ⟨w, hw, hwe⟩ := hz
    have hwz : w = z :=
      H.backwardSurvivorIncomingFootprintMap_injective first (H.activeStage t) hle G K
        (Subtype.ext hwe)
    subst w
    exact hB.2 v hv z hw

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

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

open _root_.Manifold TopologicalSpace in
private theorem exists_common_flow_of_parabolicallyRmControlledBall_of_time_gt
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (ht : H.time (H.activeStage t) < t.val) (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) := by
  classical
  obtain ⟨hr, a, hat, ha, htraces⟩ := hball
  let U : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat
  let G := (H.closedPrefixAt t ht).restrictIncoming le_rfl (H.closedPrefixAt t ht).lt le_rfl
  let L := (H.closedPrefixAt t ht).endpointTerminalLimitMetric (H.stageAt t)
  have hG (v : ℝ) : G.flow.base.metric v = H.stageMetric last v := H.closedPrefixAt_metric t ht v
  have hinit : G.flow.base.metric (H.time last) = H.initialMetric last := H.closedPrefixAt_initial t ht
  have hsurv (x : U) : x.val ∈ H.backwardSurvivorDomain first last hle :=
    ⟨(htraces x.val x.property).choose⟩
  let Ψ₀ : U → H.backwardSurvivorDomain first last hle := fun x => ⟨x.val, hsurv x⟩
  have hΨ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ₀ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  have hregular (x : U) : Ψ₀ x ∈ H.backwardSurvivorIncomingDomain first last hle G := by
    change x.val ∈ G.terminalRegularRegion
    rw [(H.closedPrefixAt t ht).terminalRegularRegion_eq_univ]
    exact mem_univ _
  let Ψ : U → H.backwardSurvivorIncomingDomain first last hle G := fun x => ⟨Ψ₀ x, hregular x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hregular (hΨ₀ x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) ∘ Ψ
  have hf (j : H.StageInterval first last) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΨ
  have hflast (x : U) : f ⟨last, hle, le_rfl⟩ x = x.val :=
    H.backwardSurvivorMap_last first last hle (Ψ₀ x)
  obtain ⟨gflow, hslabs, hlast, _, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  let S₀ : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) t.val
        ((H.time_strictMono.monotone hle).trans ht.le)) := { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t.val hat)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) le_rfl)
    (Ioo_subset_Ioo (H.activeStage_time_le a) le_rfl)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t.val)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    rcases lt_or_eq_of_le hv.2 with hvt | rfl
    · rw [H.metric_eq_stage_pullback_of_backwardSurvivorIncoming first last hle t.val G L gflow
        (fun i hi hl v hv => hslabs i hi hl v (Ico_subset_Icc_self hv))
        (fun v hv => hlast v (Ico_subset_Icc_self hv)) (fun v _ => hG v)
        j.val j.property.1 j.property.2 hjv hvt]
      exact localPullMetric_comp (H.stageMetric j.val v)
        (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) Ψ
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
          (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΨ (hf j)
    · have hj : j = ⟨last, hle, le_rfl⟩ :=
        Subtype.ext ((H.mem_stageDomain_iff t j.val).mp hjv).symm
      subst j
      rw [hlast _ ⟨ht.le, le_rfl⟩, ObservedHistory.backwardSurvivorIncomingMetric]
      have hend : L.extendedMetric t.val =
          (H.stageMetric last t.val).restrictOpen G.terminalRegularOpen :=
        H.closedPrefixAt_endpointTerminalLimitMetric_extendedMetric t ht le_rfl
      rw [hend, ← localPullMetric_subtype_val]
      let k := H.backwardSurvivorIncomingMap first last hle G
      have hk := H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G
      have hv := isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen
      have hc := isLocalDiffeomorph_comp hv (isLocalDiffeomorph_comp hk hΨ)
      rw [localPullMetric_comp _ k Ψ hk hΨ (isLocalDiffeomorph_comp hk hΨ),
        localPullMetric_comp _ Subtype.val (k ∘ Ψ) hv (isLocalDiffeomorph_comp hk hΨ) hc]
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [localPullMetric_inner, localPullMetric_inner]
      have hfend : f ⟨last, hle, le_rfl⟩ = Subtype.val ∘ (k ∘ Ψ) := by
        funext y
        exact H.backwardSurvivorMap_last first last hle (Ψ y).val
      exact congrArg (fun F : U → (H.stage last).Carrier =>
        (H.stageMetric last t.val).inner (F x)
          (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) hfend.symm
  refine ⟨a, hat, ha, U, rfl, f, hf, ?_, ?_, hflast, S, hS, hmetric, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (fun x y hxy => Subtype.ext (congrArg (fun z : H.backwardSurvivorDomain first last hle => z.val) hxy))
  · intro i hi hl x
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ψ₀ x)
  · intro v hv x
    let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval first last :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    change r ^ 4 * normSq0S (S.base.metric v) x 4 (metricRm04At (S.base.metric v) x) ≤ 1
    rw [hmetric j v hv (H.activeStage_mem v'), normSq0S_metricRm04At_localPullMetric]
    obtain ⟨A, hA⟩ := htraces x.val x.property
    have hpoint : f j x = A.point j.val j.property.1 j.property.2 :=
      H.backwardSurvivorMap_eq_point first last hle j.val j.property.1 j.property.2 (Ψ₀ x) A
    rw [hpoint]
    exact hA.1 v' hav hvt

open _root_.Manifold TopologicalSpace in
theorem exists_common_flow_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) := by
  classical
  rcases lt_or_eq_of_le (H.activeStage_time_le t) with ht | ht
  · exact H.exists_common_flow_of_parabolicallyRmControlledBall_of_time_gt t ht p r hball
  obtain ⟨hr, a, hat, ha, htraces⟩ := hball
  have hatlt : a.val < t.val := by nlinarith [sq_pos_of_pos hr]
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat
  have hlt : first < last := lt_of_le_of_ne hle (by
    intro he
    have hleft := H.activeStage_time_le a
    change H.time first ≤ a.val at hleft
    rw [he, ht] at hleft
    exact (not_le_of_gt hatlt) hleft)
  let U : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  have hsurv (x : U) : x.val ∈ H.backwardSurvivorDomain first last hle :=
    ⟨(htraces x.val x.property).choose⟩
  let Ψ : U → H.backwardSurvivorDomain first last hle := fun x => ⟨x.val, hsurv x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Ψ
  have hf (j : H.StageInterval first last) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2) hΨ
  have hflast (x : U) : f ⟨last, hle, le_rfl⟩ x = x.val :=
    H.backwardSurvivorMap_last first last hle (Ψ x)
  obtain ⟨gflow, hslabs, hstages, _, hsol⟩ :=
    H.exists_backwardSurvivor_isSolutionOn first last hlt
  let S₀ : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle)
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le) :=
    { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t.val hat)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) ht.ge)
    (Ioo_subset_Ioo (H.activeStage_time_le a) ht.ge)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t.val)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    let q := H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2
    have hq := H.backwardSurvivorMap_isLocalDiffeomorph first last hle
      j.val j.property.1 j.property.2
    by_cases hj : j.val = last
    · have hvlast : v = H.time last :=
        le_antisymm (hv.2.trans ht.ge) (hj ▸ H.time_le_of_mem_stageDomain hjv)
      have hvj : v = H.time j.val := hvlast.trans (congrArg H.time hj).symm
      rw [hvj, hstages j.val j.property.1 j.property.2]
      rw [ObservedHistory.backwardSurvivorInitialMetric, ← H.stageMetric_initial]
      exact localPullMetric_comp _ q Ψ hq hΨ (hf j)
    · have hjlt : j.val < last := lt_of_le_of_ne j.property.2 hj
      rcases j with ⟨j, hjfirst, hjlast⟩
      cases j using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hjlt)
      | cast i =>
        have hil : i.succ ≤ last := hjlt
        have htt : v ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
          simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hjv
        rw [hslabs i hjfirst hil v (Ico_subset_Icc_self htt),
          ObservedHistory.backwardSurvivorSlabMetric,
          (H.event i).terminal.extendedMetric_before htt.2]
        have hinner :
            localPullMetric (((H.event i).incoming.flow.base.metric v).restrictOpen
              (H.event i).incoming.terminalRegularOpen)
              (H.backwardSurvivorTerminalMap first last hle i hjfirst hil)
              (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hjfirst hil) =
            localPullMetric ((H.event i).incoming.flow.base.metric v) q hq := by
          rw [← localPullMetric_subtype_val]
          exact localPullMetric_comp _ _ _ _ _ hq
        rw [hinner]
        simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using
          (localPullMetric_comp ((H.event i).incoming.flow.base.metric v) q Ψ hq hΨ
            (hf ⟨i.castSucc, hjfirst, hjlast⟩))
  refine ⟨a, hat, ha, U, rfl, f, hf, ?_, ?_, hflast, S, hS, hmetric, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (fun x y hxy => Subtype.ext (congrArg (fun z : H.backwardSurvivorDomain first last hle => z.val) hxy))
  · intro i hi hl x
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ψ x)
  · intro v hv x
    let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval first last :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    change r ^ 4 * normSq0S (S.base.metric v) x 4 (metricRm04At (S.base.metric v) x) ≤ 1
    rw [hmetric j v hv (H.activeStage_mem v'), normSq0S_metricRm04At_localPullMetric]
    obtain ⟨A, hA⟩ := htraces x.val x.property
    have hpoint : f j x = A.point j.val j.property.1 j.property.2 :=
      H.backwardSurvivorMap_eq_point first last hle j.val j.property.1 j.property.2 (Ψ x) A
    rw [hpoint]
    exact hA.1 v' hav hvt

open _root_.Manifold TopologicalSpace in
theorem exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) ∧
              S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U ∧
              ∃ (pU : U) (K : Set U), pU.val = p ∧
                Subtype.val '' K = riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ∧
                IsCompact K ∧ pU ∈ interior K ∧
                ∀ x ∈ frontier K,
                  ENNReal.ofReal (r / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := by
  classical
  have hr : 0 < r := hball.1
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_parabolicallyRmControlledBall t p r hball
  have hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U := by
    have h := hmetric ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ t
      ⟨hat, le_rfl⟩ (H.activeStage_mem t)
    have heq : f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ = Subtype.val :=
      funext hlast
    simpa only [heq, localPullMetric_subtype_val] using h
  have hpU : p ∈ U := by
    change p ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let pU : U := ⟨p, hpU⟩
  let K : Set U := Subtype.val ⁻¹'
    riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)
  have hclosed : IsClosed (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)) :=
    Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _
  have hsubset : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ⊆
      range (Subtype.val : U → (H.stageAt t).Carrier) := by
    rw [Subtype.range_coe, hU]
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hK : IsCompact K :=
    U.isOpenEmbedding'.isEmbedding.isInducing.isCompact_preimage' hclosed.isCompact hsubset
  have himage : Subtype.val '' K =
      riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) :=
    image_preimage_eq_of_subset hsubset
  have hpinterior : pU ∈ interior K := by
    have h := Geometry.Metric.mem_interior_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) p (by linarith : 0 < r / 2)
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding
        U.isOpenEmbedding' K] at h
    obtain ⟨x, hx, hxp⟩ := h
    exact (show x = pU from Subtype.ext hxp) ▸ hx
  refine ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm,
    hterminal, pU, K, rfl, himage, hK, hpinterior, ?_⟩
  intro x hx
  have hfrontier : x.val ∈ frontier
      (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)) := by
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
        U.isOpenEmbedding' hK]
    exact ⟨x, hx, rfl⟩
  have hdist := Geometry.Metric.riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf
    (H.stageMetric (H.activeStage t) t) p hfrontier
  rw [hterminal, ← hdist]
  exact riemannianEDistOf_le_restrictOpen
    (H.stageMetric (H.activeStage t) t) U pU x


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

open scoped BigOperators in
open _root_.Manifold TopologicalSpace _root_.MeasureTheory in
theorem exists_uniform_time_sum_stageRegularizedAction_gt_of_parabolicallyRmControlledBall
    (A B E r : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hr : 0 < r) :
    ∃ w : ℝ, 0 < w ∧ w ≤ r ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p r →
      ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
        ∃ U : Opens (H.stageAt t).Carrier,
          (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
          ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ H.activeStage t), ∀ x : U,
                (H.event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∃ S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat),
                IsSolutionOn S ∧
                (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                  ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                    S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
                (∀ v ∈ Icc a.val t.val, ∀ x : U,
                  r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) ∧
                S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U ∧
                ∃ (pU : U) (K : Set U), pU.val = p ∧
                  Subtype.val '' K = riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ∧
                  IsCompact K ∧ pU ∈ interior K ∧
                  (∀ x ∈ frontier K,
                    ENNReal.ofReal (r / 2) ≤ riemannianEDistOf (S.base.metric t) pU x) ∧
                  ∀ (first : Fin (H.eventCount + 1)) (v τ : ℝ),
                    0 < τ → τ ≤ w → τ ≤ v → v ≤ E →
                    ∀ (j : H.StageInterval (H.activeStage a) (H.activeStage t))
                      (hfirst : first ≤ j.val),
                    t.val - v ^ 2 ∈ H.stageDomain first →
                    t.val - τ ^ 2 ∈ H.stageDomain j.val →
                    ∀ α : (k : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage k.val).Carrier,
                    (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α k)) →
                    (∀ k, IntervalIntegrable (H.stageRegularizedLagrangian k.val t (α k)) volume
                      (H.regularizedStageStart t 0 k.val) (H.regularizedStageEnd t v k.val)) →
                    (∀ k, ∀ s ∈ Ioo
                      (H.regularizedStageStart t 0 k.val) (H.regularizedStageEnd t v k.val),
                      -B ≤ metricScalarAt (H.stageMetric k.val (t.val - s ^ 2)) (α k s)) →
                    α ⟨H.activeStage t, hfirst.trans j.property.2, le_rfl⟩ 0 = p →
                    (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
                      ∃ z : (H.event i).old,
                        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
                          (Real.sqrt (t.val - H.time i.succ)) ∧
                        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
                          (Real.sqrt (t.val - H.time i.succ))) →
                    α ⟨j.val, hfirst, j.property.2⟩ τ ∉ f j '' K →
                    A < ∑ k : H.StageInterval first (H.activeStage t),
                      H.stageRegularizedAction k.val t (α k)
                        (H.regularizedStageStart t 0 k.val) (H.regularizedStageEnd t v k.val) := by
  obtain ⟨w₁, hw₁, hmodel⟩ :=
    exists_uniform_time_sum_stageRegularizedAction_gt_of_point_outside_controlled_image.{u, u}
      A B E (1 / r ^ 4) (r / 2) hB hE (by linarith)
  refine ⟨min r w₁, lt_min hr hw₁, min_le_left _ _, ?_⟩
  intro H t p hball
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm,
      hterminal, pU, K, hpU, himage, hK, hpinterior, hseparation⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall t p r hball
  refine ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm,
    hterminal, pU, K, hpU, himage, hK, hpinterior, hseparation, ?_⟩
  intro first v τ hτ hτw hτv hvE j hfirst hlower hphysical α hα hint hscalar hrecent hnode hout
  let S' := S.timeRestrict
    (RealTimeInterval.closed (t.val - r ^ 2) t.val (sub_le_self _ (sq_nonneg r)))
  have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS
    (Icc_subset_Icc ha.le le_rfl) (Ioo_subset_Ioo ha.le le_rfl)
  have hupper : t.val ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.activeStage_time_le t, H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩
  apply hmodel U H first (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat)
    f hf hinj hcross t r v τ hτ (hτw.trans (min_le_right _ _))
    (hτw.trans (min_le_left _ _)) hτv hvE j hfirst S' hS' hupper hlower hphysical
    (fun k s hs hstage => hmetric k s ⟨ha.le.trans hs.1, hs.2.le⟩ hstage)
    (fun s hs x => by
      change normSq0S (S.base.metric s) x 4 (S.base.rm04 s x) ≤ 1 / r ^ 4
      apply (le_div_iff₀ (pow_pos hr 4)).mpr
      simpa only [mul_comm] using hRm s ⟨ha.le.trans hs.1, hs.2⟩ x)
    K hK pU hpinterior hseparation α hα hint hscalar ?_ hnode hout
  rw [hlast, hpU]
  exact hrecent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem isParabolicallyRmControlledBall.exists_regularCrossing_at_event_time
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (i : Fin H.eventCount) (ht : t.val = H.time i.succ) :
    let hi : H.activeStage t = i.succ := H.activeStage_eq_of_maximal t i.succ
      (by rw [ht]) (fun k hk => H.time_strictMono.le_iff_le.mp (by simpa only [ht] using hk))
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      (H.event i).RegularCrossing x.val (hi ▸ p) := by
  intro hi
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  have hmem : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A, _⟩ := htrace p hmem
  have hafirst : H.activeStage a ≤ i.castSucc := by
    have htime : H.time (H.activeStage a) < H.time i.succ :=
      (H.activeStage_time_le a).trans_lt (by rw [ha, ht]; exact sub_lt_self _ (sq_pos_of_pos hr))
    have hlt := H.time_strictMono.lt_iff_lt.mp htime
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  have hlast (last : Fin (H.eventCount + 1)) (heq : last = i.succ)
      (y : (H.stage last).Carrier) (hle : H.activeStage a ≤ last)
      (B : BackwardPointTrace H (H.activeStage a) last hle y) :
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing x.val (heq ▸ y) := by
    subst last
    have hcross := B.crossing i hafirst le_rfl
    rw [B.endpoint_eq] at hcross
    exact ⟨⟨_, hcross.mem_terminalRegularRegion (H.event i)⟩, hcross⟩
  exact hlast _ hi p (H.activeStage_mono hat) A

theorem isParabolicallyRmControlledBall.regularCrossing_of_oldOutput_at_event_time
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (i : Fin H.eventCount) (ht : t.val = H.time i.succ) :
    let hi : H.activeStage t = i.succ := H.activeStage_eq_of_maximal t i.succ
      (by rw [ht]) (fun k hk => H.time_strictMono.le_iff_le.mp (by simpa only [ht] using hk))
    ∀ z : (H.event i).old, (H.event i).oldOutput z = (hi ▸ p) →
      (H.event i).RegularCrossing z.val.val (hi ▸ p) := by
  intro hi z hz
  obtain ⟨x, hx⟩ := hball.exists_regularCrossing_at_event_time H i ht
  rw [(H.event i).oldOutput_eq_iff_of_regularCrossing z hx |>.mp hz]
  exact hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
