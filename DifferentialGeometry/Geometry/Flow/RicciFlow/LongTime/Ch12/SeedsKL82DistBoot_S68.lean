import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82DistBootTerminal_S68
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82HistoryDistance_CX11

/-!
# CH12-S68, Group G3: the distance bootstrap `dist_trace_boot_S68`

The first-exit form of `dist_trace_le_CX11` (KL 82.1, distance of a trace point to the centre
trace): the Ricci bound `Ric ≤ C/(v−a)` is assumed only on the fixed balls `B_v(X(v), R0)` (what
claim (C) provides), together with the margin
`d_t(p,q) + 16√(C/3)√(t−a) + √(3(t−a)/C) < R0`.  The backward Fin-induction over the events is
CX11's, with the slab step `dist_boot_slab_S68` (inside `incoming_dist_boot_terminal_S68`) in place
of CX11's, and the margin at every slab end `b ≤ t` coming from
`budget b + 16√(C/3)√(b−a) = d + 16√(C/3)√(t−a)` and `√(3(b−a)/C) ≤ √(3(t−a)/C)`.
-/

set_option autoImplicit false

noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

/-- **G3.**  The G4 distance bound across every event, in extended distance, with the Ricci bound
only on the fixed balls `B_v(X(v), R0)` and the margin `hR0`.  This is the `hboot` binder of
`kl82_1_of_claim_O25` ("[FROZEN] CH12-O25 G2" (b)). -/
theorem dist_trace_boot_S68 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) {p q : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {C ρ R0 : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hq : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q < ENNReal.ofReal ρ)
    (hroom : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) < ρ / 2)
    (hR0 : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) +
        Real.sqrt (3 * ((t : ℝ) - a) / C) < R0)
    (hSF : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
          (H.activeStage_mono hav) z))
    (hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
      ∀ w : TangentSpace ThreeModel z,
      ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
        C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      traceEDist_CX11 H (hat := hat) X A v hav hvt ≤
        ENNReal.ofReal ((riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
          16 * Real.sqrt (C / 3) * (Real.sqrt ((t : ℝ) - a) - Real.sqrt ((v : ℝ) - a))) := by
  let d := (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal
  let B := 16 * Real.sqrt (C / 3)
  let budget (v : ℝ) := d + B * (Real.sqrt ((t : ℝ) - a) - Real.sqrt (v - a))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget0 (v : ℝ) (hvt : v ≤ t) : 0 ≤ budget v := by
    have hh := Real.sqrt_le_sqrt (sub_le_sub_right hvt (a : ℝ))
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hB (sub_nonneg.mpr hh))
  have hbudgetρ (v : ℝ) : budget v < ρ := by
    have hh := mul_nonneg hB (Real.sqrt_nonneg (v - a))
    dsimp [budget, d, B] at hh ⊢
    linarith
  have hfin := ne_top_of_lt hq
  have hbudgetmargin (b : ℝ) (hbt : b ≤ t) :
      budget b + 16 * Real.sqrt (C / 3) * Real.sqrt (b - a) +
        Real.sqrt (3 * (b - a) / C) < R0 := by
    have hr : Real.sqrt (3 * (b - a) / C) ≤ Real.sqrt (3 * ((t : ℝ) - a) / C) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hC.le)
    have hbd : budget b + 16 * Real.sqrt (C / 3) * Real.sqrt (b - a) =
        d + 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) := by
      dsimp [budget, B]
      ring
    rw [hbd]
    dsimp only [d] at hR0 ⊢
    linarith
  have hRicStage (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hva : (a : ℝ) < v) (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
      (haj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t) :
      ∀ z : (H.stage j).Carrier, ∀ w : TangentSpace ThreeModel z,
        riemannianEDistOf (H.stageMetric j v) (X.point j haj hjt) z < ENNReal.ofReal R0 →
        ricciTensor (H.stageMetric j v) z w w ≤
          C / ((v : ℝ) - a) * (H.stageMetric j v).inner z w w := by
    subst j
    intro z w hz
    exact hRic v hav hvt hva z hz w
  have hSFStage (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
      (haj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t) :
      ∀ z ∈ riemannianBallOf (H.stageMetric j v) (X.point j haj hjt) ρ,
        Nonempty (BackwardPointTrace H (H.activeStage a) j haj z) := by
    subst j
    exact hSF v hav hvt
  have hslab (j : Fin (H.eventCount + 1)) (haj : H.activeStage a ≤ j)
      (hjt : j ≤ H.activeStage t) (b : ℝ) (hbt : b ≤ t)
      (G : (H.stage j).IncomingSlab (H.time j) b) (L : G.TerminalLimitMetric)
      (hactive : ∀ v : Icc (0 : ℝ) H.horizon, H.time j ≤ v.val → v.val < b → H.activeStage v = j)
      (hmetric : ∀ v ∈ Ico (H.time j) b, H.stageMetric j v = G.flow.base.metric v)
      (xm ym : G.terminalRegularOpen) (hxm : xm.val = X.point j haj hjt)
      (hym : ym.val = A.point j haj hjt)
      (hterm : riemannianEDistOf L.metric xm ym ≤ ENNReal.ofReal (budget b))
      (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hvj : H.time j ≤ v.val) (hvb : v.val < b) :
      traceEDist_CX11 H (hat := hat) X A v hav hvt ≤ ENNReal.ofReal (budget v) := by
    have hh := incoming_dist_boot_terminal_S68 G L hvj hvb hav hC
      (hbudget0 b hbt) xm ym hterm (hbudgetmargin b hbt) (fun z hz => by
        let z' : Icc (0 : ℝ) H.horizon :=
          ⟨z, v.property.1.trans hz.1.le, hz.2.le.trans (hbt.trans t.property.2)⟩
        have haz : a ≤ z' := hav.trans hz.1.le
        have hzt : z' ≤ t := hz.2.le.trans hbt
        have hjz := hactive z' (hvj.trans hz.1.le) hz.2
        have hr := hRicStage z' haz hzt (hav.trans_lt hz.1) j hjz haj hjt
        rw [hmetric z ⟨hvj.trans hz.1.le, hz.2⟩, ← hxm] at hr
        exact hr)
    rw [traceEDist_at_stage_CX11 H (hat := hat) X A v hav hvt j (hactive v hvj hvb) haj hjt,
      hmetric v ⟨hvj, hvb⟩, ← hxm, ← hym]
    convert hh using 1
    congr 1
    dsimp [budget, B]
    ring
  have hsame (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hj : H.activeStage v = H.activeStage t) :
      traceEDist_CX11 H (hat := hat) X A v hav hvt ≤ ENNReal.ofReal (budget v) := by
    by_cases hve : v = t
    · subst v
      simp only [traceEDist_CX11, X.endpoint_eq, A.endpoint_eq]
      dsimp [budget, d]
      rw [sub_self, mul_zero, add_zero, ENNReal.ofReal_toReal hfin]
    have hvlt : v < t := lt_of_le_of_ne hvt hve
    have hregular : H.time (H.activeStage t) < t.val := by
      have hh := H.activeStage_time_le v
      rw [hj] at hh
      exact hh.trans_lt hvlt
    let P := H.closedPrefixAt t hregular
    let G := P.restrictIncoming le_rfl P.lt le_rfl
    let L := P.endpointTerminalLimitMetric (H.stageAt t)
    have hfull : G.terminalRegularRegion = univ := P.terminalRegularRegion_eq_univ (H.stageAt t)
    let xm : G.terminalRegularOpen := ⟨p, by change p ∈ G.terminalRegularRegion; rw [hfull]; trivial⟩
    let ym : G.terminalRegularOpen := ⟨q, by change q ∈ G.terminalRegularRegion; rw [hfull]; trivial⟩
    have hL : L.metric = (H.stageMetric (H.activeStage t) t).restrictOpen G.terminalRegularOpen := by
      change (P.flow.base.metric t).restrictOpen G.terminalRegularOpen = _
      rw [H.closedPrefixAt_metric]
    have hterm : riemannianEDistOf L.metric xm ym ≤ ENNReal.ofReal (budget t) := by
      rw [hL, edist_restrict_eq_center_CX11 _ _ xm ym (ρ := ρ) (by
        intro z _; change z ∈ G.terminalRegularRegion; rw [hfull]; trivial) hq]
      dsimp [budget, d]
      rw [sub_self, mul_zero, add_zero, ENNReal.ofReal_toReal hfin]
    exact hslab (H.activeStage t) (H.activeStage_mono hat) le_rfl t le_rfl G L
      (fun w hw hwt => le_antisymm (H.activeStage_mono hwt.le) (H.le_activeStage w _ hw))
      (fun w _ => (H.closedPrefixAt_metric t hregular w).symm) xm ym X.endpoint_eq.symm
      A.endpoint_eq.symm hterm v hav hvt (by simpa only [hj] using H.activeStage_time_le v) hvlt
  have hstage (j : Fin (H.eventCount + 1)) :
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), H.activeStage v = j →
        traceEDist_CX11 H (hat := hat) X A v hav hvt ≤ ENNReal.ofReal (budget v) := by
    induction j using Fin.reverseInduction with
    | last =>
      intro v hav hvt hj
      apply hsame v hav hvt
      exact le_antisymm (H.activeStage_mono hvt) (hj.symm ▸ Fin.le_last _)
    | cast i ih =>
      intro v hav hvt hj
      have haj : H.activeStage a ≤ i.castSucc := hj ▸ H.activeStage_mono hav
      have hjt : i.castSucc ≤ H.activeStage t := hj ▸ H.activeStage_mono hvt
      by_cases hit : i.castSucc = H.activeStage t
      · exact hsame v hav hvt (hj.trans hit)
      have hist : i.succ ≤ H.activeStage t := Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hjt hit)
      let e : Icc (0 : ℝ) H.horizon :=
        ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
      have hae : a ≤ e :=
        (time_lt_of_activeStage_lt_CX2 H a i.succ (haj.trans_lt i.castSucc_lt_succ)).le
      have het : e ≤ t := (H.time_strictMono.monotone hist).trans (H.activeStage_time_le t)
      have hej : H.activeStage e = i.succ := H.activeStage_at_time i.succ
      have hedist := ih e hae het hej
      rw [traceEDist_at_stage_CX11 H (hat := hat) X A e hae het i.succ hej
        (haj.trans i.castSucc_lt_succ.le) hist] at hedist
      have hmetricE : H.stageMetric i.succ e = H.initialMetric i.succ := H.stageMetric_initial i.succ
      rw [hmetricE] at hedist
      let U := H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le
      let Bx := (X.restrictLast (haj.trans i.castSucc_lt_succ.le) hist).restrictFirst haj i.castSucc_lt_succ.le
      let By := (A.restrictLast (haj.trans i.castSucc_lt_succ.le) hist).restrictFirst haj i.castSucc_lt_succ.le
      let xp : U := ⟨X.point i.succ (haj.trans i.castSucc_lt_succ.le) hist, ⟨Bx⟩⟩
      let yp : U := ⟨A.point i.succ (haj.trans i.castSucc_lt_succ.le) hist, ⟨By⟩⟩
      have hball : riemannianBallOf (H.initialMetric i.succ) xp.val ρ ⊆ U := by
        have hSFstage := hSFStage e hae het i.succ hej (haj.trans i.castSucc_lt_succ.le) hist
        rw [hmetricE] at hSFstage
        intro z hz
        obtain ⟨Z⟩ := hSFstage z hz
        exact ⟨Z.restrictFirst haj i.castSucc_lt_succ.le⟩
      have hyshort : riemannianEDistOf (H.initialMetric i.succ) xp.val yp.val < ENNReal.ofReal ρ :=
        hedist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (hbudgetρ e))
      have hevent := terminal_edist_le_output_of_survivor_ball_CX11 H i xp yp hball hyshort
      let xm : (H.event i).incoming.terminalRegularOpen :=
        ⟨X.point i.castSucc haj hjt, (X.crossing i haj hist).mem_terminalRegularRegion (H.event i)⟩
      let ym : (H.event i).incoming.terminalRegularOpen :=
        ⟨A.point i.castSucc haj hjt, (A.crossing i haj hist).mem_terminalRegularRegion (H.event i)⟩
      have hxm : H.backwardSurvivorTerminalMap i.castSucc i.succ i.castSucc_lt_succ.le
          i le_rfl le_rfl xp = xm := by
        apply Subtype.ext
        exact H.backwardSurvivorMap_eq_point i.castSucc i.succ i.castSucc_lt_succ.le
          i.castSucc le_rfl i.castSucc_lt_succ.le xp Bx
      have hym : H.backwardSurvivorTerminalMap i.castSucc i.succ i.castSucc_lt_succ.le
          i le_rfl le_rfl yp = ym := by
        apply Subtype.ext
        exact H.backwardSurvivorMap_eq_point i.castSucc i.succ i.castSucc_lt_succ.le
          i.castSucc le_rfl i.castSucc_lt_succ.le yp By
      rw [hxm, hym] at hevent
      exact hslab i.castSucc haj hjt e het (H.event i).incoming (H.event i).terminal
        (fun w hw hwe => activeStage_on_event_CX2 H i w ⟨hw, hwe⟩)
        (fun w _ => by simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc])
        xm ym rfl rfl (hevent.trans hedist) v hav hvt
        (by simpa only [hj] using H.activeStage_time_le v)
        (time_lt_of_activeStage_lt_CX2 H v i.succ (hj.symm ▸ i.castSucc_lt_succ))
  intro v hav hvt
  exact hstage (H.activeStage v) v hav hvt rfl

end GC.LongTime.Ch12
