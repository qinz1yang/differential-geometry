import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventSurvival_S146
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

/-!
# CH12-S146, group 2a: the abstract downward survival induction

For an observed history `H`, a trace `B` from stage `j0` to the last stage (ending at `q`), a tube `|Rm| ≤ Kb` of radius
`Abar` around `B` on every incoming slab, and a "barrier from survival" step `hbar`, every point `y` of stage `m ≥ j0`
within `a` (`a * exp(9 Kb (T - time m)) < Abar`) of `B.point m` has a forward trace to the last stage ending in `Tgt`.
Radii: `a_{i.succ} = a_{i.castSucc} * exp(9 Kb (time i.succ - time i.castSucc))` (no compounding, strictness from `ℓ < a`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem surv_induction_S146 {H : ObservedHistory.{u}} {j0 : Fin (H.eventCount + 1)}
    {q : (H.stage (Fin.last H.eventCount)).Carrier}
    (B : BackwardPointTrace H j0 (Fin.last H.eventCount) (Fin.le_last _) q)
    (Tgt : (H.stage (Fin.last H.eventCount)).Carrier → Prop) {Kb Abar T : ℝ} (hK : 0 ≤ Kb)
    (hT : H.time (Fin.last H.eventCount) ≤ T)
    (hslab : ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
      (L : G.TerminalLimitMetric) {u w : P.Carrier} {Kb ℓ R : ℝ}, 0 ≤ Kb → 0 ≤ ℓ →
      Real.exp (9 * Kb * (s - a)) * ℓ < R →
      (∀ t ∈ Ico a s, ∀ x ∈ riemannianBallOf (G.flow.base.metric t) u R,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x)) ≤ Kb) →
      riemannianEDistOf (G.flow.base.metric a) u w < ENNReal.ofReal ℓ →
      ∃ u' w' : G.terminalRegularOpen, u'.val = u ∧ w'.val = w ∧
        riemannianEDistOf L.metric u' w' ≤ ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ))
    (htube : ∀ (i : Fin H.eventCount) (hi : j0 ≤ i.castSucc),
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t)
        (B.point i.castSucc hi (i.castSucc_lt_succ.le.trans (Fin.le_last _))) Abar,
        Real.sqrt (normSq0S ((H.event i).incoming.flow.base.metric t) x 4
          ((H.event i).incoming.flow.base.rm04 t x)) ≤ Kb)
    (hlast : ∀ a : ℝ, 0 < a → a * Real.exp (9 * Kb * (T - H.time (Fin.last H.eventCount))) < Abar →
      ∀ y : (H.stage (Fin.last H.eventCount)).Carrier,
        riemannianEDistOf (H.initialMetric (Fin.last H.eventCount)) q y < ENNReal.ofReal a → Tgt y)
    (hbar : ∀ (i : Fin H.eventCount) (hi : j0 ≤ i.castSucc),
      (∀ a : ℝ, 0 < a → a * Real.exp (9 * Kb * (T - H.time i.succ)) < Abar →
        ∀ y : (H.stage i.succ).Carrier,
          riemannianEDistOf (H.initialMetric i.succ)
            (B.point i.succ (hi.trans i.castSucc_lt_succ.le) (Fin.le_last _)) y < ENNReal.ofReal a →
          ∃ yf, Tgt yf ∧ ∃ A : BackwardPointTrace H i.succ (Fin.last H.eventCount) (Fin.le_last _) yf,
            A.point i.succ le_rfl (Fin.le_last _) = y) →
      ∀ a : ℝ, 0 < a → a * Real.exp (9 * Kb * (T - H.time i.succ)) < Abar →
        riemannianBallOf (H.event i).outputMetric
          (B.point i.succ (hi.trans i.castSucc_lt_succ.le) (Fin.le_last _)) a ⊆
          interior (range (H.event i).oldOutput)) :
    ∀ (m : Fin (H.eventCount + 1)) (hm : j0 ≤ m) (a : ℝ), 0 < a →
      a * Real.exp (9 * Kb * (T - H.time m)) < Abar →
      ∀ y : (H.stage m).Carrier,
        riemannianEDistOf (H.initialMetric m) (B.point m hm (Fin.le_last _)) y < ENNReal.ofReal a →
        ∃ yf, Tgt yf ∧ ∃ A : BackwardPointTrace H m (Fin.last H.eventCount) (Fin.le_last _) yf,
          A.point m le_rfl (Fin.le_last _) = y := by
  intro m
  induction m using Fin.reverseInduction with
  | last =>
    intro hm a ha hae y hy
    have hq : B.point (Fin.last H.eventCount) hm le_rfl = q := B.endpoint_eq
    refine ⟨y, hlast a ha hae y ?_, BackwardPointTrace.singleton H _ y, rfl⟩
    rw [← hq]; exact hy
  | cast i ih =>
    intro hm a ha hae y hy
    have hi1 : j0 ≤ i.succ := hm.trans i.castSucc_lt_succ.le
    have ih' := ih hi1
    set Δ : ℝ := H.time i.succ - H.time i.castSucc with hΔ
    set c₁ : ℝ := Real.exp (9 * Kb * Δ) with hc₁
    have hc₁pos : 0 < c₁ := Real.exp_pos _
    have hts : H.time i.succ ≤ T :=
      ((H.time_strictMono.monotone (Fin.le_last _)).trans hT)
    have hE1 : 1 ≤ Real.exp (9 * Kb * (T - H.time i.succ)) :=
      Real.one_le_exp (by have : 0 ≤ T - H.time i.succ := sub_nonneg.2 hts; positivity)
    have hEsplit : Real.exp (9 * Kb * (T - H.time i.castSucc)) =
        c₁ * Real.exp (9 * Kb * (T - H.time i.succ)) := by
      rw [hc₁, ← Real.exp_add]; congr 1; rw [hΔ]; ring
    -- choose ℓ strictly between the distance and a
    have hy' : riemannianEDistOf ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
        (B.point i.castSucc hm (i.castSucc_lt_succ.le.trans (Fin.le_last _))) y <
        ENNReal.ofReal a := by rw [H.event_initial i]; exact hy
    have hne : riemannianEDistOf ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
        (B.point i.castSucc hm (i.castSucc_lt_succ.le.trans (Fin.le_last _))) y ≠ ⊤ := hy'.ne_top
    set d : ℝ := (riemannianEDistOf ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
        (B.point i.castSucc hm (i.castSucc_lt_succ.le.trans (Fin.le_last _))) y).toReal with hd
    have hdlt : d < a := by
      rw [hd]; exact (ENNReal.toReal_lt_of_lt_ofReal hy')
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    set ℓ : ℝ := (d + a) / 2 with hℓ
    have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
    have hℓa : ℓ < a := by rw [hℓ]; linarith
    have hdℓ : riemannianEDistOf ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
        (B.point i.castSucc hm (i.castSucc_lt_succ.le.trans (Fin.le_last _))) y <
        ENNReal.ofReal ℓ := by
      rw [← ENNReal.ofReal_toReal hne]
      exact (ENNReal.ofReal_lt_ofReal_iff (by rw [hℓ]; linarith)).2 (by rw [hℓ]; linarith)
    have hroom : c₁ * ℓ < Abar := by
      calc c₁ * ℓ < c₁ * a := mul_lt_mul_of_pos_left hℓa hc₁pos
        _ ≤ c₁ * a * Real.exp (9 * Kb * (T - H.time i.succ)) := le_mul_of_one_le_right (by positivity) hE1
        _ = a * Real.exp (9 * Kb * (T - H.time i.castSucc)) := by rw [hEsplit]; ring
        _ < Abar := hae
    have hae' : (a * c₁) * Real.exp (9 * Kb * (T - H.time i.succ)) < Abar := by
      have : (a * c₁) * Real.exp (9 * Kb * (T - H.time i.succ)) =
          a * Real.exp (9 * Kb * (T - H.time i.castSucc)) := by rw [hEsplit]; ring
      rw [this]; exact hae
    have hprot := hbar i hm ih' (a * c₁) (mul_pos ha hc₁pos) hae'
    have hcross := B.crossing i hm (Fin.le_last _)
    obtain ⟨y', hy'c, hy'd⟩ := event_survival_S146 (H.event i)
      (fun hK' hℓ' hroom' hRm' hw' => hslab (H.event i).incoming (H.event i).terminal hK' hℓ' hroom' hRm' hw')
      hcross hK hℓ0 (R := Abar) (A := a * c₁) hroom (htube i hm)
      (by simpa only [H.event_output i] using hprot)
      (by rw [mul_comm a c₁]; exact mul_lt_mul_of_pos_left hℓa hc₁pos) hdℓ
    have hy'a : riemannianEDistOf (H.initialMetric i.succ)
        (B.point i.succ hi1 (Fin.le_last _)) y' < ENNReal.ofReal (a * c₁) := by
      rw [← H.event_output i]
      refine lt_of_le_of_lt hy'd ((ENNReal.ofReal_lt_ofReal_iff (mul_pos ha hc₁pos)).2 ?_)
      rw [mul_comm a c₁]; exact mul_lt_mul_of_pos_left hℓa hc₁pos
    obtain ⟨yf, hTgt, A', hA'⟩ := ih' (a * c₁) (mul_pos ha hc₁pos) hae' y' hy'a
    refine ⟨yf, hTgt, A'.prepend y (hA'.symm ▸ hy'c), ?_⟩
    exact BackwardPointTrace.prepend_point_first A' y _

end GC.LongTime.Ch12
