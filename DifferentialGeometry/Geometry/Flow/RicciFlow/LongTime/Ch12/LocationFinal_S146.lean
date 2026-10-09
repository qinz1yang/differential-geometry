import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SlabForward_S147
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthPt_S146

/-!
# CH12-S146, group 2c: the last stage of the survival induction (location in `B(p, 2ρ)`)

`final_location_S146`: a point `y` of the last stage with `d_{initialMetric last}(q, y) < a`, `a e^{9 Kb (s.time - time last)} < Abar ≤ ρ`,
and the tube `|Rm| ≤ Kb` on `B_t(q, Abar)` for `t ∈ [time last, s.time]` (final slab), lies in `B_{s.metric}(p, 2ρ)`.
Proof: the final slab as an `IncomingSlab` (`restrictIncoming`, as in `fwd_scalar_lower_S134`) + `slab_forward_ball_S147`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

theorem final_location_S146 (s : RegularSlice F.observation) {p q : s.stage.Carrier}
    {ρ Kb Abar a : ℝ} (hK : 0 ≤ Kb) (ha : 0 < a)
    (hae : a * Real.exp (9 * Kb * (s.time - (sliceHistoryR_O3 F s).time
      (Fin.last (sliceHistoryR_O3 F s).eventCount))) < Abar) (hAρ : Abar ≤ ρ)
    (hq : q ∈ riemannianBallOf s.metric p ρ)
    (htube : ∀ t ∈ Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time,
      ∀ x ∈ riemannianBallOf ((sliceSlabR_O3 F s).flow.base.metric t) q Abar,
        Real.sqrt (normSq0S ((sliceSlabR_O3 F s).flow.base.metric t) x 4
          ((sliceSlabR_O3 F s).flow.base.rm04 t x)) ≤ Kb)
    (y : s.stage.Carrier)
    (hy : riemannianEDistOf ((sliceHistoryR_O3 F s).initialMetric (Fin.last (sliceHistoryR_O3 F s).eventCount))
      q y < ENNReal.ofReal a) :
    y ∈ riemannianBallOf s.metric p (2 * ρ) := by
  let G := (sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl
  let L := (sliceSlabR_O3 F s).endpointTerminalLimitMetric
    ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))
  have hne := hy.ne_top
  set d : ℝ := (riemannianEDistOf ((sliceHistoryR_O3 F s).initialMetric
      (Fin.last (sliceHistoryR_O3 F s).eventCount)) q y).toReal with hd
  have hdlt : d < a := ENNReal.toReal_lt_of_lt_ofReal hy
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  set ℓ : ℝ := (d + a) / 2 with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
  have hℓa : ℓ < a := by rw [hℓ]; linarith
  have hdℓ : riemannianEDistOf ((sliceHistoryR_O3 F s).initialMetric
      (Fin.last (sliceHistoryR_O3 F s).eventCount)) q y < ENNReal.ofReal ℓ := by
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by rw [hℓ]; linarith)).2 (by rw [hℓ]; linarith)
  have hc := Real.exp_pos (9 * Kb * (s.time - (sliceHistoryR_O3 F s).time
      (Fin.last (sliceHistoryR_O3 F s).eventCount)))
  have hroom : Real.exp (9 * Kb * (s.time - (sliceHistoryR_O3 F s).time
      (Fin.last (sliceHistoryR_O3 F s).eventCount))) * ℓ < Abar :=
    calc _ < Real.exp (9 * Kb * (s.time - (sliceHistoryR_O3 F s).time
          (Fin.last (sliceHistoryR_O3 F s).eventCount))) * a := mul_lt_mul_of_pos_left hℓa hc
      _ = a * _ := mul_comm _ _
      _ < Abar := hae
  have hw : riemannianEDistOf (G.flow.base.metric ((sliceHistoryR_O3 F s).time
      (Fin.last (sliceHistoryR_O3 F s).eventCount))) q y < ENNReal.ofReal ℓ := by
    have h0 := sliceSlabR_initial_O3 F s
    change riemannianEDistOf ((sliceSlabR_O3 F s).flow.base.metric _) q y < _
    rw [h0]; exact hdℓ
  obtain ⟨u', w', hu', hw', hdd⟩ := slab_forward_ball_S147 G L hK hℓ0 hroom
    (fun t ht x hx => htube t ⟨ht.1, ht.2.le⟩ x hx) hw
  have hLm : L.metric = s.metric.restrictOpen G.terminalRegularOpen := by
    change ((sliceSlabR_O3 F s).flow.base.metric s.time).restrictOpen _ = _
    rw [sliceSlabR_metric_time_O3 F s]
    rfl
  have hle := riemannianEDistOf_le_restrictOpen s.metric G.terminalRegularOpen u' w'
  rw [← hLm] at hle
  have h1 : riemannianEDistOf s.metric q y ≤ ENNReal.ofReal ρ := by
    have : riemannianEDistOf s.metric u'.val w'.val ≤ ENNReal.ofReal Abar :=
      hle.trans (hdd.trans (ENNReal.ofReal_le_ofReal (hroom.le)))
    rw [hu', hw'] at this
    exact this.trans (ENNReal.ofReal_le_ofReal hAρ)
  have htri := riemannianEDistOf_triangle s.metric p q y
  have hsum : riemannianEDistOf s.metric p y < ENNReal.ofReal ρ + ENNReal.ofReal ρ :=
    htri.trans_lt (ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hq h1)
  have hρ : 0 ≤ ρ := by
    have h0 : 0 ≤ Real.exp (9 * Kb * (s.time - (sliceHistoryR_O3 F s).time
      (Fin.last (sliceHistoryR_O3 F s).eventCount))) * ℓ := by positivity
    linarith only [h0, hroom, hAρ]
  change riemannianEDistOf s.metric p y < ENNReal.ofReal (2 * ρ)
  rwa [two_mul, ENNReal.ofReal_add hρ hρ]

end GC.LongTime.Ch12
