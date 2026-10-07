import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric

/-!
# S-CH11-FIX9 port of astra `DistinctPoleBirthWeightedMinimum`（`PortC11P`）

来源：donor `DistinctPoleBirthWeightedMinimum.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `hhi'`：`nlinarith only [hhi, haction]` 在本树失败（`12 * v ^ 3 / rho ^ 2` 与
  `6 * v ^ 3 / rho ^ 2` 被当成不同原子）→ 先显式 `2 * action ≤ 12 * v ^ 3 / rho ^ 2`
  （`ring` 改写 + `mul_le_mul_of_nonneg_left haction`），再 `linarith`。

原路径 `DistinctPoleBirthWeightedMinimum` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem backward_trace_point_before_birth_eq_old
    (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (trace : BackwardPointTrace H first last hle endpoint)
    (i : Fin H.eventCount) (hlast : last = i.succ) (hf : first ≤ i.castSucc)
    (z : (H.event i).old) (hz : HEq ((H.event i).oldOutput z) endpoint) :
    trace.point i.castSucc hf (i.castSucc_le_succ.trans hlast.symm.le) = z.val.val := by
  have hEndpoint (j : Fin (H.eventCount + 1)) (hjf : first ≤ j) (hjl : j ≤ last)
      (hj : j = last) : HEq (trace.point j hjf hjl) endpoint := by
    subst j
    exact heq_of_eq trace.endpoint_eq
  obtain ⟨w, _hwInterior, hwin, hwout⟩ := trace.crossing i hf hlast.symm.le
  have hwz : (H.event i).oldOutput w = (H.event i).oldOutput z :=
    eq_of_heq ((heq_of_eq hwout).trans
      ((hEndpoint i.succ (hf.trans i.castSucc_le_succ) hlast.symm.le hlast.symm).trans hz.symm))
  have hweq : w = z := (H.event i).oldOutput_injective hwz
  exact hwin.symm.trans (congrArg (fun y : (H.event i).old => y.val.val) hweq)

private theorem exists_pos_clock_distance_lt_of_birth_terminal_distance_lt
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount)
    (hbirth : t.val = H.time i.succ) (O z : (H.event i).old) (R : ℝ)
    (hdist : riemannianEDistOf (H.event i).terminal.metric
      ((H.event i).oldTerminal O) ((H.event i).oldTerminal z) < ENNReal.ofReal R) :
    ∃ e : ℝ, 0 < e ∧ e ^ 2 < t.val - H.time i.castSucc ∧
      ∀ v : ℝ, 0 < v → v < e →
        riemannianEDistOf (H.stageMetric i.castSucc (t.val - v ^ 2))
          O.val.val z.val.val < ENNReal.ofReal R := by
  have hpast : H.time i.castSucc < t.val := by
    rw [hbirth]
    exact H.time_strictMono i.castSucc_lt_succ
  have hnear : ∀ᶠ s in 𝓝[<] t.val,
      riemannianEDistOf (H.stageMetric i.castSucc s) O.val.val z.val.val < ENNReal.ofReal R := by
    rw [hbirth]
    filter_upwards [(H.event i).terminal.eventually_riemannianEDistOf_lt
      ((H.event i).oldTerminal O) ((H.event i).oldTerminal z) hdist] with s hs
    simpa only [stageMetric_castSucc_apply, (H.event i).oldTerminal_eq] using hs
  obtain ⟨d, hd, hbound⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hpast).mp hnear
  let e : ℝ := Real.sqrt ((t.val - d) / 2)
  have hed : 0 < (t.val - d) / 2 := by linarith only [hd.2]
  have he : 0 < e := Real.sqrt_pos.mpr hed
  have he2 : e ^ 2 = (t.val - d) / 2 := Real.sq_sqrt hed.le
  refine ⟨e, he, ?_, ?_⟩
  · linarith only [he2, hd.1, hd.2]
  · intro v hv hve
    have hv2 : v ^ 2 < e ^ 2 := (sq_lt_sq₀ hv.le he.le).mpr hve
    exact hbound ⟨by linarith only [hv2, he2, hd.2],
      sub_lt_self _ (sq_pos_of_pos hv)⟩

/-- A birth pole uses the same full trace and original weighted infimum.
The actual common cap family gives incoming terminal distance control; its
controlled pole trace then supplies the genuine initial finite competitor. -/
theorem exists_distinct_pole_initial_weighted_minimum_and_limit_at_birth
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ z, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ z)
    (hscalar : ∀ z, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) z)
    (aSeed t : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (p x : (H.stageAt t).Carrier) (r rho A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A)
    (hSeedClock : (aSeed : ℝ) = (t : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hPoleTest : H.isParabolicallyRmControlledBall t x rho)
    (hrecent : 2 * r ^ 2 < (t : ℝ))
    (i : Fin H.eventCount) (hactive : H.activeStage t = i.succ)
    (hbirth : (t : ℝ) = H.time i.succ)
    {Dcap εcap : ℝ} {mcap : ℕ}
    (S : ∀ b : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed Dcap mcap εcap b)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (Oold xold : (H.event i).old)
    (hO : HEq ((H.event i).oldOutput Oold) p)
    (hx : HEq ((H.event i).oldOutput xold) x)
    (hOoutside : ∀ b, (H.event i).oldOutput Oold ∉ (S b).window ''
      {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hxoutside : ∀ b, (H.event i).oldOutput xold ∉ (S b).window ''
      {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r)) :
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    (∃ e : ℝ, 0 < e ∧ e ≤ r / 4 ∧ e ≤ rho / 2 ∧
      e ^ 2 < (t : ℝ) - H.time i.castSucc ∧ 6 * e ^ 3 / rho ^ 2 ≤ r / 4 ∧
      ∀ v : ℝ, 0 < v → v < e →
        ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - v ^ 2 ∧
          H.activeStage a = i.castSucc ∧
          let first := H.activeStage a
          let last := H.activeStage t
          let hle := H.activeStage_mono hat
          let O := seedTrace.point first (H.activeStage_mono has) hle
          ∃ poleTrace : BackwardPointTrace H first last hle x,
            poleTrace.isRmControlled (hat := hat) rho ∧
            let y := poleTrace.point first le_rfl hle
            riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
              ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) ∧
            ∃ action : ℝ,
              action ∈ H.regularizedC1ActionValues first last hle t 0 v x y ∧
              (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v x y ∧
              H.regularizedCost first last hle t (3 / a₀) 0 v x y ≤ (action : WithTop ℝ) ∧
              action ≤ 6 * v ^ 3 / rho ^ 2 ∧
              ∃ (q : (H.stage first).Carrier) (L m : ℝ),
                H.regularizedCost first last hle t (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
                riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O q <
                  ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
                L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
                H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q = (m : WithTop ℝ) ∧
                M v = (m : WithTop ℝ) ∧ 0 < m ∧
                2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧
                m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 ∧
                ∀ z : (H.stage first).Carrier,
                  H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q ≤
                    H.physicalWeightedCost first last hle t (3 / a₀) r A v x O z) ∧
    (∀ᶠ v in 𝓝[>] (0 : ℝ), M v ≠ ⊤) ∧
    Tendsto (fun v : ℝ => (M v).untopD 0 / v) (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
  classical
  intro M
  obtain ⟨hrho, aPole, hPoleTime, hPoleClock, hPoleTraces⟩ := hPoleTest
  have hxball : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) x rho := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) x x < ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hrho
  obtain ⟨fullPoleTrace, hFullPoleTrace⟩ := hPoleTraces x hxball
  have hpostDistAt (j : Fin (H.eventCount + 1)) (hj : j = i.succ)
      (p' x' : (H.stage j).Carrier)
      (hp' : HEq ((H.event i).oldOutput Oold) p')
      (hx' : HEq ((H.event i).oldOutput xold) x')
      (hd : riemannianEDistOf (H.stageMetric j t.val) p' x' < ENNReal.ofReal (A * r)) :
      riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput Oold) ((H.event i).oldOutput xold) < ENNReal.ofReal (A * r) := by
    subst j
    rw [← eq_of_heq hp', ← eq_of_heq hx', hbirth, H.stageMetric_initial,
      ← H.event_output i] at hd
    exact hd
  have hpostDist := hpostDistAt (H.activeStage t) hactive p x hO hx hdist
  have hterminalDist :=
    ((H.event i).oldTerminal_edist_le_of_outside_canonical_cap_windows S
      (records i).old_eq_retained hcanonical hε hD Oold xold hOoutside hxoutside).trans_lt
        hpostDist
  obtain ⟨R, hdR, hRAr⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hterminalDist)
  have hR : riemannianEDistOf (H.event i).terminal.metric
      ((H.event i).oldTerminal Oold) ((H.event i).oldTerminal xold) < ENNReal.ofReal R :=
    (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hterminalDist)).mpr hdR
  obtain ⟨eD, heD, heDage, hDistance⟩ :=
    exists_pos_clock_distance_lt_of_birth_terminal_distance_lt H t i hbirth Oold xold R hR
  have hgapCont : Continuous (fun w : ℝ => r * (A * (1 - 2 * w ^ 2 / r ^ 2))) := by
    fun_prop
  have hgap0 : R < r * (A * (1 - 2 * (0 : ℝ) ^ 2 / r ^ 2)) := by
    simpa only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero, mul_one, mul_comm r A]
      using hRAr
  have hgap : ∀ᶠ w in 𝓝 (0 : ℝ), R < r * (A * (1 - 2 * w ^ 2 / r ^ 2)) :=
    hgapCont.continuousAt.eventually (Ioi_mem_nhds hgap0)
  have hcubeCont : Continuous (fun w : ℝ => 6 * w ^ 3 / rho ^ 2) := by fun_prop
  have hcube0 : 6 * (0 : ℝ) ^ 3 / rho ^ 2 < r / 4 := by
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div] using
      (div_pos hr (by norm_num : (0 : ℝ) < 4))
  have hcubeNear : ∀ᶠ w in 𝓝 (0 : ℝ), 6 * w ^ 3 / rho ^ 2 < r / 4 :=
    hcubeCont.continuousAt.eventually (Iio_mem_nhds hcube0)
  obtain ⟨d, hd, hsmall⟩ := Metric.eventually_nhds_iff.mp (hgap.and hcubeNear)
  let e : ℝ := min eD (min (r / 4) (min (rho / 2) (d / 2)))
  have he : 0 < e := lt_min heD (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have heeD : e ≤ eD := min_le_left _ _
  have her : e ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have herho : e ≤ rho / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hed : e < d := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (half_lt_self hd)
  have heage : e ^ 2 < (t : ℝ) - H.time i.castSucc :=
    (pow_le_pow_left₀ he.le heeD 2).trans_lt heDage
  have heDist : dist e (0 : ℝ) < d := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using hed
  have hecube : 6 * e ^ 3 / rho ^ 2 ≤ r / 4 := (hsmall heDist).2.le
  have hHI := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  have hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ z : (H.stage j).Carrier, -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) z := by
    intro j s hs z
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num) ha₀ (le_add_of_nonneg_right htime)
    exact (show -(3 / a₀) ≤ -3 / (a₀ + s) by
      simpa only [neg_div] using neg_le_neg hratio).trans (hHI.1 j s hs z).2
  have hlocal : ∀ v : ℝ, 0 < v → v < e →
      ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
        (a : ℝ) = (t : ℝ) - v ^ 2 ∧
        H.activeStage a = i.castSucc ∧
        let first := H.activeStage a
        let last := H.activeStage t
        let hle := H.activeStage_mono hat
        let O := seedTrace.point first (H.activeStage_mono has) hle
        ∃ poleTrace : BackwardPointTrace H first last hle x,
          poleTrace.isRmControlled (hat := hat) rho ∧
          let y := poleTrace.point first le_rfl hle
          riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
            ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) ∧
          ∃ action : ℝ,
            action ∈ H.regularizedC1ActionValues first last hle t 0 v x y ∧
            (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v x y ∧
            H.regularizedCost first last hle t (3 / a₀) 0 v x y ≤ (action : WithTop ℝ) ∧
            action ≤ 6 * v ^ 3 / rho ^ 2 ∧
            ∃ (q : (H.stage first).Carrier) (L m : ℝ),
              H.regularizedCost first last hle t (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
              riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O q <
                ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
              L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
              H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q = (m : WithTop ℝ) ∧
              M v = (m : WithTop ℝ) ∧ 0 < m ∧
              2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧
              m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 ∧
              ∀ z : (H.stage first).Carrier,
                H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q ≤
                  H.physicalWeightedCost first last hle t (3 / a₀) r A v x O z := by
    intro v hv hve
    have hvr : v ≤ r / 4 := hve.le.trans her
    have hvrHalf : v ≤ r / 2 := by linarith
    have hvrho : v ≤ rho / 2 := hve.le.trans herho
    have hv2r : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv.le (by linarith : v ≤ r) 2
    have hv2rho : v ^ 2 ≤ rho ^ 2 :=
      pow_le_pow_left₀ hv.le (by linarith : v ≤ rho) 2
    have hasTime : (aSeed : ℝ) ≤ (t : ℝ) - v ^ 2 := by
      rw [hSeedClock]
      linarith only [hv2r]
    let a : Icc (0 : ℝ) H.horizon :=
      ⟨(t : ℝ) - v ^ 2, aSeed.property.1.trans hasTime,
        (sub_le_self (t : ℝ) (sq_nonneg v)).trans t.property.2⟩
    have has : aSeed ≤ a := hasTime
    have hat : a ≤ t := sub_le_self (t : ℝ) (sq_nonneg v)
    have hPoleA : aPole ≤ a := by
      change (aPole : ℝ) ≤ (t : ℝ) - v ^ 2
      rw [hPoleClock]
      linarith only [hv2rho]
    have hstage : H.activeStage a = i.castSucc := by
      apply (H.mem_stageDomain_iff a i.castSucc).mp
      change (t : ℝ) - v ^ 2 ∈ H.stageDomain i.castSucc
      rw [stageDomain, Fin.lastCases_castSucc]
      refine ⟨?_, ?_⟩
      · have hh := (pow_le_pow_left₀ hv.le hve.le 2).trans_lt heage
        linarith only [hh]
      · rw [← hbirth]
        exact sub_lt_self _ (sq_pos_of_pos hv)
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    let poleTrace : BackwardPointTrace H first last hle x :=
      fullPoleTrace.restrictFirst (H.activeStage_mono hPoleA) hle
    have hpTrace : poleTrace.isRmControlled (hat := hat) rho :=
      hFullPoleTrace.restrictFirst fullPoleTrace hrho.le le_rfl hPoleA hat
    let y := poleTrace.point first le_rfl hle
    have hpair (j : Fin (H.eventCount + 1)) (hs : H.activeStage aSeed ≤ j)
        (hxj : first ≤ j) (hj : j ≤ last) (heq : j = i.castSucc) :
        riemannianEDistOf (H.stageMetric j ((t : ℝ) - v ^ 2))
          (seedTrace.point j hs hj) (poleTrace.point j hxj hj) =
            riemannianEDistOf (H.stageMetric i.castSucc ((t : ℝ) - v ^ 2))
              Oold.val.val xold.val.val := by
      subst j
      rw [backward_trace_point_before_birth_eq_old H seedTrace i hactive hs Oold hO,
        backward_trace_point_before_birth_eq_old H poleTrace i hactive hxj xold hx]
    have hvDist : dist v (0 : ℝ) < d := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hv] using hve.trans hed
    have hsmallv := hsmall hvDist
    have hplateau : riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) := by
      rw [show riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y =
          riemannianEDistOf (H.stageMetric i.castSucc ((t : ℝ) - v ^ 2))
            Oold.val.val xold.val.val from
        hpair first (H.activeStage_mono has) le_rfl hle hstage]
      exact (hDistance v hv (hve.trans_le heeD)).trans_le
        (ENNReal.ofReal_le_ofReal hsmallv.1.le)
    obtain ⟨action, hC1, haction⟩ :=
      poleTrace.exists_regularizedC1ActionValues_le_of_isRmControlled hrho hv.le rfl hpTrace
    have hAC : (action : WithTop ℝ) ∈
        H.regularizedActionValues first last hle t (3 / a₀) 0 v x y :=
      H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle
        (fun j w hw z => hfloor j.val ((t : ℝ) - w ^ 2)
          (H.mapsTo_regularizedStage_Ioo t 0 v j.val hw) z) x y hC1
    have hcostle := H.regularizedCost_le_of_competitor first last hle t (3 / a₀) 0 v x y hAC
    have hhalf : v ^ 2 ≤ r ^ 2 / 2 := by
      have hh := pow_le_pow_left₀ hv.le hvrHalf 2
      nlinarith only [hh, sq_nonneg r]
    have hshift : 0 ≤ A * (1 - 2 * v ^ 2 / r ^ 2) := by
      apply mul_nonneg (by linarith only [hA])
      have hh : 2 * v ^ 2 / r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).mpr (by linarith)
      linarith only [hh]
    have hroom : 2 * v ^ 3 / r ^ 2 ≤ r / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      have hh := pow_le_pow_left₀ hv.le hvrHalf 3
      nlinarith only [hh]
    have hLsc : LowerSemicontinuous (H.regularizedCost first last hle t (3 / a₀) 0 v x) :=
      H.lowerSemicontinuous_regularizedCost first last hle t (3 / a₀) 0 v
        (by simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t)
        (fun j w hw z => hfloor j.val ((t : ℝ) - w ^ 2)
          (H.mapsTo_regularizedStage_Ioo t 0 v j.val hw) z) x
    have hLower (z : (H.stage first).Carrier) :
        ((-2 * v ^ 3 / r ^ 2 : ℝ) : WithTop ℝ) ≤
          H.regularizedCost first last hle t (3 / a₀) 0 v x z :=
      H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀ hfixed hscalar
        first last hle hr hv.le hhalf hrecent x z
    have hactionSmall : action ≤ r / 4 := haction.trans hsmallv.2.le
    have hplateau' : riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 20)) :=
      hplateau.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith only [hr]))
    obtain ⟨q, L, m, hcost, hinner, hLact, hLr, hW, hInf, hmpos, hlo, hhi, hglobal⟩ :=
      H.exists_physicalWeightedCost_minimum_of_plateau_competitor first last hle t (3 / a₀)
        r A v x O y hr hv hshift hroom hLsc hLower action hAC hactionSmall hplateau'
    have hM : M v = (m : WithTop ℝ) := by
      dsimp only [M, tracedPhysicalWeightedMinimum]
      rw [dite_eq_left hasTime]
      exact hInf
    have hhi' : m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 := by
      have h12 : 2 * action ≤ 12 * v ^ 3 / rho ^ 2 := by
        have h6 : 12 * v ^ 3 / rho ^ 2 = 2 * (6 * v ^ 3 / rho ^ 2) := by ring
        rw [h6]
        exact mul_le_mul_of_nonneg_left haction (by norm_num)
      linarith only [hhi, h12]
    refine ⟨a, has, hat, rfl, hstage, poleTrace, hpTrace, hplateau,
      action, hC1, hAC, hcostle, haction, q, L, m,
      hcost, hinner, hLact, hLr, hW, hM, hmpos, hlo, hhi', hglobal⟩
  have hbds : ∀ᶠ v in 𝓝[>] (0 : ℝ),
      M v ≠ ⊤ ∧ 2 * r - 4 * v ^ 3 / r ^ 2 ≤ (M v).untopD 0 / v ∧
        (M v).untopD 0 / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT he] with v hv
    obtain ⟨a, has, hat, hclock, hstage, trace, htrace, hplateau, action, hC1, hAC,
      hcostle, haction, q, L, m, hcost, hinner, hLact, hLr, hW, hM, hmpos, hlo, hhi, hglobal⟩ :=
      hlocal v hv.1 hv.2
    rw [hM, WithTop.untopD_coe]
    exact ⟨WithTop.coe_ne_top, hlo, hhi⟩
  have hlowLimit : Tendsto (fun v : ℝ => 2 * r - 4 * v ^ 3 / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
    have hc : Continuous (fun v : ℝ => 2 * r - 4 * v ^ 3 / r ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, sub_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hhighLimit : Tendsto (fun v : ℝ => 2 * r + 12 * v ^ 3 / rho ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
    have hc : Continuous (fun v : ℝ => 2 * r + 12 * v ^ 3 / rho ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨⟨e, he, her, herho, heage, hecube, hlocal⟩,
    hbds.mono (fun _ h => h.1),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowLimit hhighLimit
      (hbds.mono (fun _ h => h.2.1)) (hbds.mono (fun _ h => h.2.2))⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
