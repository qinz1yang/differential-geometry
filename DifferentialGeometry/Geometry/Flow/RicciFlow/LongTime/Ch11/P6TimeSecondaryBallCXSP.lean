import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SecondaryBallBoundsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SecondaryTraceDepthCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodSuffixCXSP

/-!
# CX-SPINE: an actual common trace window for the secondary open ball

The history time core supplies the terminal spatial witness. Its scalar bound
and the real center footprint pay the point-window inputs on the exact open
ball of radius 1/sqrt(Rn). Equal physical clocks identify a common starting a.
The secondary depth theta is chosen before L; the late time may depend on L.
A shorter positive beta pays the explicit time-derivative and half-window
budgets. Restricting the actual traces preserves their original footprint;
the time core then bounds scalar curvature along every complete trace.
The time-core constants are independent of the chain construction constants.
All conclusions use the original history and its original Afac footprint.
The only surgery-scale guard is neckRadius(t) <= r, with no upper bound on
r/neckRadius(t); a sequence with that ratio tending to infinity is eventually
in this regime. The Rn/Q scalar band is a separate endpoint hypothesis.
The upstream seed shift may query the time core at a larger factor, but its
output footprint remains Afac. No kappa supply or RegularSlice is used here.
This is a secondary-ball trace producer, not a proof of the full hspine.
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u
/-- TimeCore 与实际 chain 在精确 secondary 开球上生产共同 a、全部 traces，
以及独立于 L 的 secondary depth。 -/
theorem exists_prepared_time_secondary_ball_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ C : ℝ, 1 ≤ C → 2 * C2 ≤ C →
        ∃ θ : ℝ, 0 < θ ∧ θ = β0 / (2 * (C + 1)) ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (C * L + 1)) / Real.sqrt Q
        let β := β0 / (C * L + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        let U := riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Real.sqrt Rn)⁻¹
        ∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) ∧ 1 ≤ Q * (a : ℝ) ∧
          H.time (H.activeStage a) < (t : ℝ) - θ / Rn ∧
          ∀ x ∈ U, ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) ∧
              metricScalarAt (H.stageMetric (H.activeStage v) v)
                (B.point (H.activeStage v) (H.activeStage_mono hav)
                  (H.activeStage_mono hvt)) ≤ 2 * ((C * L) * Q) := by
  obtain ⟨ε₀, hε₀, hpoint⟩ := exists_prepared_time_trace_window_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨Kcan, Tcan, _hKcan, hTcan, hcanonical⟩ := hb Afac (zero_lt_one.trans hA)
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  obtain ⟨H0, hH0, hpointA⟩ := hpoint S F q hTower hdiag hacc hrad hord hb Afac hA
  have hHpos : 0 < H0 := by linarith
  let L0 : ℝ := max (max 3 (1 + Kcan / H0)) (1 + 10000 * KG / H0)
  have hL03 : 3 ≤ L0 := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨H0, L0, hH0, hL03, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, βold, hlam0, hβold, hpointM⟩ := hpointA d0 Δ γ hd0 hΔ hγ hbuffer
  let β0 : ℝ := min βold (min (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
  have hβ0 : 0 < β0 := by dsimp [β0]; positivity
  have hβoldle : β0 ≤ βold := min_le_left _ _
  have hβH : β0 ≤ H0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβtime : (Ctime : ℝ) * β0 ≤ 1 / 4 := by
    have h := (min_le_right βold _).trans
      (min_le_right (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ((Ctime : ℝ) + 1))).mp h
    nlinarith only [hmul, hβ0]
  refine ⟨lam0, β0, hlam0, hβ0, ?_⟩
  intro C hC hC2
  let θ : ℝ := β0 / (2 * (C + 1))
  have hθpos : 0 < θ := div_pos hβ0 (by linarith)
  refine ⟨θ, hθpos, rfl, ?_⟩
  intro L hL
  have hL3 : 3 ≤ L := hL03.trans hL
  have hmL : L ≤ C * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ L)
  have hm : 1 / 2 ≤ C * L := by linarith
  have hden : 0 < C * L + 1 := by linarith
  have hthreshold : Kcan ≤ H0 * (L - 1) := by
    have h := (le_max_right 3 (1 + Kcan / H0)).trans
      ((le_max_left _ _).trans hL)
    have hratio : Kcan / H0 ≤ L - 1 := by linarith
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  have hGoodCoef : 10000 * KG ≤ H0 * (C * L) := by
    have h := (le_max_right (max 3 (1 + Kcan / H0)) _).trans hL
    have hratio : 10000 * KG / H0 ≤ C * L := by linarith
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  obtain ⟨TS, _hTS, hpointN⟩ := hpointM (C * L) hm
  refine ⟨max (max Tcan (2 * TG)) TS,
    hTcan.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro n H t p r Q ell β ht htime hsmall hvol hguard aSeed haT hclock seedTrace
    y dCenter hdCenter hfit hcenter Rn hlower hupper U
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos hr))
  have hM : 0 < (C * L) * Q := mul_pos (by linarith) hQ
  have hradH : 0 < 1 / Real.sqrt H0 := one_div_pos.mpr (Real.sqrt_pos.mpr hHpos)
  have hcenterA : dCenter < Afac := by linarith only [hfit, hbuffer, hradH, hΔ, hγ]
  have hyA : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (Afac * r) := by
    apply hcenter.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (zero_lt_one.trans hA) hr)).mpr
    exact mul_lt_mul_of_pos_right hcenterA hr
  have hR : Kcan * (r ^ 2)⁻¹ ≤ Rn := by
    have hmul := mul_le_mul_of_nonneg_right hthreshold (inv_nonneg.mpr (sq_nonneg r))
    have hle : Kcan * (r ^ 2)⁻¹ ≤ Q * (L - 1) := by
      dsimp only [Q]
      nlinarith only [hmul]
    exact hle.trans hlower.le
  obtain ⟨W, _hchart⟩ := (hcanonical n t p r
    ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
    htime hsmall hvol y hyA hR).1
  have hyU : y ∈ U := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) y y < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos))
  have hscalar := (secondary_unit_ball_scalar_CXSP W hC hC2 hL3 hQ hupper).2
  have hdist := secondary_unit_ball_distance_CXSP
    (H.stageMetric (H.activeStage t) t) hHpos hr hL3 hlower hdCenter hfit hcenter
  have hpointX (x : (H.stageAt t).Carrier) (hx : x ∈ U) :=
    hpointN n t p r ((le_max_right _ _).trans ht) htime hsmall hvol hguard
      aSeed haT hclock seedTrace x (hscalar x hx) (hdist x hx)
  obtain ⟨aold, haoldSeed, _haoldt, haoldClock, _holdDepth, _hcenterTrace⟩ := hpointX y hyU
  have hβ : 0 < β := div_pos hβ0 hden
  have hβle : β ≤ βold / (C * L + 1) := div_le_div_of_nonneg_right hβoldle hden.le
  have hβH' : β ≤ H0 / 4 :=
    (div_le_self hβ0.le (by linarith : 1 ≤ C * L + 1)).trans hβH
  have htau : 0 < β / Q := div_pos hβ hQ
  have htauR : β / Q ≤ r ^ 2 / 4 := calc
    β / Q ≤ (H0 / 4) / Q := div_le_div_of_nonneg_right hβH' hQ.le
    _ = r ^ 2 / 4 := by dsimp only [Q]; field_simp [hHpos.ne', hr.ne']
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - β / Q,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r], (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have hclocks (a' : Icc (0 : ℝ) H.horizon)
      (ha' : (a' : ℝ) = (t : ℝ) - (βold / (C * L + 1)) / Q) : a' ≤ a := by
    change (a' : ℝ) ≤ (t : ℝ) - β / Q
    rw [ha']
    exact sub_le_sub_left (div_le_div_of_nonneg_right hβle hQ.le) _
  have haa : aSeed ≤ a := haoldSeed.trans (hclocks aold haoldClock)
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - β / Q
    nlinarith only [htauR, sq_nonneg r]
  have haClock : (a : ℝ) = (t : ℝ) - β / Q := rfl
  have hdepth : Q * ((t : ℝ) - a) = β := by
    change Q * ((t : ℝ) - ((t : ℝ) - β / Q)) = β
    rw [sub_sub_cancel, mul_div_cancel₀ _ hQ.ne']
  have hQa : 1 ≤ Q * (a : ℝ) := by
    have hra : r ^ 2 ≤ (a : ℝ) := by
      rw [haClock]
      nlinarith only [htime, htauR, sq_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hra hQ.le
    have hQr : Q * r ^ 2 = H0 := by dsimp only [Q]; field_simp [hr.ne']
    rw [hQr] at hmul
    linarith only [hmul, hH0]
  have hratio : L - 1 < Rn / Q := by
    apply (lt_div_iff₀ hQ).mpr
    simpa only [mul_comm] using hlower
  have hθdepth : θ / Rn < β / Q :=
    (secondary_depth_lt_uniform_window_CXSP hC hL3 hQ hratio hβ0).2
  have hstart : H.time (H.activeStage a) ≤ (t : ℝ) - β / Q :=
    (H.activeStage_time_le a).trans_eq haClock
  have hbudget : Ctime * ((C * L) * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    have heq : (C * L + 1) * β = β0 := mul_div_cancel₀ _ hden.ne'
    have hmb : C * L * β ≤ β0 := by nlinarith only [heq, hβ]
    have htb := (mul_le_mul_of_nonneg_left hmb Ctime.coe_nonneg).trans hβtime
    have hc : Ctime * ((C * L) * Q) * ((t : ℝ) - a) = Ctime * (C * L * β) := by
      rw [haClock, sub_sub_cancel]
      field_simp [hQ.ne']
    rw [hc]
    linarith only [htb]
  have hGoodThreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ (C * L) * Q := by
    have hmul := mul_le_mul_of_nonneg_right hGoodCoef (inv_nonneg.mpr (sq_nonneg r))
    dsimp only [Q]
    nlinarith only [hmul]
  refine ⟨a, haa, hat, haClock, hdepth, hhalf, hQa,
    hstart.trans_lt (sub_lt_sub_left hθdepth t), ?_⟩
  intro x hx
  obtain ⟨ax, _haxSeed, _haxt, hxClock, _hxDepth, Bold, hBold⟩ := hpointX x hx
  have haxa : ax ≤ a := hclocks ax hxClock
  let B := Bold.restrictFirst (H.activeStage_mono haxa) (H.activeStage_mono hat)
  let AA := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
  have hdistance (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      AA.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
      AA.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        AA.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) :=
    hBold v (haxa.trans hav) hvt
  have hcontrol := B.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hRv => by
      have hfoot : B.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt) ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
            (H.activeStage_mono hvt)) (Afac * r) :=
        (hdistance v hav hvt).1.trans_le (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (by linarith : d0 + Δ ≤ Afac) hr.le))
      have hGoodV := hGood n t p r
        ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
        htime hsmall hvol aSeed haT hclock seedTrace v (haa.trans hav) hvt
        (hhalf.trans (show (a : ℝ) ≤ v from hav)) _ hfoot
        (hGoodThreshold.trans_lt hRv).le
      exact hGoodV.2 hage htop) (hscalar x hx) hbudget
  exact ⟨B, fun v hav hvt =>
    ⟨(hdistance v hav hvt).1, (hdistance v hav hvt).2, hcontrol v hav hvt⟩⟩

end GC.LongTime.Ch11
