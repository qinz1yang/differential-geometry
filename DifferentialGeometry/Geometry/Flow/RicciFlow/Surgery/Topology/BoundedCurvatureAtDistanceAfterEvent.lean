import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowPointTimeSlack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventPullback

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem sqrt_two_mul_le_of_le_sqrt_exp_mul {A R Rσ d : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hRσ : 0 < Rσ) (hRσR : Rσ ≤ 2 * R) (hd : 0 ≤ d)
    (hdr : d ≤ Real.sqrt (Real.exp 1) * (A / Real.sqrt R)) :
    Real.sqrt 2 * d ≤ 4 * A / Real.sqrt Rσ := by
  have hsR := Real.sqrt_pos.mpr hR
  have hsσ := Real.sqrt_pos.mpr hRσ
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hse : Real.sqrt (Real.exp 1) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [Real.exp_one_lt_d9])
  have hσle : Real.sqrt Rσ ≤ Real.sqrt 2 * Real.sqrt R := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hRσR
  have hdR : d * Real.sqrt R ≤ Real.sqrt (Real.exp 1) * A := by
    rw [mul_div_assoc', le_div_iff₀ hsR] at hdr
    exact hdr
  rw [le_div_iff₀ hsσ]
  calc Real.sqrt 2 * d * Real.sqrt Rσ ≤ Real.sqrt 2 * d * (Real.sqrt 2 * Real.sqrt R) :=
        mul_le_mul_of_nonneg_left hσle (mul_nonneg hs2n hd)
    _ = 2 * (d * Real.sqrt R) := by linear_combination (d * Real.sqrt R) * hs2
    _ ≤ 2 * (Real.sqrt (Real.exp 1) * A) := by linarith
    _ ≤ 4 * A := by linarith [mul_le_mul_of_nonneg_right hse hA.le]

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ (j : Fin H.eventCount) {s : ℝ}
        (Gk : (H.stage j.succ).IncomingSlab (H.time j.succ) s),
        Gk.flow.base.metric (H.time j.succ) = H.initialMetric j.succ →
      ∀ {t : ℝ} (_ : H.time j.succ < t) (_ : t < s)
        (y : (H.stage j.succ).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * Gk.flow.scalar t y → Λ ≤ Gk.flow.scalar t y →
      Λ ≤ Gk.flow.scalar t y * H.time j.succ →
      (∀ x, |Gk.flow.scalar t x - Gk.flow.scalar (H.time j.succ) x| ≤ Gk.flow.scalar t y / 4) →
      (∀ x (v : TangentSpace ThreeModel x),
        (Gk.flow.base.metric (H.time j.succ)).inner x v v ≤
          Real.exp 1 * (Gk.flow.base.metric t).inner x v v) →
      H.EventSlabsSpatiallyCanonical ε C1 C2 q j.succ →
      H.EventSlabsDerivative Ctime q j.succ → H.EventSlabsGradient Cgrad q j.succ →
      H.EventSlabsPinched phi → H.NoncollapsedBefore κ ρ (H.time j.succ) →
      Λ ≤ ρ * Real.sqrt (Gk.flow.scalar t y) →
      ¬ H.CapWindowPoint records j.succ y (H.time j.succ) Dcap θ →
      ∀ z ∈ riemannianBallOf (Gk.flow.base.metric t) y (A / Real.sqrt (Gk.flow.scalar t y)),
        Gk.flow.scalar t z ≤ Q * Gk.flow.scalar t y := by
  obtain ⟨QB, ΛB, DB, RB, ζB, hQB, hΛB, hDB, hDRB, hζB, hB⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event.{u} hεle κ
      C1 C2 hκ Ctime Cgrad hphi (4 * A) (by positivity) (2 * Cq) (θ / 2) (by positivity)
  have hTE := StandardCap.transitionEnd_pos
  set Kc : ℝ := 2 * QB + 1 with hKc
  set W : ℝ := 2 * StandardCap.transitionEnd +
    Real.sqrt (8 * Kc) * (Real.sqrt (Real.exp 1) * A) with hW
  set Dcap : ℝ := max DB W + 1 with hDcap
  have hDBle : DB ≤ Dcap := by rw [hDcap]; linarith [le_max_left DB W]
  have hWlt : W < Dcap := by rw [hDcap]; linarith [le_max_right DB W]
  have hTEDcap : StandardCap.transitionEnd < Dcap := hDB.trans_le hDBle
  obtain ⟨ε₀, hε₀, hsc⟩ :=
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u} Dcap hTEDcap
  refine ⟨2 * QB + 2, 4 * ΛB, Dcap, max RB Dcap, min ζB (min (1 / 2) ε₀), by linarith,
    by linarith, hTEDcap, le_max_right _ _, lt_min hζB (lt_min (by norm_num) hε₀), ?_⟩
  intro H p₀ δb ρb p records hrec hRrad hord hζ j s Gk hGk t hat hts y q ρ hq hqy hΛy hΛa
    hclose hmet hspat hder hgrad hpinch hnc hρ hnot z hz
  set R := Gk.flow.scalar t y with hRdef
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hsR := Real.sqrt_pos.mpr hR0
  have hRa (x : (H.stage j.succ).Carrier) :
      Gk.flow.scalar (H.time j.succ) x = metricScalarAt (H.initialMetric j.succ) x := by
    change metricScalarAt (Gk.flow.base.metric (H.time j.succ)) x = _
    rw [hGk]
  have hRay := hclose y
  rw [hRa y, abs_le] at hRay
  have ha0 : 0 < H.time j.succ := by
    have h := H.time_strictMono (Fin.succ_pos j)
    rwa [H.time_zero] at h
  have hcan := hrec.2.2.2.2.2.1
  have hDmodel : Dcap ≤ p.modelRadius := by
    rw [hrec.2.1]
    exact (le_max_right _ _).trans hRrad
  have hacc : p.modelAccuracy ≤ 1 / 2 := by
    rw [hrec.2.2.2.1]
    exact hζ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hscale (i : Fin H.eventCount) (b : (H.toHistory.event i).RetainedBoundaryIndex)
      (w : ThreeBall) :
      ((records i).static b).neck.scale / 2 ≤
        metricScalarAt ((records i).static b).witness.metric
          (((records i).static b).witness.cap w) :=
    hsc (H.toHistory.event i) hDmodel
      (by rw [hrec.2.2.2.1]; exact hζ.trans ((min_le_right _ _).trans (min_le_right _ _)))
      (by rw [hrec.2.2.1]; exact hord) ((records i).static b) (hcan i b) w
  have hle : j.castSucc ≤ j.succ := j.castSucc_lt_succ.le
  set U := H.toHistory.backwardSurvivorDomain j.castSucc j.succ hle with hU
  have hyU : y ∈ U := by
    by_contra hyU
    exact hnot (H.capWindowPoint_at_event_of_not_regularCrossing records hcan j
      (H.not_regularCrossing_of_not_mem_backwardSurvivorDomain j hyU) (by linarith) hθ.le)
  obtain ⟨S, hS, hSb⟩ := H.exists_forall_neck_scale_le records
  set lo : ℝ := max (max (H.time j.castSucc) (H.time j.succ / 2))
    (H.time j.succ - θ / (2 * S)) with hlo
  have hloa : lo < H.time j.succ := by
    have h1 : H.time j.castSucc < H.time j.succ := H.time_strictMono j.castSucc_lt_succ
    have h2 : 0 < θ / (2 * S) := by positivity
    exact max_lt (max_lt h1 (by linarith)) (by linarith)
  obtain ⟨σ, ⟨hsc1, hdist⟩, hσlo, hσa⟩ :=
    ((H.toHistory.eventually_backwardSurvivor_scalar_close_and_edist_le j
      (δ := R / 8) (by positivity)).and (Ioo_mem_nhdsLT hloa)).exists
  have hσj : H.time j.castSucc < σ :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hσlo
  have hσhalf : H.time j.succ / 2 < σ :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hσlo
  have hσθ : H.time j.succ - θ / (2 * S) < σ := (le_max_right _ _).trans_lt hσlo
  have hslack : S * (H.time j.succ - σ) ≤ θ - θ / 2 := by
    have h1 : H.time j.succ - σ ≤ θ / (2 * S) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hS.le
    have h3 : S * (θ / (2 * S)) = θ / 2 := by field_simp
    linarith
  let Φ := H.toHistory.backwardSurvivorMap j.castSucc j.succ hle j.castSucc le_rfl hle
  let y' : U := ⟨y, hyU⟩
  set G := (H.toHistory.event j).incoming with hG
  have hyσ := hsc1 y'
  rw [abs_lt] at hyσ
  change -(R / 8) < metricScalarAt (G.flow.base.metric σ) (Φ y') -
      metricScalarAt (H.initialMetric j.succ) y ∧ _ at hyσ
  have hRσlo : R / 2 ≤ G.flow.scalar σ (Φ y') := by
    change R / 2 ≤ metricScalarAt (G.flow.base.metric σ) (Φ y')
    linarith [hyσ.1, hyσ.2]
  have hRσhi : G.flow.scalar σ (Φ y') ≤ 2 * R := by
    change metricScalarAt (G.flow.base.metric σ) (Φ y') ≤ 2 * R
    linarith [hyσ.1, hyσ.2]
  have hRσ0 : 0 < G.flow.scalar σ (Φ y') := by linarith
  have hCq : 0 ≤ Cq := by
    by_contra hneg
    have : Cq * R < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hR0
    linarith
  have hqσ : q ≤ 2 * Cq * G.flow.scalar σ (Φ y') := by
    have h1 : Cq * R ≤ Cq * (2 * G.flow.scalar σ (Φ y')) :=
      mul_le_mul_of_nonneg_left (by linarith) hCq
    linarith
  have hΛσ : ΛB ≤ G.flow.scalar σ (Φ y') := by linarith
  have hΛσt : ΛB ≤ G.flow.scalar σ (Φ y') * σ := by
    have h1 : R / 2 * (H.time j.succ / 2) ≤ G.flow.scalar σ (Φ y') * σ :=
      mul_le_mul hRσlo hσhalf.le (by positivity) hRσ0.le
    linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra hneg
    have : ρ * Real.sqrt R < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hsR
    linarith
  have hsqσ : Real.sqrt R / 2 ≤ Real.sqrt (G.flow.scalar σ (Φ y')) := by
    rw [Real.le_sqrt (by positivity) hRσ0.le, div_pow, Real.sq_sqrt hR0.le]
    linarith
  have hρσ : ΛB ≤ ρ * Real.sqrt (G.flow.scalar σ (Φ y')) := by
    have := mul_le_mul_of_nonneg_left hsqσ hρ0
    linarith
  have hcross : (H.toHistory.event j).RegularCrossing (Φ y') y := by
    have h := H.toHistory.backwardSurvivorMap_crossing j.castSucc j.succ hle j le_rfl le_rfl y'
    rwa [H.toHistory.backwardSurvivorMap_last] at h
  have hnotσ : ¬ H.CapWindowPoint records j.castSucc (Φ y') σ DB (θ / 2) := by
    rintro ⟨j', hl', A', b, x, hx, hxn, hage⟩
    have hcw : H.CapWindowPoint records j.succ y σ DB (θ / 2) :=
      ⟨j', hl'.trans hle, A'.append y hcross, b, x,
        by rw [BackwardPointTrace.append_point_before]; exact hx, hxn, hage⟩
    exact hnot ((hcw.of_le_time hσa.le hSb hslack).mono hDBle le_rfl)
  have hBσ := hB H p₀ δb ρb records hrec ((le_max_left _ _).trans hRrad) hord
    (hζ.trans (min_le_left _ _)) j hσj hσa (Φ y') q ρ hq hqσ hΛσ hΛσt
    (fun x hx => hspat j j.castSucc_lt_succ x σ ⟨hσj, hσa⟩ hx)
    (fun i hi => hder i (hi.trans j.castSucc_lt_succ))
    (fun x v hv hx => hder j j.castSucc_lt_succ x v ⟨hv.1, hv.2.trans hσa⟩ hx)
    (fun x v hv hx => hgrad j j.castSucc_lt_succ x v ⟨hv.1, hv.2.trans hσa⟩ hx)
    hpinch (H.noncollapsedBefore_mono hσa.le hnc) hρσ hnotσ
  set r : ℝ := Real.sqrt (Real.exp 1) * (A / Real.sqrt R) with hr
  have hbound : ∀ d : ℝ, d ≤ r → riemannianBallOf (H.initialMetric j.succ) y d ⊆ U →
      ∀ w ∈ riemannianBallOf (H.initialMetric j.succ) y d,
        metricScalarAt (H.initialMetric j.succ) w ≤ Kc * R := by
    intro d hdr hsub w hw
    have hd0 : 0 < d := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hw)
    let w' : U := ⟨w, hsub hw⟩
    have h1 : riemannianEDistOf ((H.initialMetric j.succ).restrictOpen U) y' w' <
        ENNReal.ofReal d :=
      Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset _ U y' w'
        hsub hw
    have h3 : riemannianEDistOf (G.flow.base.metric σ) (Φ y') (Φ w') <
        ENNReal.ofReal (Real.sqrt 2 * d) := by
      have hm := ENNReal.mul_lt_mul_left
        (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < Real.sqrt 2)).ne'
        ENNReal.ofReal_ne_top h1
      rw [mul_comm _ (ENNReal.ofReal (Real.sqrt 2)),
        mul_comm (ENNReal.ofReal d)] at hm
      calc _ ≤ _ := hdist y' w'
        _ < ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal d := hm
        _ = _ := (ENNReal.ofReal_mul (Real.sqrt_nonneg 2)).symm
    have h4 := sqrt_two_mul_le_of_le_sqrt_exp_mul hA hR0 hRσ0 hRσhi hd0.le hdr
    have h5 := hBσ (Φ w') (lt_of_lt_of_le h3 (ENNReal.ofReal_le_ofReal h4))
    have h6 := hsc1 w'
    rw [abs_lt] at h6
    change metricScalarAt (G.flow.base.metric σ) (Φ w') ≤
      QB * metricScalarAt (G.flow.base.metric σ) (Φ y') at h5
    change metricScalarAt (G.flow.base.metric σ) (Φ y') ≤ 2 * R at hRσhi
    change -(R / 8) < metricScalarAt (G.flow.base.metric σ) (Φ w') -
      metricScalarAt (H.initialMetric j.succ) w ∧ _ at h6
    have h7 : QB * metricScalarAt (G.flow.base.metric σ) (Φ y') ≤ QB * (2 * R) :=
      mul_le_mul_of_nonneg_left hRσhi (by linarith)
    change metricScalarAt (H.initialMetric j.succ) w ≤ (2 * QB + 1) * R
    linarith [h6.1, h6.2]
  have hsubU : riemannianBallOf (H.initialMetric j.succ) y r ⊆ U := by
    by_contra hns
    obtain ⟨q₀, hq₀U, d₀, hd₀, hd₀r, hdeq, hsub, hcl⟩ :=
      OrientedThreeStage.exists_first_touch_of_not_subset (H.stage j.succ)
        (H.initialMetric j.succ) U hyU hns
    have hRq : metricScalarAt (H.initialMetric j.succ) q₀ ≤ Kc * R :=
      closure_minimal (fun w hw => hbound d₀ hd₀r.le hsub w hw)
        (isClosed_le (metricScalar_smooth (H.initialMetric j.succ)).continuous continuous_const)
        hcl
    have hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * (Kc * R)) * d₀ < Dcap := by
      have hKc0 : 0 < 8 * Kc := by rw [hKc]; linarith
      have hs8 := Real.sqrt_pos.mpr hKc0
      rw [show 8 * (Kc * R) = 8 * Kc * R by ring, Real.sqrt_mul hKc0.le]
      have hdR : d₀ * Real.sqrt R < Real.sqrt (Real.exp 1) * A := by
        have := mul_lt_mul_of_pos_right hd₀r hsR
        rwa [hr, mul_assoc, div_mul_cancel₀ A hsR.ne'] at this
      have : Real.sqrt (8 * Kc) * Real.sqrt R * d₀ <
          Real.sqrt (8 * Kc) * (Real.sqrt (Real.exp 1) * A) := by
        rw [mul_assoc, mul_comm (Real.sqrt R) d₀]
        exact mul_lt_mul_of_pos_left hdR hs8
      linarith
    exact hnot (H.capWindowPoint_at_event_of_edist_le records hcan hscale hacc j
      (H.not_regularCrossing_of_not_mem_backwardSurvivorDomain j hq₀U) hRq
      (by rw [riemannianEDistOf_comm, hdeq]) hd₀.le hwin hDmodel hθ.le)
  have hzr : z ∈ riemannianBallOf (H.initialMetric j.succ) y r := by
    have h := riemannianBallOf_subset_of_inner_le_mul (Gk.flow.base.metric t)
      (Gk.flow.base.metric (H.time j.succ)) y (Real.exp_pos 1) (fun x _ v => hmet x v) hz
    rwa [hGk] at h
  have hz1 := hbound r le_rfl hsubU z hzr
  have hz2 := hclose z
  rw [hRa z, abs_le] at hz2
  rw [hKc] at hz1
  linarith [hz2.1, hz2.2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
