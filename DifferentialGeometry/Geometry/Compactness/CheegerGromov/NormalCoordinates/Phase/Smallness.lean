import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness
import DifferentialGeometry.Analysis.ODE.PhaseEndpointInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalRadiusProfile
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Flow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

open Filter Set Topology
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry
namespace HCGCompactness

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section RawPhaseSmallness

variable [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile

def phaseRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : Real :=
  h.ratio * hd.mu R / 4

theorem phaseRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : 0 < h.phaseRadius R := by
  dsimp only [phaseRadius]
  exact div_pos (h.floor_pos R) (by norm_num)

theorem phaseRadius_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    Metric.ball (0 : E) (h.phaseRadius R) ⊆
      Metric.ball (0 : E) (hb.radius k x) := by
  apply Metric.ball_subset_ball
  calc
    h.phaseRadius R ≤ h.ratio * hd.mu R := by
      dsimp only [phaseRadius]
      nlinarith [h.floor_pos R]
    _ ≤ hb.radius k x := h.floor_le_radius hx

theorem phaseRadius_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    Metric.ball (0 : E) (h.phaseRadius R) ⊆ Metric.ball (0 : E)
      (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply Metric.ball_subset_ball
  dsimp only [phaseRadius]
  exact div_le_div_of_nonneg_right (h.floor_le_exp hx) (by norm_num)

end NormalRadiusProfile

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem normalPhaseK_zero
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) : normalPhaseK h 0 = 0 := by
  apply NNReal.eq
  simp [normalPhaseK]
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseK_cont
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) :
    Continuous (normalPhaseK h) := by
  unfold normalPhaseK
  apply Continuous.subtype_mk
  fun_prop

omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseK_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) :
    Tendsto (normalPhaseK h) (nhds 0) (nhds 0) := by
  have hcont : Tendsto (normalPhaseK h) (nhds (0 : NNReal))
      (nhds (normalPhaseK h 0)) := (normalPhaseK_cont h).continuousAt
  simpa using hcont

omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseErr_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) :
    Tendsto (fun R ↦ PhaseFlow.phaseErr (normalPhaseK h R))
      (nhds 0) (nhds 0) :=
  PhaseFlow.phaseErr_tendsto.comp (normalPhaseK_lim h)

omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseErr_lt_ev
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ R in nhds 0, PhaseFlow.phaseErr (normalPhaseK h R) < eps :=
  normalPhaseErr_lim h (Iio_mem_nhds heps)

omit [NeZero (Module.finrank Real E)] in
theorem exists_normal_q_lt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    {r : Real} (hr : 0 < r) {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps := by
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
    htwo (normalPhaseErr_lt_ev (I := I) h heps)
  obtain ⟨δ, hδ, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (δ / 4) (min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos hδ (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqδ : qReal ≤ δ / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) δ := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < δ
    rw [sub_zero, abs_of_pos hqReal]
    exact hqδ.trans_lt (div_lt_self hδ (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
    herr q hqBall
  have hqRadius' : 4 * qReal < r := by
    nlinarith
  have hqProd : qReal * (24 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 12 * C * qReal ≤ 1 := by
    nlinarith
  have hmul : 0 ≤ qReal * (1 - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  refine ⟨q, ?_, ?_, ?_, herrQ⟩
  · exact_mod_cast hqReal
  · change 4 * qReal < r
    exact hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith

namespace NormalRadiusProfile

theorem exists_phase_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < h.phaseRadius R ∧
      3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < eps :=
  exists_normal_q_lt (I := I) hb (h.phaseRadius_pos R) heps

theorem exists_phase_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ : Real,
      0 < aq ∧ 0 < aδ ∧
      ∀ R, 0 ≤ R →
        ∃ q : NNReal,
          (q : Real) = aq * hd.mu R ∧
          6 * (q : Real) < h.phaseRadius R ∧
          3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 ∧
          aδ * hd.mu R ≤
            ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
              ((q : Real) / 2) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  have hT : 0 < T := PhaseFlow.freeDiagInv_pos (E := E)
  have hTReal : (0 : Real) < T := by exact_mod_cast hT
  let epsInv : NNReal := T / (48 * (N + 1))
  have hepsInv : 0 < epsInv := by
    dsimp only [epsInv]
    exact div_pos hT (mul_pos (by norm_num) (by positivity))
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < epsInv :=
    htwo (normalPhaseErr_lt_ev (I := I) hb hepsInv)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := hb.metricC 1
  have hC : 0 ≤ C := hb.metricC_nonneg 1
  have hμ0 : 0 < hd.mu 0 := hd.mu_pos 0
  let accelBound : Real := 1 / (36 * (C + 1))
  have hden : 0 < 36 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccel : 0 < accelBound := one_div_pos.mpr hden
  let aq : Real := min (h.ratio / 48)
    (min (eps / (2 * hd.mu 0)) (accelBound / hd.mu 0))
  have haq : 0 < aq := by
    dsimp only [aq]
    exact lt_min (div_pos h.ratio_pos (by norm_num))
      (lt_min (div_pos heps (mul_pos (by norm_num) hμ0))
        (div_pos haccel hμ0))
  let aδ : Real := (T : Real) * aq / 4
  have haδ : 0 < aδ := by
    dsimp only [aδ]
    exact div_pos (mul_pos hTReal haq) (by norm_num)
  refine ⟨aq, aδ, haq, haδ, ?_⟩
  intro R hR
  have hμR : 0 < hd.mu R := hd.mu_pos R
  have hμle : hd.mu R ≤ hd.mu 0 := hd.mu_antitone hR
  let qReal : Real := aq * hd.mu R
  have hqReal : 0 < qReal := mul_pos haq hμR
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have haqRatio : aq ≤ h.ratio / 48 := min_le_left _ _
  have haqEps : aq ≤ eps / (2 * hd.mu 0) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haqAccel : aq ≤ accelBound / hd.mu 0 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqEps : qReal ≤ eps / 2 := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (eps / (2 * hd.mu 0)) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqEps hμ0.le
      _ = eps / 2 := by field_simp [ne_of_gt hμ0]
  have hqAccel : qReal ≤ accelBound := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (accelBound / hd.mu 0) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqAccel hμ0.le
      _ = accelBound := by field_simp [ne_of_gt hμ0]
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (half_lt_self heps)
  have herrQ : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < epsInv :=
    herr q hqBall
  have hN1 : (1 : NNReal) ≤ N + 1 := by
    exact le_add_of_nonneg_left N.2
  have hden_ge : (2 : NNReal) ≤ 48 * (N + 1) := by
    calc
      (2 : NNReal) = 2 * 1 := by norm_num
      _ ≤ 2 * (N + 1) := mul_le_mul_of_nonneg_left hN1 (by norm_num)
      _ ≤ 48 * (N + 1) :=
        mul_le_mul_of_nonneg_right (by norm_num) (N + 1).2
  have heps_le : epsInv ≤ T / 2 := by
    dsimp only [epsInv]
    exact div_le_div_of_nonneg_left T.2 (by norm_num) hden_ge
  have herrHalf : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 :=
    herrQ.trans_le heps_le
  have hqRadius : 6 * (q : Real) < h.phaseRadius R := by
    have haRatio : 6 * aq < h.ratio / 4 := by
      nlinarith [h.ratio_pos]
    calc
      6 * (q : Real) = (6 * aq) * hd.mu R := by
        change 6 * qReal = _
        dsimp only [qReal]
        ring
      _ < (h.ratio / 4) * hd.mu R := mul_lt_mul_of_pos_right haRatio hμR
      _ = h.phaseRadius R := by
        dsimp only [phaseRadius]
        ring
  have hqProd : qReal * (36 * (C + 1)) ≤ 1 := by
    calc
      qReal * (36 * (C + 1)) ≤ accelBound * (36 * (C + 1)) :=
        mul_le_mul_of_nonneg_right hqAccel hden.le
      _ = 1 := by
        dsimp only [accelBound]
        field_simp [ne_of_gt hden]
  have hlinear : 18 * C * qReal ≤ 1 := by
    nlinarith [mul_nonneg hC hqReal.le]
  have hmul : 0 ≤ qReal * (1 - 18 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  have hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real) := by
    change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  have herrOut : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T := by
    calc
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 := herrHalf
      _ < T := by exact_mod_cast (half_lt_self hTReal)
  have hinvErr :
      N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 := by
    let c : NNReal := PhaseFlow.phaseErr (normalPhaseK hb (2 * q))
    have hdenInv : 0 < 48 * (N + 1) :=
      mul_pos (by norm_num) (by positivity)
    have hsmall : c * (48 * (N + 1)) < T := by
      apply (lt_div_iff₀ hdenInv).mp
      simpa only [c, epsInv] using herrQ
    have hfac : 24 * N + 1 ≤ 48 * (N + 1) := by
      nlinarith [N.2]
    have hcFac : c * (24 * N + 1) < T :=
      (mul_le_mul_of_nonneg_left hfac c.2).trans_lt hsmall
    have honeFac : (1 : NNReal) ≤ 24 * N + 1 := by
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) N.2)
    have hct : c < T := by
      calc
        c = c * 1 := by rw [mul_one]
        _ ≤ c * (24 * N + 1) :=
          mul_le_mul_of_nonneg_left honeFac c.2
        _ < T := hcFac
    have hdiff : 0 < T - c := tsub_pos_iff_lt.mpr hct
    have hnum : 24 * (N * c) < T - c := by
      rw [lt_tsub_iff_right]
      calc
        24 * (N * c) + c = c * (24 * N + 1) := by ring
        _ < T := hcFac
    rw [show N * (T - c)⁻¹ * c = (N * c) / (T - c) by
      rw [div_eq_mul_inv]
      ring]
    rw [div_lt_iff₀ hdiff]
    rw [show (1 / 24 : NNReal) * (T - c) = (T - c) / 24 by ring]
    exact (lt_div_iff₀ (by norm_num : (0 : NNReal) < 24)).2 <| by
      simpa only [mul_comm] using hnum
  have herrReal :
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : Real) < (T : Real) / 2 := by
    exact_mod_cast herrHalf
  have hmargin : (T : Real) / 2 ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) := by
    rw [NNReal.coe_sub herrOut.le]
    linarith
  have hδlower : aδ * hd.mu R ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) := by
    calc
      aδ * hd.mu R = ((T : Real) / 2) * (qReal / 2) := by
        dsimp only [aδ, qReal]
        ring
      _ ≤ ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          (qReal / 2) :=
        mul_le_mul_of_nonneg_right hmargin (div_nonneg hqReal.le (by norm_num))
      _ = ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) := rfl
  exact ⟨q, rfl, hqRadius, hqAcc, herrOut, hinvErr, hδlower⟩

end NormalRadiusProfile

end RawPhaseSmallness

section ControlledPhaseSmallness

variable [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
@[simp] theorem chartPhaseK_zero
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) :
    chartPhaseK g b 0 = 0 := by
  apply NNReal.eq
  simp [chartPhaseK]
  rfl

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem chartPhaseK_cont
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) :
    Continuous (chartPhaseK g b) := by
  unfold chartPhaseK
  apply Continuous.subtype_mk
  fun_prop

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem chartPhaseK_lim
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) :
    Tendsto (chartPhaseK g b) (nhds 0) (nhds 0) := by
  have hcont : Tendsto (chartPhaseK g b) (nhds (0 : NNReal))
      (nhds (chartPhaseK g b 0)) := (chartPhaseK_cont g b).continuousAt
  simpa using hcont

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem chartPhaseErr_lim
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) :
    Tendsto (fun R ↦ PhaseFlow.phaseErr (chartPhaseK g b R))
      (nhds 0) (nhds 0) :=
  PhaseFlow.phaseErr_tendsto.comp (chartPhaseK_lim g b)

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem chartPhaseErr_lt_ev
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [hSigma : SigmaCompactSpace M] [hT2 : T2Space M]
    [hTangentT2 : T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g)
    {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ R in nhds 0, PhaseFlow.phaseErr (chartPhaseK g b R) < eps := by
  let _ := hSigma
  let _ := hT2
  let _ := hTangentT2
  exact chartPhaseErr_lim g b (Iio_mem_nhds heps)

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem exists_chart_q_lt
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g)
    {r : Real} (hr : 0 < r) {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps := by
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps :=
    htwo (chartPhaseErr_lt_ev g b heps)
  obtain ⟨δ, hδ, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := b.C 1
  have hC : 0 ≤ C := b.C_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (δ / 4) (min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos hδ (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqδ : qReal ≤ δ / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) δ := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < δ
    rw [sub_zero, abs_of_pos hqReal]
    exact hqδ.trans_lt (div_lt_self hδ (by norm_num))
  have herrQ : PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps :=
    herr q hqBall
  have hqRadius' : 4 * qReal < r := by
    nlinarith
  have hqProd : qReal * (24 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 12 * C * qReal ≤ 1 := by
    nlinarith
  have hmul : 0 ≤ qReal * (1 - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  refine ⟨q, ?_, ?_, ?_, herrQ⟩
  · exact_mod_cast hqReal
  · change 4 * qReal < r
    exact hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem exists_chart_biq_lt
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g)
    {r : Real} (hr : 0 < r) {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      6 * (q : Real) < r ∧
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) ∧
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps := by
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps :=
    htwo (chartPhaseErr_lt_ev g b heps)
  obtain ⟨epsBall, hepsBall, herr⟩ :=
    Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := b.C 1
  have hC : 0 ≤ C := b.C_nonneg 1
  let accelBound : Real := 1 / (18 * (C + 1))
  have hden : 0 < 18 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (epsBall / 4) (min (r / 12) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos hepsBall (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqEps : qReal ≤ epsBall / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 12 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) epsBall := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < epsBall
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (div_lt_self hepsBall (by norm_num))
  have herrQ : PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < eps :=
    herr q hqBall
  have hqRadius' : 6 * qReal < r := by
    nlinarith
  have hqProd : qReal * (18 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 18 * C * qReal ≤ 1 := by
    nlinarith
  have hcoef : 12 * C * qReal ≤ (2 / 3 : Real) := by
    nlinarith
  have hmul : 0 ≤ qReal * ((2 / 3 : Real) - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hcoef)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hqReal
  · change 6 * qReal < r
    exact hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  · exact herrQ

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
theorem exists_chart_biq
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g)
    {r : Real} (hr : 0 < r) :
    ∃ q : NNReal, 0 < q ∧
      6 * (q : Real) < r ∧
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) ∧
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  exact exists_chart_biq_lt (I := I) g b hr
    (PhaseFlow.freeDiagInv_pos (E := E))

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
theorem exists_chart_biq_inv
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g)
    {r : Real} (hr : 0 < r) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ q : NNReal, 0 < q ∧
      6 * (q : Real) < r ∧
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) ∧
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < T ∧
      N * (T - PhaseFlow.phaseErr (chartPhaseK g b (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < 1 / 24 := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  have hT : 0 < T := PhaseFlow.freeDiagInv_pos (E := E)
  let epsInv : NNReal := T / (48 * (N + 1))
  have hepsInv : 0 < epsInv := by
    dsimp only [epsInv]
    exact div_pos hT (mul_pos (by norm_num) (by positivity))
  obtain ⟨q, hq, hqWide, hqAccel, herrQ⟩ :=
    exists_chart_biq_lt (I := I) g b hr hepsInv
  have hN1 : (1 : NNReal) ≤ N + 1 := by
    exact le_add_of_nonneg_left N.2
  have hden_ge : (2 : NNReal) ≤ 48 * (N + 1) := by
    calc
      (2 : NNReal) = 2 * 1 := by norm_num
      _ ≤ 2 * (N + 1) := mul_le_mul_of_nonneg_left hN1 (by norm_num)
      _ ≤ 48 * (N + 1) :=
        mul_le_mul_of_nonneg_right (by norm_num) (N + 1).2
  have heps_le : epsInv ≤ T / 2 := by
    dsimp only [epsInv]
    exact div_le_div_of_nonneg_left T.2 (by norm_num) hden_ge
  have herrHalf :
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < T / 2 :=
    herrQ.trans_le heps_le
  have herr :
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < T :=
    herrHalf.trans (half_lt_self hT)
  have hinvErr :
      N * (T - PhaseFlow.phaseErr (chartPhaseK g b (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) < 1 / 24 := by
    let cErr : NNReal := PhaseFlow.phaseErr (chartPhaseK g b (2 * q))
    have hdenInv : 0 < 48 * (N + 1) :=
      mul_pos (by norm_num) (by positivity)
    have hsmall : cErr * (48 * (N + 1)) < T := by
      apply (lt_div_iff₀ hdenInv).mp
      simpa only [cErr, epsInv] using herrQ
    have hfac : 24 * N + 1 ≤ 48 * (N + 1) := by
      nlinarith [N.2]
    have hcFac : cErr * (24 * N + 1) < T :=
      (mul_le_mul_of_nonneg_left hfac cErr.2).trans_lt hsmall
    have honeFac : (1 : NNReal) ≤ 24 * N + 1 := by
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) N.2)
    have hct : cErr < T := by
      calc
        cErr = cErr * 1 := by rw [mul_one]
        _ ≤ cErr * (24 * N + 1) :=
          mul_le_mul_of_nonneg_left honeFac cErr.2
        _ < T := hcFac
    have hdiff : 0 < T - cErr := tsub_pos_iff_lt.mpr hct
    have hnum : 24 * (N * cErr) < T - cErr := by
      rw [lt_tsub_iff_right]
      calc
        24 * (N * cErr) + cErr = cErr * (24 * N + 1) := by ring
        _ < T := hcFac
    rw [show N * (T - cErr)⁻¹ * cErr = (N * cErr) / (T - cErr) by
      rw [div_eq_mul_inv]
      ring]
    rw [div_lt_iff₀ hdiff]
    rw [show (1 / 24 : NNReal) * (T - cErr) = (T - cErr) / 24 by ring]
    exact (lt_div_iff₀ (by norm_num : (0 : NNReal) < 24)).2 <| by
      simpa only [mul_comm] using hnum
  exact ⟨q, hq, hqWide, hqAccel, herr, hinvErr⟩

end ControlledPhaseSmallness

end HCGCompactness
end DifferentialGeometry
