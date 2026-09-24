import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Endpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseMetricBoundsAssembly

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter Topology
open scoped Manifold ContDiff ENNReal NNReal Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

theorem exists_quarterBall_bound_not_uniform :
    ∃ F : Nat → Real → Real →L[Real] Real →L[Real] Real,
      (∀ j : Nat, ∃ C : Real, 0 ≤ C ∧
        ∀ z ∈ Metric.ball (0 : Real) (1 / 4), ‖F j z‖ ≤ C) ∧
      ¬ ∃ C : Real, ∀ j : Nat, ∀ z ∈ Metric.ball (0 : Real) (1 / 4),
        ‖F j z‖ ≤ C := by
  refine ⟨fun j z => ((j : Real) * (|z - 1 / 2|)⁻¹) •
    ContinuousLinearMap.mul Real Real, ?_, ?_⟩
  · intro j
    refine ⟨4 * (j : Real) * ‖ContinuousLinearMap.mul Real Real‖,
      by positivity, ?_⟩
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
    have hzlt : z < 1 / 4 := (abs_lt.mp hz).2
    have habs : |z - 1 / 2| = 1 / 2 - z := by
      rw [abs_of_neg (by linarith)]
      ring
    have hge : (1 / 4 : Real) ≤ |z - 1 / 2| := by
      rw [habs]
      linarith
    have hpos : 0 < |z - 1 / 2| := lt_of_lt_of_le (by norm_num) hge
    have hinv : (|z - 1 / 2|)⁻¹ ≤ 4 := by
      have h := one_div_le_one_div_of_le (a := (1 / 4 : Real)) (by norm_num) hge
      simpa using h
    have hcoef : ‖((j : Real) * (|z - 1 / 2|)⁻¹)‖ =
        (j : Real) * (|z - 1 / 2|)⁻¹ := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg j) (inv_nonneg.mpr hpos.le))]
    rw [norm_smul, hcoef]
    have hj : (0 : Real) ≤ (j : Real) := Nat.cast_nonneg j
    have hL : (0 : Real) ≤ ‖ContinuousLinearMap.mul Real Real‖ := norm_nonneg _
    nlinarith [hinv, mul_nonneg hj hL, hj, hL]
  · rintro ⟨C, hC⟩
    have hL1 : (1 : Real) ≤ ‖ContinuousLinearMap.mul Real Real‖ := by
      have hval : ContinuousLinearMap.mul Real Real 1 1 = 1 := by simp
      have h1 : ‖ContinuousLinearMap.mul Real Real 1 1‖ ≤
          ‖ContinuousLinearMap.mul Real Real 1‖ * ‖(1 : Real)‖ :=
        ContinuousLinearMap.le_opNorm (ContinuousLinearMap.mul Real Real 1) 1
      have h2 : ‖ContinuousLinearMap.mul Real Real 1‖ ≤
          ‖ContinuousLinearMap.mul Real Real‖ * ‖(1 : Real)‖ :=
        ContinuousLinearMap.le_opNorm (ContinuousLinearMap.mul Real Real) 1
      rw [hval, norm_one, mul_one] at h1
      rw [norm_one, mul_one] at h2
      linarith
    let j : Nat := Nat.ceil (max C 0) + 1
    have hj1 : (1 : Real) ≤ (j : Real) := by
      have h0 : (0 : Real) ≤ (Nat.ceil (max C 0) : Real) := Nat.cast_nonneg _
      simp only [j]
      push_cast
      linarith
    have hjC : C < (j : Real) := by
      have hceil : max C 0 ≤ (Nat.ceil (max C 0) : Real) := Nat.le_ceil _
      have h0 : (0 : Real) ≤ (Nat.ceil (max C 0) : Real) := Nat.cast_nonneg _
      simp only [j]
      push_cast
      linarith [le_max_left C 0]
    have hz : (0 : Real) ∈ Metric.ball (0 : Real) (1 / 4) := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      norm_num
    have hbound := hC j 0 hz
    have hnorm : ‖(fun j z => ((j : Real) * (|z - 1 / 2|)⁻¹) •
        ContinuousLinearMap.mul Real Real) j 0‖ =
        2 * (j : Real) * ‖ContinuousLinearMap.mul Real Real‖ := by
      have hc : ‖(((j : Real) * (|(0 : Real) - 1 / 2|)⁻¹) : Real)‖ =
          2 * (j : Real) := by
        have h0 : |(0 : Real) - 1 / 2| = 1 / 2 := by norm_num
        rw [Real.norm_eq_abs, h0, show ((1 / 2 : Real))⁻¹ = 2 by norm_num,
          abs_of_nonneg (by positivity)]
        ring
      rw [norm_smul, hc]
    rw [hnorm] at hbound
    have hstep : 2 * (j : Real) ≤
        2 * (j : Real) * ‖ContinuousLinearMap.mul Real Real‖ := by
      have h := mul_le_mul_of_nonneg_left hL1 (by linarith : (0 : Real) ≤ 2 * (j : Real))
      rw [mul_one] at h
      exact h
    linarith

namespace SeqBallNormalChartData

omit [CompleteSpace E] in
theorem chartPhaseK_metricBoundsTwoPiece_val
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} {x : (X.obj j).M}
    (hn : hd.dist j x (X.obj j).basepoint <= n) (R : NNReal) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (chartPhaseK (X.obj j).metric (d.metricBoundsTwoPiece hreal x hn) R : Real)) =
      (6 * (d.twoPieceC (n := n) (j := j) x 1) ^ 2 +
          3 * d.twoPieceC (n := n) (j := j) x 2) * (R : Real) ^ 2 +
        6 * d.twoPieceC (n := n) (j := j) x 1 * (R : Real) := by
  rfl

omit [CompleteSpace E] in
theorem chartPhaseK_metricBounds_val_of_shell
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} {x : (X.obj j).M}
    (hn : hd.dist j x (X.obj j).basepoint <= n) (hnj : n + 2 <= j) (R : NNReal) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (chartPhaseK (X.obj j).metric (d.metricBounds hreal x hn) R : Real)) =
      (6 * (d.metricC n 1) ^ 2 + 3 * d.metricC n 2) * (R : Real) ^ 2 +
        6 * d.metricC n 1 * (R : Real) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have h1 : (d.metricBounds hreal x hn).C 1 = d.metricC n 1 :=
    d.metricBounds_C_eq (I := I) hreal x hn (by omega)
  have h2 : (d.metricBounds hreal x hn).C 2 = d.metricC n 2 :=
    d.metricBounds_C_eq (I := I) hreal x hn hnj
  change (6 * (d.metricBounds hreal x hn).C 1 ^ 2 +
      3 * (d.metricBounds hreal x hn).C 2) * (R : Real) ^ 2 +
      6 * (d.metricBounds hreal x hn).C 1 * (R : Real) =
    (6 * (d.metricC n 1) ^ 2 + 3 * d.metricC n 2) * (R : Real) ^ 2 +
      6 * d.metricC n 1 * (R : Real)
  rw [h1, h2]

omit [CompleteSpace E] in
theorem chartPhaseK_metricBounds_eq_metricBoundsTwoPiece
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} {x : (X.obj j).M}
    (hn : hd.dist j x (X.obj j).basepoint <= n) (hnj : n + 2 <= j) (R : NNReal) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     chartPhaseK (X.obj j).metric (d.metricBounds hreal x hn) R) =
      (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
       letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
       letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
       letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
       chartPhaseK (X.obj j).metric (d.metricBoundsTwoPiece hreal x hn) R) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  apply NNReal.eq
  rw [chartPhaseK_metricBounds_val_of_shell (I := I) d hreal hn hnj R]
  rw [chartPhaseK_metricBoundsTwoPiece_val (I := I) d hreal hn R]
  rw [d.twoPieceC_eq_of_shell (n := n) (j := j) x (show n + 1 <= j by omega),
    d.twoPieceC_eq_of_shell (n := n) (j := j) x hnj]

omit [CompleteSpace E] in
theorem exists_phase_scale_of_chartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {j : Nat} {x : (X.obj j).M}
    (b : letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
         letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
         letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
         letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
         (d.chart j x).MetricBounds (X.obj j).metric)
    (C1 : Real) (hC1 : 0 <= C1) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ : Real,
      0 < aq ∧ 0 < aδ ∧
      ∀ R, 0 ≤ R →
        ∃ q : NNReal,
          (q : Real) = aq * hd.mu R ∧
          6 * (q : Real) < d.phaseRadius R ∧
          3 * C1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < 1 / 24 ∧
          aδ * hd.mu R ≤
            ((T - PhaseFlow.phaseErr
                (chartPhaseK (X.obj j).metric b (2 * q)) : NNReal) : Real) *
              ((q : Real) / 2) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
  let : T2Space (X.obj j).M := (X.obj j).t2
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
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
  have htwo : Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < epsInv :=
    htwo (chartPhaseErr_lt_ev (I := I) (X.obj j).metric b hepsInv)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := C1
  have hC : 0 ≤ C := hC1
  have hμ0 : 0 < hd.mu 0 := hd.mu_pos 0
  let accelBound : Real := 1 / (36 * (C + 1))
  have hden : 0 < 36 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccel : 0 < accelBound := one_div_pos.mpr hden
  let aq : Real := min (d.ratio / 48)
    (min (eps / (2 * hd.mu 0)) (accelBound / hd.mu 0))
  have haq : 0 < aq := by
    dsimp only [aq]
    exact lt_min (div_pos d.ratio_pos (by norm_num))
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
  have haqRatio : aq ≤ d.ratio / 48 := min_le_left _ _
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
  have herrQ : PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < epsInv :=
    herr q hqBall
  have hN1 : (1 : NNReal) ≤ N + 1 := le_add_of_nonneg_left N.2
  have hden_ge : (2 : NNReal) ≤ 48 * (N + 1) := by
    calc
      (2 : NNReal) = 2 * 1 := by norm_num
      _ ≤ 2 * (N + 1) := mul_le_mul_of_nonneg_left hN1 (by norm_num)
      _ ≤ 48 * (N + 1) :=
        mul_le_mul_of_nonneg_right (by norm_num) (N + 1).2
  have heps_le : epsInv ≤ T / 2 := by
    dsimp only [epsInv]
    exact div_le_div_of_nonneg_left T.2 (by norm_num) hden_ge
  have herrHalf : PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < T / 2 :=
    herrQ.trans_le heps_le
  have hqRadius : 6 * (q : Real) < d.phaseRadius R := by
    have haRatio : 6 * aq < d.ratio / 4 := by
      nlinarith [d.ratio_pos]
    calc
      6 * (q : Real) = (6 * aq) * hd.mu R := by
        change 6 * qReal = _
        dsimp only [qReal]
        ring
      _ < (d.ratio / 4) * hd.mu R :=
        mul_lt_mul_of_pos_right haRatio hμR
      _ = d.phaseRadius R := by
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
  have hqAcc : 3 * C1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real) := by
    change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  have herrOut : PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < T := by
    calc
      PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < T / 2 := herrHalf
      _ < T := by exact_mod_cast (half_lt_self hTReal)
  have hinvErr :
      N * (T - PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) < 1 / 24 := by
    let c : NNReal := PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q))
    have hdenInv : 0 < 48 * (N + 1) :=
      mul_pos (by norm_num) (by positivity)
    have hsmall : c * (48 * (N + 1)) < T := by
      apply (lt_div_iff₀ hdenInv).mp
      simpa only [c, epsInv] using herrQ
    have hfac : 24 * N + 1 ≤ 48 * (N + 1) := by
      nlinarith [N.2]
    have hcFac : c * (24 * N + 1) < T :=
      (mul_le_mul_of_nonneg_left hfac c.2).trans_lt hsmall
    have honeFac : (1 : NNReal) ≤ 24 * N + 1 :=
      le_add_of_nonneg_left (mul_nonneg (by norm_num) N.2)
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
      (PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) : Real) < (T : Real) / 2 := by
    exact_mod_cast herrHalf
  have hmargin : (T : Real) / 2 ≤
      ((T - PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) : NNReal) : Real) := by
    rw [NNReal.coe_sub herrOut.le]
    linarith
  have hδlower : aδ * hd.mu R ≤
      ((T - PhaseFlow.phaseErr (chartPhaseK (X.obj j).metric b (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) := by
    calc
      aδ * hd.mu R = ((T : Real) / 2) * (qReal / 2) := by
        dsimp only [aδ, qReal]
        ring
      _ ≤ ((T - PhaseFlow.phaseErr
              (chartPhaseK (X.obj j).metric b (2 * q)) : NNReal) : Real) *
          (qReal / 2) :=
        mul_le_mul_of_nonneg_right hmargin (div_nonneg hqReal.le (by norm_num))
      _ = ((T - PhaseFlow.phaseErr
              (chartPhaseK (X.obj j).metric b (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) := rfl
  exact ⟨q, rfl, hqRadius, hqAcc, herrOut, hinvErr, hδlower⟩

omit [CompleteSpace E] in
def HasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real) : Prop :=
  (∀ q : Nat, 0 ≤ C q) ∧
    ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        (d.chart j x).radius / 4 ≤ b.radius ∧ b.C 1 ≤ C 1 ∧ b.C 2 ≤ C 2

omit [CompleteSpace E] in
def HasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real) : Prop :=
  (∀ q : Nat, 0 ≤ C q) ∧
    ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
      (d.chart j x).MetricDerivBound (X.obj j).metric
          (Metric.ball (0 : E) ((d.chart j x).radius / 4)) 1 (C 1) ∧
        (d.chart j x).MetricDerivBound (X.obj j).metric
          (Metric.ball (0 : E) ((d.chart j x).radius / 4)) 2 (C 2)

omit [CompleteSpace E] in
def HasQuarterRadiusChartBoundsOnBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) (C : Nat → Real) : Prop :=
  (∀ q : Nat, 0 ≤ C q) ∧
    ∀ (j : Nat) (x : (X.obj j).M),
      hd.dist j x (X.obj j).basepoint ≤ R →
        letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
        letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
        letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
        letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
        (d.chart j x).MetricDerivBound (X.obj j).metric
            (Metric.ball (0 : E) ((d.chart j x).radius / 4)) 1 (C 1) ∧
          (d.chart j x).MetricDerivBound (X.obj j).metric
            (Metric.ball (0 : E) ((d.chart j x).radius / 4)) 2 (C 2)

omit [CompleteSpace E] in
theorem hasQuarterRadiusChartBounds_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real)
    (h : d.HasFullRadiusChartBounds C) : d.HasQuarterRadiusChartBounds C := by
  refine ⟨h.1, ?_⟩
  intro j x
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  obtain ⟨b, hrad, hb1, hb2⟩ := h.2 j x
  have hsub : Metric.ball (0 : E) ((d.chart j x).radius / 4) ⊆
      Metric.ball (0 : E) b.radius := Metric.ball_subset_ball hrad
  exact ⟨fun z hz => (b.deriv 1 z (hsub hz)).trans hb1,
    fun z hz => (b.deriv 2 z (hsub hz)).trans hb2⟩

omit [CompleteSpace E] in
theorem hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real)
    (h : d.HasQuarterRadiusChartBounds C) : d.HasFullRadiusChartBounds C := by
  refine ⟨h.1, ?_⟩
  intro j x
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hsub : Metric.ball (0 : E) ((d.chart j x).radius / 4) ⊆
      Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball (by linarith [(d.chart j x).radius_pos])
  refine ⟨
    { C := fun q => if q = 1 then C 1 else if q = 2 then C 2 else
        max 0 (Classical.choose
          (exists_metricDerivBound_quarter (I := I) d j x q))
      C_nonneg := ?_
      radius := (d.chart j x).radius / 4
      radius_pos := by linarith [(d.chart j x).radius_pos]
      equiv := fun z hz v => d.metric_equiv j x z (hsub hz) v
      deriv := ?_ }, ?_, ?_, ?_⟩
  · intro q
    split_ifs with h1 h2
    · exact h.1 1
    · exact h.1 2
    · exact le_max_left 0 _
  · intro q
    split_ifs with h1 h2
    · subst h1
      exact (h.2 j x).1
    · subst h2
      exact (h.2 j x).2
    · exact fun z hz => ((Classical.choose_spec
          (exists_metricDerivBound_quarter (I := I) d j x q)).2 z hz).trans
        (le_max_right 0 _)
  · simp
  · simp
  · simp

omit [CompleteSpace E] in
theorem hasQuarterRadiusChartBoundsOnBall_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real)
    (h : d.HasQuarterRadiusChartBounds C) (R : Real) :
    d.HasQuarterRadiusChartBoundsOnBall R C :=
  ⟨h.1, fun j x _ => h.2 j x⟩

omit [CompleteSpace E] in
theorem hasFullRadiusChartBounds_iff_forall_hasQuarterRadiusChartBoundsOnBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (C : Nat → Real) :
    d.HasFullRadiusChartBounds C ↔
      ∀ R : Real, 0 ≤ R → d.HasQuarterRadiusChartBoundsOnBall R C := by
  constructor
  · intro h R _
    exact d.hasQuarterRadiusChartBoundsOnBall_of_hasQuarterRadiusChartBounds C
      (d.hasQuarterRadiusChartBounds_of_hasFullRadiusChartBounds C h) R
  · intro h
    refine d.hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds C ⟨?_, ?_⟩
    · exact (h 0 le_rfl).1
    · intro j x
      exact (h (max 0 (hd.dist j x (X.obj j).basepoint))
        (le_max_left 0 _)).2 j x (le_max_right 0 _)

omit [CompleteSpace E] in
theorem of_boundedGeometryNormalChartData_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) :
    (SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d).HasFullRadiusChartBounds
      (fun q => d.metricC q) := by
  refine ⟨fun q => d.metricC_nonneg q, ?_⟩
  intro j x
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  refine ⟨d.metricBounds j x, ?_, le_rfl, le_rfl⟩
  exact div_le_self (le_of_lt (d.chart j x).radius_pos) (by norm_num)

omit [CompleteSpace E] in
theorem of_boundedGeometryNormalChartData_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) :
    (of_boundedGeometryNormalChartData (I := I) d).HasQuarterRadiusChartBounds
      (fun q => d.metricC q) := by
  refine ⟨fun q => d.metricC_nonneg q, ?_⟩
  intro j x
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hsub : Metric.ball (0 : E) ((d.chart j x).radius / 4) ⊆
      Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball (by linarith [(d.chart j x).radius_pos])
  exact ⟨fun z hz => d.metric_deriv j 1 x z (hsub hz),
    fun z hz => d.metric_deriv j 2 x z (hsub hz)⟩

omit [CompleteSpace E] in
theorem of_boundedGeometryNormalChartData_hasQuarterRadiusChartBoundsOnBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (R : Real) :
    (of_boundedGeometryNormalChartData (I := I) d).HasQuarterRadiusChartBoundsOnBall
      R (fun q => d.metricC q) :=
  hasQuarterRadiusChartBoundsOnBall_of_hasQuarterRadiusChartBounds
    (of_boundedGeometryNormalChartData (I := I) d) (fun q => d.metricC q)
    (of_boundedGeometryNormalChartData_hasQuarterRadiusChartBounds (I := I) d) R

omit [CompleteSpace E] in
theorem exists_metricBounds_C_eq_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {d : SeqBallNormalChartData (I := I) X hd} {C : Nat → Real}
    (h : d.HasFullRadiusChartBounds C) {j : Nat} {x : (X.obj j).M} :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
      (d.chart j x).radius / 4 ≤ b.radius ∧ b.C 1 = C 1 ∧ b.C 2 = C 2 := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  obtain ⟨hb, hrad, hb1, hb2⟩ := h.2 j x
  refine ⟨{ hb with
      C := fun q => if q = 1 then C q else if q = 2 then C q else max (hb.C q) (C q)
      C_nonneg := ?_
      deriv := ?_ }, hrad, ?_, ?_⟩
  · intro q
    by_cases h1 : q = 1
    · subst h1
      simpa using h.1 1
    · by_cases h2 : q = 2
      · subst h2
        simpa using h.1 2
      · simpa [h1, h2] using le_trans (hb.C_nonneg q) (le_max_left (hb.C q) (C q))
  · intro q z hz
    by_cases h1 : q = 1
    · subst h1
      simpa using (hb.deriv 1 z hz).trans hb1
    · by_cases h2 : q = 2
      · subst h2
        simpa using (hb.deriv 2 z hz).trans hb2
      · simpa [h1, h2] using (hb.deriv q z hz).trans (le_max_left (hb.C q) (C q))
  · simp
  · simp

omit [CompleteSpace E] in
theorem exists_metricBounds_C_eq_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {d : SeqBallNormalChartData (I := I) X hd} {C : Nat → Real}
    (h : d.HasQuarterRadiusChartBounds C) {j : Nat} {x : (X.obj j).M} :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
      (d.chart j x).radius / 4 ≤ b.radius ∧ b.C 1 = C 1 ∧ b.C 2 = C 2 :=
  d.exists_metricBounds_C_eq_of_hasFullRadiusChartBounds
    (d.hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds C h)

omit [CompleteSpace E] in
theorem exists_metricBounds_phaseRadius_le_chartPhaseK_val_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {d : SeqBallNormalChartData (I := I) X hd} {C : Nat → Real}
    (h : d.HasFullRadiusChartBounds C) {j : Nat} {x : (X.obj j).M} {R : Real}
    (hR : hd.dist j x (X.obj j).basepoint ≤ R) (q : NNReal) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
      Metric.ball (0 : E) (d.phaseRadius R) ⊆ Metric.ball (0 : E) b.radius ∧
      (chartPhaseK (X.obj j).metric b q : Real) =
        (6 * (C 1) ^ 2 + 3 * C 2) * (q : Real) ^ 2 + 6 * C 1 * (q : Real) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  obtain ⟨b, hrad, hb1, hb2⟩ :=
    d.exists_metricBounds_C_eq_of_hasFullRadiusChartBounds h (j := j) (x := x)
  refine ⟨b, ?_, ?_⟩
  · apply Metric.ball_subset_ball
    have hquarter : d.phaseRadius R ≤ (d.chart j x).radius / 4 := by
      rw [d.radius_eq]
      dsimp only [phaseRadius]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd.mu_antitone hR) d.ratio_pos.le) (by norm_num)
    linarith
  · change (6 * (b.C 1) ^ 2 + 3 * b.C 2) * (q : Real) ^ 2 +
        6 * b.C 1 * (q : Real) =
      (6 * (C 1) ^ 2 + 3 * C 2) * (q : Real) ^ 2 + 6 * C 1 * (q : Real)
    rw [hb1, hb2]

omit [CompleteSpace E] in
theorem exists_min_scale_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasFullRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ aMin : Real,
      0 < aq ∧ 0 < aδ ∧ 0 < aMin ∧
      ∀ R, 0 ≤ R →
        ∃ (q : NNReal) (δ : Real),
          0 < q ∧ 0 < δ ∧
          (q : Real) = aq * hd.mu R ∧
          aδ * hd.mu R ≤ δ ∧
          6 * (q : Real) < d.phaseRadius R ∧
          3 * C 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr
              (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < 1 / 24 ∧
          2 * (aMin * hd.mu R) < (q : Real) ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ R →
            letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
            letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
            letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
            letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
            letI : T2Space (X.obj k).M := (X.obj k).t2
            letI : T2Space (TangentBundle I (X.obj k).M) :=
              (X.obj k).t2TangentBundle
            ∃ e : OpenPartialHomeomorph (E × E) (E × E),
              IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k)
                  (hconn k) x q δ e (c := d.chart k x) ∧
                NormalDiagFence (I := I) (X.obj k) x q e
                  (c := d.chart k x) ∧
                ApproximatesLinearOn
                  (e.symm : E × E → E × E)
                  ((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))
                  e.target
                  (N * (T - PhaseFlow.phaseErr
                      (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
                    PhaseFlow.phaseErr
                      (chartPhaseK (X.obj j₀).metric b₀ (2 * q))) ∧
                aMin * hd.mu R ≤ (d.chart k x).radius := by
  let : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
  let : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
  let : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
  let : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
  let : T2Space (X.obj j₀).M := (X.obj j₀).t2
  let : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  intro hb₀1 hb₀2
  obtain ⟨aq, aδ, haq, haδ, hscale⟩ :=
    d.exists_phase_scale_of_chartBounds (j := j₀) (x := x₀) b₀ (C 1) (hC.1 1)
  let aMin : Real := min (aq / 4) d.ratio
  have haMin : 0 < aMin := by
    dsimp only [aMin]
    exact lt_min (div_pos haq (by norm_num)) d.ratio_pos
  have haMinq : aMin ≤ aq / 4 := by
    dsimp only [aMin]
    exact min_le_left _ _
  have haMinRatio : aMin ≤ d.ratio := by
    dsimp only [aMin]
    exact min_le_right _ _
  refine ⟨aq, aδ, aMin, haq, haδ, haMin, ?_⟩
  intro R hR
  obtain ⟨q, hqeq, hqWide, hqAcc, herr, hinvErr, hδlower⟩ := hscale R hR
  have hqReal : (0 : Real) < q := by
    rw [hqeq]
    exact mul_pos haq (hd.mu_pos R)
  have hq : 0 < q := by exact_mod_cast hqReal
  let δ : Real :=
    ((T - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) : NNReal) : Real) *
      ((q : Real) / 2)
  have hδ : 0 < δ :=
    (mul_pos haδ (hd.mu_pos R)).trans_le (by simpa only [δ] using hδlower)
  have hMinq : 2 * (aMin * hd.mu R) < (q : Real) := by
    calc
      2 * (aMin * hd.mu R) ≤ 2 * ((aq / 4) * hd.mu R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right haMinq (hd.mu_nonneg R)) (by norm_num)
      _ = (q : Real) / 2 := by rw [hqeq]; ring
      _ < (q : Real) := half_lt_self hqReal
  refine ⟨q, δ, hq, hδ, hqeq, ?_, hqWide, hqAcc, herr, hinvErr, hMinq, ?_⟩
  · simpa only [δ] using hδlower
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let c := d.chart k x
  obtain ⟨b, hrad, hb1, hb2⟩ :=
    d.exists_metricBounds_C_eq_of_hasFullRadiusChartBounds hC (j := k) (x := x)
  have hrMetric : Metric.ball (0 : E) (d.phaseRadius R) ⊆ Metric.ball (0 : E) b.radius := by
    apply Metric.ball_subset_ball
    have hquarter : d.phaseRadius R ≤ (d.chart k x).radius / 4 := by
      rw [d.radius_eq]
      dsimp only [phaseRadius]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le) (by norm_num)
    linarith
  have hrQuarter : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (c.radius / 4) := by
    simpa only [c] using d.phaseRadius_chart (I := I) (j := k) (x := x) hx
  have hb1' : (chartPhaseK (X.obj k).metric b (2 * q) : Real) =
      (6 * (C 1) ^ 2 + 3 * C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * C 1 * ((2 * q : NNReal) : Real) := by
    change (6 * (b.C 1) ^ 2 + 3 * b.C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * b.C 1 * ((2 * q : NNReal) : Real) = _
    rw [hb1, hb2]
  have hb₀1' : (chartPhaseK (X.obj j₀).metric b₀ (2 * q) : Real) =
      (6 * (C 1) ^ 2 + 3 * C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * C 1 * ((2 * q : NNReal) : Real) := by
    change (6 * (b₀.C 1) ^ 2 + 3 * b₀.C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * b₀.C 1 * ((2 * q : NNReal) : Real) = _
    rw [hb₀1, hb₀2]
  have hphase : chartPhaseK (X.obj k).metric b (2 * q) =
      chartPhaseK (X.obj j₀).metric b₀ (2 * q) :=
    NNReal.eq (hb1'.trans hb₀1'.symm)
  have hqAccel : 3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤ (2 / 3 : Real) * (q : Real) := by
    rw [hb1]
    exact hqAcc
  have herr' : PhaseFlow.phaseErr (chartPhaseK (X.obj k).metric b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    rw [hphase]
    simpa only [T, N] using herr
  obtain ⟨δ', e, _hδ', hδ'eq, hdiag, hfence, hinvApprox⟩ :=
    exists_chart_diag_of (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x c b hrMetric hrQuarter q hq hqWide hqAccel herr'
  have hδ'e : δ' = δ := by
    rw [hphase] at hδ'eq
    simpa only [δ, T, N] using hδ'eq
  refine ⟨e, ?_, hfence, ?_, ?_⟩
  · simpa only [hδ'e] using hdiag
  · simpa only [hphase] using hinvApprox
  · calc
      aMin * hd.mu R ≤ d.ratio * hd.mu R :=
        mul_le_mul_of_nonneg_right haMinRatio (hd.mu_nonneg R)
      _ ≤ d.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
        mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le
      _ = (d.chart k x).radius := by rw [d.radius_eq]

omit [CompleteSpace E] in
theorem exists_diag_inv_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasFullRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric)
    (R : Real) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((N⁻¹ - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) :
          NNReal) : Real) * ((q : Real) / 2) ∧
      N * (N⁻¹ - PhaseFlow.phaseErr
          (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < 1 / 24 ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
        letI : T2Space (X.obj k).M := (X.obj k).t2
        letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e
              (c := d.chart k x) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (N * (N⁻¹ - PhaseFlow.phaseErr
                  (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
                PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q))) := by
  let : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
  let : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
  let : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
  let : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
  let : T2Space (X.obj j₀).M := (X.obj j₀).t2
  let : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
  intro hb₀1 hb₀2
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  obtain ⟨q, hq, hqWide, hqAcc₀, herr₀, hinvErr₀⟩ :=
    exists_chart_biq_inv (I := I) (X.obj j₀).metric b₀ (d.phaseRadius_pos R)
  let δ : Real :=
    ((N⁻¹ - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) : NNReal) :
      Real) * ((q : Real) / 2)
  have hmargin : 0 < N⁻¹ - PhaseFlow.phaseErr
      (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) :=
    tsub_pos_iff_lt.mpr (by simpa only [N] using herr₀)
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (by exact_mod_cast hmargin) (div_pos hqReal (by norm_num))
  refine ⟨q, δ, hq, by nlinarith [hqWide], hδ, rfl, ?_, ?_⟩
  · simpa only [N] using hinvErr₀
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let c := d.chart k x
  obtain ⟨b, hrad, hb1, hb2⟩ :=
    d.exists_metricBounds_C_eq_of_hasFullRadiusChartBounds hC (j := k) (x := x)
  have hrMetric : Metric.ball (0 : E) (d.phaseRadius R) ⊆ Metric.ball (0 : E) b.radius := by
    apply Metric.ball_subset_ball
    have hquarter : d.phaseRadius R ≤ (d.chart k x).radius / 4 := by
      rw [d.radius_eq]
      dsimp only [phaseRadius]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le) (by norm_num)
    linarith
  have hrQuarter : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (c.radius / 4) := by
    simpa only [c] using d.phaseRadius_chart (I := I) (j := k) (x := x) hx
  have hb1' : (chartPhaseK (X.obj k).metric b (2 * q) : Real) =
      (6 * (C 1) ^ 2 + 3 * C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * C 1 * ((2 * q : NNReal) : Real) := by
    change (6 * (b.C 1) ^ 2 + 3 * b.C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * b.C 1 * ((2 * q : NNReal) : Real) = _
    rw [hb1, hb2]
  have hb₀1' : (chartPhaseK (X.obj j₀).metric b₀ (2 * q) : Real) =
      (6 * (C 1) ^ 2 + 3 * C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * C 1 * ((2 * q : NNReal) : Real) := by
    change (6 * (b₀.C 1) ^ 2 + 3 * b₀.C 2) * ((2 * q : NNReal) : Real) ^ 2 +
        6 * b₀.C 1 * ((2 * q : NNReal) : Real) = _
    rw [hb₀1, hb₀2]
  have hphase : chartPhaseK (X.obj k).metric b (2 * q) =
      chartPhaseK (X.obj j₀).metric b₀ (2 * q) :=
    NNReal.eq (hb1'.trans hb₀1'.symm)
  have hqAccel : 3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤ (2 / 3 : Real) * (q : Real) := by
    rw [hb₀1] at hqAcc₀
    rw [hb1]
    exact hqAcc₀
  have herr : PhaseFlow.phaseErr (chartPhaseK (X.obj k).metric b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    rw [hphase]
    simpa only [N] using herr₀
  obtain ⟨δ', e, _hδ', hδ'eq, hdiag, hfence, hinvApprox⟩ :=
    exists_chart_diag_of (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x c b hrMetric hrQuarter q hq (by nlinarith [hqWide]) hqAccel herr
  have hδ'e : δ' = δ := by
    rw [hphase] at hδ'eq
    simpa only [δ, N] using hδ'eq
  refine ⟨e, ?_, hfence, ?_⟩
  · simpa only [hδ'e] using hdiag
  · simpa only [hphase] using hinvApprox

omit [CompleteSpace E] in
theorem exists_uniform_diag_of_hasFullRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasFullRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric)
    (R : Real) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((N⁻¹ - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) :
          NNReal) : Real) * ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
        letI : T2Space (X.obj k).M := (X.obj k).t2
        letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e (c := d.chart k x) := by
  intro hb₀1 hb₀2
  obtain ⟨q, δ, hq, hqRadius, hδ, hδeq, _hinvErr, hall⟩ :=
    d.exists_diag_inv_of_hasFullRadiusChartBounds hcomplete hconn C hC b₀ R hb₀1 hb₀2
  exact ⟨q, δ, hq, hqRadius, hδ, hδeq, fun k x hx => by
    obtain ⟨e, he, hfence, _⟩ := hall k x hx
    exact ⟨e, he, hfence⟩⟩

omit [CompleteSpace E] in
theorem exists_min_scale_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasQuarterRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ aMin : Real,
      0 < aq ∧ 0 < aδ ∧ 0 < aMin ∧
      ∀ R, 0 ≤ R →
        ∃ (q : NNReal) (δ : Real),
          0 < q ∧ 0 < δ ∧
          (q : Real) = aq * hd.mu R ∧
          aδ * hd.mu R ≤ δ ∧
          6 * (q : Real) < d.phaseRadius R ∧
          3 * C 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr
              (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < 1 / 24 ∧
          2 * (aMin * hd.mu R) < (q : Real) ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ R →
            letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
            letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
            letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
            letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
            letI : T2Space (X.obj k).M := (X.obj k).t2
            letI : T2Space (TangentBundle I (X.obj k).M) :=
              (X.obj k).t2TangentBundle
            ∃ e : OpenPartialHomeomorph (E × E) (E × E),
              IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k)
                  (hconn k) x q δ e (c := d.chart k x) ∧
                NormalDiagFence (I := I) (X.obj k) x q e
                  (c := d.chart k x) ∧
                ApproximatesLinearOn
                  (e.symm : E × E → E × E)
                  ((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))
                  e.target
                  (N * (T - PhaseFlow.phaseErr
                      (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
                    PhaseFlow.phaseErr
                      (chartPhaseK (X.obj j₀).metric b₀ (2 * q))) ∧
                aMin * hd.mu R ≤ (d.chart k x).radius := by
  exact
    d.exists_min_scale_of_hasFullRadiusChartBounds hcomplete hconn C
      (d.hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds C hC) b₀

omit [CompleteSpace E] in
theorem exists_diag_inv_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasQuarterRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric)
    (R : Real) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((N⁻¹ - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) :
          NNReal) : Real) * ((q : Real) / 2) ∧
      N * (N⁻¹ - PhaseFlow.phaseErr
          (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) < 1 / 24 ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
        letI : T2Space (X.obj k).M := (X.obj k).t2
        letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e
              (c := d.chart k x) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (N * (N⁻¹ - PhaseFlow.phaseErr
                  (chartPhaseK (X.obj j₀).metric b₀ (2 * q)))⁻¹ *
                PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q))) := by
  exact
    d.exists_diag_inv_of_hasFullRadiusChartBounds hcomplete hconn C
      (d.hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds C hC) b₀ R

omit [CompleteSpace E] in
theorem exists_uniform_diag_of_hasQuarterRadiusChartBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (C : Nat → Real) (hC : d.HasQuarterRadiusChartBounds C)
    {j₀ : Nat} {x₀ : (X.obj j₀).M}
    (b₀ : letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
          letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
          letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
          letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
          (d.chart j₀ x₀).MetricBounds (X.obj j₀).metric)
    (R : Real) :
    letI : TopologicalSpace (X.obj j₀).M := (X.obj j₀).topology
    letI : ChartedSpace H (X.obj j₀).M := (X.obj j₀).charted
    letI : IsManifold I ∞ (X.obj j₀).M := (X.obj j₀).smooth
    letI : SigmaCompactSpace (X.obj j₀).M := (X.obj j₀).sigmaCompact
    letI : T2Space (X.obj j₀).M := (X.obj j₀).t2
    letI : T2Space (TangentBundle I (X.obj j₀).M) := (X.obj j₀).t2TangentBundle
    b₀.C 1 = C 1 →
    b₀.C 2 = C 2 →
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((N⁻¹ - PhaseFlow.phaseErr (chartPhaseK (X.obj j₀).metric b₀ (2 * q)) :
          NNReal) : Real) * ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
        letI : T2Space (X.obj k).M := (X.obj k).t2
        letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e (c := d.chart k x) := by
  exact
    d.exists_uniform_diag_of_hasFullRadiusChartBounds hcomplete hconn C
      (d.hasFullRadiusChartBounds_of_hasQuarterRadiusChartBounds C hC) b₀ R

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
