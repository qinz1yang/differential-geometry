import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalData


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.NormalPhaseEndpoint

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open scoped Manifold ContDiff ENNReal NNReal Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace BoundedGeometryNormalData

def phaseRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : Real) : Real :=
  d.ratio * hd.mu R / 4


theorem phaseRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : Real) :
    0 < d.phaseRadius R := by
  exact div_pos (mul_pos d.ratio_pos (hd.mu_pos R)) (by norm_num)


theorem phaseRadius_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) {k : Nat} {x : (X.obj k).M}
    {R : Real} (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (d.metricBounds k x).radius := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply Metric.ball_subset_ball
  change d.phaseRadius R ≤ (d.chart k x).radius
  rw [d.radius_eq]
  exact (div_le_self (mul_nonneg d.ratio_pos.le (hd.mu_nonneg R))
    (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le)


theorem phaseRadius_chart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) {k : Nat} {x : (X.obj k).M}
    {R : Real} (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) ((d.chart k x).radius / 4) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply Metric.ball_subset_ball
  rw [d.radius_eq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le)
    (by norm_num)

def phaseK
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : NNReal) : NNReal where
  val := (6 * (d.metricC 1) ^ 2 + 3 * d.metricC 2) * (R : Real) ^ 2 +
    6 * d.metricC 1 * (R : Real)
  property := by
    have hA : 0 ≤ 6 * (d.metricC 1) ^ 2 + 3 * d.metricC 2 :=
      add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (d.metricC 1)))
        (mul_nonneg (by norm_num) (d.metricC_nonneg 2))
    exact add_nonneg
      (mul_nonneg hA (sq_nonneg (R : Real)))
      (mul_nonneg (mul_nonneg (by norm_num) (d.metricC_nonneg 1))
        R.coe_nonneg)


theorem chartPhaseK_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat) (x : (X.obj k).M)
    (R : NNReal) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    chartPhaseK (X.obj k).metric (d.metricBounds k x) R = d.phaseK R := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply NNReal.eq
  rfl


theorem phaseErr_lt_ev
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ R in nhds 0, PhaseFlow.phaseErr (d.phaseK R) < eps := by
  let Y := X.obj 0
  let x₀ := Y.basepoint
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let b₀ := d.metricBounds 0 x₀
  simpa only [b₀, d.chartPhaseK_eq] using
    chartPhaseErr_lt_ev (I := I) Y.metric b₀ heps


theorem exists_phase_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) :
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
          3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 ∧
          aδ * hd.mu R ≤
            ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
              ((q : Real) / 2) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
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
  have htwo : Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Filter.Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (d.phaseK (2 * q)) < epsInv :=
    htwo (d.phaseErr_lt_ev hepsInv)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := d.metricC 1
  have hC : 0 ≤ C := d.metricC_nonneg 1
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
  have herrQ : PhaseFlow.phaseErr (d.phaseK (2 * q)) < epsInv :=
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
  have herrHalf : PhaseFlow.phaseErr (d.phaseK (2 * q)) < T / 2 :=
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
  have hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real) := by
    change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  have herrOut : PhaseFlow.phaseErr (d.phaseK (2 * q)) < T := by
    calc
      PhaseFlow.phaseErr (d.phaseK (2 * q)) < T / 2 := herrHalf
      _ < T := by exact_mod_cast (half_lt_self hTReal)
  have hinvErr :
      N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 := by
    let c : NNReal := PhaseFlow.phaseErr (d.phaseK (2 * q))
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
      (PhaseFlow.phaseErr (d.phaseK (2 * q)) : Real) < (T : Real) / 2 := by
    exact_mod_cast herrHalf
  have hmargin : (T : Real) / 2 ≤
      ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) := by
    rw [NNReal.coe_sub herrOut.le]
    linarith
  have hδlower : aδ * hd.mu R ≤
      ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) := by
    calc
      aδ * hd.mu R = ((T : Real) / 2) * (qReal / 2) := by
        dsimp only [aδ, qReal]
        ring
      _ ≤ ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
          (qReal / 2) :=
        mul_le_mul_of_nonneg_right hmargin (div_nonneg hqReal.le (by norm_num))
      _ = ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) := rfl
  exact ⟨q, rfl, hqRadius, hqAcc, herrOut, hinvErr, hδlower⟩

theorem exists_min_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
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
          3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 ∧
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
                  (N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
                    PhaseFlow.phaseErr (d.phaseK (2 * q))) ∧
                aMin * hd.mu R ≤ (d.chart k x).radius := by
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  obtain ⟨aq, aδ, haq, haδ, hscale⟩ := d.exists_phase_scale
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
  obtain ⟨q, hqeq, hqWide, hqAcc, herr, hinvErr, hδlower⟩ :=
    hscale R hR
  have hqReal : (0 : Real) < q := by
    rw [hqeq]
    exact mul_pos haq (hd.mu_pos R)
  have hq : 0 < q := by exact_mod_cast hqReal
  let δ : Real :=
    ((T - PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
      ((q : Real) / 2)
  have hδ : 0 < δ :=
    (mul_pos haδ (hd.mu_pos R)).trans_le (by
      simpa only [δ] using hδlower)
  have hMinq : 2 * (aMin * hd.mu R) < (q : Real) := by
    calc
      2 * (aMin * hd.mu R) ≤ 2 * ((aq / 4) * hd.mu R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right haMinq (hd.mu_nonneg R)) (by norm_num)
      _ = (q : Real) / 2 := by rw [hqeq]; ring
      _ < (q : Real) := half_lt_self hqReal
  refine ⟨q, δ, hq, hδ, hqeq, ?_, hqWide, hqAcc, herr, hinvErr,
    hMinq, ?_⟩
  · simpa only [δ] using hδlower
  intro k x hx
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let c := d.chart k x
  let b := d.metricBounds k x
  have hrMetric : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) b.radius := by
    simpa only [b] using d.phaseRadius_metric hx
  have hrQuarter : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (c.radius / 4) := by
    simpa only [c] using d.phaseRadius_chart hx
  have hqAcc' :
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) := by
    simpa only [b, metricBounds] using hqAcc
  have herr' : PhaseFlow.phaseErr
      (chartPhaseK (X.obj k).metric b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    simpa only [b, d.chartPhaseK_eq] using herr
  obtain ⟨δ', e, _hδ', hδ'eq, hdiag, hfence, hinvApprox⟩ :=
    exists_chart_diag_of (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x c b hrMetric hrQuarter q hq hqWide hqAcc' herr'
  have hδ'eq' : δ' = δ := by
    simpa only [δ, b, d.chartPhaseK_eq] using hδ'eq
  subst δ'
  have hμ : hd.mu R ≤ hd.mu (hd.dist k x (X.obj k).basepoint) :=
    hd.mu_antitone hx
  have hradius : aMin * hd.mu R ≤ (d.chart k x).radius := by
    calc
      aMin * hd.mu R ≤ d.ratio * hd.mu R :=
        mul_le_mul_of_nonneg_right haMinRatio (hd.mu_nonneg R)
      _ ≤ d.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
        mul_le_mul_of_nonneg_left hμ d.ratio_pos.le
      _ = (d.chart k x).radius := by rw [d.radius_eq]
  refine ⟨e, hdiag, hfence, ?_, hradius⟩
  simpa only [b, d.chartPhaseK_eq] using hinvApprox

theorem exists_diag_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 ∧
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
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e
              (c := d.chart k x) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
                PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  let Y := X.obj 0
  let x₀ := Y.basepoint
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let b₀ := d.metricBounds 0 x₀
  obtain ⟨q, hq, hqWide, hqAccel₀, herr₀, hinvErr⟩ :=
    exists_chart_biq_inv (I := I) Y.metric b₀ (d.phaseRadius_pos R)
  have hqAccel :
      3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) := by
    simpa only [b₀, metricBounds] using hqAccel₀
  have herr : PhaseFlow.phaseErr (d.phaseK (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    simpa only [b₀, d.chartPhaseK_eq] using herr₀
  let δ : Real := ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹ -
        PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
    ((q : Real) / 2)
  have hmargin : 0 <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) :=
    tsub_pos_iff_lt.mpr herr
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (by exact_mod_cast hmargin)
      (div_pos hqReal (by norm_num))
  refine ⟨q, δ, hq, by nlinarith [hqWide], hδ, rfl, ?_, ?_⟩
  · simpa only [b₀, d.chartPhaseK_eq] using hinvErr
  intro k x hx
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let c := d.chart k x
  let b := d.metricBounds k x
  have hrMetric : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) b.radius := by
    simpa only [b] using d.phaseRadius_metric hx
  have hrQuarter : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (c.radius / 4) := by
    simpa only [c] using d.phaseRadius_chart hx
  have hqAccel' :
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) := by
    simpa only [b, metricBounds] using hqAccel
  have herr' : PhaseFlow.phaseErr
      (chartPhaseK (X.obj k).metric b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    simpa only [b, d.chartPhaseK_eq] using herr
  obtain ⟨δ', e, hδ', hδ'eq, hdiag, hfence, hinvApprox⟩ :=
    exists_chart_diag_of (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x c b hrMetric hrQuarter q hq hqWide hqAccel' herr'
  have hδ'eq' : δ' = δ := by
    simpa only [δ, b, d.chartPhaseK_eq] using hδ'eq
  refine ⟨e, ?_, hfence, ?_⟩
  · simpa only [hδ'eq'] using hdiag
  · simpa only [b, d.chartPhaseK_eq] using hinvApprox

theorem exists_uniform_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < d.phaseRadius R ∧
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
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
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
              x q δ e (c := d.chart k x) ∧
            NormalDiagFence (I := I) (X.obj k) x q e
              (c := d.chart k x) := by
  obtain ⟨q, δ, hq, hqRadius, hδ, hδeq, _hinvErr, hall⟩ :=
    d.exists_diag_inv hcomplete hconn R
  exact ⟨q, δ, hq, hqRadius, hδ, hδeq, fun k x hx => by
    obtain ⟨e, he, hfence, _hinvApprox⟩ := hall k x hx
    exact ⟨e, he, hfence⟩⟩

end BoundedGeometryNormalData

end HCGCompactness
end DifferentialGeometry
