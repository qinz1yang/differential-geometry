import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarGradient
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private def unitShiGradientConst (d : ℕ) : ℝ :=
  shiLocalUniformBound d 1 (1 * ((0 - -(1 / 2)) / 4))
      ((1 / 2 / (4 * Real.exp ((d : ℝ) ^ 2 * 1 * (0 - -(1 / 2))))) * Real.sqrt 1 /
        (4 * Real.exp ((d : ℝ) ^ 2 * 1 * ((0 - -(1 / 2)) / 4)))) *
    1 / Real.sqrt ((0 - -(1 / 2)) / 4) ^ 1

private theorem unitShiGradientConst_nonneg (d : ℕ) : 0 ≤ unitShiGradientConst d := by
  unfold unitShiGradientConst
  exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) zero_le_one)
    (pow_nonneg (Real.sqrt_nonneg _) _)

private theorem ofReal_inv_mul_le_iff {r ρ : ℝ} (hr : 0 < r) (e : ℝ≥0∞) :
    ENNReal.ofReal r⁻¹ * e ≤ ENNReal.ofReal ρ ↔ e ≤ ENNReal.ofReal (r * ρ) := by
  have hone : ENNReal.ofReal r * ENNReal.ofReal r⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
  have hone' : ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * ρ) = ENNReal.ofReal ρ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ← mul_assoc, inv_mul_cancel₀ hr.ne',
      one_mul]
  constructor
  · intro h
    calc
      e = ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * e) := by rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal r * ENNReal.ofReal ρ := by gcongr
      _ = ENNReal.ofReal (r * ρ) := (ENNReal.ofReal_mul hr.le).symm
  · intro h
    calc
      ENNReal.ofReal r⁻¹ * e ≤ ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * ρ) := by gcongr
      _ = ENNReal.ofReal ρ := hone'

private theorem lt_ofReal_mul_of_ofReal_inv_mul_lt {r ρ : ℝ} (hr : 0 < r) {e : ℝ≥0∞}
    (h : ENNReal.ofReal r⁻¹ * e < ENNReal.ofReal ρ) : e < ENNReal.ofReal (r * ρ) := by
  by_contra hle
  have hle' : ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * ρ) ≤ ENNReal.ofReal r⁻¹ * e := by
    gcongr
    exact not_lt.mp hle
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ← mul_assoc, inv_mul_cancel₀ hr.ne',
    one_mul] at hle'
  exact (lt_irrefl _) (h.trans_le hle')

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem unit_lRegularizedCurve_mem_ball
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (x : M) (hreg : Ioo (-1 : ℝ) 0 ⊆ D.regular)
    (h0 : (0 : ℝ) ∈ D.regular)
    (hcpt : IsCompact {y | riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (1 / 2)})
    (hRm : ∀ t ∈ Icc (-1 : ℝ) 0, ∀ y,
      riemannianEDistOf (S.base.metric 0) x y < ENNReal.ofReal 1 →
        FlowMetricBall.rmNormSq S t y ≤ 1)
    {b R : ℝ} (hb : 0 < b) (hb2 : b ≤ 1 / 2)
    (hreach : b * Real.sqrt (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2) *
      (Real.exp ((1 + 2 * ((Module.finrank ℝ E : ℝ) ^ 2 *
        unitShiGradientConst (Module.finrank ℝ E)) * b ^ 2 +
          4 * (Module.finrank ℝ E : ℝ) ^ 2 * b) * b) * (4 * R ^ 2 + 1))) < 1 / 8)
    (Z : TangentSpace I x) (hZ : (S.base.metric 0).inner x Z Z ≤ R ^ 2) :
    b ∈ lRegularizedDomain S 0 x Z ∧ ∀ q ∈ Icc (0 : ℝ) b,
      riemannianEDistOf (S.base.metric 0) x (lRegularizedCurve S 0 x Z q) <
        ENNReal.ofReal (1 / 8) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hcar : Icc (-(1 / 2) : ℝ) 0 ⊆ D.carrier := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h | h
    · exact D.regular_subset (h ▸ h0)
    · exact D.regular_subset (hreg ⟨by linarith [ht.1], h⟩)
  have hreg2 : Ioo (-(1 / 2) : ℝ) 0 ⊆ D.regular := fun t ht =>
    hreg ⟨by linarith [ht.1], ht.2⟩
  have hball1 : ∀ y, riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (1 / 2) →
      riemannianEDistOf (S.base.metric 0) x y < ENNReal.ofReal 1 := fun y hy =>
    hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num))
  have hq2 : ∀ q ∈ Icc (0 : ℝ) b, q ^ 2 ≤ 1 / 4 := fun q hq => by
    nlinarith [hq.1, hq.2]
  have hshi := shi_curvDerivNorm_on_terminal_ball S hS (a := -(1 / 2)) (b := 0) (K := 1)
    (R := 1 / 2) (by norm_num) one_pos (by norm_num) hcar hreg2 x hcpt
    (fun t ht y hy => by
      rw [one_pow]
      exact hRm t ⟨by linarith [ht.1], ht.2⟩ y (hball1 y hy))
  have hcpt8 : IsCompact {y | riemannianEDistOf (S.base.metric 0) x y ≤
      ENNReal.ofReal (1 / 8)} :=
    hcpt.of_isClosed_subset
      (Geometry.Metric.isClosed_riemannianClosedBallOf (S.base.metric 0) x (1 / 8))
      (fun y hy => (show riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (1 / 8)
        from hy).trans (ENNReal.ofReal_le_ofReal (by norm_num)))
  have hsmall : ∀ y, riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (1 / 8) →
      riemannianEDistOf (S.base.metric 0) x y < ENNReal.ofReal 1 := fun y hy =>
    hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num))
  have hslab : Icc (0 - b ^ 2) 0 ⊆ D.regular := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h | h
    · exact h ▸ h0
    · exact hreg ⟨by nlinarith [ht.1], h⟩
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  refine mem_lRegularizedDomain_and_edist_lt_of_local_gradient_ricci_bounds S hS 0 x
    (S.base.metric 0) (A := Real.exp (n ^ 2)) (G := n ^ 2 * unitShiGradientConst
      (Module.finrank ℝ E)) (K := n ^ 2) hb (by norm_num) (Real.exp_pos _).le
    (mul_nonneg hn2 (unitShiGradientConst_nonneg _)) hn2 hslab hcpt8 ?_ ?_ ?_ hreach Z hZ
  · intro q hq y hy w
    have htq : (0 : ℝ) - q ^ 2 ∈ Icc (-(1 / 2) : ℝ) 0 :=
      ⟨by linarith [hq2 q hq], by nlinarith [sq_nonneg q]⟩
    have hc := inner_le_exp_mul_inner_of_rmNormSq_le hS one_pos hcar hreg2
      (y := y) (fun u hu => by
        rw [one_pow, one_mul]
        exact hRm u ⟨by linarith [hu.1], hu.2⟩ y (hsmall y hy))
      (s₁ := 0) (s₂ := 0 - q ^ 2) ⟨by norm_num, le_rfl⟩ htq w
    refine hc.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
      (metric_inner_self_nonneg _ _ _))
    rw [show (0 : ℝ) - (0 - q ^ 2) = q ^ 2 by ring, abs_of_nonneg (sq_nonneg q)]
    nlinarith [hq2 q hq]
  · intro q hq y hy w
    have hyball : y ∈ riemannianClosedBallOf (S.base.metric 0) x (1 / 2 / 4) := by
      change riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (1 / 2 / 4)
      exact hy.trans (ENNReal.ofReal_le_ofReal (by norm_num))
    have htq : (0 : ℝ) - q ^ 2 ∈ Icc ((-(1 / 2) + 0) / 2 : ℝ) 0 :=
      ⟨by linarith [hq2 q hq], by nlinarith [sq_nonneg q]⟩
    have hbound := hshi 1 _ htq y hyball
    have hnabla : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 (0 - q ^ 2) y) ≤
        unitShiGradientConst (Module.finrank ℝ E) := by
      rw [← curvNormSq_eq]
      exact hbound
    have hg := scalar_gradient_abs_le_nabla_rm (S.base.metric (0 - q ^ 2)) y w
    calc
      _ ≤ n ^ 2 * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 (0 - q ^ 2) y) *
          Real.sqrt ((S.base.metric (0 - q ^ 2)).inner y w w) := hg
      _ ≤ n ^ 2 * unitShiGradientConst (Module.finrank ℝ E) *
          Real.sqrt ((S.base.metric (0 - q ^ 2)).inner y w w) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnabla hn2)
          (Real.sqrt_nonneg _)
  · intro q hq y hy w
    have hcurv : Tensor0SBundle.normSq0S (S.base.metric (0 - q ^ 2)) y 4
        (S.base.rm04 (0 - q ^ 2) y) ≤ 1 :=
      hRm _ ⟨by linarith [hq2 q hq], by nlinarith [sq_nonneg q]⟩ y (hsmall y hy)
    have hquad := ricci_quadratic_form_bound_of_solution_curvature_bound S y w hcurv
    rw [← metricRicciAt_apply_eq_ricciTensor, Real.sqrt_one, mul_one] at hquad
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt] using hquad

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_lRegularizedCurve_mem_ball_of_parabolic_rm_bound (R : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [SigmaCompactSpace M] {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → ∀ (T r : ℝ) (x : M), 0 < r → Ioo (T - r ^ 2) T ⊆ D.regular →
        T ∈ D.regular →
        IsCompact {y | riemannianEDistOf (S.base.metric T) x y ≤ ENNReal.ofReal (r / 2)} →
        (∀ t ∈ Icc (T - r ^ 2) T, ∀ y,
          riemannianEDistOf (S.base.metric T) x y < ENNReal.ofReal r →
            r ^ 4 * FlowMetricBall.rmNormSq S t y ≤ 1) →
        ∀ Z : TangentSpace I x, (S.base.metric T).inner x Z Z ≤ R ^ 2 →
          σ * r ∈ lRegularizedDomain S T x Z ∧ ∀ s ∈ Icc 0 (σ * r),
            riemannianEDistOf (S.base.metric T) x (lRegularizedCurve S T x Z s) <
              ENNReal.ofReal (r / 4) := by
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  let A : ℝ := Real.exp (n ^ 2)
  let G : ℝ := n ^ 2 * unitShiGradientConst (Module.finrank ℝ E)
  let K : ℝ := n ^ 2
  let Q : ℝ := Real.exp ((1 + 2 * G * (1 / 2) ^ 2 + 4 * K * (1 / 2)) * (1 / 2)) *
    (4 * R ^ 2 + 1)
  let σ : ℝ := min (1 / 2) (1 / 8 / (2 * (Real.sqrt (A * Q) + 1)))
  have hσ : 0 < σ := lt_min (by norm_num) (div_pos (by norm_num) (by positivity))
  have hσB : σ ≤ 1 / 2 := min_le_left _ _
  have hG : 0 ≤ G := mul_nonneg (sq_nonneg n) (unitShiGradientConst_nonneg _)
  have hK : 0 ≤ K := sq_nonneg n
  have hreach : σ * Real.sqrt (A * (Real.exp ((1 + 2 * G * σ ^ 2 + 4 * K * σ) * σ) *
      (4 * R ^ 2 + 1))) < 1 / 8 := by
    have hσR : σ ≤ 1 / 8 / (2 * (Real.sqrt (A * Q) + 1)) := min_le_right _ _
    have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.sqrt (A * Q) + 1))).mp hσR
    have hσ2 : σ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hσ.le hσB 2
    have hcoeff : 1 + 2 * G * σ ^ 2 + 4 * K * σ ≤
        1 + 2 * G * (1 / 2) ^ 2 + 4 * K * (1 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hσ2 hG, mul_le_mul_of_nonneg_left hσB hK]
    have hexp := Real.exp_le_exp.mpr (mul_le_mul hcoeff hσB hσ.le (by positivity))
    have hQ : Real.exp ((1 + 2 * G * σ ^ 2 + 4 * K * σ) * σ) * (4 * R ^ 2 + 1) ≤ Q :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    calc
      _ ≤ σ * Real.sqrt (A * Q) := mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le)) hσ.le
      _ < 1 / 8 := by nlinarith [Real.sqrt_nonneg (A * Q)]
  refine ⟨σ, hσ, hσB.trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ D S hS T r x hr hreg hT hcpt hRm Z hZ
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hlam : 0 < (r ^ 2)⁻¹ := inv_pos.mpr hr2
  have hTc : T ∈ D.carrier := D.regular_subset hT
  have hsqrt : Real.sqrt (r ^ 2)⁻¹ = r⁻¹ := by rw [Real.sqrt_inv, Real.sqrt_sq hr.le]
  have htime : ∀ s, parabolicTime T (r ^ 2)⁻¹ s = T + s * r ^ 2 := fun s => by
    unfold parabolicTime
    rw [div_inv_eq_mul]
  have hmetric : ∀ s, (parabolicSolution S T (r ^ 2)⁻¹ hlam hTc).base.metric s =
      scaleMetric (r ^ 2)⁻¹ hlam (S.base.metric (T + s * r ^ 2)) := fun s => by
    rw [← htime]
    rfl
  have hedist : ∀ y, riemannianEDistOf
      ((parabolicSolution S T (r ^ 2)⁻¹ hlam hTc).base.metric 0) x y =
        ENNReal.ofReal r⁻¹ * riemannianEDistOf (S.base.metric T) x y := fun y => by
    rw [hmetric, zero_mul, add_zero, edistOf_scale, hsqrt]
  have hregR : Ioo (-1 : ℝ) 0 ⊆ (parabolicInterval D T (r ^ 2)⁻¹ hTc).regular := by
    intro s hs
    change parabolicTime T (r ^ 2)⁻¹ s ∈ D.regular
    rw [htime]
    exact hreg ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have h0R : (0 : ℝ) ∈ (parabolicInterval D T (r ^ 2)⁻¹ hTc).regular := by
    change parabolicTime T (r ^ 2)⁻¹ 0 ∈ D.regular
    rw [parabolicTime_zero]
    exact hT
  have hset : {y | riemannianEDistOf ((parabolicSolution S T (r ^ 2)⁻¹ hlam hTc).base.metric 0)
      x y ≤ ENNReal.ofReal (1 / 2)} =
        {y | riemannianEDistOf (S.base.metric T) x y ≤ ENNReal.ofReal (r / 2)} := by
    ext y
    simp only [mem_ofPred_eq]
    rw [hedist, ofReal_inv_mul_le_iff hr, show r * (1 / 2) = r / 2 by ring]
  have hRmR : ∀ t ∈ Icc (-1 : ℝ) 0, ∀ y,
      riemannianEDistOf ((parabolicSolution S T (r ^ 2)⁻¹ hlam hTc).base.metric 0) x y <
        ENNReal.ofReal 1 →
      FlowMetricBall.rmNormSq (parabolicSolution S T (r ^ 2)⁻¹ hlam hTc) t y ≤ 1 := by
    intro t ht y hy
    rw [hedist] at hy
    have hy' := lt_ofReal_mul_of_ofReal_inv_mul_lt hr hy
    rw [mul_one] at hy'
    have h := hRm (T + t * r ^ 2) ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ y hy'
    unfold FlowMetricBall.rmNormSq at h ⊢
    rw [parabolicRmNormSq, inv_inv, htime, show (r ^ 2) ^ 2 = r ^ 4 by ring]
    exact h
  have hZ' : ((parabolicSolution S T (r ^ 2)⁻¹ hlam hTc).base.metric 0).inner x
      ((Real.sqrt (r ^ 2)⁻¹)⁻¹ • Z) ((Real.sqrt (r ^ 2)⁻¹)⁻¹ • Z) ≤ R ^ 2 := by
    rw [hmetric, zero_mul, add_zero, scaleMetric_inner_inv_sqrt_smul]
    exact hZ
  obtain ⟨hdom, hball⟩ := unit_lRegularizedCurve_mem_ball
    (parabolicSolution S T (r ^ 2)⁻¹ hlam hTc)
    (parabolicSolution_isSolutionOn S hS T _ hlam hTc) x hregR h0R (hset ▸ hcpt) hRmR hσ hσB
    hreach _ hZ'
  have hdomEq := lRegularizedDomain_parabolic S T (r ^ 2)⁻¹ hlam hTc T x Z
  rw [parabolicBackward_self] at hdomEq
  rw [hdomEq] at hdom
  have hc : Real.sqrt (r ^ 2)⁻¹ ≠ 0 := by
    rw [hsqrt]
    exact inv_ne_zero hr.ne'
  refine ⟨?_, fun s hs => ?_⟩
  · have hmem := (Set.mem_smul_set_iff_inv_smul_mem₀ hc _ σ).mp hdom
    rwa [hsqrt, inv_inv, smul_eq_mul, mul_comm] at hmem
  · have hcurve := lRegularizedCurve_parabolic S hS T (r ^ 2)⁻¹ hlam hTc T x Z s
    rw [parabolicBackward_self] at hcurve
    have hsσ : Real.sqrt (r ^ 2)⁻¹ * s ∈ Icc (0 : ℝ) σ := by
      rw [hsqrt]
      refine ⟨mul_nonneg (inv_nonneg.mpr hr.le) hs.1, ?_⟩
      rw [inv_mul_le_iff₀ hr]
      linarith [hs.2]
    have h := hball _ hsσ
    rw [hcurve, hedist] at h
    exact (lt_ofReal_mul_of_ofReal_inv_mul_lt hr h).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))

end DifferentialGeometry.PDE.RicciFlow.Perelman
