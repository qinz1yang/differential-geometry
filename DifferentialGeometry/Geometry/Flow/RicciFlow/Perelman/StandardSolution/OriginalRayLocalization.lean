import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.OriginalRaySpeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FixedSetVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

def originalRayLocalizationEpsilon (n : ℕ) : ℝ :=
  min (originalRaySpeedEpsilon n) (1 / (8 * (1 + (n : ℝ) ^ 2)))

theorem originalRayLocalizationEpsilon_pos (n : ℕ) :
    0 < originalRayLocalizationEpsilon n := by
  exact lt_min (originalRaySpeedEpsilon_pos n) (by positivity)

private theorem localization_metric_factor_le (n : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ originalRayLocalizationEpsilon n) :
    Real.exp (2 * (n : ℝ) ^ 2 * epsilon) ≤ 4 / 3 := by
  have hsmall : epsilon ≤ 1 / (8 * (1 + (n : ℝ) ^ 2)) :=
    hepsilonSmall.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 8 * (1 + (n : ℝ) ^ 2))).mp hsmall
  have hquarter : 2 * (n : ℝ) ^ 2 * epsilon ≤ 1 / 4 := by
    nlinarith only [hmul, hepsilon.le]
  have hnonneg : 0 ≤ 2 * (n : ℝ) ^ 2 * epsilon := by positivity
  have hlt : 2 * (n : ℝ) ^ 2 * epsilon < 1 := by linarith only [hquarter]
  apply (Real.exp_bound_div_one_sub_of_interval hnonneg hlt).trans
  apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
  nlinarith only [hquarter]

private theorem first_exit_closed
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {gamma : ℝ → X} {b : ℝ} (hb : 0 < b)
    (hgamma : ContinuousOn gamma (Icc (0 : ℝ) b))
    (h0 : gamma 0 ∈ interior K) (hbK : gamma b ∉ K) :
    ∃ t : ℝ, t ∈ Ioc (0 : ℝ) b ∧
      (∀ s ∈ Icc (0 : ℝ) t, gamma s ∈ K) ∧ gamma t ∈ frontier K := by
  let J := Icc (0 : ℝ) b
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let gammaJ : J → X := fun t ↦ gamma t
  let A : Set J := gammaJ ⁻¹' (interior K)ᶜ
  have hgammaJ : Continuous gammaJ := hgamma.domRestrict
  have hA : IsClosed A := isOpen_interior.isClosed_compl.preimage hgammaJ
  have hbA : (⟨b, by simp [J, hb.le]⟩ : J) ∈ A := by
    change gamma b ∉ interior K
    exact fun h ↦ hbK (interior_subset h)
  obtain ⟨t, htA, htmin⟩ := hA.isCompact.exists_isMinOn
    ⟨⟨b, by simp [J, hb.le]⟩, hbA⟩ continuous_subtype_val.continuousOn
  have htNot : gamma (t : ℝ) ∉ interior K := htA
  have htne : (t : ℝ) ≠ 0 := by
    intro h
    apply htNot
    simpa only [h] using h0
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.property.1 (Ne.symm htne)
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t, gamma s ∈ interior K := by
    intro s hs
    by_contra hsNot
    let sJ : J := ⟨s, hs.1, hs.2.le.trans t.property.2⟩
    have hsA : sJ ∈ A := hsNot
    exact (not_le_of_gt hs.2) (htmin hsA)
  have htClosure : (t : ℝ) ∈ closure (Ico (0 : ℝ) t) := by
    rw [closure_Ico (Ne.symm htne)]
    exact ⟨htpos.le, le_rfl⟩
  have hcont : ContinuousWithinAt gamma (Ico (0 : ℝ) t) t :=
    (hgamma t t.property).mono fun s hs ↦ ⟨hs.1, hs.2.le.trans t.property.2⟩
  have htK : gamma t ∈ K := by
    have h := hcont.mem_closure htClosure fun s hs ↦ interior_subset (hbefore s hs)
    simpa only [hK.closure_eq] using h
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, ?_⟩
  · intro s hs
    by_cases hst : s = t
    · simpa only [hst] using htK
    · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
  · rw [frontier, hK.closure_eq]
    exact ⟨htK, htNot⟩

section Prefix

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] {D : RealTimeInterval}

private theorem original_ray_prefix_edist_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      ∀ x ∈ B.set, B.radius ^ 4 * FlowMetricBall.rmNormSq S t x ≤ 1)
    (hcomplete : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hqual : ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ originalRayLocalizationEpsilon (Module.finrank ℝ E))
    (Z : TangentSpace I B.center)
    (hZ : Real.sqrt ((S.base.metric (time : ℝ)).inner B.center Z Z) ≤
      1 / (10 * Real.sqrt epsilon))
    (a : ℝ) (ha : 0 < a) (haScale : a ≤ Real.sqrt (epsilon * B.radius ^ 2))
    (haDom : a ∈ lRegularizedDomain S (time : ℝ) B.center Z)
    (hprefix : ∀ s ∈ Icc (0 : ℝ) a,
      riemannianEDistOf (S.base.metric (time : ℝ)) B.center
        (lRegularizedCurve S (time : ℝ) B.center Z s) ≤ ENNReal.ofReal (B.radius / 3)) :
    riemannianEDistOf (S.base.metric (time : ℝ)) B.center
      (lRegularizedCurve S (time : ℝ) B.center Z a) < ENNReal.ofReal (B.radius / 3) := by
  let T : ℝ := time
  let r : ℝ := B.radius
  let alpha : ℝ → M := lRegularizedCurve S T B.center Z
  let n := Module.finrank ℝ E
  have hr : 0 < r := B.radius_pos
  have hepsSpeed : epsilon ≤ originalRaySpeedEpsilon n :=
    hepsilonSmall.trans (min_le_left _ _)
  have heps100 : epsilon ≤ 1 / 100 :=
    hepsSpeed.trans (show originalRaySpeedEpsilon n ≤ 1 / 100 from min_le_left _ _)
  have heps1 : epsilon < 1 := by linarith only [heps100]
  have hscale : Real.sqrt (epsilon * r ^ 2) = Real.sqrt epsilon * r := by
    rw [Real.sqrt_mul hepsilon.le, Real.sqrt_sq hr.le]
  have hsquare (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) : s ^ 2 ≤ epsilon * r ^ 2 := by
    calc
      s ^ 2 ≤ (Real.sqrt (epsilon * r ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hs.1 (hs.2.trans haScale) 2
      _ = _ := Real.sq_sqrt (mul_nonneg hepsilon.le (sq_nonneg r))
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      T - s ^ 2 ∈ Icc (T - epsilon * r ^ 2) T :=
    ⟨by linarith only [hsquare s hs], sub_le_self _ (sq_nonneg s)⟩
  have hbig (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      T - s ^ 2 ∈ Icc (T - r ^ 2) T := by
    have h := mul_le_mul_of_nonneg_right heps1.le (sq_nonneg r)
    exact ⟨by linarith only [hsquare s hs, h], sub_le_self _ (sq_nonneg s)⟩
  have hlate (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      T - s ^ 2 ∈ Icc (T - r ^ 2 / 2) T := by
    have h := mul_le_mul_of_nonneg_right heps100 (sq_nonneg r)
    exact ⟨by nlinarith only [hsquare s hs, h, sq_nonneg r],
      sub_le_self _ (sq_nonneg s)⟩
  have hhalf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      riemannianEDistOf (S.base.metric T) B.center (alpha s) < ENNReal.ofReal (r / 2) := by
    apply (hprefix s hs).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r / 2)).mpr
    linarith only [hr]
  have hinball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) : alpha s ∈ B.set := by
    change riemannianEDistOf (S.base.metric T) B.center (alpha s) < ENNReal.ofReal r
    exact (hhalf s hs).trans (by
      apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
      linarith only [hr])
  have hgrad (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      |(S.base.metric (T - s ^ 2)).inner (alpha s)
        (gradientFun (I := I) (S.base.metric (T - s ^ 2))
          (S.scalar (T - s ^ 2)) (alpha s)) (lVelocity (I := I) alpha s)| ≤
        (fixedBallScalarGradientConstant n / r ^ 3) *
          Real.sqrt (lRegularizedSpeedSq S T alpha s) := by
    let clock : RealTimeInterval.FlowTime D := ⟨T - s ^ 2, hslab (hbig s hs)⟩
    have h := (fixed_ball_curvature_and_scalar_gradient_bound S hS B hslab hreg
      hRm hcomplete hqual (alpha s) (hhalf s hs) clock (hlate s hs)).2
    simpa only [lRegularizedSpeedSq] using h (lVelocity (I := I) alpha s)
  have hsqrt : Real.sqrt (1 / r ^ 4) = 1 / r ^ 2 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
      show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (one_div_pos.mpr (sq_pos_of_pos hr)).le
  have hric (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      |S.ricciAt (T - s ^ 2) (alpha s)
        (vec2 (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))| ≤
      ((n : ℝ) ^ 2 / r ^ 2) * lRegularizedSpeedSq S T alpha s := by
    have hcurv : normSq0S (I := I) (S.base.metric (T - s ^ 2)) (alpha s) 4
        (S.base.rm04 (T - s ^ 2) (alpha s)) ≤ 1 / r ^ 4 := by
      apply (le_div_iff₀ (pow_pos hr 4)).mpr
      simpa only [FlowMetricBall.rmNormSq, mul_comm] using hRm (T - s ^ 2) (hbig s hs) (alpha s) (hinball s hs)
    have h := ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S (alpha s) (lVelocity (I := I) alpha s) hcurv
    rw [← metricRicciAt_apply_eq_ricciTensor, hsqrt] at h
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt, lRegularizedSpeedSq,
      n, div_eq_mul_inv, one_mul] using h
  have hspeed := lRegCurve_speedSq_le_of_local_bounds S hS T B.center Z
    r hr epsilon hepsilon hepsSpeed a ha (haScale.trans_eq hscale) haDom hZ hgrad hric
  have hmetric := fixed_set_metric_comparison_of_rm S hS T r hr hslab hreg hRm
    hepsilon heps1
  have hfactor := localization_metric_factor_le n epsilon hepsilon hepsilonSmall
  have hreference (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) :
      (S.base.metric T).inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s) ≤ 4 / (45 * epsilon) := by
    have hcomp := (hmetric (T - s ^ 2) (hclock s hs)).2
      (alpha s) (hinball s hs) (lVelocity (I := I) alpha s)
    calc
      _ ≤ Real.exp (2 * (n : ℝ) ^ 2 * epsilon) * lRegularizedSpeedSq S T alpha s := hcomp.1
      _ ≤ (4 / 3 : ℝ) * (1 / (15 * epsilon)) :=
        mul_le_mul hfactor (hspeed s hs) (lRegularizedSpeedSq_nonneg S T alpha s) (by norm_num)
      _ = _ := by field_simp [hepsilon.ne']; ring
  have hregular : IsLRegularizedCurveOn S T alpha (Icc (0 : ℝ) a) B.center Z := by
    simpa only [uIcc_of_le ha.le] using lRegularizedCurve_isLRegularizedCurveOn S hS T B.center Z ha haDom
  have hE := lRegCurve_reference_integrable (S.base.metric T) hregular
  have hEI : IntervalIntegrable (fun s ↦ (S.base.metric T).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume 0 a := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le ha.le] using hE
  have hEC : curveEnergy (S.base.metric T) alpha 0 a ≤ a * (4 / (45 * epsilon)) := by
    have h := intervalIntegral.integral_mono_on ha.le hEI intervalIntegrable_const hreference
    simpa only [curveEnergy, lVelocity, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul] using h
  have hdist := edistOf_le_budget (S.base.metric T) ha.le
    (lRegularizedCurve_c1On S hS T B.center Z haDom) hE hEC
  have hprodnonneg : 0 ≤ Real.sqrt a * Real.sqrt (a * (4 / (45 * epsilon))) := by positivity
  have hprodsq : (Real.sqrt a * Real.sqrt (a * (4 / (45 * epsilon)))) ^ 2 =
      a ^ 2 * (4 / (45 * epsilon)) := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt (by positivity)]
    ring
  have hbudget : a ^ 2 * (4 / (45 * epsilon)) ≤ 4 * r ^ 2 / 45 := by
    calc
      _ ≤ (epsilon * r ^ 2) * (4 / (45 * epsilon)) :=
        mul_le_mul_of_nonneg_right (hsquare a ⟨ha.le, le_rfl⟩) (by positivity)
      _ = _ := by field_simp [hepsilon.ne']
  have hstrictsq : (Real.sqrt a * Real.sqrt (a * (4 / (45 * epsilon)))) ^ 2 < (r / 3) ^ 2 := by
    rw [hprodsq]
    nlinarith only [hbudget, sq_pos_of_pos hr]
  have hstrict : Real.sqrt a * Real.sqrt (a * (4 / (45 * epsilon))) < r / 3 :=
    (sq_lt_sq₀ hprodnonneg (by positivity)).mp hstrictsq
  have hdist' : riemannianEDistOf (S.base.metric T) B.center (alpha a) ≤
      ENNReal.ofReal (Real.sqrt a * Real.sqrt (a * (4 / (45 * epsilon)))) := by
    simpa only [alpha, lRegularizedCurve_zero, sub_zero] using hdist
  exact hdist'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict)

end Prefix

section OriginalInjectivity

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] {D : RealTimeInterval}

theorem lRegCurve_mem_terminal_third_ball_of_fixed_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      ∀ x ∈ B.set, B.radius ^ 4 * FlowMetricBall.rmNormSq S t x ≤ 1)
    (hcomplete : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hqual : ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ originalRayLocalizationEpsilon (Module.finrank ℝ E))
    (Z : TangentSpace I B.center)
    (hZ : Real.sqrt ((S.base.metric (time : ℝ)).inner B.center Z Z) ≤
      1 / (10 * Real.sqrt epsilon))
    (hinj : Z ∈ lInjDomain (E := E) (I := I) S (time : ℝ) B.center (epsilon * B.radius ^ 2)) :
    ∀ s ∈ Icc (0 : ℝ) (Real.sqrt (epsilon * B.radius ^ 2)),
      s ∈ lRegularizedDomain S (time : ℝ) B.center Z ∧
        riemannianEDistOf (S.base.metric (time : ℝ)) B.center
          (lRegularizedCurve S (time : ℝ) B.center Z s) < ENNReal.ofReal (B.radius / 3) := by
  let b : ℝ := Real.sqrt (epsilon * B.radius ^ 2)
  let alpha : ℝ → M := lRegularizedCurve S (time : ℝ) B.center Z
  let g := S.base.metric (time : ℝ)
  let K : Set M := {x | riemannianEDistOf g B.center x ≤ ENNReal.ofReal (B.radius / 3)}
  let O : Set M := {x | riemannianEDistOf g B.center x < ENNReal.ofReal (B.radius / 3)}
  have hr : 0 < B.radius := B.radius_pos
  obtain ⟨sigma, hsigma, hmin⟩ := hinj
  have hpositive : (Z, sigma) ∈ lExpPosDom S (time : ℝ) B.center := hmin.1
  have hsigmaDom := ((mem_lExpPosDom S (time : ℝ) B.center Z sigma).mp hpositive).2.2
  have hbDom : b ∈ lRegularizedDomain S (time : ℝ) B.center Z :=
    lRegularizedDomain_segment S (time : ℝ) B.center Z hsigmaDom (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt hsigma.le)
  have hdomain (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      s ∈ lRegularizedDomain S (time : ℝ) B.center Z :=
    lRegularizedDomain_segment S (time : ℝ) B.center Z hbDom hs.1 hs.2
  have hcont : Continuous (fun x : M ↦ riemannianEDistOf g B.center x) := by
    simpa only [riemannianEDistOf] using continuous_riemannianEDist g B.center
  have hK : IsClosed K := isClosed_le hcont continuous_const
  have hO : IsOpen O := isOpen_lt hcont continuous_const
  have hOK : O ⊆ interior K := by
    apply interior_maximal ?_ hO
    intro x hx
    change riemannianEDistOf g B.center x ≤ ENNReal.ofReal (B.radius / 3)
    exact (show riemannianEDistOf g B.center x < ENNReal.ofReal (B.radius / 3) from hx).le
  have hzero : alpha 0 ∈ O := by
    change riemannianEDistOf g B.center (lRegularizedCurve S (time : ℝ) B.center Z 0) < _
    rw [lRegularizedCurve_zero, riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (show 0 < B.radius / 3 by positivity)
  have hclosed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) : alpha s ∈ K := by
    by_contra hsNot
    have hspos : 0 < s := by
      apply lt_of_le_of_ne hs.1
      intro h
      apply hsNot
      simpa only [← h] using interior_subset (hOK hzero)
    have hc1 := lRegularizedCurve_c1On S hS (time : ℝ) B.center Z (hdomain s hs)
    obtain ⟨a, ha, hprefix, hfront⟩ := first_exit_closed hK hspos hc1.continuousOn
      (hOK hzero) hsNot
    have hascale : a ≤ b := ha.2.trans hs.2
    have haDom := hdomain a ⟨ha.1.le, hascale⟩
    have hstrict := original_ray_prefix_edist_lt S hS B hslab hreg hRm hcomplete hqual
      epsilon hepsilon hepsilonSmall Z hZ a ha.1 hascale haDom hprefix
    have hinside : alpha a ∈ interior K := hOK hstrict
    exact hfront.2 hinside
  intro s hs
  refine ⟨hdomain s hs, ?_⟩
  by_cases hs0 : s = 0
  · subst s
    exact hzero
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    exact original_ray_prefix_edist_lt S hS B hslab hreg hRm hcomplete hqual
      epsilon hepsilon hepsilonSmall Z hZ s hspos hs.2 (hdomain s hs)
      (fun u hu ↦ hclosed u ⟨hu.1, hu.2.trans hs.2⟩)

end OriginalInjectivity

end DifferentialGeometry.PDE.RicciFlow

end
