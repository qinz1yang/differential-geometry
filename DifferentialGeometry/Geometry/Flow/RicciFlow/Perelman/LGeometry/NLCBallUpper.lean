import DifferentialGeometry.Analysis.Integration.Measure.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCSourceTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.CurvatureBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem exp_quarter_le {x : Real} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x ≤ 4 / 3 := by
  calc
    Real.exp x ≤ 1 / (1 - x) :=
      Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
    _ ≤ 4 / 3 := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem lRedLen_scale
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D') (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D'.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          ∀ Z : TangentSpace J B.center,
            Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                1 / (8 * Real.sqrt eps) →
              Z ∈ lInjDomain S (time : Real) B.center (eps * B.radius ^ 2) →
                -((Module.finrank Real F : Real) ^ 2 * eps) ≤
                  redLength S (time : Real) B.center
                    (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
                    (eps * B.radius ^ 2) := by
  obtain ⟨epsR, hepsR, hrange⟩ :=
    lRegRange_scale (J := J) S hS time hrho hreg
  let eps₀ : Real := min epsR 1
  have heps₀ : 0 < eps₀ := lt_min hepsR zero_lt_one
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ hZinj
  have hepsR' : eps ≤ epsR := heps₀.trans (min_le_left epsR 1)
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_right epsR 1)
  let tau : Real := eps * B.radius ^ 2
  let b : Real := Real.sqrt eps * B.radius
  let n : Real := Module.finrank Real F
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hb : Real.sqrt tau = b := by
    dsimp only [tau, b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  have hbpos : 0 < b := by rw [← hb]; exact Real.sqrt_pos.2 htau
  have hbSq : b ^ 2 = tau := by rw [← hb, Real.sq_sqrt htau.le]
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hrange' := hrange eps heps hepsR' B hBrho hB Z hZ
  dsimp only at hrange'
  obtain ⟨sigma, hsigma, hmin⟩ := hZinj
  have hminTau : (Z, tau) ∈ lMinDomain S (time : Real) B.center := by
    exact lMinDomain_down S hS (time : Real) B.center Z hmin htau
      (by simpa only [tau] using hsigma.le)
  have hdomTau : (Z, tau) ∈ lExpPosDom S (time : Real) B.center :=
    ((mem_lMinDomain S (time : Real) B.center Z tau).1 hminTau).1
  have hbdom : b ∈ lRegDomain S (time : Real) B.center Z := by
    rcases (mem_lExpPosDom S (time : Real) B.center Z tau).1 hdomTau with
      ⟨_, _, hdom⟩
    simpa only [hb] using hdom
  let alpha : Real → N := lRegCurve S (time : Real) B.center Z
  have halpha : ContMDiffOn (modelWithCornersSelf Real Real) J 1 alpha
      (Icc (0 : Real) b) := by
    simpa only [alpha] using
      lRegCurve_c1On S hS (time : Real) B.center Z hbdom
  have hregRay : ∀ s ∈ Icc (0 : Real) b,
      (time : Real) - s ^ 2 ∈ D'.regular := by
    intro s hs
    exact lRegDomain_reg S (time : Real) B.center Z
      (lRegDomain_seg S (time : Real) B.center Z hbdom hs.1 hs.2)
  have hLagInt : IntervalIntegrable (lRegLag S (time : Real) alpha) volume 0 b :=
    lRegLag_int_c1 S hS.smoothMetric ⟨hS.scalarCont⟩ (time : Real) 0 b
      hbpos.le alpha halpha hregRay
  have hconstInt : IntervalIntegrable (fun _ : Real ↦ -2 * b ^ 2 * K)
      volume 0 b := intervalIntegrable_const
  have hLagLower : ∀ s ∈ Icc (0 : Real) b,
      -2 * b ^ 2 * K ≤ lRegLag S (time : Real) alpha s := by
    intro s hs
    have hsSq : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hbpos.le).2 hs.2
    have hbRad : b ^ 2 ≤ B.radius ^ 2 := by
      rw [hbSq]
      dsimp only [tau]
      nlinarith [sq_nonneg B.radius]
    have htimeB : (time : Real) - s ^ 2 ∈
        Icc ((time : Real) - B.radius ^ 2) (time : Real) :=
      ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have hsc : -K ≤ S.scalar ((time : Real) - s ^ 2) (alpha s) := by
      have hsc' := scalar_ge_of_rm (I := J) B hB htimeB (hrange' s hs).2
      rw [show Module.finrank Real (TangentSpace J (alpha s)) =
        Module.finrank Real F from rfl] at hsc'
      simpa only [K, n, alpha, SolutionOn.scalar, SolutionFamily.scalar] using hsc'
    have hkin : 0 ≤ (1 / 2 : Real) *
        (S.base.metric ((time : Real) - s ^ 2)).inner (alpha s)
          (lVelocity (I := J) alpha s) (lVelocity (I := J) alpha s) := by
      apply mul_nonneg (by norm_num)
      by_cases hv : lVelocity (I := J) alpha s = 0
      · rw [hv]
        rw [((S.base.metric ((time : Real) - s ^ 2)).inner (alpha s)).map_zero,
          zero_apply]
      · exact ((S.base.metric ((time : Real) - s ^ 2)).pos
          (alpha s) (lVelocity (I := J) alpha s) hv).le
    have hscalar : -2 * b ^ 2 * K ≤
        2 * s ^ 2 * S.scalar ((time : Real) - s ^ 2) (alpha s) := by
      have h₁ : -2 * b ^ 2 * K ≤ -2 * s ^ 2 * K := by
        nlinarith
      have h₂ : -2 * s ^ 2 * K ≤
          2 * s ^ 2 * S.scalar ((time : Real) - s ^ 2) (alpha s) := by
        nlinarith [sq_nonneg s]
      exact h₁.trans h₂
    dsimp only [lRegLag]
    linarith
  have haction : -2 * b ^ 2 * K * b ≤
      lRegAction S (time : Real) alpha 0 b := by
    change -2 * b ^ 2 * K * b ≤
      ∫ u : Real in 0..b, lRegLag S (time : Real) alpha u
    have hmono := intervalIntegral.integral_mono_on hbpos.le hconstInt hLagInt hLagLower
    calc
      -2 * b ^ 2 * K * b = b * (-2 * b ^ 2 * K) := by ring
      _ ≤ ∫ u : Real in 0..b, lRegLag S (time : Real) alpha u := by
        simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hmono
  have hcost : lCost S (time : Real) B.center
      (lExp S (time : Real) B.center Z tau) tau =
        lRegAction S (time : Real) alpha 0 b := by
    have hlen : lLength S (time : Real)
        (fun r : Real ↦ lExp S (time : Real) B.center Z r) 0 tau =
          lRegAction S (time : Real) alpha 0 b := by
      change lLength S (time : Real) (sqrtReparam alpha) 0 tau =
        lRegAction S (time : Real) alpha 0 b
      simpa only [hb] using
        lLength_sqrt (I := J) S (time : Real) alpha tau htau.le
    exact (((mem_lMinDomain S (time : Real) B.center Z tau).1 hminTau).2.symm).trans hlen
  have hscaleK : B.radius ^ 2 * K = n ^ 2 := by
    dsimp only [K, n]
    have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
    rw [show 1 / (B.radius ^ 2) ^ 2 = (1 / B.radius ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
    field_simp [B.radius_pos.ne']
  have hb2K : b ^ 2 * K = n ^ 2 * eps := by
    rw [hbSq]
    dsimp only [tau]
    calc
      eps * B.radius ^ 2 * K = eps * (B.radius ^ 2 * K) := by ring
      _ = eps * n ^ 2 := by rw [hscaleK]
      _ = n ^ 2 * eps := by ring
  rw [redLength, hcost, hb]
  have hden : 0 < 2 * b := mul_pos (by norm_num) hbpos
  apply (le_div_iff₀ hden).2
  calc
    -(n ^ 2 * eps) * (2 * b) = -2 * (n ^ 2 * eps) * b := by ring
    _ = -2 * (b ^ 2 * K) * b := by rw [hb2K]
    _ = -2 * b ^ 2 * K * b := by ring
    _ ≤ lRegAction S (time : Real) alpha 0 b := haction

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem lRedDen_scale
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D') (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D'.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          ∀ Z : TangentSpace J B.center,
            Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                1 / (8 * Real.sqrt eps) →
              Z ∈ lInjDomain S (time : Real) B.center (eps * B.radius ^ 2) →
                redDensity S (time : Real) B.center
                    (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
                    (eps * B.radius ^ 2) ≤
                  Real.exp
                    ((Module.finrank Real F : Real) ^ 2 * eps -
                      ((Module.finrank Real F : Real) / 2) *
                        Real.log (eps * B.radius ^ 2) -
                      ((Module.finrank Real F : Real) / 2) *
                        Real.log (4 * Real.pi)) := by
  obtain ⟨eps₀, heps₀, hlen⟩ :=
    lRedLen_scale (J := J) S hS time hrho hreg
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ hZinj
  have hlen' := hlen eps heps heps₀ B hBrho hB Z hZ hZinj
  unfold redDensity
  apply Real.exp_le_exp.mpr
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem src_norm_sublevel_measurable
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) (R : Real) :
    MeasurableSet
      {Z : E | Real.sqrt ((S.base.metric T).inner x Z Z) ≤ R} := by
  apply measurableSet_le
  · fun_prop
  · fun_prop

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem src_norm_superlevel_measurable
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) (R : Real) :
    MeasurableSet
      {Z : E | R < Real.sqrt ((S.base.metric T).inner x Z Z)} := by
  apply measurableSet_lt measurable_const
  fun_prop

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem lRedJac_ball_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          let tau := eps * B.radius ^ 2
          let c := Real.exp
            ((Module.finrank Real E : Real) ^ 2 * eps -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
          (∫⁻ Z : E in
              lInjDomain S (time : Real) B.center tau ∩
                {Z | Real.sqrt
                  ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                    1 / (8 * Real.sqrt eps)},
              ENNReal.ofReal
                (lRedJac S (time : Real) B.center Z tau *
                  lSrcDensity S (time : Real) B.center)
                ∂(modelHaar (E := E))) ≤
            ENNReal.ofReal c *
              riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric ((time : Real) - tau)) B.set := by
  obtain ⟨epsD, hepsD, hden⟩ :=
    lRedDen_scale (J := I) S hS time hrho hreg
  obtain ⟨epsE, hepsE, hend⟩ :=
    lExp_scale_ball (J := I) S hS time hrho hreg
  let eps₀ : Real := min epsD epsE
  have heps₀ : 0 < eps₀ := lt_min hepsD hepsE
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB
  dsimp only
  let tau : Real := eps * B.radius ^ 2
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩
    {Z | Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
      1 / (8 * Real.sqrt eps)}
  let Ψ := lExpPartial S hS (time : Real) B.center tau
    (mul_pos heps (sq_pos_of_pos B.radius_pos))
  have hepsD' : eps ≤ epsD := heps₀.trans (min_le_left epsD epsE)
  have hepsE' : eps ≤ epsE := heps₀.trans (min_le_right epsD epsE)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hnormMeas : MeasurableSet
      {Z : E | Real.sqrt
        ((S.base.metric (time : Real)).inner B.center Z Z) ≤
          1 / (8 * Real.sqrt eps)} := by
    exact src_norm_sublevel_measurable S (time : Real) B.center
      (1 / (8 * Real.sqrt eps))
  have hAmeas : MeasurableSet A := by
    exact (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter hnormMeas
  have hAsource : A ⊆ Ψ.source := by
    dsimp only [Ψ]
    rw [lExpPartial_source S hS (time : Real) B.center tau htau]
    exact inter_subset_left
  have hImageMeas : MeasurableSet (Ψ '' A) :=
    measurableSet_image_param_global (I := I) Ψ hAmeas hAsource
  have hImageBall : Ψ '' A ⊆ B.set := by
    rintro y ⟨Z, hZA, rfl⟩
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS (time : Real) B.center tau htau hZA.1]
    simpa only [tau] using hend eps heps hepsE' B hBrho hB Z hZA.2
  have hImageDen : ∀ y ∈ Ψ '' A,
      ENNReal.ofReal (redDensity S (time : Real) B.center y tau) ≤
        ENNReal.ofReal c := by
    rintro y ⟨Z, hZA, rfl⟩
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS (time : Real) B.center tau htau hZA.1]
    apply ENNReal.ofReal_le_ofReal
    simpa only [c, tau] using
      hden eps heps hepsD' B hBrho hB Z hZA.2 hZA.1
  have hparam :
      (∫⁻ y in Ψ '' A,
          ENNReal.ofReal (redDensity S (time : Real) B.center y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric ((time : Real) - tau))) =
        ∫⁻ Z in A,
          ENNReal.ofReal
              (paramDensity (S.base.metric ((time : Real) - tau)) Ψ Z) *
            ENNReal.ofReal (redDensity S (time : Real) B.center (Ψ Z) tau)
          ∂modelHaar (E := E) :=
    riemVol_param_lint (I := I) (S.base.metric ((time : Real) - tau)) Ψ
      (fun y ↦ ENNReal.ofReal (redDensity S (time : Real) B.center y tau))
      hAmeas hAsource
  have hsmallEq :
      (∫⁻ Z in A,
          ENNReal.ofReal
            (lRedJac S (time : Real) B.center Z tau *
              lSrcDensity S (time : Real) B.center)
          ∂modelHaar (E := E)) =
        ∫⁻ y in Ψ '' A,
          ENNReal.ofReal (redDensity S (time : Real) B.center y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric ((time : Real) - tau)) := by
    rw [hparam]
    refine MeasureTheory.setLIntegral_congr_fun hAmeas ?_
    intro Z hZA
    dsimp only [Ψ]
    rw [lExpPartial_density S hS (time : Real) B.center tau htau hZA.1,
      lExpPartial_apply S hS (time : Real) B.center tau htau hZA.1]
    rw [← ENNReal.ofReal_mul (lExpDensity_pos S hS (time : Real)
      B.center htau hZA.1).le]
    exact congrArg ENNReal.ofReal
      (lRedJac_mul_src S hS (time : Real) B.center htau hZA.1)
  change (∫⁻ Z in A,
      ENNReal.ofReal
        (lRedJac S (time : Real) B.center Z tau *
          lSrcDensity S (time : Real) B.center)
      ∂modelHaar (E := E)) ≤ _
  calc
    (∫⁻ Z in A,
        ENNReal.ofReal
          (lRedJac S (time : Real) B.center Z tau *
            lSrcDensity S (time : Real) B.center)
        ∂modelHaar (E := E)) =
      ∫⁻ y in Ψ '' A,
        ENNReal.ofReal (redDensity S (time : Real) B.center y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) := hsmallEq
    _ ≤ ∫⁻ _y in Ψ '' A, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) :=
      MeasureTheory.setLIntegral_mono' hImageMeas hImageDen
    _ ≤ ∫⁻ _y in B.set, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) :=
      MeasureTheory.lintegral_mono_set hImageBall
    _ = ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) B.set := by
      rw [MeasureTheory.setLIntegral_const]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem ballVol_move_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho →
          riemannianVolumeMeasure (I := I) (M := M)
              (S.base.metric ((time : Real) - eps * B.radius ^ 2)) B.set ≤
            ENNReal.ofReal
                (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
              B.volume := by
  obtain ⟨A, hA, hmetric⟩ :=
    lMetric_scale (I := I) S hS (time : Real) hrho hreg
  let eps₀ : Real := min 1 (1 / (8 * (A * rho ^ 2 + 1)))
  have hden : 0 < A * rho ^ 2 + 1 := by
    nlinarith [mul_nonneg hA (sq_nonneg rho)]
  have heps₀ : 0 < eps₀ :=
    lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hden))
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_left 1 _)
  have hepsM : eps ≤ 1 / (8 * (A * rho ^ 2 + 1)) :=
    heps₀.trans (min_le_right 1 _)
  let Q : Real := Real.exp (2 * A * eps * B.radius ^ 2)
  have hQpos : 0 < Q := Real.exp_pos _
  have harg0 : 0 ≤ 2 * A * eps * B.radius ^ 2 := by positivity
  have harg : 2 * A * eps * B.radius ^ 2 ≤ 1 / 4 := by
    have hrad : B.radius ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ B.radius_pos.le hrho.le).2 hBrho
    have hscale : eps * (A * rho ^ 2 + 1) ≤ 1 / 8 := by
      apply (le_div_iff₀ (by norm_num : 0 < (8 : Real))).2
      calc
        eps * (A * rho ^ 2 + 1) * 8 = eps * (8 * (A * rho ^ 2 + 1)) := by ring
        _ ≤ (1 / (8 * (A * rho ^ 2 + 1))) *
            (8 * (A * rho ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_right hepsM (by positivity)
        _ = 1 := by field_simp [hden.ne']
    have hAr : A * B.radius ^ 2 ≤ A * rho ^ 2 :=
      mul_le_mul_of_nonneg_left hrad hA
    calc
      2 * A * eps * B.radius ^ 2 = 2 * eps * (A * B.radius ^ 2) := by ring
      _ ≤ 2 * eps * (A * rho ^ 2) := by
        exact mul_le_mul_of_nonneg_left hAr (mul_nonneg (by norm_num) heps.le)
      _ ≤ 2 * (eps * (A * rho ^ 2 + 1)) := by
        have hAρ : A * rho ^ 2 ≤ A * rho ^ 2 + 1 := by linarith
        calc
          2 * eps * (A * rho ^ 2) ≤ 2 * eps * (A * rho ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hAρ (mul_nonneg (by norm_num) heps.le)
          _ = 2 * (eps * (A * rho ^ 2 + 1)) := by ring
      _ ≤ 1 / 4 := by linarith
  have hQle : Q ≤ 4 / 3 := by
    exact exp_quarter_le harg0 harg
  have ht : (time : Real) - eps * B.radius ^ 2 ∈
      Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
    ⟨le_rfl, sub_le_self _ (mul_nonneg heps.le (sq_nonneg B.radius))⟩
  have hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      (S.base.metric ((time : Real) - eps * B.radius ^ 2)).inner x v v ≤
        Q * (S.base.metric (time : Real)).inner x v v := by
    intro x v
    simpa only [Q] using
      (hmetric eps heps.le heps1 B.radius B.radius_pos hBrho
        ((time : Real) - eps * B.radius ^ 2) ht x v).2
  have hmeasure := volumeMeasure_le (I := I) (M := M)
    (S.base.metric (time : Real))
    (S.base.metric ((time : Real) - eps * B.radius ^ 2)) hQpos hcomp
  have hfactor : ENNReal.ofReal
      (Real.sqrt (Q ^ Module.finrank Real E)) ≤
        ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    exact pow_le_pow_left₀ hQpos.le hQle _
  calc
    riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric ((time : Real) - eps * B.radius ^ 2)) B.set ≤
      (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real))) B.set := hmeasure B.set
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by simp
    _ ≤ ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by
      simpa only [mul_comm] using
        mul_le_mul_right hfactor
          (riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (time : Real)) B.set)
    _ = ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) * B.volume := by
      rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem redVolume_ball_eta [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular)
    (eta : ENNReal) (heta : 0 < eta) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          let tau := eps * B.radius ^ 2
          let c := Real.exp
            ((Module.finrank Real E : Real) ^ 2 * eps -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
          redVolume S (time : Real) B.center tau ≤
            ENNReal.ofReal c *
                (ENNReal.ofReal
                    (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
                  B.volume) +
              eta := by
  obtain ⟨epsJ, hepsJ, hsmall⟩ :=
    lRedJac_ball_le (I := I) S hS time hrho hreg
  obtain ⟨epsV, hepsV, hmove⟩ :=
    ballVol_move_le (I := I) S hS time hrho hreg
  obtain ⟨R, hR, htail⟩ :=
    lSrcGauss_unif (E := E) (I := I) (M := M) (D := D)
      eta heta
  let d : Real := 1 / (8 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hRone)
  let eps₀ : Real := min epsJ (min epsV (min 1 (d ^ 2)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsJ (lt_min hepsV (lt_min zero_lt_one (sq_pos_of_pos hd)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB
  dsimp only
  have hepsJ' : eps ≤ epsJ :=
    heps₀.trans (min_le_left epsJ (min epsV (min 1 (d ^ 2))))
  have hepsV' : eps ≤ epsV :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      (min_le_left epsV (min 1 (d ^ 2))))
  have heps1 : eps ≤ 1 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      ((min_le_right epsV (min 1 (d ^ 2))).trans (min_le_left 1 (d ^ 2))))
  have hepsd : eps ≤ d ^ 2 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      ((min_le_right epsV (min 1 (d ^ 2))).trans (min_le_right 1 (d ^ 2))))
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsqrtd : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsd⟩
  have hcut : R ≤ 1 / (8 * Real.sqrt eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsqrteps)).2
    calc
      R * (8 * Real.sqrt eps) ≤ (R + 1) * (8 * Real.sqrt eps) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (R + 1) * (8 * d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrtd (by norm_num)) hRone.le
      _ = 1 := by
        dsimp only [d]
        field_simp [hRone.ne']
  let tau : Real := eps * B.radius ^ 2
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let q : E → Real := fun Z ↦
    Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z)
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩ {Z | q Z ≤ 1 / (8 * Real.sqrt eps)}
  let C : Set E := U ∩ {Z | 1 / (8 * Real.sqrt eps) < q Z}
  let f : E → ENNReal := fun Z ↦
    ENNReal.ofReal
      (lRedJac S (time : Real) B.center Z tau *
        lSrcDensity S (time : Real) B.center)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hCmeas : MeasurableSet C := by
    apply (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter
    dsimp only [q]
    exact src_norm_superlevel_measurable S (time : Real) B.center
      (1 / (8 * Real.sqrt eps))
  have hunion : A ∪ C = U := by
    ext Z
    simp only [A, C, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (hZ | hZ) <;> exact hZ.1
    · intro hZ
      exact (le_or_gt (q Z) (1 / (8 * Real.sqrt eps))).elim
        (fun h ↦ Or.inl ⟨hZ, h⟩) (fun h ↦ Or.inr ⟨hZ, h⟩)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro Z hZA hZC
    exact (not_lt_of_ge
      (show q Z ≤ 1 / (8 * Real.sqrt eps) from hZA.2))
      (show 1 / (8 * Real.sqrt eps) < q Z from hZC.2)
  have hsmall' : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        (ENNReal.ofReal
            (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
          B.volume) := by
    calc
      (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
          ENNReal.ofReal c *
            riemannianVolumeMeasure (I := I) (M := M)
              (S.base.metric ((time : Real) - tau)) B.set := by
        simpa only [A, U, q, f, tau, c] using
          hsmall eps heps hepsJ' B hBrho hB
      _ ≤ ENNReal.ofReal c *
          (ENNReal.ofReal
              (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
            B.volume) := by
        simpa only [mul_comm] using
          mul_le_mul_right (hmove eps heps hepsV' B hBrho) (ENNReal.ofReal c)
  have htail' : (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤ eta := by
    calc
      (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤
          ∫⁻ Z : E in
            {Z | 1 / (8 * Real.sqrt eps) < q Z},
            ENNReal.ofReal (lSrcGauss S (time : Real) B.center Z)
              ∂(modelHaar (E := E)) := by
        simpa only [C, U, q, f] using
          lRedJac_tail_le S hS (time : Real) B.center tau
            (1 / (8 * Real.sqrt eps)) htau
      _ ≤ ∫⁻ Z : E in {Z | R < q Z},
          ENNReal.ofReal (lSrcGauss S (time : Real) B.center Z)
            ∂(modelHaar (E := E)) := by
        apply MeasureTheory.lintegral_mono_set
        intro Z hZ
        exact lt_of_le_of_lt hcut hZ
      _ ≤ eta := by
        simpa only [q] using htail S (time : Real) B.center
  rw [redVolume_lint S hS (time : Real) B.center tau htau (by
    intro t ht
    apply hreg
    have hrSq : B.radius ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ B.radius_pos.le hrho.le).2 hBrho
    have htauR : tau ≤ rho ^ 2 := by
      dsimp only [tau]
      calc
        eps * B.radius ^ 2 ≤ 1 * B.radius ^ 2 :=
          mul_le_mul_of_nonneg_right heps1 (sq_nonneg B.radius)
        _ ≤ rho ^ 2 := by simpa only [one_mul] using hrSq
    exact ⟨by linarith [ht.1], ht.2⟩)]
  change (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) ≤ _
  calc
    (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) =
        (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) +
          ∫⁻ Z in C, f Z ∂(modelHaar (E := E)) := by
      rw [← hunion]
      exact MeasureTheory.lintegral_union hCmeas hdisj
    _ ≤ ENNReal.ofReal c *
          (ENNReal.ofReal
              (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
            B.volume) +
        eta := add_le_add hsmall' htail'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem redVolume_ball_le [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          let tau := eps * B.radius ^ 2
          let c := Real.exp
            ((Module.finrank Real E : Real) ^ 2 * eps -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
          redVolume S (time : Real) B.center tau ≤
            ENNReal.ofReal c *
                (ENNReal.ofReal
                    (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
                  B.volume) +
              (1 / 4 : ENNReal) := by
  exact redVolume_ball_eta (I := I) S hS time hrho hreg
    (1 / 4 : ENNReal) (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
