import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FixedSetVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Curvature.ScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false
noncomputable section

open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

def reducedSourceGaussianTail (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : EuclideanSpace ℝ (Fin n) in {y | R < ‖y‖},
    ENNReal.ofReal (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ *
      Real.exp (-‖y‖ ^ 2)) ∂volume

theorem reducedSourceGaussianTail_small (n : ℕ) [NeZero n]
    (eta : ℝ≥0∞) (heta : 0 < eta) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ eps₀ < 1 ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ eps₀ →
        reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤ eta := by
  obtain ⟨R, hR, htail⟩ := gaussianPosDef_uniform_tail (n := Fin n) eta heta
  have hstd : reducedSourceGaussianTail n R ≤ eta := by
    have hh := htail (1 : Matrix (Fin n) (Fin n) ℝ) Matrix.PosDef.one
    rw [gaussSPDTail_eq _ Matrix.PosDef.one R] at hh
    simpa only [reducedSourceGaussianTail, Fintype.card_fin] using hh
  let d : ℝ := 1 / (10 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hRone)
  let eps₀ : ℝ := min (1 / 2) (d ^ 2)
  refine ⟨eps₀, lt_min (by norm_num) (sq_pos_of_pos hd), ?_, ?_⟩
  · exact (min_le_left (1 / 2 : ℝ) (d ^ 2)).trans_lt (by norm_num)
  intro eps heps hsmall
  have hsqrt : Real.sqrt eps ≤ d :=
    (Real.sqrt_le_iff).mpr ⟨hd.le, hsmall.trans (min_le_right _ _)⟩
  have hcut : R ≤ 1 / (10 * Real.sqrt eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr heps))).mpr
    calc
      R * (10 * Real.sqrt eps) ≤ (R + 1) * (10 * Real.sqrt eps) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (R + 1) * (10 * d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hRone.le
      _ = 1 := by dsimp only [d]; field_simp [hRone.ne']
  exact (MeasureTheory.lintegral_mono_set
    (fun y hy ↦ lt_of_le_of_lt hcut hy)).trans hstd

section Geometry

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem lSourceGaussian_tail_eq_reducedSourceGaussianTail
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (R : ℝ) :
    (∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E)) =
        reducedSourceGaussianTail (Module.finrank ℝ E) R := by
  rw [lSourceGaussian_tail_eq_spd S T x R]
  simpa only [reducedSourceGaussianTail, Fintype.card_fin] using
    gaussSPDTail_eq (lSourceGram S T x) (lSourceGram_posDef S T x) R

omit [NeZero (Module.finrank ℝ E)] in
private theorem original_min_and_nonconj
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    (Z, tau) ∈ lMinDomain S T x ∧ ¬ IsLConjugate S T x Z tau := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hreg : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith only [ht.1]
    have hclock := lExpPosDom_regularity S T x Z hdom
      ⟨Real.sqrt_nonneg (T - t), Real.sqrt_le_sqrt hback⟩
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]; ring
    simpa only [heq] using hclock
  obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
  exact ⟨lMinDomain_down_of_rm S hS K T x Z hmin htau hlt.le hK,
    lMinVec_nconj_lt_of_rm S hS K T x hmin hlt hK⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem original_ray_redLength_lower_of_fixed_set_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (r : ℝ) (hr : 0 < r) {U : Set M}
    (hRmQual : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (hRm : ∀ t ∈ Icc (T - r ^ 2) T, ∀ y ∈ U,
      r ^ 4 * normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x (eps * r ^ 2))
    (hcontain : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt (eps * r ^ 2)),
      lRegularizedCurve S T x Z s ∈ U) :
    -((Module.finrank ℝ E : ℝ) ^ 2 * eps) ≤
      redLength S T x (lExp S T x Z (eps * r ^ 2)) (eps * r ^ 2) := by
  let tau : ℝ := eps * r ^ 2
  let b : ℝ := Real.sqrt tau
  let n : ℝ := Module.finrank ℝ E
  let K : ℝ := n ^ 2 * Real.sqrt (1 / r ^ 4)
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos hr)
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hbSq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hmin := (original_min_and_nonconj S hS T x hRmQual htau hZ).1
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).mp hmin).1
  have hbdom : b ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).mp hdom).2.2
  have halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (Icc 0 b) :=
    lRegularizedCurve_c1On S hS T x Z hbdom
  have hregRay : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ lRegularizedDomain_regularity S T x Z
      (lRegularizedDomain_segment S T x Z hbdom hs.1 hs.2)
  have hLagInt : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume 0 b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 b hb.le alpha halpha hregRay
  have hLagLower : ∀ s ∈ Icc (0 : ℝ) b,
      -2 * b ^ 2 * K ≤ lRegularizedLagrangian S T alpha s := by
    intro s hs
    have hsSq : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
    have hbRad : b ^ 2 ≤ r ^ 2 := by
      rw [hbSq]; dsimp only [tau]; nlinarith [sq_nonneg r]
    have htime : T - s ^ 2 ∈ Icc (T - r ^ 2) T :=
      ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have hcurv : normSq0S (I := I) (S.base.metric (T - s ^ 2)) (alpha s) 4
        (S.base.rm04 (T - s ^ 2) (alpha s)) ≤ 1 / r ^ 4 := by
      apply (le_div_iff₀ (pow_pos hr 4)).mpr
      simpa only [mul_comm] using hRm (T - s ^ 2) htime (alpha s) (hcontain s hs)
    have hsc0 := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) (alpha s)
    have hsc1 : |S.scalar (T - s ^ 2) (alpha s)| ≤
        n ^ 2 * Real.sqrt (normSq0S (I := I)
          (S.base.metric (T - s ^ 2)) (alpha s) 4
          (S.base.rm04 (T - s ^ 2) (alpha s))) := by
      simpa only [n, SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
        metricRm04_apply,
        show Module.finrank ℝ (TangentSpace I (alpha s)) = Module.finrank ℝ E from rfl]
        using hsc0
    have hsc : -K ≤ S.scalar (T - s ^ 2) (alpha s) := by
      have habs : |S.scalar (T - s ^ 2) (alpha s)| ≤ K :=
        hsc1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcurv) (sq_nonneg n))
      exact (neg_le_neg habs).trans (neg_abs_le _)
    have hkin : 0 ≤ (1 / 2 : ℝ) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) := by
      apply mul_nonneg (by norm_num)
      by_cases hv : lVelocity (I := I) alpha s = 0
      · rw [hv, ((S.base.metric (T - s ^ 2)).inner (alpha s)).map_zero, zero_apply]
      · exact ((S.base.metric (T - s ^ 2)).pos (alpha s)
          (lVelocity (I := I) alpha s) hv).le
    have hscalar : -2 * b ^ 2 * K ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) := by
      have h₁ : -2 * b ^ 2 * K ≤ -2 * s ^ 2 * K := by nlinarith
      have h₂ : -2 * s ^ 2 * K ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) := by
        nlinarith [sq_nonneg s]
      exact h₁.trans h₂
    dsimp only [lRegularizedLagrangian]
    linarith
  have haction : -2 * b ^ 2 * K * b ≤ lRegularizedAction S T alpha 0 b := by
    have hm := intervalIntegral.integral_mono_on hb.le
      (show IntervalIntegrable (fun _ : ℝ ↦ -2 * b ^ 2 * K) volume 0 b from
        intervalIntegrable_const) hLagInt hLagLower
    change -2 * b ^ 2 * K * b ≤ ∫ s in 0..b, lRegularizedLagrangian S T alpha s
    calc
      -2 * b ^ 2 * K * b = b * (-2 * b ^ 2 * K) := by ring
      _ ≤ ∫ s in 0..b, lRegularizedLagrangian S T alpha s := by
        simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hm
  have hcost : lCost S T x (lExp S T x Z tau) tau = lRegularizedAction S T alpha 0 b := by
    have hlen : lLength S T (fun q : ℝ ↦ lExp S T x Z q) 0 tau =
        lRegularizedAction S T alpha 0 b := by
      change lLength S T (squareRootReparametrization alpha) 0 tau = lRegularizedAction S T alpha 0 b
      exact lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha tau htau.le
    exact (((mem_lMinDomain S T x Z tau).mp hmin).2.symm).trans hlen
  have hscale : r ^ 2 * K = n ^ 2 := by
    dsimp only [K]
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
      show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp,
      Real.sqrt_sq (one_div_pos.mpr (sq_pos_of_pos hr)).le]
    field_simp [hr.ne']
  have hbK : b ^ 2 * K = n ^ 2 * eps := by
    rw [hbSq]
    change eps * r ^ 2 * K = n ^ 2 * eps
    calc
      eps * r ^ 2 * K = eps * (r ^ 2 * K) := by ring
      _ = n ^ 2 * eps := by rw [hscale]; ring
  change -(n ^ 2 * eps) ≤ redLength S T x (lExp S T x Z tau) tau
  rw [redLength, hcost]
  apply (le_div_iff₀ (mul_pos (by norm_num) hb)).mpr
  calc
    -(n ^ 2 * eps) * (2 * Real.sqrt tau) = -2 * b ^ 2 * K * b := by
      change -(n ^ 2 * eps) * (2 * b) = -2 * b ^ 2 * K * b
      rw [← hbK]
      ring
    _ ≤ lRegularizedAction S T alpha 0 b := haction

variable [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

theorem redVolume_fixed_terminal_ball_split
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D)
    (hgT : RiemannianMetricComplete (I := I) (S.base.metric (time : ℝ)))
    (B : FlowMetricBall S time)
    (hRmQual : ∀ sigma : ℝ, 0 < sigma → Icc ((time : ℝ) - sigma) (time : ℝ) ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc ((time : ℝ) - sigma) (time : ℝ), ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ y ∈ B.set,
      B.radius ^ 4 * normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1)
    (hcontain : ∀ Z : E,
      Z ∈ lInjDomain S (time : ℝ) B.center (eps * B.radius ^ 2) →
      Real.sqrt ((S.base.metric (time : ℝ)).inner B.center Z Z) ≤
          1 / (10 * Real.sqrt eps) →
      ∀ s ∈ Icc (0 : ℝ) (Real.sqrt (eps * B.radius ^ 2)),
        lRegularizedCurve S (time : ℝ) B.center Z s ∈ B.set) :
    DifferentialGeometry.PDE.RicciFlow.redVolume
        S (time : ℝ) B.center (eps * B.radius ^ 2) ≤
      ENNReal.ofReal (Real.exp
        ((((Module.finrank ℝ E : ℝ) ^ 2 + (Module.finrank ℝ E : ℝ) ^ 3) * eps) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (eps * B.radius ^ 2) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) * B.volume +
        reducedSourceGaussianTail (Module.finrank ℝ E) (1 / (10 * Real.sqrt eps)) := by
  let T : ℝ := time
  let n : ℝ := Module.finrank ℝ E
  let tau : ℝ := eps * B.radius ^ 2
  let R : ℝ := 1 / (10 * Real.sqrt eps)
  let c : ℝ := Real.exp
    (n ^ 2 * eps - (n / 2) * Real.log tau - (n / 2) * Real.log (4 * Real.pi))
  let v : ℝ := Real.exp (n ^ 3 * eps)
  let U : Set E := lInjDomain S T B.center tau
  let A : Set E := U ∩ {Z | Real.sqrt ((S.base.metric T).inner B.center Z Z) ≤ R}
  let C : Set E := U ∩ {Z | R < Real.sqrt ((S.base.metric T).inner B.center Z Z)}
  let f : E → ℝ≥0∞ := fun Z ↦
    ENNReal.ofReal (lReducedJacobian S T B.center Z tau * lSourceDensity S T B.center)
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hshort : Icc (T - tau) T ⊆ D.regular := by
    have hh : tau < B.radius ^ 2 := by
      simpa only [tau, one_mul] using
        mul_lt_mul_of_pos_right heps1 (sq_pos_of_pos B.radius_pos)
    intro t ht
    apply hreg
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨Φ, hsource, _himage, hmap⟩ :=
    exists_lExpPartial_of_rm S hS T hgT B.center hRmQual tau htau
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hΨsource : Ψ.source = U := hsource
  have hΨmap : Set.EqOn Ψ (fun Z : E ↦ lExp S T B.center Z tau) Ψ.source := by
    intro Z hZ
    apply hmap
    change Z ∈ U
    rwa [← hΨsource]
  have hUmeas : MeasurableSet U := by rw [← hΨsource]; exact Ψ.open_source.measurableSet
  have hAmeas : MeasurableSet A := by
    apply hUmeas.inter
    apply measurableSet_le <;> fun_prop
  have hCmeas : MeasurableSet C := by
    apply hUmeas.inter
    apply measurableSet_lt <;> fun_prop
  have hAsource : A ⊆ Ψ.source := by rw [hΨsource]; exact inter_subset_left
  have hImageMeas : MeasurableSet (Ψ '' A) :=
    measurableSet_image_param_global (I := I) Ψ hAmeas hAsource
  have hImageBall : Ψ '' A ⊆ B.set := by
    rintro y ⟨Z, hZA, rfl⟩
    rw [hΨmap (hAsource hZA)]
    change lRegularizedCurve S T B.center Z (Real.sqrt tau) ∈ B.set
    exact hcontain Z hZA.1 hZA.2 (Real.sqrt tau) ⟨Real.sqrt_nonneg _, le_rfl⟩
  have hImageDen : ∀ y ∈ Ψ '' A, ENNReal.ofReal (redDensity S T B.center y tau) ≤
      ENNReal.ofReal c := by
    rintro y ⟨Z, hZA, rfl⟩
    rw [hΨmap (hAsource hZA)]
    apply ENNReal.ofReal_le_ofReal
    have hlen := original_ray_redLength_lower_of_fixed_set_rm
      S hS T B.center B.radius B.radius_pos hRmQual hRm heps heps1.le hZA.1
        (hcontain Z hZA.1 hZA.2)
    change -(n ^ 2 * eps) ≤ redLength S T B.center (lExp S T B.center Z tau) tau at hlen
    dsimp only [redDensity, c]
    apply Real.exp_le_exp.mpr
    linarith
  have hsmallEq : (∫⁻ Z in A, f Z ∂modelHaar (E := E)) =
      ∫⁻ y in Ψ '' A, ENNReal.ofReal (redDensity S T B.center y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) := by
    rw [riemVol_param_lint (I := I) (S.base.metric (T - tau)) Ψ
      (fun y ↦ ENNReal.ofReal (redDensity S T B.center y tau)) hAmeas hAsource]
    refine MeasureTheory.setLIntegral_congr_fun hAmeas ?_
    intro Z hZA
    have hZsrc := hAsource hZA
    obtain ⟨hmin, hnconj⟩ := original_min_and_nonconj S hS T B.center hRmQual htau hZA.1
    have hdom := ((mem_lMinDomain S T B.center Z tau).mp hmin).1
    dsimp only [f]
    rw [paramDensity_eq_lExpDensity_of_eqOn S T B.center tau Ψ hΨmap Z hZsrc,
      hΨmap hZsrc]
    rw [← ENNReal.ofReal_mul (lExpDensity_pos_of_nonconj S T B.center Z tau hdom hnconj).le]
    exact congrArg ENNReal.ofReal
      (lRedJac_mul_src_of_nonconj S T B.center Z tau hdom hnconj)
  have hsmall : (∫⁻ Z in A, f Z ∂modelHaar (E := E)) ≤
      ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) B.set := by
    rw [hsmallEq]
    calc
      _ ≤ ∫⁻ _y in Ψ '' A, ENNReal.ofReal c
          ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) :=
        MeasureTheory.setLIntegral_mono' hImageMeas hImageDen
      _ ≤ ∫⁻ _y in B.set, ENNReal.ofReal c
          ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) :=
        MeasureTheory.lintegral_mono_set hImageBall
      _ = _ := by rw [MeasureTheory.setLIntegral_const]
  have hopen : IsOpen B.set := by
    have hd : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric T) B.center y) := by
      simpa only [riemannianEDistOf] using
        DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
          (S.base.metric T) B.center
    exact isOpen_lt hd continuous_const
  have hmove : riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau)) B.set ≤ ENNReal.ofReal v * B.volume := by
    exact (fixed_set_volume_comparison_of_rm S hS T B.radius hopen.measurableSet
      B.radius_pos hslab hreg hRm heps heps1).2
  have hsmallFinal : (∫⁻ Z in A, f Z ∂modelHaar (E := E)) ≤
      ENNReal.ofReal (Real.exp
        ((n ^ 2 + n ^ 3) * eps - (n / 2) * Real.log tau -
          (n / 2) * Real.log (4 * Real.pi))) * B.volume := by
    calc
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal v * B.volume) :=
        hsmall.trans (mul_le_mul le_rfl hmove (by positivity) (by positivity))
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        have hcv : c * v = Real.exp
            ((n ^ 2 + n ^ 3) * eps - (n / 2) * Real.log tau -
              (n / 2) * Real.log (4 * Real.pi)) := by
          dsimp only [c, v]
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hcv]
  have htail : (∫⁻ Z in C, f Z ∂modelHaar (E := E)) ≤
      reducedSourceGaussianTail (Module.finrank ℝ E) R := by
    calc
      _ ≤ ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner B.center Z Z)},
          ENNReal.ofReal (lSourceGaussian S T B.center Z) ∂modelHaar (E := E) :=
        lRedJac_tail_le_of_rm S hS T B.center hRmQual tau R htau
      _ = _ := lSourceGaussian_tail_eq_reducedSourceGaussianTail S T B.center R
  have hunion : A ∪ C = U := by
    ext Z
    simp only [A, C, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hZ
      exact (le_or_gt (Real.sqrt ((S.base.metric T).inner B.center Z Z)) R).elim
        (fun h ↦ Or.inl ⟨hZ, h⟩) (fun h ↦ Or.inr ⟨hZ, h⟩)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro Z hZA hZC
    have hle : Real.sqrt ((S.base.metric T).inner B.center Z Z) ≤ R := hZA.2
    have hlt : R < Real.sqrt ((S.base.metric T).inner B.center Z Z) := hZC.2
    exact (not_lt_of_ge hle) hlt
  rw [redVolume_lint_of_rm S hS T hgT B.center hRmQual tau htau hshort]
  change (∫⁻ Z in U, f Z ∂modelHaar (E := E)) ≤ _
  calc
    _ = (∫⁻ Z in A, f Z ∂modelHaar (E := E)) +
        ∫⁻ Z in C, f Z ∂modelHaar (E := E) := by
      rw [← hunion]
      exact MeasureTheory.lintegral_union hCmeas hdisj
    _ ≤ _ := add_le_add hsmallFinal htail

end Geometry
end DifferentialGeometry.PDE.RicciFlow

end
