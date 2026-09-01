import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.CompactCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.DomainContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.QuadraticBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FlowUniformEquivalence
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lGrad_scale [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ rho : Real} (hreg : Icc t₀ t₁ ⊆ D.regular)
    (hrho : 0 < rho) :
    ∃ A : Real, 0 ≤ A ∧ ∀ r : Real, 0 < r → r ≤ rho →
      ∀ t ∈ Icc t₀ t₁, ∀ x (v : TangentSpace I x),
        |(S.base.metric t).inner x
            (gradientFun (I := I) (S.base.metric t) (S.scalar t) x) v| ≤
          (A / r ^ 3) * Real.sqrt ((S.base.metric t).inner x v v) := by
  obtain ⟨C, hC, hgrad⟩ := lGrad_bound (I := I) S hS hreg
  refine ⟨C * rho ^ 3, mul_nonneg hC (by positivity), ?_⟩
  intro r hr hrle t ht x v
  have hrpow : r ^ 3 ≤ rho ^ 3 :=
    pow_le_pow_left₀ hr.le hrle 3
  have hscale : C ≤ C * rho ^ 3 / r ^ 3 := by
    rw [le_div_iff₀ (pow_pos hr 3)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrpow hC
  exact (hgrad t ht x v).trans
    (mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg _))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lRegRicci_le
    (S : SolutionOn (I := I) (M := M) D)
    (time : RealTimeInterval.FlowTime D) (B : FlowMetricBall S time)
    (hB : B.IsRmControlled) {alpha : Real → M} {s : Real}
    (htime : (time : Real) - s ^ 2 ∈
      Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hpoint : alpha s ∈ B.setAt ((time : Real) - s ^ 2)) :
    |S.ricciAt ((time : Real) - s ^ 2) (alpha s)
        (vec2 (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s))| ≤
      (Module.finrank Real E : Real) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) *
          lRegSpeedSq S (time : Real) alpha s := by
  have hcurv : FlowMetricBall.rmNormSq S ((time : Real) - s ^ 2) (alpha s) ≤
      1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using
      hB.2 ((time : Real) - s ^ 2) htime (alpha s) hpoint
  have hquad := ricci_quadratic_form_bound_of_solution_curvature_bound
    (I := I) S (alpha s)
    (lVelocity (I := I) alpha s) hcurv
  rw [← metricRicciAt_apply_eq_ricciTensor] at hquad
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt, lRegSpeedSq] using hquad

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lRegSpeed_ball [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) (B : FlowMetricBall S time)
    (hB : B.IsRmControlled) {rho t₀ t₁ : Real}
    (hrho : 0 < rho) (hBrho : B.radius ≤ rho)
    (hreg : Icc t₀ t₁ ⊆ D.regular)
    {alpha : Real → M} {J : Set Real}
    {Z : TangentSpace I B.center}
    (halpha : IsLRegCurveOn S (time : Real) alpha J B.center Z)
    (a b R : Real) (hR : 0 ≤ R) (hJ : uIcc a b ⊆ J)
    (hsR : ∀ s ∈ uIcc a b, |s| ≤ R)
    (htime : ∀ s ∈ uIcc a b,
      (time : Real) - s ^ 2 ∈ Icc t₀ t₁ ∩
        Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hpoint : ∀ s ∈ uIcc a b,
      alpha s ∈ B.setAt ((time : Real) - s ^ 2)) :
    ∃ C : Real, 0 ≤ C ∧
      lRegSpeedSq S (time : Real) alpha b ≤
        Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * |b - a|) *
          (lRegSpeedSq S (time : Real) alpha a +
            (1 + 2 * C * R ^ 2) /
              (1 + 2 * C * R ^ 2 + 4 * C * R)) := by
  obtain ⟨A, hA, hgradA⟩ := lGrad_scale (I := I) S hS hreg hrho
  let Cgrad : Real := A / B.radius ^ 3
  let Cric : Real := (Module.finrank Real E : Real) ^ 2 *
    Real.sqrt (1 / B.radius ^ 4)
  let C : Real := max Cgrad Cric
  have hCgrad : 0 ≤ Cgrad := by
    exact div_nonneg hA (pow_nonneg B.radius_pos.le 3)
  have hCric : 0 ≤ Cric := by
    exact mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := le_max_of_le_left hCgrad
  refine ⟨C, hC, ?_⟩
  apply lRegSpeedSq_le_of_gradient_ricci_bounds (I := I) S hS (time : Real) halpha
    a b C R hC hR hJ hsR
  · intro s hs
    have hgrad := hgradA B.radius B.radius_pos hBrho
      ((time : Real) - s ^ 2) (htime s hs).1 (alpha s)
      (lVelocity (I := I) alpha s)
    exact hgrad.trans (mul_le_mul_of_nonneg_right
      (le_max_left Cgrad Cric) (Real.sqrt_nonneg _))
  · intro s hs
    have hric := lRegRicci_le (I := I) S time B hB
      (htime s hs).2 (hpoint s hs)
    exact hric.trans (mul_le_mul_of_nonneg_right
      (le_max_right Cgrad Cric)
      (lRegSpeedSq_nonneg (I := I) S (time : Real) alpha s))

private theorem speedDeriv_two
    {s R G K U P Q : Real} (hs : |s| ≤ R) (hR : 0 ≤ R)
    (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hP : |P| ≤ G * Real.sqrt U) (hQ : |Q| ≤ K * U) :
    |4 * s ^ 2 * P - 4 * s * Q| ≤
      (1 + 2 * G * R ^ 2 + 4 * K * R) * U +
        (1 + 2 * G * R ^ 2) := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hsSq : s ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hs0 hR).2 hs
  have hsqrt : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsqrtSq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hU
  have hsqrtYoung : 2 * Real.sqrt U ≤ U + 1 := by
    nlinarith [sq_nonneg (Real.sqrt U - 1)]
  calc
    |4 * s ^ 2 * P - 4 * s * Q| ≤
        |4 * s ^ 2 * P| + |4 * s * Q| := abs_sub _ _
    _ = 4 * s ^ 2 * |P| + 4 * |s| * |Q| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg s)]
      norm_num
    _ ≤ 4 * R ^ 2 * (G * Real.sqrt U) + 4 * R * (K * U) := by
      gcongr
    _ ≤ (1 + 2 * G * R ^ 2 + 4 * K * R) * U +
        (1 + 2 * G * R ^ 2) := by
      nlinarith [mul_nonneg hG (sq_nonneg R)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lRegSpeed_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x} (halpha : IsLRegCurveOn S T alpha J x Z)
    (a b G K R : Real) (hG : 0 ≤ G) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hJ : Set.uIcc a b ⊆ J)
    (hsR : ∀ s ∈ Set.uIcc a b, |s| ≤ R)
    (hgrad : ∀ s ∈ Set.uIcc a b,
      |(S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s)| ≤
        G * Real.sqrt (lRegSpeedSq S T alpha s))
    (hric : ∀ s ∈ Set.uIcc a b,
      |S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))| ≤
        K * lRegSpeedSq S T alpha s) :
    lRegSpeedSq S T alpha b ≤
      Real.exp ((1 + 2 * G * R ^ 2 + 4 * K * R) * |b - a|) *
        (lRegSpeedSq S T alpha a +
          (1 + 2 * G * R ^ 2) /
            (1 + 2 * G * R ^ 2 + 4 * K * R)) := by
  let U : Real → Real := lRegSpeedSq S T alpha
  let U' : Real → Real := fun s ↦
    4 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s) -
      4 * s * S.ricciAt (T - s ^ 2) (alpha s)
        (vec2 (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s))
  have hk : 0 < 1 + 2 * G * R ^ 2 + 4 * K * R := by
    nlinarith [mul_nonneg hG (sq_nonneg R), mul_nonneg hK hR]
  have hd : 0 < 1 + 2 * G * R ^ 2 := by
    nlinarith [mul_nonneg hG (sq_nonneg R)]
  apply DifferentialGeometry.HCGCompactness.affineGronwall_of_abs_deriv_le
    U U' hk hd
  · intro s hs
    exact lRegSpeedSq_nonneg (I := I) S T alpha s
  · intro s hs
    simpa only [U, U'] using
      hasDerivAt_lRegSpeedSq (I := I) S hS T halpha (hJ hs)
  · intro s hs
    apply speedDeriv_two (hsR s hs) hR hG
      (lRegSpeedSq_nonneg (I := I) S T alpha s)
      (hgrad s hs) (hric s hs)

private theorem scale_ric_eq (n : Nat) {r : Real} (hr : 0 < r) :
    r ^ 2 * ((n : Real) ^ 2 * Real.sqrt (1 / r ^ 4)) = (n : Real) ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
  rw [show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
  field_simp

private theorem div_one_sub_le {x : Real} (hx : x ≤ 1 / 4) :
    1 / (1 - x) ≤ 4 / 3 := by
  apply (div_le_iff₀ (by linarith [hx])).2
  nlinarith [hx]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lRegSpeed_fixed
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D') (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D'.regular)
    (A : Real) (hA : 0 ≤ A)
    (hgrad : ∀ r : Real, 0 < r → r ≤ rho →
      ∀ t ∈ Icc ((time : Real) - rho ^ 2) (time : Real),
        ∀ x : N, ∀ v : TangentSpace J x,
          |(S.base.metric t).inner x
              (gradientFun (I := J) (S.base.metric t) (S.scalar t) x) v| ≤
            (A / r ^ 3) * Real.sqrt ((S.base.metric t).inner x v v))
    {eps : Real} (heps : 0 < eps) (heps32 : eps ≤ 1 / 32)
    (hsqrtC : Real.sqrt eps *
      (rho + 2 * A + 4 * (Module.finrank Real F : Real) ^ 2 + 1) ≤ 1 / 4)
    (B : FlowMetricBall S time) (hBrho : B.radius ≤ rho)
    (hB : B.IsRmControlled) (Z : TangentSpace J B.center)
    (hZ : Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
      1 / (8 * Real.sqrt eps)) {s : Real}
    (hs : s ∈ Icc (0 : Real) (Real.sqrt eps * B.radius))
    (hpoint : ∀ q ∈ Icc (0 : Real) s,
      lRegCurve S (time : Real) B.center Z q ∈
        B.setAt ((time : Real) - q ^ 2)) :
    lRegSpeedSq S (time : Real)
      (lRegCurve S (time : Real) B.center Z) s ≤ 1 / (8 * eps) := by
  let n : Real := Module.finrank Real F
  let C : Real := rho + 2 * A + 4 * n ^ 2 + 1
  let b : Real := Real.sqrt eps * B.radius
  have heps1 : eps ≤ 1 := by linarith
  have hsqrtC' : Real.sqrt eps * C ≤ 1 / 4 := by
    simpa only [C, n] using hsqrtC
  have heps_le_sqrt : eps ≤ Real.sqrt eps := by
    nlinarith [Real.sq_sqrt heps.le, Real.sqrt_nonneg eps]
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbRho : b ≤ rho := by
    have hsqrt1 : Real.sqrt eps ≤ 1 := by
      nlinarith [Real.sq_sqrt heps.le, Real.sqrt_nonneg eps]
    dsimp only [b]
    calc
      Real.sqrt eps * B.radius ≤ 1 * B.radius :=
        mul_le_mul_of_nonneg_right hsqrt1 B.radius_pos.le
      _ ≤ rho := by simpa only [one_mul] using hBrho
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hslab : Icc ((time : Real) - b ^ 2) (time : Real) ⊆ D'.regular := by
    intro t ht
    apply hreg
    constructor
    · have hbSqLe : b ^ 2 ≤ rho ^ 2 :=
        (sq_le_sq₀ hbpos.le hrho.le).2 hbRho
      linarith [ht.1]
    · exact ht.2
  have hbdom : b ∈ lRegDomain S (time : Real) B.center Z :=
    mem_lRegDomain_of_time_slab S hS (time : Real) B.center Z b hbpos.le hslab
  have halpha : IsLRegCurveOn S (time : Real)
      (lRegCurve S (time : Real) B.center Z) (Icc (0 : Real) b)
      B.center Z := by
    simpa only [Set.uIcc_of_le hbpos.le] using
      lRegCurve_isLRegCurveOn (I := J) S hS (time : Real) B.center Z hbpos hbdom
  let a : Real := A / B.radius ^ 3
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have ha : 0 ≤ a := div_nonneg hA (pow_nonneg B.radius_pos.le 3)
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hsle : s ≤ b := hs.2
  have hsub : Set.uIcc (0 : Real) s ⊆ Icc (0 : Real) b := by
    intro q hq
    have hq' : q ∈ Icc (0 : Real) s := by
      simpa only [Set.uIcc_of_le hs.1] using hq
    exact ⟨hq'.1, hq'.2.trans hsle⟩
  have htime : ∀ q ∈ Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈
        Icc ((time : Real) - rho ^ 2) (time : Real) ∩
          Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro q hq
    have hqb : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    have hbeps : b ^ 2 ≤ B.radius ^ 2 := by
      rw [hbSq]
      nlinarith [sq_nonneg B.radius]
    have hbrho : b ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ hbpos.le hrho.le).2 hbRho
    exact ⟨⟨by linarith, by nlinarith [sq_nonneg q]⟩,
      ⟨by linarith, by nlinarith [sq_nonneg q]⟩⟩
  have hgr := lRegSpeed_two (I := J) S hS (time : Real) halpha
    0 s a K b ha hK hbpos.le (fun _ hq ↦ hsub hq)
    (fun q hq ↦ by
      have hqI := hsub hq
      rw [abs_of_nonneg hqI.1]
      exact hqI.2)
    (fun q hq ↦ by
      have hqI := hsub hq
      simpa only [a, lRegSpeedSq] using hgrad B.radius B.radius_pos hBrho
        ((time : Real) - q ^ 2) (htime q hqI).1
        (lRegCurve S (time : Real) B.center Z q)
        (lVelocity (I := J) (lRegCurve S (time : Real) B.center Z) q))
    (fun q hq ↦ by
      have hqS : q ∈ Icc (0 : Real) s := by
        simpa only [Set.uIcc_of_le hs.1] using hq
      have hqI := hsub hq
      simpa only [K, n] using lRegRicci_le (I := J) S time B hB
        (htime q hqI).2 (hpoint q hqS))
  have hU0 : lRegSpeedSq S (time : Real)
      (lRegCurve S (time : Real) B.center Z) 0 =
        4 * (S.base.metric (time : Real)).inner B.center Z Z := by
    dsimp only [lRegSpeedSq]
    norm_num only [zero_pow, sub_zero]
    rw [lRegCurve_zero, lRegCurve_vel_zero S hS (time : Real) B.center Z
      (hreg ⟨by nlinarith [sq_nonneg rho], le_rfl⟩)]
    calc
      (S.base.metric (time : Real)).inner B.center ((2 : Real) • Z)
          ((2 : Real) • Z) =
        (2 : Real) * 2 *
          (S.base.metric (time : Real)).inner B.center Z Z :=
            metric_smul2 (I := J) (S.base.metric (time : Real)) (2 : Real) Z
      _ = 4 * (S.base.metric (time : Real)).inner B.center Z Z := by ring
  have hZsq : (S.base.metric (time : Real)).inner B.center Z Z ≤
      (1 / (8 * Real.sqrt eps)) ^ 2 := by
    have hq0 : 0 ≤ (S.base.metric (time : Real)).inner B.center Z Z := by
      by_cases hzero : Z = 0
      · subst Z
        rw [((S.base.metric (time : Real)).inner B.center).map_zero,
          zero_apply]
      · exact ((S.base.metric (time : Real)).pos B.center Z hzero).le
    rw [← Real.sq_sqrt hq0]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hZ
  have hU0le : lRegSpeedSq S (time : Real)
      (lRegCurve S (time : Real) B.center Z) 0 ≤ 1 / (16 * eps) := by
    rw [hU0]
    calc
      4 * (S.base.metric (time : Real)).inner B.center Z Z ≤
          4 * (1 / (8 * Real.sqrt eps)) ^ 2 :=
        mul_le_mul_of_nonneg_left hZsq (by norm_num)
      _ = 1 / (16 * eps) := by
        rw [div_pow, mul_pow, Real.sq_sqrt heps.le]
        field_simp [heps.ne']
        ring
  have hscaleK : B.radius ^ 2 * K = n ^ 2 := by
    simpa only [K, n] using scale_ric_eq (Module.finrank Real F) B.radius_pos
  have hb3a : a * b ^ 2 * b = A * eps * Real.sqrt eps := by
    dsimp only [a, b]
    rw [mul_pow, Real.sq_sqrt heps.le]
    field_simp [B.radius_pos.ne']
  have hb2K : K * b * b = n ^ 2 * eps := by
    calc
      K * b * b = B.radius ^ 2 * K * (Real.sqrt eps) ^ 2 := by
        dsimp only [b]
        ring
      _ = B.radius ^ 2 * K * eps := by rw [Real.sq_sqrt heps.le]
      _ = n ^ 2 * eps := by rw [hscaleK]
  let k : Real := 1 + 2 * a * b ^ 2 + 4 * K * b
  let d₁ : Real := 1 + 2 * a * b ^ 2
  have hk : 0 < k := by
    dsimp only [k]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (mul_nonneg (by norm_num) ha) (sq_nonneg b)))
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hd₁ : 0 < d₁ := by
    dsimp only [d₁]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (by norm_num) ha) (sq_nonneg b))
  have hratio : d₁ / k ≤ 1 := by
    rw [div_le_one hk]
    dsimp only [d₁, k]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hsabs : |s - 0| ≤ b := by
    rw [sub_zero, abs_of_nonneg hs.1]
    exact hs.2
  have hepssqrt : eps * Real.sqrt eps ≤ Real.sqrt eps :=
    mul_le_of_le_one_left (Real.sqrt_nonneg eps) heps1
  have hexpArg : k * |s - 0| ≤ 1 / 4 := by
    have hkb : k * |s - 0| ≤ k * b :=
      mul_le_mul_of_nonneg_left hsabs hk.le
    have hcore : k * b = b + 2 * (a * b ^ 2 * b) + 4 * (K * b * b) := by
      dsimp only [k]
      ring
    calc
      k * |s - 0| ≤ k * b := hkb
      _ = b + 2 * (a * b ^ 2 * b) + 4 * (K * b * b) := hcore
      _ = Real.sqrt eps * B.radius +
          2 * (A * eps * Real.sqrt eps) + 4 * (n ^ 2 * eps) := by
        rw [hb3a, hb2K]
      _ ≤ Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by
        have h₁ : Real.sqrt eps * B.radius ≤ Real.sqrt eps * rho :=
          mul_le_mul_of_nonneg_left hBrho (Real.sqrt_nonneg eps)
        have h₂ : A * eps * Real.sqrt eps ≤ A * Real.sqrt eps := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hepssqrt hA
        have h₃ : n ^ 2 * eps ≤ n ^ 2 * Real.sqrt eps :=
          mul_le_mul_of_nonneg_left heps_le_sqrt (sq_nonneg n)
        calc
          Real.sqrt eps * B.radius + 2 * (A * eps * Real.sqrt eps) +
                4 * (n ^ 2 * eps) ≤
              Real.sqrt eps * rho + 2 * (A * Real.sqrt eps) +
                4 * (n ^ 2 * Real.sqrt eps) :=
            add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
              (mul_le_mul_of_nonneg_left h₃ (by norm_num))
          _ = Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by ring
      _ ≤ Real.sqrt eps * C := by
        dsimp only [C]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
          (Real.sqrt_nonneg eps)
      _ ≤ 1 / 4 := hsqrtC'
  have hexp : Real.exp (k * |s - 0|) ≤ 4 / 3 := by
    have harg0 : 0 ≤ k * |s - 0| :=
      mul_nonneg hk.le (abs_nonneg _)
    calc
      Real.exp (k * |s - 0|) ≤ 1 / (1 - k * |s - 0|) :=
        Real.exp_bound_div_one_sub_of_interval harg0 (by linarith [hexpArg])
      _ ≤ 4 / 3 := div_one_sub_le hexpArg
  have hterm : 0 ≤ lRegSpeedSq S (time : Real)
        (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k :=
    add_nonneg (lRegSpeedSq_nonneg (I := J) S (time : Real)
      (lRegCurve S (time : Real) B.center Z) 0) (div_nonneg hd₁.le hk.le)
  calc
    lRegSpeedSq S (time : Real)
        (lRegCurve S (time : Real) B.center Z) s ≤
      Real.exp (k * |s - 0|) *
        (lRegSpeedSq S (time : Real)
          (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k) := by
        simpa only [k, d₁] using hgr
    _ ≤ (4 / 3 : Real) *
        (lRegSpeedSq S (time : Real)
          (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k) :=
      mul_le_mul_of_nonneg_right hexp hterm
    _ ≤ (4 / 3 : Real) * (1 / (16 * eps) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add hU0le hratio
    _ ≤ 1 / (8 * eps) := by
      field_simp [heps.ne']
      nlinarith [heps32]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegSpeed_scale
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
              let b := Real.sqrt eps * B.radius
              ∀ s ∈ Icc (0 : Real) b,
                (∀ q ∈ Icc (0 : Real) s,
                  lRegCurve S (time : Real) B.center Z q ∈
                    B.setAt ((time : Real) - q ^ 2)) →
                lRegSpeedSq S (time : Real)
                  (lRegCurve S (time : Real) B.center Z) s ≤ 1 / (8 * eps) := by
  obtain ⟨A, hA, hgrad⟩ := lGrad_scale (I := J) S hS hreg hrho
  let n : Real := Module.finrank Real F
  let C : Real := rho + 2 * A + 4 * n ^ 2 + 1
  have hC : 0 < C := by
    dsimp only [C, n]
    nlinarith [hrho, hA, sq_nonneg (Module.finrank Real F : Real)]
  let d : Real := 1 / (4 * C)
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hC)
  let eps₀ : Real := min (1 / 32 : Real) (d ^ 2)
  have heps₀ : 0 < eps₀ := lt_min (by norm_num) (sq_pos_of_pos hd)
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ
  dsimp only
  intro s hs hpoint
  have heps32 : eps ≤ 1 / 32 :=
    heps₀.trans (min_le_left (1 / 32 : Real) (d ^ 2))
  have hepsd : eps ≤ d ^ 2 :=
    heps₀.trans (min_le_right (1 / 32 : Real) (d ^ 2))
  have hsqrteps_le : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsd⟩
  have hsqrtC : Real.sqrt eps * C ≤ 1 / 4 := by
    calc
      Real.sqrt eps * C ≤ d * C :=
        mul_le_mul_of_nonneg_right hsqrteps_le hC.le
      _ = 1 / 4 := by
        dsimp only [d]
        field_simp [hC.ne']
  exact lRegSpeed_fixed S hS time hrho hreg A hA hgrad heps heps32
    (by simpa only [C, n] using hsqrtC) B hBrho hB Z hZ hs hpoint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [InnerProductSpace Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem c1_ref_int
    (g : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (a b : Real) :
    IntegrableOn (fun s ↦ g.inner (alpha s) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s)) (Icc a b) := by
  have hv : ContMDiff (modelWithCornersSelf Real Real)
      (I.prod (modelWithCornersSelf Real E)) 0
      (fun s ↦ TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s)) := by
    have ht := halpha.contMDiff_tangentMap (m := 0) (by norm_num)
    have hone : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real).tangent 0
        (fun s : Real ↦
          (TotalSpace.mk' Real s (1 : Real) :
            TangentBundle (modelWithCornersSelf Real Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    exact (ht.comp hone).congr fun _ ↦ rfl
  let cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) := g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have hq : Continuous (fun s ↦
      g.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) := by
    have hinner := Continuous.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _))
      (b := alpha) (v := fun s ↦ lVelocity (I := I) alpha s)
      (w := fun s ↦ lVelocity (I := I) alpha s) hv.continuous hv.continuous
    exact hinner.congr fun _ ↦ rfl
  exact hq.continuousOn.integrableOn_compact isCompact_Icc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRegTerm_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    IntegrableOn (fun s ↦
      (S.base.metric T).inner (lRegCurve S T x Z s)
        (lVelocity (I := I) (lRegCurve S T x Z) s)
        (lVelocity (I := I) (lRegCurve S T x Z) s)) (Icc 0 b) := by
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lRegDomain_smoothClamp S T x Z hb0 hb
  let z : E := Z
  let gamma : Real → M := fun s ↦ lRegCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have hgammaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      ((fun q : E × Real ↦ lRegCurve S T x q.1 q.2) ∘
        fun s : Real ↦ (z, rho s)) Set.univ
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma :=
    hgammaInf.of_le (by norm_num)
  have hg := c1_ref_int (I := I) (S.base.metric T) gamma hgamma 0 b
  apply hg.congr_fun_ae
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have heq : gamma =ᶠ[nhds s] lRegCurve S T x Z := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with q hq
    exact congrArg (lRegCurve S T x Z)
      (hrho_id ⟨hq.1.le, hq.2.le⟩)
  have hvel := Filter.EventuallyEq.mfderiv_eq
    (I := modelWithCornersSelf Real Real) (I' := I) heq
  simp only [gamma, lVelocity]
  rw [hvel, hrho_id ⟨hs.1.le, hs.2.le⟩]
  simp only [id_eq]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lMetric_slab [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ T : Real} (hreg : Icc t₀ t₁ ⊆ D.regular)
    (hT : T ∈ Icc t₀ t₁) :
    ∃ Q : Real, 1 ≤ Q ∧ ∀ t ∈ Icc t₀ t₁, ∀ x (v : TangentSpace I x),
      (S.base.metric T).inner x v v ≤
          Q * (S.base.metric t).inner x v v ∧
        (S.base.metric t).inner x v v ≤
          Q * (S.base.metric T).inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨A, hA, hRic⟩ := lRicci_bound (I := I) S hS hreg
  have hequiv := metric_uniform_equivalent_on_window_of_solutions (I := I)
    (fun _ : Nat ↦ S) (fun _ ↦ hS) Set.univ t₀ t₁ T 1 A
    (S.base.metric T) hreg hT (by norm_num) hA
    (fun _ ↦ by
      refine ⟨by norm_num, ?_⟩
      intro x _hx v
      simp)
    (fun _ t ht x _hx v ↦ hRic t ht x v)
  let Q : Real := Real.exp (2 * A * (t₁ - t₀))
  have htlen : 0 ≤ t₁ - t₀ := by linarith [hT.1, hT.2]
  have hQ : 1 ≤ Q := by
    rw [show (1 : Real) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (mul_nonneg
      (mul_nonneg (by norm_num) hA) htlen)
  refine ⟨Q, hQ, ?_⟩
  intro t ht x v
  let F : Real := metricEquivalenceFactor 1 A t T
  have hF : F = Real.exp (2 * A * |t - T|) := by
    simp only [F, metricEquivalenceFactor, one_mul]
  have hFpos : 0 < F := by rw [hF]; exact Real.exp_pos _
  have habs : |t - T| ≤ t₁ - t₀ := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hT.1, hT.2]
  have hFQ : F ≤ Q := by
    rw [hF]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left habs (mul_nonneg (by norm_num) hA))
  have hpair := (hequiv 0 t ht).2 x (Set.mem_univ x) v
  have hTnn : 0 ≤ (S.base.metric T).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric T).pos x v hv).le
  have htnn : 0 ≤ (S.base.metric t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric t).pos x v hv).le
  constructor
  · calc
      (S.base.metric T).inner x v v =
          F * (F⁻¹ * (S.base.metric T).inner x v v) := by
        field_simp [hFpos.ne']
      _ ≤ F * (S.base.metric t).inner x v v :=
        mul_le_mul_of_nonneg_left hpair.1 hFpos.le
      _ ≤ Q * (S.base.metric t).inner x v v :=
        mul_le_mul_of_nonneg_right hFQ htnn
  · exact hpair.2.trans
      (mul_le_mul_of_nonneg_right hFQ hTnn)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lMetric_scale [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc (T - rho ^ 2) T ⊆ D.regular) :
    ∃ A : Real, 0 ≤ A ∧ ∀ eps : Real, 0 ≤ eps → eps ≤ 1 →
      ∀ r : Real, 0 < r → r ≤ rho →
        ∀ t ∈ Icc (T - eps * r ^ 2) T, ∀ x (v : TangentSpace I x),
          (S.base.metric T).inner x v v ≤
              Real.exp (2 * A * eps * r ^ 2) *
                (S.base.metric t).inner x v v ∧
            (S.base.metric t).inner x v v ≤
              Real.exp (2 * A * eps * r ^ 2) *
                (S.base.metric T).inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨A, hA, hRic⟩ := lRicci_bound (I := I) S hS hreg
  have hT : T ∈ Icc (T - rho ^ 2) T :=
    ⟨sub_le_self T (sq_nonneg rho), le_rfl⟩
  have hequiv := metric_uniform_equivalent_on_window_of_solutions (I := I)
    (fun _ : Nat ↦ S) (fun _ ↦ hS) Set.univ (T - rho ^ 2) T T 1 A
    (S.base.metric T) hreg hT (by norm_num) hA
    (fun _ ↦ by
      refine ⟨by norm_num, ?_⟩
      intro x _hx v
      simp)
    (fun _ t ht x _hx v ↦ hRic t ht x v)
  refine ⟨A, hA, ?_⟩
  intro eps heps heps1 r hr hrho' t ht x v
  have hr2 : r ^ 2 ≤ rho ^ 2 :=
    (sq_le_sq₀ hr.le hrho.le).2 hrho'
  have hepsr : eps * r ^ 2 ≤ rho ^ 2 := by
    calc
      eps * r ^ 2 ≤ 1 * r ^ 2 :=
        mul_le_mul_of_nonneg_right heps1 (sq_nonneg r)
      _ ≤ rho ^ 2 := by simpa only [one_mul] using hr2
  have htBig : t ∈ Icc (T - rho ^ 2) T :=
    ⟨by linarith [ht.1], ht.2⟩
  let F : Real := metricEquivalenceFactor 1 A t T
  let Q : Real := Real.exp (2 * A * eps * r ^ 2)
  have hF : F = Real.exp (2 * A * |t - T|) := by
    simp only [F, metricEquivalenceFactor, one_mul]
  have hFpos : 0 < F := by rw [hF]; exact Real.exp_pos _
  have habs : |t - T| ≤ eps * r ^ 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  have hFQ : F ≤ Q := by
    rw [hF]
    have hcoef : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
    have he : 2 * A * |t - T| ≤ 2 * A * (eps * r ^ 2) := by
      nlinarith
    exact Real.exp_le_exp.mpr (by nlinarith [he])
  have hpair := (hequiv 0 t htBig).2 x (Set.mem_univ x) v
  have hTnn : 0 ≤ (S.base.metric T).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric T).pos x v hv).le
  have htnn : 0 ≤ (S.base.metric t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric t).pos x v hv).le
  constructor
  · calc
      (S.base.metric T).inner x v v =
          F * (F⁻¹ * (S.base.metric T).inner x v v) := by
        field_simp [hFpos.ne']
      _ ≤ F * (S.base.metric t).inner x v v :=
        mul_le_mul_of_nonneg_left hpair.1 hFpos.le
      _ ≤ Q * (S.base.metric t).inner x v v :=
        mul_le_mul_of_nonneg_right hFQ htnn
  · exact hpair.2.trans
      (mul_le_mul_of_nonneg_right hFQ hTnn)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_edist_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau C : Real)
    (hdom : Real.sqrt tau ∈ lRegDomain S T x Z)
    (hE : IntegrableOn (fun s ↦
      (S.base.metric T).inner (lRegCurve S T x Z s)
        (lVelocity (I := I) (lRegCurve S T x Z) s)
        (lVelocity (I := I) (lRegCurve S T x Z) s))
      (Icc 0 (Real.sqrt tau)))
    (hEC : curveEnergy (I := I) (S.base.metric T)
      (lRegCurve S T x Z) 0 (Real.sqrt tau) ≤ C) :
    riemannianEDistOf (I := I) (S.base.metric T) x
        (lExp S T x Z tau) ≤
      ENNReal.ofReal (Real.sqrt (Real.sqrt tau) * Real.sqrt C) := by
  have hsqrt : (0 : Real) ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hE' : IntegrableOn (fun s ↦
      (S.base.metric T).inner (lRegCurve S T x Z s)
        (mfderiv (modelWithCornersSelf Real Real) I
          (lRegCurve S T x Z) s (1 : Real))
        (mfderiv (modelWithCornersSelf Real Real) I
          (lRegCurve S T x Z) s (1 : Real)))
      (Icc 0 (Real.sqrt tau)) := by
    simpa only [lVelocity] using hE
  have hdist := edistOf_le_budget (I := I) (S.base.metric T) hsqrt
    (lRegCurve_c1On S hS T x Z hdom) hE' hEC
  simpa only [lRegCurve_zero, lExp, sub_zero] using hdist

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_mem_ball
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) (B : FlowMetricBall S time)
    (Z : TangentSpace I B.center) (tau C : Real)
    (hdom : Real.sqrt tau ∈ lRegDomain S (time : Real) B.center Z)
    (hE : IntegrableOn (fun s ↦
      (S.base.metric (time : Real)).inner
        (lRegCurve S (time : Real) B.center Z s)
        (lVelocity (I := I) (lRegCurve S (time : Real) B.center Z) s)
        (lVelocity (I := I) (lRegCurve S (time : Real) B.center Z) s))
      (Icc 0 (Real.sqrt tau)))
    (hEC : curveEnergy (I := I) (S.base.metric (time : Real))
      (lRegCurve S (time : Real) B.center Z) 0 (Real.sqrt tau) ≤ C)
    (hreach : Real.sqrt (Real.sqrt tau) * Real.sqrt C < B.radius) :
    lExp S (time : Real) B.center Z tau ∈ B.set := by
  have hdist := lExp_edist_le (I := I) S hS (time : Real) B.center Z tau C
    hdom hE hEC
  exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 hreach)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegRange_scale
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
              let b := Real.sqrt eps * B.radius
              ∀ s ∈ Icc (0 : Real) b,
                riemannianEDistOf (I := J) (S.base.metric (time : Real))
                    B.center (lRegCurve S (time : Real) B.center Z s) ≤
                    ENNReal.ofReal (B.radius / 2) ∧
                  lRegCurve S (time : Real) B.center Z s ∈
                    B.setAt ((time : Real) - s ^ 2) := by
  obtain ⟨epsS, hepsS, hspeed⟩ :=
    lRegSpeed_scale (J := J) S hS time hrho hreg
  obtain ⟨A, hA, hmetric⟩ :=
    lMetric_scale (I := J) S hS (time : Real) hrho hreg
  let epsM : Real := 1 / (8 * (A * rho ^ 2 + 1))
  have hden : 0 < A * rho ^ 2 + 1 := by
    nlinarith [mul_nonneg hA (sq_nonneg rho)]
  have hepsM : 0 < epsM :=
    one_div_pos.mpr (mul_pos (by norm_num) hden)
  let eps₀ : Real := min epsS (min 1 epsM)
  have heps₀ : 0 < eps₀ := lt_min hepsS (lt_min zero_lt_one hepsM)
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ
  dsimp only
  have hepsS' : eps ≤ epsS := heps₀.trans (min_le_left epsS (min 1 epsM))
  have hepsOne : eps ≤ 1 :=
    heps₀.trans ((min_le_right epsS (min 1 epsM)).trans (min_le_left 1 epsM))
  have hepsM' : eps ≤ epsM :=
    heps₀.trans ((min_le_right epsS (min 1 epsM)).trans (min_le_right 1 epsM))
  have hrSq : B.radius ^ 2 ≤ rho ^ 2 :=
    (sq_le_sq₀ B.radius_pos.le hrho.le).2 hBrho
  let b : Real := Real.sqrt eps * B.radius
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hepsr : eps * B.radius ^ 2 ≤ rho ^ 2 := by
    calc
      eps * B.radius ^ 2 ≤ 1 * B.radius ^ 2 :=
        mul_le_mul_of_nonneg_right hepsOne (sq_nonneg B.radius)
      _ ≤ rho ^ 2 := by simpa only [one_mul] using hrSq
  have hslab : Icc ((time : Real) - b ^ 2) (time : Real) ⊆ D'.regular := by
    intro t ht
    apply hreg
    rw [hbSq] at ht
    exact ⟨by linarith [ht.1, hepsr], ht.2⟩
  have hbdom : b ∈ lRegDomain S (time : Real) B.center Z :=
    mem_lRegDomain_of_time_slab S hS (time : Real) B.center Z b hbpos.le hslab
  let alpha : Real → N := lRegCurve S (time : Real) B.center Z
  have halpha : ContinuousOn alpha (Icc (0 : Real) b) := by
    simpa only [alpha] using
      (lRegCurve_c1On S hS (time : Real) B.center Z hbdom).continuousOn
  let Q : Real := Real.exp (2 * A * eps * B.radius ^ 2)
  have harg0 : 0 ≤ 2 * A * eps * B.radius ^ 2 := by positivity
  have harg : 2 * A * eps * B.radius ^ 2 ≤ 1 / 4 := by
    have hscale : eps * (A * rho ^ 2 + 1) ≤ 1 / 8 := by
      calc
        eps * (A * rho ^ 2 + 1) ≤ epsM * (A * rho ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hepsM' hden.le
        _ = 1 / 8 := by
          dsimp only [epsM]
          field_simp [hden.ne']
    have hAr : A * B.radius ^ 2 ≤ A * rho ^ 2 :=
      mul_le_mul_of_nonneg_left hrSq hA
    have hsmall : eps * (A * B.radius ^ 2) ≤ 1 / 8 := by
      calc
        eps * (A * B.radius ^ 2) ≤ eps * (A * rho ^ 2) :=
          mul_le_mul_of_nonneg_left hAr heps.le
        _ ≤ eps * (A * rho ^ 2 + 1) := by
          gcongr
          linarith
        _ ≤ 1 / 8 := hscale
    nlinarith [hsmall]
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact Real.exp_pos _
  have hQle : Q ≤ 4 / 3 := by
    calc
      Q ≤ 1 / (1 - 2 * A * eps * B.radius ^ 2) :=
        by
          dsimp only [Q]
          exact Real.exp_bound_div_one_sub_of_interval harg0 (by linarith [harg])
      _ ≤ 4 / 3 := div_one_sub_le harg
  have hsqrtQ : Real.sqrt Q < 2 := by
    have hsq := Real.sq_sqrt hQpos.le
    nlinarith [Real.sqrt_nonneg Q]
  let : RiemannianBundle (fun x : N ↦ TangentSpace J x) :=
    ⟨(S.base.metric (time : Real)).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F
      (fun x : N ↦ TangentSpace J x) :=
    ⟨(S.base.metric (time : Real)).inner,
      (S.base.metric (time : Real)).contMDiff.continuous,
      fun _ _ _ ↦ rfl⟩
  let K : Set N := {y | riemannianEDistOf (I := J)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 2)}
  let O : Set N := {y | riemannianEDistOf (I := J)
    (S.base.metric (time : Real)) B.center y < ENNReal.ofReal (B.radius / 2)}
  have hKclosed : IsClosed K := by
    dsimp only [K]
    exact isClosed_le
      (continuous_riemannianEDist (S.base.metric (time : Real)) B.center)
      continuous_const
  have hOopen : IsOpen O := by
    dsimp only [O]
    exact isOpen_lt
      (continuous_riemannianEDist (S.base.metric (time : Real)) B.center)
      continuous_const
  have hOK : O ⊆ K := by
    intro y hy
    change riemannianEDistOf (I := J) (S.base.metric (time : Real))
      B.center y < ENNReal.ofReal (B.radius / 2) at hy
    change riemannianEDistOf (I := J) (S.base.metric (time : Real))
      B.center y ≤ ENNReal.ofReal (B.radius / 2)
    exact hy.le
  have hcenterO : B.center ∈ O := by
    change riemannianEDistOf (I := J) (S.base.metric (time : Real))
      B.center B.center < ENNReal.ofReal (B.radius / 2)
    simpa only [riemannianEDistOf_self] using
      ENNReal.ofReal_pos.2 (half_pos B.radius_pos)
  have hcenterK : B.center ∈ interior K :=
    (interior_maximal hOK hOopen) hcenterO
  have hKmove : ∀ q ∈ Icc (0 : Real) b, alpha q ∈ K →
      alpha q ∈ B.setAt ((time : Real) - q ^ 2) := by
    intro q hq hqK
    change riemannianEDistOf (I := J) (S.base.metric (time : Real))
      B.center (alpha q) ≤ ENNReal.ofReal (B.radius / 2) at hqK
    have hqSq : q ^ 2 ≤ eps * B.radius ^ 2 := by
      rw [← hbSq]
      exact (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    have hqt : (time : Real) - q ^ 2 ∈
        Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
      ⟨by linarith [hqSq], by nlinarith [sq_nonneg q]⟩
    have hquad : ∀ x (v : TangentSpace J x),
        (S.base.metric ((time : Real) - q ^ 2)).inner x v v ≤
          Q * (S.base.metric (time : Real)).inner x v v := by
      intro x v
      simpa only [Q] using (hmetric eps heps.le hepsOne B.radius B.radius_pos
        hBrho ((time : Real) - q ^ 2) hqt x v).2
    have hdist := edistOf_le_of_quad (I := J)
      (S.base.metric (time : Real))
      (S.base.metric ((time : Real) - q ^ 2)) hQpos hquad
      B.center (alpha q)
    change riemannianEDistOf (I := J)
      (S.base.metric ((time : Real) - q ^ 2)) B.center (alpha q) <
        ENNReal.ofReal B.radius
    calc
      riemannianEDistOf (I := J)
          (S.base.metric ((time : Real) - q ^ 2)) B.center (alpha q) ≤
          ENNReal.ofReal (Real.sqrt Q) *
            riemannianEDistOf (I := J) (S.base.metric (time : Real))
              B.center (alpha q) := hdist
      _ ≤ ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal (B.radius / 2) :=
        by simpa only [mul_comm] using
          mul_le_mul_right hqK (ENNReal.ofReal (Real.sqrt Q))
      _ = ENNReal.ofReal (Real.sqrt Q * (B.radius / 2)) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
          nlinarith [B.radius_pos, hsqrtQ])
  intro s hs
  have hsK : alpha s ∈ K := by
    by_contra hsK
    have hsne : s ≠ 0 := by
      intro hs0
      apply hsK
      simpa only [hs0, alpha, lRegCurve_zero] using interior_subset hcenterK
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
    have halpha0 : alpha 0 ∈ interior K := by
      simpa only [alpha, lRegCurve_zero] using hcenterK
    have halphaS : ContinuousOn alpha (Icc (0 : Real) s) :=
      halpha.mono fun q hq ↦ ⟨hq.1, hq.2.trans hs.2⟩
    obtain ⟨t, ht, hstay, hfront⟩ :=
      exists_first_exit_frontier hKclosed hspos halphaS halpha0 hsK
    have hfrontNot : alpha t ∉ interior K := by
      rw [frontier, hKclosed.closure_eq] at hfront
      exact hfront.2
    have hmove : ∀ q ∈ Icc (0 : Real) t,
        alpha q ∈ B.setAt ((time : Real) - q ^ 2) := by
      intro q hq
      exact hKmove q ⟨hq.1, hq.2.trans (ht.2.trans hs.2)⟩ (hstay q hq)
    have htDom : t ∈ lRegDomain S (time : Real) B.center Z := by
      have htslab : Icc ((time : Real) - t ^ 2) (time : Real) ⊆ D'.regular := by
        intro q hq
        apply hslab
        constructor
        · have htSq : t ^ 2 ≤ b ^ 2 :=
            (sq_le_sq₀ ht.1.le hbpos.le).2 (ht.2.trans hs.2)
          linarith [hq.1]
        · exact hq.2
      exact mem_lRegDomain_of_time_slab S hS (time : Real) B.center Z t ht.1.le htslab
    have hE := lRegTerm_int (I := J) S hS (time : Real) B.center Z ht.1 htDom
    have hterm : ∀ q ∈ Icc (0 : Real) t,
        (S.base.metric (time : Real)).inner (alpha q)
          (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q) ≤
            1 / (6 * eps) := by
      intro q hq
      have hqSq : q ^ 2 ≤ eps * B.radius ^ 2 := by
        rw [← hbSq]
        exact (sq_le_sq₀ hq.1 hbpos.le).2
          (hq.2.trans (ht.2.trans hs.2))
      have hqt : (time : Real) - q ^ 2 ∈
          Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
        ⟨by linarith [hqSq], by nlinarith [sq_nonneg q]⟩
      have hqSpeed := hspeed eps heps hepsS' B hBrho hB Z hZ q
        ⟨hq.1, hq.2.trans (ht.2.trans hs.2)⟩ (fun u hu ↦
          hmove u ⟨hu.1, hu.2.trans hq.2⟩)
      have hquad :
          (S.base.metric (time : Real)).inner (alpha q)
              (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q) ≤
            Q * (S.base.metric ((time : Real) - q ^ 2)).inner (alpha q)
              (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q) := by
        simpa only [Q] using (hmetric eps heps.le hepsOne B.radius B.radius_pos
          hBrho ((time : Real) - q ^ 2) hqt (alpha q)
            (lVelocity (I := J) alpha q)).1
      calc
        (S.base.metric (time : Real)).inner (alpha q)
            (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q) ≤
          Q * (S.base.metric ((time : Real) - q ^ 2)).inner (alpha q)
            (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q) := hquad
        _ ≤ Q * (1 / (8 * eps)) :=
          mul_le_mul_of_nonneg_left (by
            simpa only [alpha, lRegSpeedSq] using hqSpeed) hQpos.le
        _ ≤ (4 / 3 : Real) * (1 / (8 * eps)) :=
          mul_le_mul_of_nonneg_right hQle (by positivity)
        _ = 1 / (6 * eps) := by
          field_simp [heps.ne']
          norm_num
    have hEint : IntervalIntegrable (fun q ↦
        (S.base.metric (time : Real)).inner (alpha q)
          (lVelocity (I := J) alpha q) (lVelocity (I := J) alpha q))
        volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le]
      simpa only [alpha] using hE
    have hEC : curveEnergy (I := J) (S.base.metric (time : Real)) alpha 0 t ≤
        t / (6 * eps) := by
      calc
        curveEnergy (I := J) (S.base.metric (time : Real)) alpha 0 t ≤
            ∫ _q in (0 : Real)..t, 1 / (6 * eps) := by
          unfold curveEnergy
          exact intervalIntegral.integral_mono_on ht.1.le hEint
            intervalIntegrable_const hterm
        _ = t / (6 * eps) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
    let Bhalf : FlowMetricBall S time :=
      ⟨B.center, B.radius / 2, half_pos B.radius_pos⟩
    have hreach : Real.sqrt (Real.sqrt (t ^ 2)) *
        Real.sqrt (t / (6 * eps)) < Bhalf.radius := by
      have hC0 : 0 ≤ t / (6 * eps) :=
        div_nonneg ht.1.le (mul_nonneg (by norm_num) heps.le)
      have htSq : t ^ 2 ≤ eps * B.radius ^ 2 := by
        rw [← hbSq]
        exact (sq_le_sq₀ ht.1.le hbpos.le).2 (ht.2.trans hs.2)
      have hepsr : 0 < eps * B.radius ^ 2 :=
        mul_pos heps (sq_pos_of_pos B.radius_pos)
      have hleft0 : 0 ≤ Real.sqrt (Real.sqrt (t ^ 2)) *
          Real.sqrt (t / (6 * eps)) := by positivity
      have hright0 : 0 ≤ Bhalf.radius := Bhalf.radius_pos.le
      apply (sq_lt_sq₀ hleft0 hright0).1
      dsimp only [Bhalf]
      rw [mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos ht.1,
        Real.sq_sqrt ht.1.le, Real.sq_sqrt hC0]
      field_simp [heps.ne']
      nlinarith [htSq]
    have hhalf := lExp_mem_ball (I := J) S hS time Bhalf Z (t ^ 2)
      (t / (6 * eps)) (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1] using htDom)
      (by simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1, alpha, Bhalf] using hE)
      (by simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1, alpha, Bhalf] using hEC)
      hreach
    have halphaHalf : alpha t ∈ Bhalf.set := by
      simpa only [alpha, Bhalf, lExp, Real.sqrt_sq_eq_abs, abs_of_pos ht.1] using hhalf
    have hhalfO : Bhalf.set ⊆ O := by
      intro y hy
      simpa only [O, Bhalf, FlowMetricBall.set, FlowMetricBall.setAt] using hy
    exact hfrontNot ((interior_maximal hOK hOopen) (hhalfO halphaHalf))
  constructor
  · change riemannianEDistOf (I := J) (S.base.metric (time : Real)) B.center
        (lRegCurve S (time : Real) B.center Z s) ≤
      ENNReal.ofReal (B.radius / 2) at hsK ⊢
    exact hsK
  · simpa only [alpha] using hKmove s hs hsK

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExp_scale_ball
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
              lExp S (time : Real) B.center Z (eps * B.radius ^ 2) ∈ B.set := by
  obtain ⟨eps₀, heps₀, hrange⟩ :=
    lRegRange_scale (J := J) S hS time hrho hreg
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ
  let b : Real := Real.sqrt eps * B.radius
  have hbpos : 0 < b := mul_pos (Real.sqrt_pos.2 heps) B.radius_pos
  have hb : Real.sqrt (eps * B.radius ^ 2) = b := by
    dsimp only [b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  have hrangeB := hrange eps heps heps₀ B hBrho hB Z hZ b
    ⟨hbpos.le, le_rfl⟩
  change riemannianEDistOf (I := J) (S.base.metric (time : Real)) B.center
      (lExp S (time : Real) B.center Z (eps * B.radius ^ 2)) <
        ENNReal.ofReal B.radius
  rw [lExp, hb]
  exact hrangeB.1.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      linarith [B.radius_pos]))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReg_small_ball
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D')
    (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') (B : FlowMetricBall S time)
    (R : Real) (hT : (time : Real) ∈ D'.regular) :
    ∃ eps : Real, 0 < eps ∧
      ∀ Z : TangentSpace J B.center,
        Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤ R →
        ∀ b : Real, |b| < eps →
          b ∈ lRegDomain S (time : Real) B.center Z ∧
            lRegCurve S (time : Real) B.center Z b ∈ B.set := by
  classical
  let A := lSrcGram S (time : Real) B.center
  let L := spdSqrtEquiv A (lSrcGram_pd S (time : Real) B.center)
  let K : Set F :=
    (fun y ↦ (toEuclidean (E := F)).symm (L.symm y)) ''
      Metric.closedBall 0 R
  let curve : F × Real → N := fun p ↦
    lRegCurve S (time : Real) B.center p.1 p.2
  let U : Set (F × Real) :=
    lRegJointDom S (time : Real) B.center ∩ curve ⁻¹' B.set
  have hKcpt : IsCompact K := by
    exact (isCompact_closedBall (0 : EuclideanSpace Real
      (Fin (Module.finrank Real F))) R).image
        ((toEuclidean (E := F)).symm.continuous.comp L.symm.continuous)
  have hBopen : IsOpen B.set := by
    let : RiemannianBundle (fun x : N ↦ TangentSpace J x) :=
      ⟨(S.base.metric (time : Real)).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle F
        (fun x : N ↦ TangentSpace J x) :=
      ⟨(S.base.metric (time : Real)).inner,
        (S.base.metric (time : Real)).contMDiff.continuous,
        fun _ _ _ ↦ rfl⟩
    change IsOpen {y : N |
      Manifold.riemannianEDist J B.center y < ENNReal.ofReal B.radius}
    exact isOpen_lt
      (continuous_riemannianEDist (S.base.metric (time : Real)) B.center)
      continuous_const
  have hFcont : ContinuousOn curve (lRegJointDom S (time : Real) B.center) := by
    simpa only [curve] using
      (lRegCurve_smoothOn S hS (time : Real) B.center).continuousOn
  have hUopen : IsOpen U := by
    exact hFcont.isOpen_inter_preimage
      (lRegJointDom_open S hS (time : Real) B.center) hBopen
  have hK0 : K ×ˢ ({0} : Set Real) ⊆ U := by
    rintro ⟨Z, _⟩ ⟨hZ, rfl⟩
    change TangentSpace J B.center at Z
    refine ⟨zero_mem_lRegDomain S hS (time : Real) B.center Z hT, ?_⟩
    simpa only [curve, Set.mem_preimage, lRegCurve_zero] using
      (show B.center ∈ B.set by
        change riemannianEDistOf (I := J) (S.base.metric (time : Real))
          B.center B.center < ENNReal.ofReal B.radius
        simpa only [riemannianEDistOf_self] using
          ENNReal.ofReal_pos.2 B.radius_pos)
  have hK0cpt : IsCompact (K ×ˢ ({0} : Set Real)) :=
    hKcpt.prod isCompact_singleton
  obtain ⟨eps, heps, hepsU⟩ :=
    hK0cpt.exists_thickening_subset_open hUopen hK0
  refine ⟨eps, heps, ?_⟩
  intro Z hZR b hb
  change F at Z
  have hnorm : ‖L (toEuclidean Z)‖ =
      Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) := by
    rw [← Real.sqrt_sq (norm_nonneg _), spdSqrt_norm_sq]
    exact congrArg Real.sqrt (lSrcGram_quad S (time : Real) B.center Z)
  have hZK : Z ∈ K := by
    refine ⟨L (toEuclidean Z), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, hnorm]
      exact hZR
    · simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hUb : (Z, b) ∈ U := by
    apply hepsU
    rw [Metric.mem_thickening_iff]
    refine ⟨(Z, (0 : Real)), ⟨hZK, rfl⟩, ?_⟩
    calc
      dist (Z, b) (Z, (0 : Real)) = dist b 0 := dist_prod_same_left
      _ = |b| := by rw [Real.dist_eq, sub_zero]
      _ < eps := hb
  change (Z, b) ∈ lRegJointDom S (time : Real) B.center ∧
    lRegCurve S (time : Real) B.center Z b ∈ B.set at hUb
  change b ∈ lRegDomain S (time : Real) B.center Z ∧
    lRegCurve S (time : Real) B.center Z b ∈ B.set
  exact hUb

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExp_small_ball
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D')
    (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') (B : FlowMetricBall S time)
    (R : Real) (hT : (time : Real) ∈ D'.regular) :
    ∃ eps : Real, 0 < eps ∧
      ∀ Z : TangentSpace J B.center,
        Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤ R →
        ∀ tau : Real, Real.sqrt tau < eps →
          lExp S (time : Real) B.center Z tau ∈ B.set := by
  obtain ⟨eps, heps, hmem⟩ :=
    lReg_small_ball (J := J) S hS time B R hT
  refine ⟨eps, heps, ?_⟩
  intro Z hZR tau htau
  exact (hmem Z hZR (Real.sqrt tau) (by
    rw [abs_of_nonneg (Real.sqrt_nonneg tau)]
    exact htau)).2

end DifferentialGeometry.PDE.RicciFlow.Perelman
