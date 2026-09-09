import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.BallEstimate.EndpointControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.MetricComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff ENNReal Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_lRegularizedSpeedSq_le :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                let b := Real.sqrt eps * B.radius
                ∀ s ∈ Set.Icc (0 : Real) b,
                  s ∈ lRegularizedDomain S (time : Real) B.center Z →
                  (∀ q ∈ Set.Icc (0 : Real) s,
                    riemannianEDistOf (I := I)
                        (S.base.metric ((time : Real) - q ^ 2)) B.center
                        (lRegularizedCurve S (time : Real) B.center Z q) <
                      ENNReal.ofReal (B.radius / 8)) →
                  lRegularizedSpeedSq S (time : Real)
                      (lRegularizedCurve S (time : Real) B.center Z) s ≤
                    (4 / 3 : Real) *
                      (lRegularizedSpeedSq S (time : Real)
                        (lRegularizedCurve S (time : Real) B.center Z) 0 + 1) := by
  obtain ⟨theta, A, htheta, hthetaOne, hA, hgrad⟩ :=
    FlowMetricBall.scalar_gradient_estimate (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  let n : Real := Module.finrank Real E
  let C₀ : Real := rho + 2 * A + 4 * n ^ 2 + 1
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀, n]
    nlinarith [hrho, hA.le, sq_nonneg (Module.finrank Real E : Real)]
  let d : Real := 1 / (4 * C₀)
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hC₀)
  let eps₀ : Real := min (theta / 2) (min 1 (d ^ 2))
  have heps₀ : 0 < eps₀ := by
    dsimp only [eps₀]
    exact lt_min (div_pos htheta (by norm_num))
      (lt_min zero_lt_one (sq_pos_of_pos hd))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z
  dsimp only
  intro s hs hsdom hpoint
  let b : Real := Real.sqrt eps * B.radius
  let G : Real := A / B.radius ^ 3
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have hepsTheta : eps ≤ theta / 2 := by
    exact heps₀.trans (min_le_left (theta / 2) (min 1 (d ^ 2)))
  have hepsOne : eps ≤ 1 := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min 1 (d ^ 2) := min_le_right _ _
      _ ≤ 1 := min_le_left _ _
  have hepsD : eps ≤ d ^ 2 := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min 1 (d ^ 2) := min_le_right _ _
      _ ≤ d ^ 2 := min_le_right _ _
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hepsLtOne : eps < 1 := by
    calc
      eps ≤ theta / 2 := hepsTheta
      _ < 1 := by linarith [hthetaOne]
  have hbSqLt : b ^ 2 < B.radius ^ 2 := by
    rw [hbSq]
    nlinarith [sq_pos_of_pos B.radius_pos]
  by_cases hsZero : s = 0
  · subst s
    have hU := lRegularizedSpeedSq_nonneg (I := I) S (time : Real)
      (lRegularizedCurve S (time : Real) B.center Z) 0
    nlinarith
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
  have halpha : IsLRegularizedCurveOn S (time : Real)
      (lRegularizedCurve S (time : Real) B.center Z) (Set.Icc (0 : Real) s)
      B.center Z := by
    simpa only [Set.uIcc_of_le hs.1] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS (time : Real) B.center Z hspos hsdom
  have hG : 0 ≤ G := div_nonneg hA.le (pow_nonneg B.radius_pos.le 3)
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hsle : s ≤ b := hs.2
  have hsub : Set.uIcc (0 : Real) s ⊆ Set.Icc (0 : Real) b := by
    intro q hq
    have hq' : q ∈ Set.Icc (0 : Real) s := by
      simpa only [Set.uIcc_of_le hs.1] using hq
    exact ⟨hq'.1, hq'.2.trans hsle⟩
  have htimeGrad : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈ Set.Icc
        ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    have hqTheta : q ^ 2 ≤ theta * B.radius ^ 2 / 2 := by
      calc
        q ^ 2 ≤ b ^ 2 := hqSq
        _ = eps * B.radius ^ 2 := hbSq
        _ ≤ theta * B.radius ^ 2 / 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hepsTheta
            (sq_nonneg B.radius)]
    exact ⟨by linarith, by nlinarith [sq_nonneg q]⟩
  have htimeBall : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈ Set.Icc
        ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    exact ⟨by linarith [hqSq, hbSqLt], by nlinarith [sq_nonneg q]⟩
  have hgr := lRegularizedSpeedSq_le_of_gradient_ricci_bounds (I := I) S hS (time : Real) halpha
    0 s G K b hG hK
    (fun _ hq ↦ by simpa only [Set.uIcc_of_le hs.1] using hq)
    (fun q hq ↦ by
      have hqI := hsub hq
      rw [abs_of_nonneg hqI.1]
      exact hqI.2)
    (fun q hq ↦ by
      have hqI := hsub hq
      have hqS : q ∈ Set.Icc (0 : Real) s := by
        simpa only [Set.uIcc_of_le hs.1] using hq
      simpa only [G, lRegularizedSpeedSq] using
        hgrad hS B hB hreg hcomplete ((time : Real) - q ^ 2)
          (htimeGrad q hqI)
          (lRegularizedCurve S (time : Real) B.center Z q)
          (lVelocity (I := I) (lRegularizedCurve S (time : Real) B.center Z) q)
          (hpoint q hqS))
    (fun q hq ↦ by
      have hqI := hsub hq
      have hqS : q ∈ Set.Icc (0 : Real) s := by
        simpa only [Set.uIcc_of_le hs.1] using hq
      have hmem : lRegularizedCurve S (time : Real) B.center Z q ∈
          B.setAt ((time : Real) - q ^ 2) := by
        change riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - q ^ 2)) B.center
            (lRegularizedCurve S (time : Real) B.center Z q) <
          ENNReal.ofReal B.radius
        exact (hpoint q hqS).trans_le
          (ENNReal.ofReal_le_ofReal (by nlinarith [B.radius_pos]))
      simpa only [K, n] using
        lRegularizedRicci_le (I := I) S time B hB (htimeBall q hqI) hmem)
  have hscaleK : B.radius ^ 2 * K = n ^ 2 := by
    dsimp only [K]
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one,
      show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]
    field_simp [B.radius_pos.ne']
  have hb3G : G * b ^ 2 * b = A * eps * Real.sqrt eps := by
    dsimp only [G, b]
    rw [mul_pow, Real.sq_sqrt heps.le]
    field_simp [B.radius_pos.ne']
  have hb2K : K * b * b = n ^ 2 * eps := by
    calc
      K * b * b = B.radius ^ 2 * K * (Real.sqrt eps) ^ 2 := by
        dsimp only [b]
        ring
      _ = B.radius ^ 2 * K * eps := by rw [Real.sq_sqrt heps.le]
      _ = n ^ 2 * eps := by rw [hscaleK]
  let k : Real := 1 + 2 * G * b ^ 2 + 4 * K * b
  let d₁ : Real := 1 + 2 * G * b ^ 2
  have hk : 0 < k := by
    dsimp only [k]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (mul_nonneg (by norm_num) hG) (sq_nonneg b)))
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hd₁ : 0 < d₁ := by
    dsimp only [d₁]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (by norm_num) hG) (sq_nonneg b))
  have hratio : d₁ / k ≤ 1 := by
    rw [div_le_one hk]
    dsimp only [d₁, k]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hsabs : |s - 0| ≤ b := by
    rw [sub_zero, abs_of_nonneg hs.1]
    exact hs.2
  have hepsSqrt : eps ≤ Real.sqrt eps := by
    nlinarith [Real.sq_sqrt heps.le, Real.sqrt_nonneg eps, hepsOne]
  have hepsMul : eps * Real.sqrt eps ≤ Real.sqrt eps :=
    mul_le_of_le_one_left (Real.sqrt_nonneg eps) hepsOne
  have hsqrtD : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsD⟩
  have hsqrtC₀ : Real.sqrt eps * C₀ ≤ 1 / 4 := by
    calc
      Real.sqrt eps * C₀ ≤ d * C₀ :=
        mul_le_mul_of_nonneg_right hsqrtD hC₀.le
      _ = 1 / 4 := by
        dsimp only [d]
        field_simp [hC₀.ne']
  have hexpArg : k * |s - 0| ≤ 1 / 4 := by
    have hkb : k * |s - 0| ≤ k * b :=
      mul_le_mul_of_nonneg_left hsabs hk.le
    have hcore : k * b = b + 2 * (G * b ^ 2 * b) + 4 * (K * b * b) := by
      dsimp only [k]
      ring
    calc
      k * |s - 0| ≤ k * b := hkb
      _ = b + 2 * (G * b ^ 2 * b) + 4 * (K * b * b) := hcore
      _ = Real.sqrt eps * B.radius +
          2 * (A * eps * Real.sqrt eps) + 4 * (n ^ 2 * eps) := by
        rw [hb3G, hb2K]
      _ ≤ Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by
        have h₁ : Real.sqrt eps * B.radius ≤ Real.sqrt eps * rho :=
          mul_le_mul_of_nonneg_left hBrho (Real.sqrt_nonneg eps)
        have h₂ : A * eps * Real.sqrt eps ≤ A * Real.sqrt eps := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hepsMul hA.le
        have h₃ : n ^ 2 * eps ≤ n ^ 2 * Real.sqrt eps :=
          mul_le_mul_of_nonneg_left hepsSqrt (sq_nonneg n)
        calc
          Real.sqrt eps * B.radius + 2 * (A * eps * Real.sqrt eps) +
                4 * (n ^ 2 * eps) ≤
              Real.sqrt eps * rho + 2 * (A * Real.sqrt eps) +
                4 * (n ^ 2 * Real.sqrt eps) :=
            add_le_add (add_le_add h₁
              (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
              (mul_le_mul_of_nonneg_left h₃ (by norm_num))
          _ = Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by ring
      _ ≤ Real.sqrt eps * C₀ := by
        dsimp only [C₀]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg eps)
      _ ≤ 1 / 4 := hsqrtC₀
  have hexp : Real.exp (k * |s - 0|) ≤ 4 / 3 := by
    have hbound := Real.exp_bound_div_one_sub_of_interval
      (mul_nonneg hk.le (abs_nonneg _)) (by linarith [hexpArg])
    refine hbound.trans ?_
    apply (div_le_iff₀ (by linarith [hexpArg])).2
    nlinarith [hexpArg]
  have hterm : 0 ≤ lRegularizedSpeedSq S (time : Real)
        (lRegularizedCurve S (time : Real) B.center Z) 0 + d₁ / k :=
    add_nonneg (lRegularizedSpeedSq_nonneg (I := I) S (time : Real)
      (lRegularizedCurve S (time : Real) B.center Z) 0) (div_nonneg hd₁.le hk.le)
  calc
    lRegularizedSpeedSq S (time : Real)
        (lRegularizedCurve S (time : Real) B.center Z) s ≤
      Real.exp (k * |s - 0|) *
        (lRegularizedSpeedSq S (time : Real)
          (lRegularizedCurve S (time : Real) B.center Z) 0 + d₁ / k) := by
        simpa only [k, d₁] using hgr
    _ ≤ (4 / 3 : Real) *
        (lRegularizedSpeedSq S (time : Real)
          (lRegularizedCurve S (time : Real) B.center Z) 0 + d₁ / k) :=
      mul_le_mul_of_nonneg_right hexp hterm
    _ ≤ (4 / 3 : Real) *
        (lRegularizedSpeedSq S (time : Real)
          (lRegularizedCurve S (time : Real) B.center Z) 0 + 1) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right hratio _)
        (by norm_num)

private theorem source_sq_eq {eps : Real} (heps : 0 < eps) :
    4 * (1 / (128 * Real.sqrt eps)) ^ 2 = 1 / (4096 * eps) := by
  rw [div_pow, mul_pow, Real.sq_sqrt heps.le]
  field_simp [heps.ne']
  ring

private theorem source_speed_le {eps U : Real} (heps : 0 < eps)
    (hU : U ≤ (1 / (128 * Real.sqrt eps)) ^ 2) :
    4 * U ≤ 1 / (4096 * eps) := by
  calc
    4 * U ≤ 4 * (1 / (128 * Real.sqrt eps)) ^ 2 :=
      mul_le_mul_of_nonneg_left hU (by norm_num)
    _ = 1 / (4096 * eps) := source_sq_eq heps

private theorem one_le_scaled {eps : Real} (heps : 0 < eps)
    (hsmall : eps ≤ 1 / 8192) : (1 : Real) ≤ 1 / (8192 * eps) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) heps)).2
  calc
    1 * ((8192 : Real) * eps) = (8192 : Real) * eps := one_mul _
    _ ≤ (8192 : Real) * (1 / 8192 : Real) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : Real) ≤ 8192)
    _ = 1 := by norm_num

private theorem speed_absorb {eps U : Real} (heps : 0 < eps)
    (hU : U ≤ 1 / (4096 * eps)) (hone : 1 ≤ 1 / (8192 * eps)) :
    (4 / 3 : Real) * (U + 1) ≤ 1 / (2048 * eps) := by
  calc
    (4 / 3 : Real) * (U + 1) ≤
        (4 / 3 : Real) *
          (1 / (4096 * eps) + 1 / (8192 * eps)) :=
      mul_le_mul_of_nonneg_left (add_le_add hU hone) (by norm_num)
    _ = 1 / (2048 * eps) := by
      field_simp [heps.ne']
      ring

private theorem reach_small {t eps r : Real} (ht : 0 < t) (heps : 0 < eps)
    (htSq : t ^ 2 ≤ eps * r ^ 2) (hr : 0 < r) :
    Real.sqrt (Real.sqrt (t ^ 2)) * Real.sqrt (t / (1536 * eps)) <
      r / 32 := by
  have hC0 : 0 ≤ t / (1536 * eps) :=
    div_nonneg ht.le (mul_nonneg (by norm_num) heps.le)
  have hscalePos : 0 < eps * r ^ 2 :=
    mul_pos heps (sq_pos_of_pos hr)
  have hleft0 : 0 ≤ Real.sqrt (Real.sqrt (t ^ 2)) *
      Real.sqrt (t / (1536 * eps)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ r / 32 :=
    div_nonneg hr.le (by norm_num)
  apply (sq_lt_sq₀ hleft0 hright0).1
  rw [mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos ht,
    Real.sq_sqrt ht.le, Real.sq_sqrt hC0]
  field_simp [heps.ne']
  nlinarith only [htSq, hscalePos]

private theorem edist_move_lt
    [NeZero (Module.finrank Real E)] {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    (hreg : Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular)
    (hcompleteT :
      RiemannianMetricComplete (I := I) (S.base.metric (time : Real)))
    {eps q : Real} (heps : 0 < eps) (hepsOne : eps < 1)
    (hqSq : q ^ 2 ≤ eps * B.radius ^ 2)
    (hsmall : 2 * (Module.finrank Real E : Real) ^ 2 * eps ≤
      Real.log (4 / 3))
    {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center x ≤ ENNReal.ofReal (B.radius / 32)) :
    riemannianEDistOf (I := I)
        (S.base.metric ((time : Real) - q ^ 2)) B.center x <
      ENNReal.ofReal (B.radius / 16) := by
  let n : Real := Module.finrank Real E
  let P : Real := Real.exp
    ((n ^ 2 / B.radius ^ 2) *
      ((time : Real) - ((time : Real) - q ^ 2)))
  have hnne : 0 ≤ n ^ 2 * eps :=
    mul_nonneg (sq_nonneg n) heps.le
  have hdim : n ^ 2 * eps ≤ Real.log (4 / 3) := by
    calc
      n ^ 2 * eps = 1 * (n ^ 2 * eps) := by ring
      _ ≤ 2 * (n ^ 2 * eps) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnne
      _ = 2 * n ^ 2 * eps := by ring
      _ ≤ Real.log (4 / 3) := by simpa only [n] using hsmall
  have hParg :
      (n ^ 2 / B.radius ^ 2) *
          ((time : Real) - ((time : Real) - q ^ 2)) ≤
        Real.log (4 / 3) := by
    calc
      (n ^ 2 / B.radius ^ 2) *
            ((time : Real) - ((time : Real) - q ^ 2)) =
          (n ^ 2 / B.radius ^ 2) * q ^ 2 := by ring
      _ ≤ (n ^ 2 / B.radius ^ 2) * (eps * B.radius ^ 2) :=
        mul_le_mul_of_nonneg_left hqSq (by positivity)
      _ = n ^ 2 * eps := by
        field_simp [B.radius_pos.ne']
      _ ≤ Real.log (4 / 3) := hdim
  have hPpos : 0 < P := Real.exp_pos _
  have hPle : P ≤ 4 / 3 := by
    calc
      P ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr hParg
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have hqLt : q ^ 2 < B.radius ^ 2 := by
    calc
      q ^ 2 ≤ eps * B.radius ^ 2 := hqSq
      _ < B.radius ^ 2 := by
        nlinarith [hepsOne, sq_pos_of_pos B.radius_pos]
  have hregSmall : Set.Ioc ((time : Real) - q ^ 2) (time : Real) ⊆
      D.regular := by
    intro t ht
    apply hreg
    exact ⟨by linarith [ht.1, hqLt], ht.2⟩
  have hstB : Set.Icc ((time : Real) - q ^ 2) (time : Real) ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro t ht
    exact ⟨(sub_lt_sub_left hqLt (time : Real)).le.trans ht.1, ht.2⟩
  have hPr : P * (B.radius / 32) < B.radius := by
    calc
      P * (B.radius / 32) ≤ (4 / 3 : Real) * (B.radius / 32) :=
        mul_le_mul_of_nonneg_right hPle
          (div_nonneg B.radius_pos.le (by norm_num))
      _ < B.radius := by nlinarith only [B.radius_pos]
  have hPr16 : P * (B.radius / 32) < B.radius / 16 := by
    calc
      P * (B.radius / 32) ≤ (4 / 3 : Real) * (B.radius / 32) :=
        mul_le_mul_of_nonneg_right hPle
          (div_nonneg B.radius_pos.le (by norm_num))
      _ < B.radius / 16 := by nlinarith only [B.radius_pos]
  have hxP :
      ENNReal.ofReal P *
            riemannianEDistOf (I := I) (S.base.metric (time : Real))
              B.center x <
          ENNReal.ofReal B.radius := by
    calc
      ENNReal.ofReal P *
            riemannianEDistOf (I := I) (S.base.metric (time : Real))
              B.center x ≤
          ENNReal.ofReal P * ENNReal.ofReal (B.radius / 32) :=
        mul_le_mul_of_nonneg_left hx (by exact bot_le)
      _ = ENNReal.ofReal (P * (B.radius / 32)) := by
        rw [ENNReal.ofReal_mul hPpos.le]
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 hPr
  have hdist := FlowMetricBall.riemannianEDistOf_le_exp_mul (I := I)
    (s := (time : Real) - q ^ 2) (t := (time : Real)) hS B hB
    (sub_le_self _ (sq_nonneg q)) (fun t ht => hregSmall ⟨ht.1, ht.2.le⟩) hstB hcompleteT
    (x := x) (by simpa only [P, n] using hxP)
  calc
    riemannianEDistOf (I := I)
        (S.base.metric ((time : Real) - q ^ 2)) B.center x ≤
        ENNReal.ofReal P *
          riemannianEDistOf (I := I) (S.base.metric (time : Real))
            B.center x := hdist
    _ ≤ ENNReal.ofReal P * ENNReal.ofReal (B.radius / 32) :=
      mul_le_mul_of_nonneg_left hx (by exact bot_le)
    _ = ENNReal.ofReal (P * (B.radius / 32)) := by
      rw [ENNReal.ofReal_mul hPpos.le]
    _ < ENNReal.ofReal (B.radius / 16) :=
      (ENNReal.ofReal_lt_ofReal_iff (by
        nlinarith only [B.radius_pos])).2 hPr16

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_lRegularizedCurve_mem_ball :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                  1 / (128 * Real.sqrt eps) →
                let b := Real.sqrt eps * B.radius
                ∀ s ∈ Set.Icc (0 : Real) b,
                  s ∈ lRegularizedDomain S (time : Real) B.center Z ∧
                    riemannianEDistOf (I := I)
                        (S.base.metric (time : Real)) B.center
                        (lRegularizedCurve S (time : Real) B.center Z s) <
                      ENNReal.ofReal (B.radius / 32) ∧
                    riemannianEDistOf (I := I)
                        (S.base.metric ((time : Real) - s ^ 2)) B.center
                        (lRegularizedCurve S (time : Real) B.center Z s) <
                      ENNReal.ofReal (B.radius / 16) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro rho hrho
    refine ⟨1 / 4, by norm_num, ?_⟩
    intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z hZ
    dsimp only
    let b : ℝ := Real.sqrt eps * B.radius
    have hb : 0 < b := mul_pos (Real.sqrt_pos.mpr heps) B.radius_pos
    have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
      dsimp only [b]
      rw [mul_pow, Real.sq_sqrt heps.le]
    have hslab : Icc ((time : ℝ) - b ^ 2) (time : ℝ) ⊆ D.regular := by
      intro q hq
      apply hreg
      constructor
      · nlinarith [hq.1, sq_pos_of_pos B.radius_pos]
      · exact hq.2
    let alpha := lRegularizedCurve S (time : ℝ) B.center Z
    have hv (x : M) (v : TangentSpace I x) : v = 0 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
      exact Subsingleton.elim _ _
    have hspeed (s : ℝ) : lRegularizedSpeedSq S (time : ℝ) alpha s = 0 := by
      unfold lRegularizedSpeedSq
      rw [hv (alpha s) (lVelocity (I := I) alpha s)]
      simp
    have hconstant (s : ℝ) (hs : 0 ≤ s)
        (hdom : s ∈ lRegularizedDomain S (time : ℝ) B.center Z) : alpha s = B.center := by
      have hc := (lRegularizedCurve_c1On S hS (time : ℝ) B.center Z hdom).continuousOn
      have heq := isPreconnected_Icc.constant hc
        (right_mem_Icc.mpr hs) (left_mem_Icc.mpr hs)
      simpa only [alpha, lRegularizedCurve_zero] using heq
    have hbdom := mem_lRegularizedDomain_of_isCompact_range_of_speed_le S hS
      (time : ℝ) B.center Z b hb.le hslab {B.center} isCompact_singleton 0
      (fun s hs hdom => Set.mem_singleton_iff.mpr (hconstant s hs.1 hdom))
      (fun s _ _ => (hspeed s).le)
    intro s hs
    have hsdom := lRegularizedDomain_segment S (time : ℝ) B.center Z hbdom hs.1 hs.2
    have heq := hconstant s hs.1 hsdom
    refine ⟨hsdom, ?_, ?_⟩
    · change riemannianEDistOf (S.base.metric (time : ℝ)) B.center (alpha s) < _
      rw [heq, riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (div_pos B.radius_pos (by norm_num))
    · change riemannianEDistOf (S.base.metric ((time : ℝ) - s ^ 2)) B.center (alpha s) < _
      rw [heq, riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (div_pos B.radius_pos (by norm_num))
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  obtain ⟨theta, htheta, hthetaOne, hspeed⟩ :=
    exists_pos_lRegularizedSpeedSq_le (E := E) (I := I) (M := M)
  obtain ⟨epsM, hepsM, hmetric⟩ :=
    FlowMetricBall.exists_pos_inner_exp_bounds_on_terminal_ball (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  obtain ⟨epsS, hepsS, hspeed'⟩ := hspeed rho hrho
  let n : Real := Module.finrank Real E
  let epsF : Real := Real.log (4 / 3) / (2 * (n ^ 2 + 1))
  have hdenF : 0 < 2 * (n ^ 2 + 1) := by positivity
  have hepsF : 0 < epsF :=
    div_pos (Real.log_pos (by norm_num)) hdenF
  let eps₀ : Real := min epsS (min epsM (min epsF (1 / 8192)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsS (lt_min hepsM (lt_min hepsF (by norm_num)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z hZ
  dsimp only
  have hepsS' : eps ≤ epsS :=
    heps₀.trans (min_le_left epsS (min epsM (min epsF (1 / 8192))))
  have hepsM' : eps ≤ epsM := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ epsM := min_le_left _ _
  have hepsF' : eps ≤ epsF := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ min epsF (1 / 8192) := min_le_right _ _
      _ ≤ epsF := min_le_left _ _
  have hepsTiny : eps ≤ (1 / 8192 : Real) := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ min epsF (1 / 8192) := min_le_right _ _
      _ ≤ 1 / 8192 := min_le_right _ _
  have hepsOne : eps < 1 := by linarith
  let b : Real := Real.sqrt eps * B.radius
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hbSqLt : b ^ 2 < B.radius ^ 2 := by
    rw [hbSq]
    nlinarith [sq_pos_of_pos B.radius_pos]
  have hTreg : (time : Real) ∈ D.regular :=
    hreg ⟨by nlinarith [sq_pos_of_pos B.radius_pos], le_rfl⟩
  have hslab : Set.Icc ((time : Real) - b ^ 2) (time : Real) ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨by linarith [hq.1, hbSqLt], hq.2⟩
  have hcompleteT :
      RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) :=
    hcomplete (time : Real)
      ⟨sub_le_self _ (mul_nonneg htheta.le (sq_nonneg B.radius)), le_rfl⟩
  let alpha : Real → M := lRegularizedCurve S (time : Real) B.center Z
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have hKcompact : IsCompact K := by
    simpa only [K] using
      RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcompleteT B.center (B.radius / 32)
  let Q : Real := Real.exp (2 * n ^ 2 * eps)
  have harg : 2 * n ^ 2 * eps ≤ Real.log (4 / 3) := by
    have hcore : eps * (2 * (n ^ 2 + 1)) ≤ Real.log (4 / 3) := by
      apply (le_div_iff₀ hdenF).mp
      simpa only [epsF] using hepsF'
    nlinarith [sq_nonneg n, heps.le]
  have hQpos : 0 < Q := Real.exp_pos _
  have hQle : Q ≤ 4 / 3 := by
    calc
      Q ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr harg
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have htime : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈
        Set.Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    rw [hbSq] at hqSq
    exact ⟨by linarith, by nlinarith [sq_nonneg q]⟩
  have hKmove : ∀ q ∈ Set.Icc (0 : Real) b, alpha q ∈ K →
      riemannianEDistOf (I := I)
          (S.base.metric ((time : Real) - q ^ 2)) B.center (alpha q) <
        ENNReal.ofReal (B.radius / 16) := by
    intro q hq hqK
    have hqSq : q ^ 2 ≤ eps * B.radius ^ 2 := by
      have hqb : q ^ 2 ≤ b ^ 2 :=
        (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
      simpa only [hbSq] using hqb
    apply edist_move_lt (I := I) hS B hB hreg hcompleteT
      heps hepsOne hqSq harg
    simpa only [K, Set.mem_ofPred_eq] using hqK
  have hU0 : lRegularizedSpeedSq S (time : Real) alpha 0 =
      4 * (S.base.metric (time : Real)).inner B.center Z Z := by
    dsimp only [lRegularizedSpeedSq, alpha]
    norm_num only [zero_pow, sub_zero]
    rw [lRegularizedCurve_zero, lRegularizedCurve_velocity_zero S hS (time : Real) B.center Z hTreg]
    calc
      (S.base.metric (time : Real)).inner B.center ((2 : Real) • Z)
          ((2 : Real) • Z) =
        (2 : Real) * 2 *
          (S.base.metric (time : Real)).inner B.center Z Z :=
            metric_smul2 (I := I) (S.base.metric (time : Real)) (2 : Real) Z
      _ = 4 * (S.base.metric (time : Real)).inner B.center Z Z := by ring
  have hZsq : (S.base.metric (time : Real)).inner B.center Z Z ≤
      (1 / (128 * Real.sqrt eps)) ^ 2 := by
    have hZ0 : 0 ≤ (S.base.metric (time : Real)).inner B.center Z Z :=
      metric_inner_self_nonneg (S.base.metric (time : Real)) B.center Z
    have hZrhs : 0 ≤ 1 / (128 * Real.sqrt eps) :=
      (one_div_pos.mpr (mul_pos (by norm_num) hsqrteps)).le
    rw [← Real.sq_sqrt hZ0]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hZrhs).2 hZ
  have hU0le : lRegularizedSpeedSq S (time : Real) alpha 0 ≤ 1 / (4096 * eps) := by
    rw [hU0]
    exact source_speed_le heps hZsq
  have hone : (1 : Real) ≤ 1 / (8192 * eps) :=
    one_le_scaled heps hepsTiny
  have hspeedBound : ∀ q ∈ Set.Icc (0 : Real) b,
      q ∈ lRegularizedDomain S (time : Real) B.center Z →
      (∀ u ∈ Set.Icc (0 : Real) q, alpha u ∈ K) →
      lRegularizedSpeedSq S (time : Real) alpha q ≤ 1 / (2048 * eps) := by
    intro q hq hqDom hqK
    have hmove : ∀ u ∈ Set.Icc (0 : Real) q,
        riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - u ^ 2)) B.center (alpha u) <
          ENNReal.ofReal (B.radius / 16) := by
      intro u hu
      exact hKmove u ⟨hu.1, hu.2.trans hq.2⟩ (hqK u hu)
    have hqSpeed := hspeed' hS B hBrho hB hreg hcomplete eps heps hepsS'
      Z q hq hqDom (fun u hu =>
        (hmove u hu).trans_le (ENNReal.ofReal_le_ofReal (by nlinarith [B.radius_pos])))
    exact hqSpeed.trans (speed_absorb heps hU0le hone)
  have hcompare : ∀ q ∈ Set.Icc (0 : Real) b, ∀ y : M,
      riemannianEDistOf (S.base.metric (time : Real)) B.center y ≤
        ENNReal.ofReal (B.radius / 32) → ∀ v : TangentSpace I y,
      (S.base.metric (time : Real)).inner y v v ≤
        (4 / 3 : Real) * (S.base.metric ((time : Real) - q ^ 2)).inner y v v := by
    intro q hq y hy v
    have hpair := hmetric hS B hB (fun t ht => hreg ⟨ht.1, ht.2.le⟩)
      hcompleteT eps heps hepsM' ((time : Real) - q ^ 2) (htime q hq) y hy v
    have hn := metric_inner_self_nonneg (S.base.metric ((time : Real) - q ^ 2)) y v
    calc
      (S.base.metric (time : Real)).inner y v v =
          Q * (Real.exp (-(2 * n ^ 2 * eps)) *
            (S.base.metric (time : Real)).inner y v v) := by
              rw [← mul_assoc]
              dsimp only [Q]
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Q * (S.base.metric ((time : Real) - q ^ 2)).inner y v v :=
        mul_le_mul_of_nonneg_left hpair.1 hQpos.le
      _ ≤ (4 / 3 : Real) * (S.base.metric ((time : Real) - q ^ 2)).inner y v v :=
        mul_le_mul_of_nonneg_right hQle hn
  have hreach : b * Real.sqrt ((4 / 3 : Real) * (1 / (2048 * eps))) < B.radius / 32 := by
    have hraw := reach_small hbpos heps hbSq.le B.radius_pos
    have heq : Real.sqrt (Real.sqrt (b ^ 2)) * Real.sqrt (b / (1536 * eps)) =
        b * Real.sqrt ((4 / 3 : Real) * (1 / (2048 * eps))) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hbpos]
      rw [show b / (1536 * eps) = b * ((4 / 3 : Real) * (1 / (2048 * eps))) by ring]
      rw [Real.sqrt_mul hbpos.le, ← mul_assoc, ← pow_two, Real.sq_sqrt hbpos.le]
    exact heq ▸ hraw
  obtain ⟨hbdom, hrange⟩ :=
    mem_lRegularizedDomain_and_edist_lt_of_prefix_speed_le S hS (time : Real)
      B.center Z (S.base.metric (time : Real)) b (B.radius / 32) (4 / 3)
      (1 / (2048 * eps)) hbpos.le (div_pos B.radius_pos (by norm_num))
      (by norm_num) hslab hKcompact
      hcompare hspeedBound hreach
  intro s hs
  have hsdom := lRegularizedDomain_segment S (time : Real) B.center Z hbdom hs.1 hs.2
  exact ⟨hsdom, hrange s hs, hKmove s hs (hrange s hs).le⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_lExp_mem_ball :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                  1 / (128 * Real.sqrt eps) →
                lExp S (time : Real) B.center Z (eps * B.radius ^ 2) ∈
                  B.set := by
  obtain ⟨theta, htheta, hthetaOne, hrange⟩ :=
    exists_pos_lRegularizedCurve_mem_ball (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  obtain ⟨eps₀, heps₀, hrange'⟩ := hrange rho hrho
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z hZ
  let b : Real := Real.sqrt eps * B.radius
  have hbpos : 0 < b := mul_pos (Real.sqrt_pos.2 heps) B.radius_pos
  have hb : Real.sqrt (eps * B.radius ^ 2) = b := by
    dsimp only [b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs,
      abs_of_pos B.radius_pos]
  have hrangeB := hrange' hS B hBrho hB hreg hcomplete eps heps heps₀ Z hZ b
    ⟨hbpos.le, le_rfl⟩
  change riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
      (lExp S (time : Real) B.center Z (eps * B.radius ^ 2)) <
        ENNReal.ofReal B.radius
  rw [lExp, hb]
  exact hrangeB.2.1.trans
    ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))

end DifferentialGeometry.PDE.RicciFlow.Perelman
