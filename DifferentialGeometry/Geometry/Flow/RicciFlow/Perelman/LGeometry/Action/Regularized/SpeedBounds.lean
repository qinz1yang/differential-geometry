import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivativeBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem hasDerivAt_lRegSpeedSq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x} (halpha : IsLRegCurveOn S T alpha J x Z)
    {s : Real} (hs : s ∈ J) :
    HasDerivAt (lRegSpeedSq S T alpha)
      (4 * s ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (alpha s)
            (gradientFun (I := I) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (alpha s))
            (lVelocity (I := I) alpha s) -
        4 * s * S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))) s := by
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  obtain ⟨ht, hmd, hvel, hacc⟩ := halpha.2.2 s hs
  have hinner := lRegInner_deriv (I := I) S hS T alpha A A s ht hmd
    (by simpa only [A] using hvel) (by simpa only [A] using hvel)
  have hforce := lRegAccel_inner (I := I) S T s (alpha s) (A s) (A s)
  rw [hacc] at hinner
  have hsymm :
      (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lRegAccel S T s (alpha s) (A s)) (A s) =
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (A s) (lRegAccel S T s (alpha s) (A s)) :=
    (S.base.metric (T - s ^ 2)).symm (alpha s) _ _
  change HasDerivAt (lRegSpeedSq S T alpha) _ s at hinner ⊢
  rw [hsymm, hforce] at hinner
  simpa only [A] using hinner.congr_deriv (by ring)

private theorem speedDeriv_le
    {s R C U G Q : Real} (hs : |s| ≤ R) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hG : |G| ≤ C * Real.sqrt U) (hQ : |Q| ≤ C * U) :
    |4 * s ^ 2 * G - 4 * s * Q| ≤
      (1 + 2 * C * R ^ 2 + 4 * C * R) * U +
        (1 + 2 * C * R ^ 2) := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hsSq : s ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hs0 hR).2 hs
  have hsqrt : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsqrtSq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hU
  have hsqrtYoung : 2 * Real.sqrt U ≤ U + 1 := by
    nlinarith [sq_nonneg (Real.sqrt U - 1)]
  calc
    |4 * s ^ 2 * G - 4 * s * Q| ≤
        |4 * s ^ 2 * G| + |4 * s * Q| := abs_sub _ _
    _ = 4 * s ^ 2 * |G| + 4 * |s| * |Q| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg s)]
      norm_num
    _ ≤ 4 * R ^ 2 * (C * Real.sqrt U) + 4 * R * (C * U) := by
      gcongr
    _ ≤ (1 + 2 * C * R ^ 2 + 4 * C * R) * U +
        (1 + 2 * C * R ^ 2) := by
      nlinarith [mul_nonneg hC (sq_nonneg R), mul_nonneg hC hR]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegSpeedSq_le_of_gradient_ricci_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x} (halpha : IsLRegCurveOn S T alpha J x Z)
    (a b C R : Real) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hJ : Set.uIcc a b ⊆ J)
    (hsR : ∀ s ∈ Set.uIcc a b, |s| ≤ R)
    (hgrad : ∀ s ∈ Set.uIcc a b,
      |(S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s)| ≤
        C * Real.sqrt (lRegSpeedSq S T alpha s))
    (hric : ∀ s ∈ Set.uIcc a b,
      |S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))| ≤
        C * lRegSpeedSq S T alpha s) :
    lRegSpeedSq S T alpha b ≤
      Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * |b - a|) *
        (lRegSpeedSq S T alpha a +
          (1 + 2 * C * R ^ 2) / (1 + 2 * C * R ^ 2 + 4 * C * R)) := by
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
  have hk : 0 < 1 + 2 * C * R ^ 2 + 4 * C * R := by
    nlinarith [mul_nonneg hC (sq_nonneg R), mul_nonneg hC hR]
  have hd : 0 < 1 + 2 * C * R ^ 2 := by
    nlinarith [mul_nonneg hC (sq_nonneg R)]
  apply DifferentialGeometry.HCGCompactness.affineGronwall_of_abs_deriv_le
    U U' hk hd
  · intro s hs
    exact lRegSpeedSq_nonneg (I := I) S T alpha s
  · intro s hs
    simpa only [U, U'] using
      hasDerivAt_lRegSpeedSq (I := I) S hS T halpha (hJ hs)
  · intro s hs
    apply speedDeriv_le (hsR s hs) hR hC
      (lRegSpeedSq_nonneg (I := I) S T alpha s)
      (hgrad s hs) (hric s hs)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegInitialVector_inner_le_of_integral_speedSq_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : Real → M} {x : M} {Z : TangentSpace I x}
    (B eps C R K : Real) (hB : 0 < B) (hepsB : eps ≤ B)
    (hBR : B ≤ R) (hC : 0 ≤ C)
    (halpha : IsLRegCurveOn S T alpha (Set.Icc 0 B) x Z)
    (hgrad : ∀ s ∈ Set.Icc 0 B,
      |(S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s)| ≤
        C * Real.sqrt (lRegSpeedSq S T alpha s))
    (hric : ∀ s ∈ Set.Icc 0 B,
      |S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))| ≤
        C * lRegSpeedSq S T alpha s)
    (hkin : (∫ s in 0..B, lRegSpeedSq S T alpha s) ≤ K) :
    4 * eps * (S.base.metric T).inner x Z Z ≤
      Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * R) *
        (K + R *
          ((1 + 2 * C * R ^ 2) /
            (1 + 2 * C * R ^ 2 + 4 * C * R))) := by
  let U : Real → Real := lRegSpeedSq S T alpha
  let k : Real := 1 + 2 * C * R ^ 2 + 4 * C * R
  let d : Real := 1 + 2 * C * R ^ 2
  let e : Real := Real.exp (k * R)
  have hR : 0 ≤ R := hB.le.trans hBR
  have hk : 0 < k := by
    dsimp only [k]
    nlinarith [mul_nonneg hC (sq_nonneg R), mul_nonneg hC hR]
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_nonneg hC (sq_nonneg R)]
  have hratio : 0 ≤ d / k := (div_pos hd hk).le
  have hUcont : ContinuousOn U (Set.Icc 0 B) := by
    intro s hs
    exact (hasDerivAt_lRegSpeedSq (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
  have hUcont' : ContinuousOn U (Set.uIcc 0 B) := by
    simpa only [Set.uIcc_of_le hB.le] using hUcont
  have hUint : IntervalIntegrable U MeasureTheory.volume 0 B :=
    hUcont'.intervalIntegrable
  have hpoint : ∀ s ∈ Set.Icc 0 B, U 0 ≤ e * (U s + d / k) := by
    intro s hs
    have hsub : Set.uIcc s 0 ⊆ Set.Icc 0 B := by
      intro r hr
      have hr' : r ∈ Set.Icc 0 s := by
        rw [Set.uIcc_comm, Set.uIcc_of_le hs.1] at hr
        exact hr
      exact ⟨hr'.1, hr'.2.trans hs.2⟩
    have hsr : ∀ r ∈ Set.uIcc s 0, |r| ≤ R := by
      intro r hr
      have hrI := hsub hr
      rw [abs_of_nonneg hrI.1]
      exact hrI.2.trans hBR
    have hgr := lRegSpeedSq_le_of_gradient_ricci_bounds (I := I) S hS T halpha s 0 C R hC hR
      (fun _ hr ↦ hsub hr) hsr
      (fun r hr ↦ hgrad r (hsub hr))
      (fun r hr ↦ hric r (hsub hr))
    have hdist : |(0 : Real) - s| ≤ R := by
      rw [zero_sub, abs_neg, abs_of_nonneg hs.1]
      exact hs.2.trans hBR
    have hexp : Real.exp (k * |(0 : Real) - s|) ≤ e := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hdist hk.le
    have hterm : 0 ≤ U s + d / k :=
      add_nonneg (lRegSpeedSq_nonneg (I := I) S T alpha s) hratio
    calc
      U 0 ≤ Real.exp (k * |(0 : Real) - s|) * (U s + d / k) := by
        simpa only [U, k, d] using hgr
      _ ≤ e * (U s + d / k) :=
        mul_le_mul_of_nonneg_right hexp hterm
  have hconstInt : IntervalIntegrable (fun _ : Real ↦ U 0)
      MeasureTheory.volume 0 B := intervalIntegrable_const
  have hshiftInt : IntervalIntegrable (fun s ↦ U s + d / k)
      MeasureTheory.volume 0 B :=
    hUint.add (intervalIntegrable_const :
      IntervalIntegrable (fun _ : Real ↦ d / k) MeasureTheory.volume 0 B)
  have hrhsInt : IntervalIntegrable (fun s ↦ e * (U s + d / k))
      MeasureTheory.volume 0 B := hshiftInt.const_mul e
  have hmono := intervalIntegral.integral_mono_on hB.le
    hconstInt hrhsInt hpoint
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hUint intervalIntegrable_const,
    intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hmid : B * U 0 ≤ e * (K + B * (d / k)) := by
    calc
      B * U 0 ≤ e * ((∫ s in 0..B, U s) + B * (d / k)) := hmono
      _ ≤ e * (K + B * (d / k)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [add_comm] using add_le_add_right hkin (B * (d / k))
  have hleft : eps * U 0 ≤ B * U 0 :=
    mul_le_mul_of_nonneg_right hepsB
      (lRegSpeedSq_nonneg (I := I) S T alpha 0)
  have hright : e * (K + B * (d / k)) ≤ e * (K + R * (d / k)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact add_le_add_right (mul_le_mul_of_nonneg_right hBR hratio) K
  have hU0 : U 0 = 4 * (S.base.metric T).inner x Z Z := by
    dsimp only [U, lRegSpeedSq]
    norm_num only [zero_pow, sub_zero]
    change (S.base.metric T).inner (alpha 0)
      (lVelocity (I := I) alpha 0) (lVelocity (I := I) alpha 0) = _
    rw [halpha.2.1, halpha.1]
    have htwo : (2 : Nat) • Z = (2 : Real) • Z := by
      simp only [two_smul]
    calc
      (S.base.metric T).inner x ((2 : Nat) • Z) ((2 : Nat) • Z) =
          (S.base.metric T).inner x ((2 : Real) • Z) ((2 : Real) • Z) := by
        rw [htwo]
      _ =
          (2 : Real) * 2 * (S.base.metric T).inner x Z Z :=
        metric_smul2 (I := I) (S.base.metric T) (2 : Real) Z
      _ = 4 * (S.base.metric T).inner x Z Z := by ring
  change 4 * eps * (S.base.metric T).inner x Z Z ≤
    e * (K + R * (d / k))
  calc
    4 * eps * (S.base.metric T).inner x Z Z = eps * U 0 := by
      rw [hU0]
      ring
    _ ≤ e * (K + R * (d / k)) := hleft.trans (hmid.trans hright)

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
