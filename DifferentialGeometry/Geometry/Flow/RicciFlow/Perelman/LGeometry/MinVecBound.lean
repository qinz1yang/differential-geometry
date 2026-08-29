import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMaxAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayGlobalize

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E]
  [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRayAction_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegDomain S T x Z)
    (hreg : ∀ s ∈ Set.Icc (0 : Real) B, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegSpeedSq S T (lRegCurve S T x Z)) volume 0 B ∧
      IntervalIntegrable (lRegLag S T (lRegCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegCurve S T x Z
  have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) B) x Z := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegCurve_isReg (I := I) S hS T x Z hB hdom
  have hkinCont : ContinuousOn (lRegSpeedSq S T alpha)
      (Set.Icc (0 : Real) B) := by
    intro s hs
    exact (lRegSpeedSq_deriv (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
  have hkin : IntervalIntegrable (lRegSpeedSq S T alpha) volume 0 B := by
    have hkinCont' : ContinuousOn (lRegSpeedSq S T alpha)
        (Set.uIcc (0 : Real) B) := by
      simpa only [Set.uIcc_of_le hB.le] using hkinCont
    exact hkinCont'.intervalIntegrable
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have halphaCont : ContinuousOn alpha (Set.Icc (0 : Real) B) :=
    (lRegCurve_c1On (I := I) S hS T x Z hdom).continuousOn
  have hpair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halphaCont
  have hmaps : Set.MapsTo (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro s hs
    exact ⟨D.regular_subset (hreg s hs), Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun s : Real ↦ S.scalar (T - s ^ 2) (alpha s))
      (Set.Icc (0 : Real) B) := by
    simpa only [Function.comp_def] using
      hSc.scalar_continuousOn.comp hpair hmaps
  have hpotCont : ContinuousOn
      (fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      (Set.uIcc (0 : Real) B) := by
    have hcoef : Continuous (fun s : Real ↦ 2 * s ^ 2) :=
      continuous_const.mul (continuous_id.pow 2)
    have hpotCont' := hcoef.continuousOn.mul hscalar
    rw [Set.uIcc_of_le hB.le]
    with_unfolding_all exact hpotCont'
  have hpot : IntervalIntegrable
      (fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume 0 B := hpotCont.intervalIntegrable
  refine ⟨?_, ?_⟩
  · simpa only [alpha] using hkin
  · with_unfolding_all exact
      (hkin.const_mul (1 / 2 : Real)).add hpot

omit [InnerProductSpace Real E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private theorem initNorm_bdd
    (g : SmoothRiemannianMetric I M) (x : M)
    (Z : Nat → TangentSpace I x) (w Q : Real) (hw : 0 < w)
    (hmetric : ∀ n, w * g.inner x (Z n) (Z n) ≤ Q) :
    Bornology.IsBounded (Set.range Z) := by
  let c : Real := gpCoerciveConst (I := I) g x
  have hc : 0 < c := gpCoerciveConst_pos (I := I) g x
  let d : Real := w * c
  have hd : 0 < d := mul_pos hw hc
  let R : Real := Real.sqrt (Q / d)
  have hnorm : ∀ n, ‖Z n‖ ≤ R := by
    intro n
    have hcoerc : c * ‖Z n‖ ^ 2 ≤ g.inner x (Z n) (Z n) := by
      with_unfolding_all exact gpCoerciveConst_le (I := I) g x (Z n)
    have hscaled : d * ‖Z n‖ ^ 2 ≤ Q := by
      calc
        d * ‖Z n‖ ^ 2 = w * (c * ‖Z n‖ ^ 2) := by
          simp only [d]
          ring
        _ ≤ w * g.inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc hw.le
        _ ≤ Q := hmetric n
    have hsq : ‖Z n‖ ^ 2 ≤ Q / d := by
      rw [le_div_iff₀ hd]
      simpa only [mul_comm] using hscaled
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [R, Real.sqrt_sq (norm_nonneg (Z n))] using hsqrt
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨R, ?_⟩
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRayMetric_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B A : Real) (hB : 0 < B)
    (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B ∈ lRegDomain S T x (Z n))
    (hact : ∀ n,
      lRegAction S T (lRegCurve S T x (Z n)) 0 B ≤ A) :
    ∃ Q : Real, ∀ n,
      4 * B * (S.base.metric T).inner x (Z n) (Z n) ≤ Q := by
  have hback : ∀ s ∈ Set.Icc (0 : Real) B,
      T - s ^ 2 ∈ Set.Icc (T - B ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hs.1 hB.le).2 hs.2
    exact ⟨sub_le_sub_left hsq T, sub_le_self T (sq_nonneg s)⟩
  have hreg : ∀ s ∈ Set.Icc (0 : Real) B, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ hslab (hback s hs)
  obtain ⟨Cg, hCg, hgrad⟩ := lGrad_bound (I := I) S hS hslab
  obtain ⟨Cr, hCr, hric⟩ := lRicci_bound (I := I) S hS hslab
  let C : Real := max Cg Cr
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg Cr)
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  obtain ⟨Cp, hkinBound⟩ :=
    lRegKinetic_bound (I := I) S hSc T 0 B A hB.le (by
      intro s hs
      exact D.regular_subset (hreg s hs))
  let K : Real := 2 * (A - Cp * (B - 0))
  let Q : Real :=
    Real.exp ((1 + 2 * C * B ^ 2 + 4 * C * B) * B) *
      (K + B * ((1 + 2 * C * B ^ 2) /
        (1 + 2 * C * B ^ 2 + 4 * C * B)))
  refine ⟨Q, ?_⟩
  intro n
  let alpha : Real → M := lRegCurve S T x (Z n)
  have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) B) x (Z n) := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegCurve_isReg (I := I) S hS T x (Z n) hB (hdom n)
  obtain ⟨hkin, hLag⟩ :=
    lRayAction_int (I := I) S hS T x (Z n) hB (hdom n) hreg
  have hkinLe :
      (∫ s in 0..B, lRegSpeedSq S T alpha s) ≤ K := by
    simpa only [alpha, K] using hkinBound alpha hkin hLag (hact n)
  apply lRegInit_bdd (I := I) S hS T B B C B K hB le_rfl le_rfl hC halpha
  · intro s hs
    have h := hgrad (T - s ^ 2) (hback s hs) (alpha s)
      (lVelocity (I := I) alpha s)
    have hconst := mul_le_mul_of_nonneg_right (le_max_left Cg Cr)
      (Real.sqrt_nonneg (lRegSpeedSq S T alpha s))
    exact h.trans (by simpa only [C, lRegSpeedSq] using hconst)
  · intro s hs
    have h := hric (T - s ^ 2) (hback s hs) (alpha s)
      (lVelocity (I := I) alpha s)
    have hconst := mul_le_mul_of_nonneg_right (le_max_right Cg Cr)
      (lRegSpeedSq_nonneg (I := I) S T alpha s)
    exact h.trans (by simpa only [C, lRegSpeedSq] using hconst)
  · exact hkinLe

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
theorem lRegInit_bound
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B A : Real) (hB : 0 < B)
    (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B ∈ lRegDomain S T x (Z n))
    (hact : ∀ n,
      lRegAction S T (lRegCurve S T x (Z n)) 0 B ≤ A) :
    Bornology.IsBounded (Set.range Z) := by
  obtain ⟨Q, hQ⟩ := lRayMetric_bdd (I := I) S hS T x Z B A hB
    hslab hdom hact
  exact initNorm_bdd (I := I) (S.base.metric T) x Z (4 * B) Q
    (mul_pos (by norm_num) hB) hQ

end DifferentialGeometry.PDE.RicciFlow.Perelman
