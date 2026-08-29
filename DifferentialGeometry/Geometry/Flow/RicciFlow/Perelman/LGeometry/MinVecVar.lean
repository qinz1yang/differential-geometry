import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMaxAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayGlobalize

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian

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
private theorem lRayInts_var
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E]
  [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRayMetric_var
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) (B eps C R A Cp : Real)
    (hB : 0 < B) (hepsB : eps ≤ B) (hBR : B ≤ R) (hC : 0 ≤ C)
    (hdom : B ∈ lRegDomain S T x Z)
    (hback : ∀ s ∈ Set.Icc (0 : Real) B,
      T - s ^ 2 ∈ Set.Icc (T - R ^ 2) T)
    (hreg : ∀ s ∈ Set.Icc (0 : Real) B, T - s ^ 2 ∈ D.regular)
    (hpot : ∀ s ∈ Set.Icc (0 : Real) B, ∀ y : M,
      Cp ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) y)
    (hgrad : ∀ t ∈ Set.Icc (T - R ^ 2) T, ∀ y (v : TangentSpace I y),
      |(S.base.metric t).inner y
          (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v| ≤
        C * Real.sqrt ((S.base.metric t).inner y v v))
    (hric : ∀ t ∈ Set.Icc (T - R ^ 2) T, ∀ y (v : TangentSpace I y),
      |S.ricciAt t y (vec2 v v)| ≤ C * (S.base.metric t).inner y v v)
    (hact : lRegAction S T (lRegCurve S T x Z) 0 B ≤ A) :
    4 * eps * (S.base.metric T).inner x Z Z ≤
      Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * R) *
        (2 * (A + |Cp| * R) + R *
          ((1 + 2 * C * R ^ 2) /
            (1 + 2 * C * R ^ 2 + 4 * C * R))) := by
  let alpha : Real → M := lRegCurve S T x Z
  have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) B) x Z := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegCurve_isReg (I := I) S hS T x Z hB hdom
  obtain ⟨hkin, hLag⟩ := lRayInts_var (I := I) S hS T x Z hB hdom hreg
  have hkinRaw := lRegKinetic_le (I := I) S T alpha 0 B A Cp hB.le
    (fun s hs ↦ hpot s hs (alpha s))
    (by simpa only [alpha] using hkin) (by simpa only [alpha] using hLag) hact
  have hCpB : -Cp * B ≤ |Cp| * R := by
    calc
      -Cp * B ≤ |Cp| * B :=
        mul_le_mul_of_nonneg_right (neg_le_abs Cp) hB.le
      _ ≤ |Cp| * R :=
        mul_le_mul_of_nonneg_left hBR (abs_nonneg Cp)
  have hkinLe : (∫ s in 0..B, lRegSpeedSq S T alpha s) ≤
      2 * (A + |Cp| * R) := by
    apply hkinRaw.trans
    linarith
  apply lRegInit_bdd (I := I) S hS T B eps C R
    (2 * (A + |Cp| * R)) hB hepsB hBR hC halpha
  · intro s hs
    simpa only [alpha, lRegSpeedSq] using
      hgrad (T - s ^ 2) (hback s hs) (alpha s)
        (lVelocity (I := I) alpha s)
  · intro s hs
    simpa only [alpha, lRegSpeedSq] using
      hric (T - s ^ 2) (hback s hs) (alpha s)
        (lVelocity (I := I) alpha s)
  · exact hkinLe

omit [InnerProductSpace Real E]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private theorem metricRange_bdd
    (g : SmoothRiemannianMetric I M) (x : M)
    (Z : Nat → TangentSpace I x)
    (eps Q : Real) (heps : 0 < eps)
    (hmetric : ∀ n, 4 * eps * g.inner x (Z n) (Z n) ≤ Q) :
    Bornology.IsBounded (Set.range Z) := by
  let c : Real := gpCoerciveConst (I := I) g x
  have hc : 0 < c := gpCoerciveConst_pos (I := I) g x
  let d : Real := 4 * eps * c
  have hd : 0 < d := mul_pos (mul_pos (by norm_num) heps) hc
  let L : Real := Real.sqrt (Q / d)
  have hnorm : ∀ n, ‖Z n‖ ≤ L := by
    intro n
    have hcoerc : c * ‖Z n‖ ^ 2 ≤ g.inner x (Z n) (Z n) := by
      with_unfolding_all exact gpCoerciveConst_le (I := I) g x (Z n)
    have hscaled : d * ‖Z n‖ ^ 2 ≤ Q := by
      calc
        d * ‖Z n‖ ^ 2 = 4 * eps * (c * ‖Z n‖ ^ 2) := by
          simp only [d]
          ring
        _ ≤ 4 * eps * g.inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc
            (mul_nonneg (by norm_num) heps.le)
        _ ≤ Q := hmetric n
    have hsq : ‖Z n‖ ^ 2 ≤ Q / d := by
      rw [le_div_iff₀ hd]
      simpa only [mul_comm] using hscaled
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [L, Real.sqrt_sq (norm_nonneg (Z n))] using hsqrt
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨L, ?_⟩
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

omit [InnerProductSpace Real E]
  [SigmaCompactSpace M] in
theorem lRegInit_var
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B : Nat → Real)
    (eps R A : Real) (heps : 0 < eps)
    (hepsB : ∀ n, eps ≤ B n) (hBR : ∀ n, B n ≤ R)
    (hslab : Set.Icc (T - R ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B n ∈ lRegDomain S T x (Z n))
    (hact : ∀ n,
      lRegAction S T (lRegCurve S T x (Z n)) 0 (B n) ≤ A) :
    Bornology.IsBounded (Set.range Z) := by
  have hBn (n : Nat) : 0 < B n := heps.trans_le (hepsB n)
  have hR : 0 ≤ R := (hBn 0).le.trans (hBR 0)
  have hbackR : ∀ s ∈ Set.Icc (0 : Real) R,
      T - s ^ 2 ∈ Set.Icc (T - R ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hs.1 hR).2 hs.2
    exact ⟨sub_le_sub_left hsq T, sub_le_self T (sq_nonneg s)⟩
  obtain ⟨Cg, hCg, hgrad⟩ := lGrad_bound (I := I) S hS hslab
  obtain ⟨Cr, hCr, hric⟩ := lRicci_bound (I := I) S hS hslab
  let C : Real := max Cg Cr
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg Cr)
  have hgradC : ∀ t ∈ Set.Icc (T - R ^ 2) T,
      ∀ y (v : TangentSpace I y),
      |(S.base.metric t).inner y
          (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v| ≤
        C * Real.sqrt ((S.base.metric t).inner y v v) := by
    intro t ht y v
    exact (hgrad t ht y v).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cg Cr) (Real.sqrt_nonneg _))
  have hricC : ∀ t ∈ Set.Icc (T - R ^ 2) T,
      ∀ y (v : TangentSpace I y),
      |S.ricciAt t y (vec2 v v)| ≤ C * (S.base.metric t).inner y v v := by
    intro t ht y v
    have hvv : 0 ≤ (S.base.metric t).inner y v v :=
      metric_inner_self_nonneg (I := I) (M := M) (S.base.metric t) y v
    exact (hric t ht y v).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cg Cr) hvv)
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  obtain ⟨Cp, hpot⟩ := lScalar_lower (I := I) S hSc T 0 R (by
    intro s hs
    have hsI : s ∈ Set.Icc (0 : Real) R := by
      simpa only [Set.uIcc_of_le hR] using hs
    exact D.regular_subset (hslab (hbackR s hsI)))
  let Q : Real :=
    Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * R) *
      (2 * (A + |Cp| * R) + R *
        ((1 + 2 * C * R ^ 2) /
          (1 + 2 * C * R ^ 2 + 4 * C * R)))
  have hmetric : ∀ n,
      4 * eps * (S.base.metric T).inner x (Z n) (Z n) ≤ Q := by
    intro n
    have hback : ∀ s ∈ Set.Icc (0 : Real) (B n),
        T - s ^ 2 ∈ Set.Icc (T - R ^ 2) T :=
      fun s hs ↦ hbackR s ⟨hs.1, hs.2.trans (hBR n)⟩
    have hreg : ∀ s ∈ Set.Icc (0 : Real) (B n),
        T - s ^ 2 ∈ D.regular :=
      fun s hs ↦ hslab (hback s hs)
    apply lRayMetric_var (I := I) S hS T x (Z n) (B n) eps C R A Cp
      (hBn n) (hepsB n) (hBR n) hC (hdom n) hback hreg
      (fun s hs y ↦ hpot s (by
        rw [Set.uIcc_of_le hR]
        exact ⟨hs.1, hs.2.trans (hBR n)⟩) y)
      hgradC hricC (hact n)
  exact metricRange_bdd (I := I) (S.base.metric T) x Z eps Q heps hmetric

end DifferentialGeometry.PDE.RicciFlow.Perelman
