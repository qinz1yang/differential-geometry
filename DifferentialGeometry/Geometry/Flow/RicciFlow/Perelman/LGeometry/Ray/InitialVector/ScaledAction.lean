import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.InitialVector.VariableEndpoint

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bornology Bundle Set MeasureTheory
open scoped ContDiff Manifold Topology

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
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rayInts_shrink
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegDomain S T x Z)
    (hreg : ∀ s ∈ Set.Icc (0 : Real) B, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegSpeedSq S T (lRegCurve S T x Z)) volume 0 B ∧
      IntervalIntegrable (lRegLagrangian S T (lRegCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegCurve S T x Z
  have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) B) x Z := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegCurve_isReg (I := I) S hS T x Z hB hdom
  have hkinCont : ContinuousOn (lRegSpeedSq S T alpha)
      (Set.Icc (0 : Real) B) := by
    intro s hs
    exact (hasDerivAt_lRegSpeedSq (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
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
    have heq : ((fun s : Real ↦ 2 * s ^ 2) *
        fun s : Real ↦ S.scalar (T - s ^ 2) (alpha s)) =
        fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) := by
      funext s
      rfl
    rw [heq] at hpotCont'
    simpa only [Set.uIcc_of_le hB.le] using hpotCont'
  have hpot : IntervalIntegrable
      (fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume 0 B := hpotCont.intervalIntegrable
  refine ⟨?_, ?_⟩
  · simpa only [alpha] using hkin
  · change IntervalIntegrable (fun s : Real ↦
      (1 / 2 : Real) * lRegSpeedSq S T alpha s +
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume 0 B
    exact (hkin.const_mul (1 / 2 : Real)).add hpot

omit [InnerProductSpace Real E] in
theorem lRegInit_shrink
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B : Nat → Real)
    (R A : Real) (hB : ∀ n, 0 < B n) (hBR : ∀ n, B n ≤ R)
    (hslab : Set.Icc (T - R ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B n ∈ lRegDomain S T x (Z n))
    (hact : ∀ n,
      lRegAction S T (lRegCurve S T x (Z n)) 0 (B n) ≤ A * B n) :
    Bornology.IsBounded (Set.range Z) := by
  have hR : 0 ≤ R := (hB 0).le.trans (hBR 0)
  obtain ⟨Cg, hCg, hgrad⟩ := lGrad_bound (I := I) S hS hslab
  obtain ⟨Cr, hCr, hric⟩ := lRicci_bound (I := I) S hS hslab
  let C : Real := max Cg Cr
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg Cr)
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  obtain ⟨Cp, hpot⟩ := exists_uniform_lower_bound_lRegPotential (I := I) S hSc T 0 R (by
    intro s hs
    have hsI : s ∈ Set.Icc (0 : Real) R := by
      simpa only [Set.uIcc_of_le hR] using hs
    have hsSq : s ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hsI.1 hR).2 hsI.2
    exact D.regular_subset (hslab
      ⟨sub_le_sub_left hsSq T, sub_le_self T (sq_nonneg s)⟩))
  let c : Real := 2 * (|A| + |Cp|) + 1
  let e : Real :=
    Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * R)
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have he : 0 < e := Real.exp_pos _
  have hmetric : ∀ n,
      4 * (S.base.metric T).inner x (Z n) (Z n) ≤ e * c := by
    intro n
    let b : Real := B n
    let alpha : Real → M := lRegCurve S T x (Z n)
    have hb : 0 < b := hB n
    have hbR : b ≤ R := hBR n
    have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) b) x (Z n) := by
      simpa only [alpha, Set.uIcc_of_le hb.le] using
        lRegCurve_isReg (I := I) S hS T x (Z n) hb (hdom n)
    have hback : ∀ s ∈ Set.Icc (0 : Real) b,
        T - s ^ 2 ∈ Set.Icc (T - R ^ 2) T := by
      intro s hs
      have hsR : s ∈ Set.Icc (0 : Real) R := ⟨hs.1, hs.2.trans hbR⟩
      have hsSq : s ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hsR.1 hR).2 hsR.2
      exact ⟨sub_le_sub_left hsSq T,
        sub_le_self T (sq_nonneg s)⟩
    have hreg : ∀ s ∈ Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular :=
      fun s hs ↦ hslab (hback s hs)
    obtain ⟨hkinInt, hlagInt⟩ := rayInts_shrink (I := I) S hS T x
      (Z n) hb (hdom n) (fun s hs ↦ hreg s (by
        simpa only [Set.uIcc_of_le hb.le] using hs))
    have hkin :
        (∫ s in 0..b, lRegSpeedSq S T alpha s) ≤
          2 * (A + |Cp|) * b := by
      have hraw := lRegKinetic_le (I := I) S T alpha 0 b (A * b) Cp hb.le
        (fun s hs ↦ hpot s (by
          rw [Set.uIcc_of_le hR]
          exact ⟨hs.1, hs.2.trans hbR⟩) (alpha s))
        hkinInt hlagInt (by simpa only [alpha, b] using hact n)
      calc
        (∫ s in 0..b, lRegSpeedSq S T alpha s) ≤
            2 * (A * b - Cp * (b - 0)) := hraw
        _ ≤ 2 * (A + |Cp|) * b := by
          have hCp : -Cp ≤ |Cp| := neg_le_abs Cp
          nlinarith
    have hinit := lRegInitialVector_inner_le_of_integral_speedSq_le (I := I) S hS T b b C b
      (2 * (A + |Cp|) * b) hb le_rfl le_rfl hC halpha
      (fun s hs ↦ by
        have h := hgrad (T - s ^ 2) (hback s hs) (alpha s)
            (lVelocity (I := I) alpha s)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg Cr)
          (Real.sqrt_nonneg _)))
      (fun s hs ↦ by
        have h := hric (T - s ^ 2) (hback s hs) (alpha s)
            (lVelocity (I := I) alpha s)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg Cr)
          (lRegSpeedSq_nonneg (I := I) S T alpha s))) hkin
    let d : Real := 1 + 2 * C * b ^ 2
    let k : Real := d + 4 * C * b
    have hd : 0 < d := by
      dsimp only [d]
      nlinarith [mul_nonneg hC (sq_nonneg b)]
    have hk : 0 < k := by
      dsimp only [k]
      nlinarith [hd, mul_nonneg hC hb.le]
    have hratio : d / k ≤ 1 := by
      rw [div_le_one hk]
      dsimp only [k]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hC) hb.le)
    have hexp :
        Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) ≤ e := by
      apply Real.exp_le_exp.mpr
      have hb2 : b ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hb.le hR).2 hbR
      have hquad : 2 * C * b ^ 2 ≤ 2 * C * R ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (mul_nonneg (by norm_num) hC)
      have hlin : 4 * C * b ≤ 4 * C * R :=
        mul_le_mul_of_nonneg_left hbR (mul_nonneg (by norm_num) hC)
      have hcoef :
          1 + 2 * C * b ^ 2 + 4 * C * b ≤
            1 + 2 * C * R ^ 2 + 4 * C * R := by
        linarith
      have hcoefR : 0 ≤ 1 + 2 * C * R ^ 2 + 4 * C * R := by
        nlinarith [mul_nonneg hC (sq_nonneg R), mul_nonneg hC hR]
      exact (mul_le_mul hcoef hbR hb.le hcoefR).trans_eq rfl
    have hterm :
        0 ≤ 2 * (A + |Cp|) + d / k := by
      have hscaled :
          0 ≤ Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
            (2 * (A + |Cp|) + d / k) := by
        have hleft : 0 ≤ 4 * b * (S.base.metric T).inner x (Z n) (Z n) :=
          mul_nonneg (mul_nonneg (by norm_num) hb.le)
            (metric_inner_self_nonneg (I := I) (M := M)
              (S.base.metric T) x (Z n))
        have hraw := hleft.trans hinit
        have hfact :
            0 ≤ Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
              (b * (2 * (A + |Cp|) + d / k)) := by
          have heq :
              2 * (A + |Cp|) * b +
                  b * ((1 + 2 * C * b ^ 2) /
                    (1 + 2 * C * b ^ 2 + 4 * C * b)) =
                b * (2 * (A + |Cp|) + d / k) := by
            change 2 * (A + |Cp|) * b +
                b * ((1 + 2 * C * b ^ 2) /
                  (1 + 2 * C * b ^ 2 + 4 * C * b)) =
              b * (2 * (A + |Cp|) +
                (1 + 2 * C * b ^ 2) /
                  (1 + 2 * C * b ^ 2 + 4 * C * b))
            ring
          rw [← heq]
          exact hraw
        have hbterm : 0 ≤ b * (2 * (A + |Cp|) + d / k) :=
          nonneg_of_mul_nonneg_right hfact (Real.exp_pos _)
        have hterm0 : 0 ≤ 2 * (A + |Cp|) + d / k :=
          nonneg_of_mul_nonneg_right hbterm hb
        exact mul_nonneg (Real.exp_pos _).le hterm0
      exact nonneg_of_mul_nonneg_right hscaled (Real.exp_pos _)
    have htermLe : 2 * (A + |Cp|) + d / k ≤ c := by
      dsimp only [c]
      nlinarith [le_abs_self A, hratio]
    have hscaled :
        4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤
          e * (b * c) := by
      calc
        4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤
            Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
              (2 * (A + |Cp|) * b +
                b * ((1 + 2 * C * b ^ 2) /
                  (1 + 2 * C * b ^ 2 + 4 * C * b))) := hinit
        _ = Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
              (b * (2 * (A + |Cp|) + d / k)) := by
          simp only [d, k]
          ring
        _ ≤ e * (b * (2 * (A + |Cp|) + d / k)) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg hb.le hterm)
        _ ≤ e * (b * c) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htermLe hb.le) he.le
    have hscaled' :
        b * (4 * (S.base.metric T).inner x (Z n) (Z n)) ≤
          b * (e * c) := by
      calc
        b * (4 * (S.base.metric T).inner x (Z n) (Z n)) =
            4 * b * (S.base.metric T).inner x (Z n) (Z n) := by ring
        _ ≤ e * (b * c) := hscaled
        _ = b * (e * c) := by ring
    exact (mul_le_mul_iff_of_pos_left hb).mp hscaled'
  let q : Real := e * c
  let g := S.base.metric T
  let a : Real := gpCoerciveConst (I := I) g x
  have ha : 0 < a := gpCoerciveConst_pos (I := I) g x
  let L : Real := Real.sqrt (q / (4 * a))
  have hnorm : ∀ n, ‖Z n‖ ≤ L := by
    intro n
    have hcoerc : a * ‖Z n‖ ^ 2 ≤ g.inner x (Z n) (Z n) := by
      with_unfolding_all exact gpCoerciveConst_le (I := I) g x (Z n)
    have hsq : ‖Z n‖ ^ 2 ≤ q / (4 * a) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) ha)]
      calc
        ‖Z n‖ ^ 2 * (4 * a) = 4 * (a * ‖Z n‖ ^ 2) := by ring
        _ ≤ 4 * g.inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc (by norm_num)
        _ ≤ q := by simpa only [q, g] using hmetric n
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [L, Real.sqrt_sq (norm_nonneg (Z n))] using hsqrt
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨L, ?_⟩
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

end DifferentialGeometry.PDE.RicciFlow.Perelman
