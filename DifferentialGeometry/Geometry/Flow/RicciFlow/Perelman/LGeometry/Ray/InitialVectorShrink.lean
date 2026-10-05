import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lRegInit_shrink_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (Z : ℕ → TangentSpace I x) (B : ℕ → ℝ)
    (R A : ℝ)
    (hB : ∀ n, 0 < B n) (hBR : ∀ n, B n ≤ R)
    (hslab : Icc (T - R ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - R ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (hdom : ∀ n, B n ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 (B n) ≤ A * B n) :
    Bornology.IsBounded (range Z) := by
  classical
  have hR : 0 ≤ R := (hB 0).le.trans (hBR 0)
  let alpha : ℕ → ℝ → M := fun n ↦ lRegularizedCurve S T x (Z n)
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  have hP : 0 ≤ P := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  let Hkin : ℝ := 2 * (|A| + 2 * R ^ 2 * P)
  have hHkin : 0 ≤ Hkin := by
    dsimp only [Hkin]
    exact mul_nonneg (by norm_num)
      (add_nonneg (abs_nonneg A)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg R)) hP))
  let F : ℝ := Real.exp (2 * P * R ^ 2)
  have hF : 0 < F := Real.exp_pos _
  have hback (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (B n)) :
      T - s ^ 2 ∈ Icc (T - R ^ 2) T := by
    have hs2 : s ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ hs.1 hR).2 (hs.2.trans (hBR n))
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hclock (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (B n)) :
      T - s ^ 2 ∈ D.regular := hslab (hback n s hs)
  have hcurve (n : ℕ) :
      IsLRegularizedCurveOn S T (alpha n) (Icc (0 : ℝ) (B n)) x (Z n) := by
    simpa only [alpha, uIcc_of_le (hB n).le] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x (Z n) (hB n) (hdom n)
  have hc1 (n : ℕ) :
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (Icc (0 : ℝ) (B n)) :=
    lRegularizedCurve_c1On (I := I) S hS T x (Z n) (hdom n)
  have hE (n : ℕ) : IntegrableOn
      (fun s ↦ (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (Icc (0 : ℝ) (B n)) :=
    lRegCurve_reference_integrable (S.base.metric T) (hcurve n)
  have hkinInt (n : ℕ) :
      IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) volume 0 (B n) :=
    intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 (B n) (hB n).le (alpha n) (hc1 n) (hclock n)
  have hLag (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) volume 0 (B n) :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 (B n) (hB n).le (alpha n) (hc1 n) (hclock n)
  have hpot (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (B n)) :
      -2 * R ^ 2 * P ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s) :=
    lRegularizedPot_lower_rm (I := I) S K T R hR hRm s
      ⟨hs.1, hs.2.trans (hBR n)⟩ (alpha n s)
  have hbudget (n : ℕ) :
      2 * (A * B n - (-2 * R ^ 2 * P) * (B n - 0)) ≤ Hkin * B n := by
    have hAbs := mul_le_mul_of_nonneg_right (le_abs_self A) (hB n).le
    dsimp only [Hkin]
    nlinarith only [hAbs]
  have hkinBound (n : ℕ) :
      (∫ s in 0..B n, lRegularizedSpeedSq S T (alpha n) s) ≤ Hkin * B n := by
    exact (lRegularizedKinetic_le (I := I) S T (alpha n) 0 (B n) (A * B n)
      (-2 * R ^ 2 * P) (hB n).le (hpot n)
      (hkinInt n) (hLag n) (hact n)).trans (hbudget n)
  have henergy (n : ℕ) :
      curveEnergy (I := I) (S.base.metric T) (alpha n) 0 (B n) ≤
        F * (Hkin * B n) := by
    have hraw := lRegularizedEnergy_le (I := I) S (S.base.metric T) T (alpha n)
      0 (B n) (A * B n) (-2 * R ^ 2 * P) F (hB n).le hF.le
      (fun s hs v ↦ lRegularizedMetric_le_rm (I := I) S hS K T R hR hslab hRm
        s ⟨hs.1, hs.2.trans (hBR n)⟩ (alpha n s) v)
      (hpot n) (hE n) (hkinInt n) (hLag n) (hact n)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hbudget n) hF.le)
  let Qenergy : ℝ := F * (Hkin * R)
  let radius : ℝ := Real.sqrt R * Real.sqrt Qenergy
  let Cpt : Set M :=
    {y : M | riemannianEDistOf (I := I) (S.base.metric T) x y ≤
      ENNReal.ofReal radius}
  have hCpt : IsCompact Cpt :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hg x radius
  have himage (n : ℕ) : alpha n '' Icc (0 : ℝ) (B n) ⊆ Cpt := by
    rintro y ⟨s, hs, rfl⟩
    have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) (B n) :=
      fun t ht ↦ ⟨ht.1, ht.2.trans hs.2⟩
    have henergyTotal :
        curveEnergy (I := I) (S.base.metric T) (alpha n) 0 (B n) ≤ Qenergy :=
      (henergy n).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hBR n) hHkin) hF.le)
    have hdist := edistOf_le_budget (I := I) (S.base.metric T) hs.1
      ((hc1 n).mono hsub) ((hE n).mono_set hsub)
      ((curveEnergy_mono (I := I) (S.base.metric T)
        le_rfl hs.1 hs.2 (hE n)).trans henergyTotal)
    have hstart : alpha n 0 = x := by simp only [alpha, lRegularizedCurve_zero]
    rw [hstart, sub_zero] at hdist
    exact hdist.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (hs.2.trans (hBR n))) (Real.sqrt_nonneg Qenergy)))
  obtain ⟨Cg, hCg, hgrad⟩ :=
    lScalarGradient_bound_on_compact S hS hslab hCpt
  let C : ℝ := max Cg P
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg P)
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : ℕ ↦ S) univ (T - R ^ 2) T K
    (fun _ t ht y _ ↦ hRm t ht y)
  let e : ℝ := Real.exp ((1 + 2 * C * R ^ 2 + 4 * C * R) * R)
  have he : 0 < e := Real.exp_pos _
  let Qinit : ℝ := e * (Hkin + 1)
  have hmetric (n : ℕ) :
      4 * (S.base.metric T).inner x (Z n) (Z n) ≤ Qinit := by
    let b : ℝ := B n
    have hb : 0 < b := hB n
    have hbR : b ≤ R := hBR n
    have hinit :
        4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤
          Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
            (Hkin * b + b * ((1 + 2 * C * b ^ 2) /
              (1 + 2 * C * b ^ 2 + 4 * C * b))) := by
      apply lRegularizedInitialVector_inner_le_of_integral_speedSq_le (I := I) S hS T b b C b (Hkin * b)
        hb le_rfl le_rfl hC (hcurve n)
      · intro s hs
        have hy : alpha n s ∈ Cpt := himage n ⟨s, hs, rfl⟩
        have h := hgrad (T - s ^ 2) (hback n s hs) (alpha n s) hy
          (lVelocity (I := I) (alpha n) s)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg P)
          (Real.sqrt_nonneg _))
      · intro s hs
        have h := hquad.2 0 (T - s ^ 2) (hback n s hs)
          (alpha n s) (mem_univ _) (lVelocity (I := I) (alpha n) s)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg P)
          (lRegularizedSpeedSq_nonneg (I := I) S T (alpha n) s))
      · exact hkinBound n
    let d : ℝ := 1 + 2 * C * b ^ 2
    let k : ℝ := d + 4 * C * b
    have hd : 0 < d := by
      dsimp only [d]
      nlinarith [mul_nonneg hC (sq_nonneg b)]
    have hk : 0 < k := by
      dsimp only [k]
      nlinarith [hd, mul_nonneg hC hb.le]
    have hratio0 : 0 ≤ d / k := (div_pos hd hk).le
    have hratio1 : d / k ≤ 1 := by
      rw [div_le_one hk]
      dsimp only [k]
      exact le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hC) hb.le)
    have hexp :
        Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) ≤ e := by
      apply Real.exp_le_exp.mpr
      have hb2 : b ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hb.le hR).2 hbR
      have hquadle : 2 * C * b ^ 2 ≤ 2 * C * R ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (mul_nonneg (by norm_num) hC)
      have hlinle : 4 * C * b ≤ 4 * C * R :=
        mul_le_mul_of_nonneg_left hbR (mul_nonneg (by norm_num) hC)
      have hcoef :
          1 + 2 * C * b ^ 2 + 4 * C * b ≤
            1 + 2 * C * R ^ 2 + 4 * C * R := by
        linarith only [hquadle, hlinle]
      have hcoefR : 0 ≤ 1 + 2 * C * R ^ 2 + 4 * C * R := by
        nlinarith [mul_nonneg hC (sq_nonneg R), mul_nonneg hC hR]
      exact mul_le_mul hcoef hbR hb.le hcoefR
    have hterm0 : 0 ≤ Hkin * b + b * (d / k) :=
      add_nonneg (mul_nonneg hHkin hb.le) (mul_nonneg hb.le hratio0)
    have hterm1 : Hkin * b + b * (d / k) ≤ b * (Hkin + 1) := by
      calc
        Hkin * b + b * (d / k) ≤ Hkin * b + b * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio1 hb.le)
        _ = b * (Hkin + 1) := by ring
    apply (mul_le_mul_iff_of_pos_left hb).mp
    calc
      b * (4 * (S.base.metric T).inner x (Z n) (Z n)) =
          4 * b * (S.base.metric T).inner x (Z n) (Z n) := by ring
      _ ≤ Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
          (Hkin * b + b * (d / k)) := by
        simpa only [d, k] using hinit
      _ ≤ e * (b * (Hkin + 1)) :=
        mul_le_mul hexp hterm1 hterm0 he.le
      _ = b * Qinit := by
        dsimp only [Qinit]
        ring
  let c : ℝ := metricCoerciveConst (I := I) (S.base.metric T) x
  have hc : 0 < c := metricCoerciveConst_pos (I := I) (S.base.metric T) x
  let den : ℝ := 4 * c
  have hden : 0 < den := mul_pos (by norm_num) hc
  have hnorm (n : ℕ) : ‖(Z n : E)‖ ≤ Real.sqrt (Qinit / den) := by
    have hcoerc : c * ‖(Z n : E)‖ ^ 2 ≤
        (S.base.metric T).inner x (Z n) (Z n) :=
      metricCoerciveConst_le (I := I) (S.base.metric T) x (Z n)
    have hscaled : den * ‖(Z n : E)‖ ^ 2 ≤ Qinit := by
      calc
        den * ‖(Z n : E)‖ ^ 2 = 4 * (c * ‖(Z n : E)‖ ^ 2) := by
          dsimp only [den]
          ring
        _ ≤ 4 * (S.base.metric T).inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc (by norm_num)
        _ ≤ Qinit := hmetric n
    have hsq : ‖(Z n : E)‖ ^ 2 ≤ Qinit / den := by
      apply (le_div_iff₀ hden).2
      simpa only [mul_comm] using hscaled
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg (Z n : E))] using h
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨Real.sqrt (Qinit / den), ?_⟩
  rintro z ⟨n, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

end DifferentialGeometry.PDE.RicciFlow

end
