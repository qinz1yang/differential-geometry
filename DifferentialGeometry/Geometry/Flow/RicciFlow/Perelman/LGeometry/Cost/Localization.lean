import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.SmoothAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

omit [CompactSpace M] in
private theorem metric_upper_from_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (C T b : ℝ) (hb : 0 ≤ b) (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (s : ℝ) (hs : s ∈ Icc 0 b) (x : M) (v : TangentSpace I x) :
    (S.base.metric (T - s ^ 2)).inner x v v ≤
      Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
        (S.base.metric T).inner x v v := by
  have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
  have ht : T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    constructor <;> linarith [sq_nonneg s]
  have hT : T ∈ Icc (T - b ^ 2) T := ⟨sub_le_self T (sq_nonneg b), le_rfl⟩
  have hm := (metric_inner_exp_bounds_of_curvature_bound S hS
    (hreg.trans D.regular_subset) (Ioo_subset_Icc_self.trans hreg) x
    (fun t ht => hRm t ht x) ht hT v).2
  have heq : |T - s ^ 2 - T| = s ^ 2 := by
    rw [show T - s ^ 2 - T = -(s ^ 2) by ring, abs_neg, abs_of_nonneg (sq_nonneg s)]
  rw [heq] at hm
  refine hm.trans (mul_le_mul_of_nonneg_right ?_
    (DifferentialGeometry.metric_inner_self_nonneg _ _ _))
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs2 (by positivity))

omit [I.Boundaryless] [CompactSpace M] in
private theorem lagrangian_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T b : ℝ) (hb : 0 ≤ b) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T α) volume 0 b := by
  have hmap : ContinuousOn (fun s : ℝ => (T, s)) (Icc 0 b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : MapsTo (fun s : ℝ => (T, s)) (Icc 0 b)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := htime
  exact ((lRegularizedLagrangian_continuousOn_carrier (I := I) (M := M) (D := D)
    S hS α hα).comp (f := fun s : ℝ => (T, s)) hmap hmaps).intervalIntegrable_of_Icc hb

omit [CompactSpace M] in
private theorem action_upper_from_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (C T b : ℝ) (hb : 0 ≤ b) (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) :
    lRegularizedAction S T α 0 b ≤
      (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) / 2) *
        curveEnergy (S.base.metric T) α 0 b +
      2 * b ^ 3 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C := by
  let Q := Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2)
  let R := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have ht : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply D.regular_subset (hreg _)
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
    constructor <;> linarith [sq_nonneg s]
  have hLag := lagrangian_integrable S hS T b hb α hα ht
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn (S.base.metric T) hα.contMDiffOn
    (a := 0) (b := b)
  have hEi : IntervalIntegrable (fun s => (S.base.metric T).inner (α s)
      (lVelocity α s) (lVelocity α s)) volume 0 b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hb, lVelocity] using hE
  have hp : ∀ s ∈ Icc 0 b, lRegularizedLagrangian S T α s ≤
      (Q / 2) * (S.base.metric T).inner (α s) (lVelocity α s) (lVelocity α s) + 2 * b ^ 2 * R := by
    intro s hs
    have hm := metric_upper_from_curvature S hS C T b hb hreg hRm s hs (α s) (lVelocity α s)
    have hpot := lRegularizedPot_upper_rm S C T b hb hRm s hs (α s)
    change 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s) ≤ 2 * b ^ 2 * R at hpot
    unfold lRegularizedLagrangian
    dsimp only [Q] at *
    nlinarith only [hm, hpot]
  have hi := intervalIntegral.integral_mono_on hb hLag
    ((hEi.const_mul (Q / 2)).add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_add (hEi.const_mul (Q / 2)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  change lRegularizedAction S T α 0 b ≤ _ at hi
  simp only [sub_zero, smul_eq_mul] at hi
  convert hi using 1
  dsimp only [Q, R, curveEnergy, lVelocity]
  ring

theorem exists_contMDiff_lCost_minimizer_in_ball_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (C T b r : ℝ) (hb : 0 < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ b = y)
    (hgap : Real.sqrt b * Real.sqrt
      (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
        (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
          curveEnergy (S.base.metric T) α₀ 0 b +
          8 * b ^ 3 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C)) < r) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α 0 = x ∧ α b = y ∧
      lLength S T (squareRootReparametrization α) 0 (b ^ 2) = lCost S T x y (b ^ 2) ∧
      ∀ s ∈ Icc 0 b, riemannianEDistOf (S.base.metric T) x (α s) < ENNReal.ofReal r := by
  have ht : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply D.regular_subset (hreg _)
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
    constructor <;> linarith [sq_nonneg s]
  obtain ⟨α, hα, h0, h1, hmin⟩ := exists_contMDiff_lCost_minimizer S hS T (b ^ 2)
    (sq_pos_of_pos hb) hreg x y α₀ hα₀ h₀ (by simpa only [Real.sqrt_sq hb.le] using h₁)
  rw [Real.sqrt_sq hb.le] at h1
  let Q := Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2)
  let R := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  let A := (Q / 2) * curveEnergy (S.base.metric T) α₀ 0 b + 2 * b ^ 3 * R
  have hcost : lCost S T x y (b ^ 2) ≤ lRegularizedAction S T α₀ 0 b := by
    have heq : lLength S T (squareRootReparametrization α₀) 0 (b ^ 2) =
        lRegularizedAction S T α₀ 0 b := by
      simpa only [Real.sqrt_sq hb.le] using
        lLength_squareRootReparametrization_eq_lRegularizedAction S T α₀ (b ^ 2) (sq_nonneg b)
    rw [← heq]
    apply csInf_le
    · exact lCost_competitors_bddBelow_of_rm_on_carrier S hS C T b hb.le x y ht hRm
    · exact ⟨α₀, hα₀, h₀, by simpa only [Real.sqrt_sq hb.le] using h₁, rfl⟩
  have hact : lRegularizedAction S T α 0 b ≤ A := by
    have heq : lLength S T (squareRootReparametrization α) 0 (b ^ 2) =
        lRegularizedAction S T α 0 b := by
      simpa only [Real.sqrt_sq hb.le] using
        lLength_squareRootReparametrization_eq_lRegularizedAction S T α (b ^ 2) (sq_nonneg b)
    rw [← heq, hmin]
    apply hcost.trans
    simpa only [A, Q, R, mul_assoc] using
      action_upper_from_curvature S hS C T b hb.le hreg hRm α₀ hα₀
  have hstay := riemannianEDistOf_lt_of_lRegularizedAction_le S hS (S.base.metric T)
    T b A (-2 * b ^ 2 * R) Q r hb.le (Real.exp_pos _).le α (hα.of_le (by simp)) ht
    (fun s hs z _ v => by
      have h := lRegularizedMetric_le_rm S hS C T b hb.le hreg hRm s hs z v
      change (S.base.metric T).inner z v v ≤
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C) * b ^ 2) *
          (S.base.metric (T - s ^ 2)).inner z v v at h
      simpa only [Q, mul_assoc] using h)
    (fun s hs => lRegularizedPot_lower_rm S C T b hb.le hRm s hs (α s)) hact ?_
  · refine ⟨α, hα, h0, h1, hmin, ?_⟩
    intro s hs
    simpa only [h0] using hstay s hs
  · convert hgap using 1
    dsimp only [A, Q, R]
    congr 2
    ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
