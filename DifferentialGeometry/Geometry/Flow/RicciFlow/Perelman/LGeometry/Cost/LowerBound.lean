import DifferentialGeometry.Analysis.Integration.Integral.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Metric.CurveEnergy

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private def actionRmFactor (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

omit [NeZero (Module.finrank Real E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem regularitySpeed_int_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedSpeedSq S T alpha) volume a b := by
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha halpha hreg
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [uIcc_of_le hab] using halpha.continuousOn)
  have hhalf : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s) volume a b := by
    convert hLag.sub hpot using 1
    funext s
    unfold lRegularizedLagrangian lRegularizedSpeedSq
    ring
  have htwice := hhalf.const_mul 2
  convert htwice using 1
  funext s
  ring

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRegularizedCosts_bdd_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) :
    BddBelow {r : Real | ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r} := by
  let C : Real := -2 * b ^ 2 * actionRmFactor E K
  have hb : 0 ≤ b := ha.trans hab
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  refine ⟨C * (b - a), ?_⟩
  intro r hr
  obtain ⟨alpha, halpha, _hstart, _hend, rfl⟩ := hr
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hkin := regularitySpeed_int_c1 (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hbound := lRegularizedKinetic_le (I := I) S T alpha a b
    (lRegularizedAction S T alpha a b) C hab
    (fun s hs ↦ lRegularizedPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s))
    hkin hLag le_rfl
  have hnonneg : 0 ≤ ∫ s in a..b, lRegularizedSpeedSq S T alpha s := by
    apply intervalIntegral.integral_nonneg hab
    intro s _hs
    exact lRegularizedSpeedSq_nonneg (I := I) S T alpha s
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [PseudoMetricSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem lRegularizedAction_ge_riemannianEDistOf_sq_div
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {tau : ℝ} (htau : 0 < tau) (g : SmoothRiemannianMetric I M)
    (htime : ∀ s ∈ Icc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc 0 (Real.sqrt tau), ∀ z : M, ∀ v : TangentSpace I z,
      g.inner z v v ≤ (S.base.metric (T - s ^ 2)).inner z v v)
    (hscalar : ∀ s ∈ Icc 0 (Real.sqrt tau), ∀ z : M,
      0 ≤ S.scalar (T - s ^ 2) z) :
    (riemannianEDistOf (I := I) g (alpha 0) (alpha (Real.sqrt tau))).toReal ^ 2 /
        (2 * Real.sqrt tau) ≤ lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g halpha.contMDiffOn
    (a := 0) (b := Real.sqrt tau)
  have href : IntervalIntegrable
      (fun s => g.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) volume 0 (Real.sqrt tau) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hb.le, lVelocity] using hE
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha)
      volume 0 (Real.sqrt tau) := by
    have hcont := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    have hcurve := hcont.comp (s := Icc 0 (Real.sqrt tau))
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => htime s hs)
    exact hcurve.intervalIntegrable_of_Icc hb.le
  have hcoerc := lRegularizedAction_ge_reference_energy_add_constant S T alpha g
    0 (Real.sqrt tau) 1 0 hb.le
    (fun s hs => by simpa only [one_mul] using hmetric s hs (alpha s) (lVelocity alpha s))
    (fun s hs => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s))
      (hscalar s hs (alpha s))) href hLag
  have henergy : curveEnergy g alpha 0 (Real.sqrt tau) ≤
      2 * lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
    simp only [zero_mul, add_zero, intervalIntegral.integral_const_mul] at hcoerc
    change (1 / 2 : ℝ) * curveEnergy g alpha 0 (Real.sqrt tau) ≤ _ at hcoerc
    linarith
  have hdist := riemannianEDistOf_toReal_sq_le_curveEnergy g hb.le halpha.contMDiffOn hE
  rw [sub_zero] at hdist
  have hbound := hdist.trans (mul_le_mul_of_nonneg_left henergy hb.le)
  apply (div_le_iff₀ (show 0 < 2 * Real.sqrt tau by positivity)).mpr
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lCost_ge_riemannianEDistOf_sq_div
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x y : M) {tau : ℝ} (htau : 0 < tau)
    (g : SmoothRiemannianMetric I M)
    (htime : ∀ s ∈ Icc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc 0 (Real.sqrt tau), ∀ z : M, ∀ v : TangentSpace I z,
      g.inner z v v ≤ (S.base.metric (T - s ^ 2)).inner z v v)
    (hscalar : ∀ s ∈ Icc 0 (Real.sqrt tau), ∀ z : M,
      0 ≤ S.scalar (T - s ^ 2) z) :
    (riemannianEDistOf (I := I) g x y).toReal ^ 2 / (2 * Real.sqrt tau) ≤
      lCost S T x y tau := by
  by_contra hnot
  obtain ⟨alpha, halpha, h0, hbEnd, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T x y tau htau
      ((riemannianEDistOf (I := I) g x y).toReal ^ 2 / (2 * Real.sqrt tau))
      (lt_of_not_ge hnot)
  have hbound := lRegularizedAction_ge_riemannianEDistOf_sq_div S hS T alpha halpha
    htau g htime hmetric hscalar
  rw [h0, hbEnd] at hbound
  exact (not_lt_of_ge hbound) hact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
end

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private theorem lRegularizedAction_ge_of_scalar_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (γ : ℝ → M)
    {a b B : ℝ} (hab : a ≤ b)
    (hscalar : ∀ t ∈ Ioo a b, -B ≤ S.scalar (T - t ^ 2) (γ t))
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) volume a b) :
    -(2 * B / 3) * (b ^ 3 - a ^ 3) ≤ lRegularizedAction S T γ a b := by
  have hh := intervalIntegral.integral_ge_of_mul_sq_le hab hint (C := -(2 * B)) (fun t ht => ?_)
  · simpa only [neg_div, lRegularizedAction] using hh
  have hs := mul_le_mul_of_nonneg_left (hscalar t ht) (by positivity : 0 ≤ 2 * t ^ 2)
  have hk := lRegularizedSpeedSq_nonneg S T γ t
  change -(2 * B) * t ^ 2 ≤ _
  dsimp only [lRegularizedLagrangian, lRegularizedSpeedSq] at hk ⊢
  nlinarith


variable [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedCosts_bdd_of_scalar_lower
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b B : ℝ} (hab : a ≤ b)
    (htime : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    (hscalar : ∀ t ∈ Ioo a b, ∀ z : M, -B ≤ S.scalar (T - t ^ 2) z)
    (x y : M) :
    BddBelow {r : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α a = x ∧ α b = y ∧ lRegularizedAction S T α a b = r} := by
  refine ⟨-(2 * B / 3) * (b ^ 3 - a ^ 3), ?_⟩
  rintro r ⟨α, hα, _, _, rfl⟩
  have hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
    have hc := lRegularizedLagrangian_continuousOn_carrier (I := I) S hS α hα
    have hm : ContinuousOn (fun r : ℝ => (T, r)) (Icc a b) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : MapsTo (fun r : ℝ => (T, r)) (Icc a b)
        {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := htime
    exact (hc.comp (f := fun r : ℝ => (T, r)) hm hmap).intervalIntegrable_of_Icc hab
  exact lRegularizedAction_ge_of_scalar_lower_bound (I := I) (M := M) S T α hab
    (fun t ht => hscalar t ht (α t)) hint


end DifferentialGeometry.PDE.RicciFlow.Perelman

end
